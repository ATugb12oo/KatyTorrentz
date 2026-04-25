"""
KatyTorrentz
============

A standalone "AI torrent sharing" style program with an EVM settlement lane.

This app is intentionally self-contained (stdlib only) and provides:
- bencode + .torrent metadata parsing
- piece hashing and a minimal storage layout
- a peer simulation transport (for local testing) and a wire-like message codec
- an "AI-ish" piece picker that adapts based on observed peer behavior
- a small HTTP JSON API for controlling swarms and reading status
- an EVM client stub that can submit/track transactions (offline-sign simulation)

Notes:
- Real BitTorrent is complex. This is a pragmatic, runnable toolkit that mirrors
  the high-level torrent flow and exposes a clean architecture.
- EVM interaction is implemented as a pluggable adapter. By default, it runs in
  "dry-run" mode using local keccak-like hashing and deterministic tx ids.
"""

from __future__ import annotations

import argparse
import asyncio
import base64
import dataclasses
import datetime as _dt
import functools
import hashlib
import hmac
import http.server
import io
import json
import logging
import os
import random
import secrets
import signal
import socket
import sqlite3
import string
import struct
import sys
import threading
import time
import traceback
import typing as t
import urllib.parse
import uuid


LOG = logging.getLogger("KatyTorrentz")


# ---------------------------------------------------------------------------
# Utilities
# ---------------------------------------------------------------------------


def utc_now() -> _dt.datetime:
    return _dt.datetime.now(tz=_dt.timezone.utc)


def clamp(v: float, lo: float, hi: float) -> float:
    if v < lo:
        return lo
    if v > hi:
        return hi
    return v


def human_bytes(n: int) -> str:
    units = ["B", "KiB", "MiB", "GiB", "TiB"]
    f = float(n)
    for u in units:
        if f < 1024.0:
            return f"{f:.2f} {u}"
        f /= 1024.0
    return f"{f:.2f} PiB"


def sha1(data: bytes) -> bytes:
    return hashlib.sha1(data).digest()


def sha256(data: bytes) -> bytes:
    return hashlib.sha256(data).digest()


def rand_hex(nbytes: int) -> str:
    return secrets.token_hex(nbytes)


def stable_json(obj: t.Any) -> str:
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def now_ms() -> int:
    return int(time.time() * 1000)


def parse_bool(s: str) -> bool:
    s2 = s.strip().lower()
    if s2 in {"1", "true", "t", "yes", "y", "on"}:
        return True
    if s2 in {"0", "false", "f", "no", "n", "off"}:
        return False
    raise ValueError(f"Invalid bool: {s!r}")


def random_peer_id() -> bytes:
    # 20-byte peer id, "KT" prefix.
    body = secrets.token_bytes(18)
    return b"KT" + body


def random_listen_port() -> int:
    return random.randint(12_000, 52_000)


def b64(b: bytes) -> str:
    return base64.b64encode(b).decode("ascii")


def b64d(s: str) -> bytes:
    return base64.b64decode(s.encode("ascii"))


class KatyError(RuntimeError):
    pass


class BencodeError(KatyError):
    pass


class TorrentError(KatyError):
    pass


class StorageError(KatyError):
    pass


class ProtocolError(KatyError):
    pass


class EVMError(KatyError):
    pass


# ---------------------------------------------------------------------------
# Bencode
# ---------------------------------------------------------------------------


def bencode(obj: t.Any) -> bytes:
    if isinstance(obj, int):
        return b"i" + str(obj).encode("ascii") + b"e"
    if isinstance(obj, bytes):
        return str(len(obj)).encode("ascii") + b":" + obj
    if isinstance(obj, str):
        b = obj.encode("utf-8")
        return str(len(b)).encode("ascii") + b":" + b
    if isinstance(obj, list):
        return b"l" + b"".join(bencode(x) for x in obj) + b"e"
    if isinstance(obj, dict):
        # keys must be bytes/str
        items: list[tuple[bytes, t.Any]] = []
        for k, v in obj.items():
            if isinstance(k, bytes):
                kb = k
            elif isinstance(k, str):
                kb = k.encode("utf-8")
            else:
                raise BencodeError(f"invalid dict key type: {type(k)}")
            items.append((kb, v))
        items.sort(key=lambda kv: kv[0])
        out = [b"d"]
        for kb, v in items:
            out.append(str(len(kb)).encode("ascii"))
            out.append(b":")
            out.append(kb)
            out.append(bencode(v))
        out.append(b"e")
        return b"".join(out)
    raise BencodeError(f"cannot bencode type: {type(obj)}")


def bdecode(data: bytes) -> t.Any:
    idx = 0

    def peek() -> int:
        nonlocal idx
        if idx >= len(data):
            raise BencodeError("unexpected EOF")
        return data[idx]

    def take(n: int) -> bytes:
        nonlocal idx
        if idx + n > len(data):
            raise BencodeError("unexpected EOF")
        b = data[idx : idx + n]
        idx += n
        return b

    def parse_int() -> int:
        nonlocal idx
        if take(1) != b"i":
            raise BencodeError("expected 'i'")
        end = data.find(b"e", idx)
        if end < 0:
            raise BencodeError("unterminated int")
        raw = data[idx:end]
        idx = end + 1
        try:
            return int(raw.decode("ascii"))
        except Exception as e:
            raise BencodeError(f"bad int: {raw!r}") from e

    def parse_bytes() -> bytes:
        nonlocal idx
        colon = data.find(b":", idx)
        if colon < 0:
            raise BencodeError("missing ':'")
        raw_len = data[idx:colon]
        try:
            ln = int(raw_len.decode("ascii"))
        except Exception as e:
            raise BencodeError(f"bad length: {raw_len!r}") from e
        idx = colon + 1
        return take(ln)

    def parse_list() -> list[t.Any]:
        if take(1) != b"l":
            raise BencodeError("expected 'l'")
        out: list[t.Any] = []
        while True:
            if peek() == ord("e"):
                take(1)
                return out
            out.append(parse_any())

    def parse_dict() -> dict[bytes, t.Any]:
        if take(1) != b"d":
            raise BencodeError("expected 'd'")
        out: dict[bytes, t.Any] = {}
        while True:
            if peek() == ord("e"):
                take(1)
                return out
            k = parse_bytes()
            v = parse_any()
            out[k] = v

    def parse_any() -> t.Any:
        c = peek()
        if c == ord("i"):
            return parse_int()
        if c == ord("l"):
            return parse_list()
        if c == ord("d"):
            return parse_dict()
        if 48 <= c <= 57:
            return parse_bytes()
        raise BencodeError(f"unexpected byte {c!r} at offset {idx}")

    obj = parse_any()
    if idx != len(data):
        raise BencodeError(f"trailing data at {idx}/{len(data)}")
    return obj


def torrent_info_hash(info_dict_bencode: bytes) -> bytes:
    # Standard BitTorrent info-hash is SHA1 of bencoded info dict.
    return sha1(info_dict_bencode)


def decode_str(x: bytes) -> str:
    try:
        return x.decode("utf-8")
    except Exception:
        return x.decode("latin-1", errors="replace")


# ---------------------------------------------------------------------------
# Torrent metadata
# ---------------------------------------------------------------------------


@dataclasses.dataclass(frozen=True)
class FileEntry:
    path: str
    length: int


@dataclasses.dataclass(frozen=True)
class TorrentInfo:
    name: str
    piece_length: int
    pieces: list[bytes]  # list of 20-byte SHA1 hashes
    files: list[FileEntry]
    info_hash: bytes
    raw_info_bencode: bytes

    @property
    def total_length(self) -> int:
        return sum(f.length for f in self.files)

    @property
    def piece_count(self) -> int:
        return len(self.pieces)


def parse_torrent_file(path: str) -> TorrentInfo:
    raw = open(path, "rb").read()
    meta = bdecode(raw)
    if not isinstance(meta, dict):
        raise TorrentError("torrent root must be dict")
    if b"info" not in meta:
        raise TorrentError("missing info dict")
    info = meta[b"info"]
    if not isinstance(info, dict):
        raise TorrentError("info must be dict")

    raw_info = bencode(info)
    ih = torrent_info_hash(raw_info)

    name_b = info.get(b"name", b"")
    if not isinstance(name_b, (bytes, bytearray)):
        raise TorrentError("bad name")
    name = decode_str(bytes(name_b)) or f"unnamed-{ih.hex()[:10]}"

    pl = info.get(b"piece length")
    if not isinstance(pl, int) or pl <= 0:
        raise TorrentError("bad piece length")

    pieces_blob = info.get(b"pieces")
    if not isinstance(pieces_blob, (bytes, bytearray)):
        raise TorrentError("bad pieces")
    pieces_blob = bytes(pieces_blob)
    if len(pieces_blob) % 20 != 0:
        raise TorrentError("pieces length must be multiple of 20")
    pieces = [pieces_blob[i : i + 20] for i in range(0, len(pieces_blob), 20)]

    files: list[FileEntry] = []
    if b"files" in info:
        fl = info[b"files"]
        if not isinstance(fl, list):
            raise TorrentError("files must be list")
        for e in fl:
            if not isinstance(e, dict):
                raise TorrentError("file entry must be dict")
            ln = e.get(b"length")
            if not isinstance(ln, int) or ln < 0:
                raise TorrentError("bad file length")
            p = e.get(b"path")
            if not isinstance(p, list) or not p:
                raise TorrentError("bad file path")
            parts: list[str] = []
            for part in p:
                if not isinstance(part, (bytes, bytearray)):
                    raise TorrentError("bad path part")
                parts.append(decode_str(bytes(part)))
            files.append(FileEntry(path=os.path.join(*parts), length=ln))
    else:
        ln = info.get(b"length")
        if not isinstance(ln, int) or ln < 0:
            raise TorrentError("bad length")
        files.append(FileEntry(path=name, length=ln))

    return TorrentInfo(
        name=name,
        piece_length=int(pl),
        pieces=pieces,
        files=files,
        info_hash=ih,
        raw_info_bencode=raw_info,
    )


# ---------------------------------------------------------------------------
# Piece storage & integrity
# ---------------------------------------------------------------------------


class PieceMap:
    def __init__(self, piece_count: int):
        self._n = piece_count
        self._bits = bytearray((piece_count + 7) // 8)

    def have(self, idx: int) -> bool:
        if idx < 0 or idx >= self._n:
            raise IndexError(idx)
        b = self._bits[idx // 8]
        return bool(b & (1 << (idx % 8)))

    def set_have(self, idx: int, v: bool = True) -> None:
        if idx < 0 or idx >= self._n:
            raise IndexError(idx)
        byte_i = idx // 8
        mask = 1 << (idx % 8)
        if v:
            self._bits[byte_i] |= mask
        else:
            self._bits[byte_i] &= (~mask) & 0xFF

    def count(self) -> int:
        return sum(bin(b).count("1") for b in self._bits)

    def to_bytes(self) -> bytes:
        return bytes(self._bits)

    @classmethod
    def from_bytes(cls, piece_count: int, data: bytes) -> "PieceMap":
        pm = cls(piece_count)
        pm._bits[:] = data[: len(pm._bits)]
        return pm


class PieceStore:
    def __init__(self, base_dir: str, info_hash: bytes, piece_length: int, piece_count: int):
        self.base_dir = base_dir
        self.info_hash = info_hash
        self.piece_length = piece_length
        self.piece_count = piece_count
        self._dir = os.path.join(base_dir, "pieces", info_hash.hex())
        os.makedirs(self._dir, exist_ok=True)

    def _piece_path(self, idx: int) -> str:
        if idx < 0 or idx >= self.piece_count:
            raise StorageError(f"piece index out of range: {idx}")
        return os.path.join(self._dir, f"{idx:06d}.bin")

    def has_piece(self, idx: int) -> bool:
        return os.path.exists(self._piece_path(idx))

    def read_piece(self, idx: int) -> bytes:
        p = self._piece_path(idx)
        try:
            return open(p, "rb").read()
        except FileNotFoundError:
            raise StorageError(f"missing piece: {idx}")

    def write_piece(self, idx: int, data: bytes) -> None:
        if len(data) > self.piece_length:
            raise StorageError("piece too long")
        p = self._piece_path(idx)
        tmp = p + f".tmp-{uuid.uuid4().hex}"
        with open(tmp, "wb") as f:
            f.write(data)
        os.replace(tmp, p)

    def verify_piece(self, idx: int, data: bytes, expected_sha1: bytes) -> bool:
        if len(expected_sha1) != 20:
            raise StorageError("expected sha1 must be 20 bytes")
        return sha1(data) == expected_sha1


# ---------------------------------------------------------------------------
# SQLite state
# ---------------------------------------------------------------------------


SCHEMA = """
PRAGMA journal_mode=WAL;
PRAGMA foreign_keys=ON;

CREATE TABLE IF NOT EXISTS torrents (
  info_hash TEXT PRIMARY KEY,
  name TEXT NOT NULL,
  created_at INTEGER NOT NULL,
  piece_length INTEGER NOT NULL,
  piece_count INTEGER NOT NULL,
  total_length INTEGER NOT NULL,
  raw_info_b64 TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS pieces (
  info_hash TEXT NOT NULL,
  idx INTEGER NOT NULL,
  have INTEGER NOT NULL,
  verified INTEGER NOT NULL,
  last_write_ms INTEGER NOT NULL,
  PRIMARY KEY (info_hash, idx),
  FOREIGN KEY(info_hash) REFERENCES torrents(info_hash) ON DELETE CASCADE
);

CREATE TABLE IF NOT EXISTS peers (
  info_hash TEXT NOT NULL,
  peer_key TEXT NOT NULL,
  addr TEXT NOT NULL,
  port INTEGER NOT NULL,
  last_seen_ms INTEGER NOT NULL,
  score REAL NOT NULL,
  flags INTEGER NOT NULL,
  PRIMARY KEY (info_hash, peer_key),
  FOREIGN KEY(info_hash) REFERENCES torrents(info_hash) ON DELETE CASCADE
);

CREATE TABLE IF NOT EXISTS receipts (
  id TEXT PRIMARY KEY,
  info_hash TEXT NOT NULL,
  kind TEXT NOT NULL,
  created_ms INTEGER NOT NULL,
  piece_idx INTEGER NOT NULL,
  amount INTEGER NOT NULL,
  digest_hex TEXT NOT NULL,
  status TEXT NOT NULL,
  tx_id TEXT,
  FOREIGN KEY(info_hash) REFERENCES torrents(info_hash) ON DELETE CASCADE
);

CREATE TABLE IF NOT EXISTS kv (
  k TEXT PRIMARY KEY,
  v TEXT NOT NULL
);
"""


class StateDB:
    def __init__(self, path: str):
        self.path = path
        self._conn = sqlite3.connect(path, check_same_thread=False)
        self._conn.row_factory = sqlite3.Row
        self._lock = threading.RLock()
        self._apply_schema()

    def _apply_schema(self) -> None:
        with self._conn:
            self._conn.executescript(SCHEMA)

    def close(self) -> None:
        with self._lock:
            self._conn.close()

    def set_kv(self, k: str, v: str) -> None:
        with self._lock, self._conn:
            self._conn.execute("INSERT INTO kv(k,v) VALUES(?,?) ON CONFLICT(k) DO UPDATE SET v=excluded.v", (k, v))

    def get_kv(self, k: str, default: str | None = None) -> str | None:
        with self._lock:
            row = self._conn.execute("SELECT v FROM kv WHERE k=?", (k,)).fetchone()
            if not row:
                return default
            return t.cast(str, row["v"])

    def add_torrent(self, ti: TorrentInfo) -> None:
        with self._lock, self._conn:
            ih = ti.info_hash.hex()
            self._conn.execute(
                "INSERT OR REPLACE INTO torrents(info_hash,name,created_at,piece_length,piece_count,total_length,raw_info_b64) VALUES(?,?,?,?,?,?,?)",
                (
                    ih,
                    ti.name,
                    int(time.time()),
                    ti.piece_length,
                    ti.piece_count,
                    ti.total_length,
                    b64(ti.raw_info_bencode),
                ),
            )
            rows = [(ih, i, 0, 0, 0) for i in range(ti.piece_count)]
            self._conn.executemany(
                "INSERT OR IGNORE INTO pieces(info_hash,idx,have,verified,last_write_ms) VALUES(?,?,?,?,?)",
                rows,
            )

    def list_torrents(self) -> list[dict[str, t.Any]]:
        with self._lock:
            rows = self._conn.execute("SELECT * FROM torrents ORDER BY created_at DESC").fetchall()
            out: list[dict[str, t.Any]] = []
            for r in rows:
                out.append(dict(r))
            return out

    def get_torrent(self, info_hash_hex: str) -> dict[str, t.Any] | None:
        with self._lock:
            r = self._conn.execute("SELECT * FROM torrents WHERE info_hash=?", (info_hash_hex,)).fetchone()
            return dict(r) if r else None

    def update_piece(self, info_hash_hex: str, idx: int, have: bool, verified: bool) -> None:
        with self._lock, self._conn:
            self._conn.execute(
                "UPDATE pieces SET have=?, verified=?, last_write_ms=? WHERE info_hash=? AND idx=?",
                (1 if have else 0, 1 if verified else 0, now_ms(), info_hash_hex, idx),
            )

    def piece_map(self, info_hash_hex: str, piece_count: int) -> PieceMap:
        with self._lock:
            rows = self._conn.execute("SELECT idx,have FROM pieces WHERE info_hash=? ORDER BY idx ASC", (info_hash_hex,)).fetchall()
            pm = PieceMap(piece_count)
            for r in rows:
                if int(r["have"]) == 1:
                    pm.set_have(int(r["idx"]), True)
            return pm

    def peer_touch(self, info_hash_hex: str, peer_key: str, addr: str, port: int, score: float, flags: int) -> None:
        with self._lock, self._conn:
            self._conn.execute(
                "INSERT INTO peers(info_hash,peer_key,addr,port,last_seen_ms,score,flags) VALUES(?,?,?,?,?,?,?) "
                "ON CONFLICT(info_hash,peer_key) DO UPDATE SET addr=excluded.addr, port=excluded.port, last_seen_ms=excluded.last_seen_ms, score=excluded.score, flags=excluded.flags",
                (info_hash_hex, peer_key, addr, port, now_ms(), float(score), int(flags)),
            )

    def list_peers(self, info_hash_hex: str, limit: int = 200) -> list[dict[str, t.Any]]:
        with self._lock:
            rows = self._conn.execute(
                "SELECT * FROM peers WHERE info_hash=? ORDER BY last_seen_ms DESC LIMIT ?",
                (info_hash_hex, int(limit)),
            ).fetchall()
            return [dict(r) for r in rows]

    def add_receipt(self, receipt_id: str, info_hash_hex: str, kind: str, piece_idx: int, amount: int, digest_hex: str) -> None:
        with self._lock, self._conn:
            self._conn.execute(
                "INSERT INTO receipts(id,info_hash,kind,created_ms,piece_idx,amount,digest_hex,status,tx_id) VALUES(?,?,?,?,?,?,?,?,?)",
                (receipt_id, info_hash_hex, kind, now_ms(), int(piece_idx), int(amount), digest_hex, "queued", None),
            )

    def list_receipts(self, info_hash_hex: str, limit: int = 200) -> list[dict[str, t.Any]]:
        with self._lock:
            rows = self._conn.execute(
                "SELECT * FROM receipts WHERE info_hash=? ORDER BY created_ms DESC LIMIT ?",
                (info_hash_hex, int(limit)),
            ).fetchall()
            return [dict(r) for r in rows]

    def set_receipt_status(self, receipt_id: str, status: str, tx_id: str | None = None) -> None:
        with self._lock, self._conn:
            self._conn.execute("UPDATE receipts SET status=?, tx_id=? WHERE id=?", (status, tx_id, receipt_id))


# ---------------------------------------------------------------------------
# Peer protocol simulation
# ---------------------------------------------------------------------------


@dataclasses.dataclass
class PeerIdentity:
    peer_id: bytes
    key: str
    addr: str
    port: int


class MessageCodec:
    """
    A minimal length-prefixed codec inspired by BT messages.
    Frame = uint32_be_len | payload
    payload = json bytes
    """

    @staticmethod
    def encode(obj: dict[str, t.Any]) -> bytes:
        payload = stable_json(obj).encode("utf-8")
        return struct.pack(">I", len(payload)) + payload

    @staticmethod
    def decode_stream(buf: bytearray) -> list[dict[str, t.Any]]:
        out: list[dict[str, t.Any]] = []
        while True:
            if len(buf) < 4:
                return out
            (ln,) = struct.unpack(">I", buf[:4])
            if ln < 2 or ln > 2_000_000:
                raise ProtocolError(f"frame length out of range: {ln}")
            if len(buf) < 4 + ln:
                return out
            payload = bytes(buf[4 : 4 + ln])
            del buf[: 4 + ln]
            try:
                out.append(json.loads(payload.decode("utf-8")))
            except Exception as e:
                raise ProtocolError("bad json frame") from e


@dataclasses.dataclass
class PeerStats:
    seen_ms: int = 0
    good_pieces: int = 0
    bad_pieces: int = 0
    bytes_sent: int = 0
    bytes_recv: int = 0
    rtt_ms_ema: float = 0.0
    trust: float = 0.5

    def score(self) -> float:
        penalty = (self.bad_pieces * 1.7) + (max(0, self.bad_pieces - self.good_pieces) * 0.8)
        base = self.trust + (self.good_pieces * 0.05) - (penalty * 0.09)
        latency_bonus = 0.0
        if self.rtt_ms_ema > 0:
            latency_bonus = clamp(700.0 / (self.rtt_ms_ema + 200.0), 0.0, 1.2) * 0.12
        return clamp(base + latency_bonus, 0.0, 1.0)

    def update_rtt(self, sample_ms: float) -> None:
        if self.rtt_ms_ema <= 0:
            self.rtt_ms_ema = float(sample_ms)
        else:
            self.rtt_ms_ema = (self.rtt_ms_ema * 0.82) + (float(sample_ms) * 0.18)


class AIChooser:
    """
    A lightweight policy that behaves like an "AI piece picker":
    - favors rare pieces (based on announced availability)
    - favors pieces likely to complete soon (near-endgame)
    - adapts to peer trust and observed bad data rate
    """

    def __init__(self, piece_count: int):
        self.piece_count = piece_count
        self.rarity = [1.0 for _ in range(piece_count)]
        self.heat = [0.0 for _ in range(piece_count)]
        self._last_update_ms = 0

    def update_rarity(self, availability: list[int]) -> None:
        if len(availability) != self.piece_count:
            raise ValueError("availability length mismatch")
        for i, a in enumerate(availability):
            # Inverse rarity with smoothing
            inv = 1.0 / (1.0 + float(a))
            self.rarity[i] = (self.rarity[i] * 0.7) + (inv * 0.3)
        self._last_update_ms = now_ms()

    def mark_hot(self, idx: int, delta: float) -> None:
        self.heat[idx] = clamp(self.heat[idx] + float(delta), 0.0, 1.0)

    def pick(self, have: PieceMap, in_flight: set[int], availability: list[int]) -> int | None:
        self.update_rarity(availability)
        best_idx = None
        best_score = -1.0
        remaining = have._n - have.count()
        endgame = remaining <= max(12, have._n // 60)
        for idx in range(self.piece_count):
            if have.have(idx) or idx in in_flight:
                continue
            a = availability[idx]
            rare = self.rarity[idx]
            hot = self.heat[idx]
            # The scoring shape intentionally differs from "typical" piece pickers.
            s = (rare * (1.1 + (0.2 if endgame else 0.0))) + (hot * 0.35) + (1.0 / (2.0 + a)) * 0.15
            if endgame and a > 0:
                s += 0.08
            if s > best_score:
                best_score = s
                best_idx = idx
        return best_idx


# ---------------------------------------------------------------------------
# EVM adapter (dry run)
# ---------------------------------------------------------------------------


@dataclasses.dataclass
class TxResult:
    tx_id: str
    submitted_ms: int
    confirmed_ms: int | None
    status: str
    payload: dict[str, t.Any]


class EVMClient:
    """
    A pragmatic EVM lane.

    - If you want real chain interaction, you can implement another adapter that
      uses web3.py or eth-account. This file sticks to stdlib and runs anywhere.
    - It still provides deterministic tx ids and a confirmation scheduler so the
      rest of the app behaves like a real system.
    """

    def __init__(self, chain_id: int, contract_address: str, signer_tag: str, confirm_delay_s: float = 1.8):
        self.chain_id = int(chain_id)
        self.contract_address = contract_address
        self.signer_tag = signer_tag
        self.confirm_delay_s = float(confirm_delay_s)
        self._lock = threading.RLock()
        self._txs: dict[str, TxResult] = {}

    def _txid(self, payload: dict[str, t.Any]) -> str:
        seed = stable_json({"chain": self.chain_id, "to": self.contract_address, "sig": self.signer_tag, "p": payload})
        h = sha256(seed.encode("utf-8")).hex()
        return "0x" + h[:64]

    def submit(self, payload: dict[str, t.Any]) -> TxResult:
        tx_id = self._txid(payload)
        with self._lock:
            if tx_id in self._txs:
                return self._txs[tx_id]
            tr = TxResult(tx_id=tx_id, submitted_ms=now_ms(), confirmed_ms=None, status="pending", payload=payload)
            self._txs[tx_id] = tr
        threading.Thread(target=self._confirm_later, args=(tx_id,), daemon=True).start()
        return tr

    def _confirm_later(self, tx_id: str) -> None:
        time.sleep(self.confirm_delay_s + random.random() * 0.6)
        with self._lock:
            tr = self._txs.get(tx_id)
            if not tr or tr.status != "pending":
                return
            tr.status = "confirmed"
            tr.confirmed_ms = now_ms()

    def get(self, tx_id: str) -> TxResult | None:
        with self._lock:
            return self._txs.get(tx_id)

    def list_recent(self, limit: int = 100) -> list[TxResult]:
        with self._lock:
            xs = sorted(self._txs.values(), key=lambda r: r.submitted_ms, reverse=True)
            return xs[: int(limit)]


# ---------------------------------------------------------------------------
# Swarm runtime
# ---------------------------------------------------------------------------


@dataclasses.dataclass
class SwarmConfig:
    announce_interval_s: float = 8.5
    request_timeout_s: float = 4.2
    max_in_flight: int = 9
    max_peer_conns: int = 14
    receipt_amount: int = 12_000  # in "wei-like" units for the dry EVM lane


@dataclasses.dataclass
class InFlightReq:
    idx: int
    peer_key: str
    sent_ms: int


class Swarm:
    def __init__(
        self,
        ti: TorrentInfo,
        db: StateDB,
        store: PieceStore,
        evm: EVMClient,
        cfg: SwarmConfig,
    ):
        self.ti = ti
        self.db = db
        self.store = store
        self.evm = evm
        self.cfg = cfg

        self._have = db.piece_map(ti.info_hash.hex(), ti.piece_count)
        self._availability = [0 for _ in range(ti.piece_count)]
        self._chooser = AIChooser(ti.piece_count)
        self._peer_stats: dict[str, PeerStats] = {}
        self._in_flight: dict[int, InFlightReq] = {}
        self._stop = asyncio.Event()
        self._tasks: list[asyncio.Task[t.Any]] = []

        self._local_peer = PeerIdentity(
            peer_id=random_peer_id(),
            key=secrets.token_hex(10),
            addr="127.0.0.1",
            port=random_listen_port(),
        )
        self._sim_net = SimNetwork.get()
        self._sim_net.register(self.ti.info_hash.hex(), self._local_peer, self)

    @property
    def info_hash_hex(self) -> str:
        return self.ti.info_hash.hex()

    def stats_snapshot(self) -> dict[str, t.Any]:
        have_cnt = self._have.count()
        return {
            "name": self.ti.name,
            "info_hash": self.info_hash_hex,
            "piece_length": self.ti.piece_length,
            "piece_count": self.ti.piece_count,
            "total_length": self.ti.total_length,
            "have_pieces": have_cnt,
            "have_percent": (have_cnt / max(1, self.ti.piece_count)) * 100.0,
            "in_flight": len(self._in_flight),
            "peers_known": len(self._peer_stats),
            "bytes_stored_dir": self.store._dir,
        }

    async def start(self) -> None:
        if self._tasks:
            return
        self._tasks = [
            asyncio.create_task(self._tick_announce(), name=f"announce:{self.info_hash_hex[:8]}"),
            asyncio.create_task(self._tick_requests(), name=f"requests:{self.info_hash_hex[:8]}"),
            asyncio.create_task(self._tick_timeouts(), name=f"timeouts:{self.info_hash_hex[:8]}"),
        ]

    async def stop(self) -> None:
        self._stop.set()
        for tsk in list(self._tasks):
            tsk.cancel()
        await asyncio.gather(*self._tasks, return_exceptions=True)
        self._tasks.clear()

    # --- peer simulation callbacks ---

    async def on_message(self, peer: PeerIdentity, msg: dict[str, t.Any]) -> dict[str, t.Any] | None:
        mt = msg.get("t")
        if mt == "announce":
            return await self._on_announce(peer, msg)
        if mt == "req_piece":
            return await self._on_req_piece(peer, msg)
        if mt == "piece":
            return await self._on_piece(peer, msg)
        return {"t": "err", "m": "unknown message"}

    async def _on_announce(self, peer: PeerIdentity, msg: dict[str, t.Any]) -> dict[str, t.Any]:
        pm_b64 = msg.get("have_b64", "")
        try:
            pm = PieceMap.from_bytes(self.ti.piece_count, b64d(pm_b64))
        except Exception:
            pm = PieceMap(self.ti.piece_count)
        self._touch_peer(peer)
        for i in range(self.ti.piece_count):
            if pm.have(i):
                self._availability[i] += 1
        return {"t": "ack", "peer_key": self._local_peer.key, "at_ms": now_ms()}

    async def _on_req_piece(self, peer: PeerIdentity, msg: dict[str, t.Any]) -> dict[str, t.Any]:
        idx = int(msg.get("idx", -1))
        if idx < 0 or idx >= self.ti.piece_count:
            return {"t": "err", "m": "bad idx"}
        if not self._have.have(idx):
            return {"t": "err", "m": "dont_have"}
        self._touch_peer(peer)
        data = self.store.read_piece(idx)
        # send piece; in real BT this would be chunked blocks
        return {
            "t": "piece",
            "idx": idx,
            "data_b64": b64(data),
            "sha1_hex": sha1(data).hex(),
            "sent_ms": now_ms(),
        }

    async def _on_piece(self, peer: PeerIdentity, msg: dict[str, t.Any]) -> dict[str, t.Any]:
        idx = int(msg.get("idx", -1))
        if idx < 0 or idx >= self.ti.piece_count:
            return {"t": "err", "m": "bad idx"}
        data_b64 = msg.get("data_b64", "")
        try:
            data = b64d(data_b64)
        except Exception:
            return {"t": "err", "m": "bad b64"}
        expected = self.ti.pieces[idx]
        good = self.store.verify_piece(idx, data, expected)
        self._touch_peer(peer)

        req = self._in_flight.pop(idx, None)
        if req:
            dt = now_ms() - req.sent_ms
            ps = self._peer_stats.get(peer.key)
            if ps:
                ps.update_rtt(dt)
        ps2 = self._peer_stats.get(peer.key)
        if ps2:
            if good:
                ps2.good_pieces += 1
                ps2.trust = clamp(ps2.trust + 0.035, 0.0, 1.0)
            else:
                ps2.bad_pieces += 1
                ps2.trust = clamp(ps2.trust - 0.11, 0.0, 1.0)
                self._chooser.mark_hot(idx, 0.22)

        if good:
            self.store.write_piece(idx, data)
            self._have.set_have(idx, True)
            self.db.update_piece(self.info_hash_hex, idx, have=True, verified=True)
            self._chooser.mark_hot(idx, -0.12)
            # create a receipt and submit to EVM dry lane
            await self._emit_receipt(kind="seed", piece_idx=idx, piece_sha1=sha1(data))
            return {"t": "ok", "m": "stored", "idx": idx}
        else:
            self.db.update_piece(self.info_hash_hex, idx, have=False, verified=False)
            return {"t": "err", "m": "hash_mismatch", "idx": idx}

    # --- periodic tasks ---

    async def _tick_announce(self) -> None:
        while not self._stop.is_set():
            try:
                await self._announce_to_simnet()
            except asyncio.CancelledError:
                raise
            except Exception:
                LOG.exception("announce tick failed")
            await asyncio.sleep(self.cfg.announce_interval_s + random.random() * 0.9)

    async def _announce_to_simnet(self) -> None:
        pm = self._have.to_bytes()
        msg = {"t": "announce", "peer_key": self._local_peer.key, "have_b64": b64(pm), "at_ms": now_ms()}
        await self._sim_net.broadcast(self.info_hash_hex, self._local_peer, msg)

    async def _tick_requests(self) -> None:
        while not self._stop.is_set():
            try:
                await self._maybe_request()
            except asyncio.CancelledError:
                raise
            except Exception:
                LOG.exception("request tick failed")
            await asyncio.sleep(0.35 + random.random() * 0.18)

    async def _maybe_request(self) -> None:
        if self._have.count() >= self.ti.piece_count:
            return
        if len(self._in_flight) >= self.cfg.max_in_flight:
            return

        peers = sorted(self._peer_stats.items(), key=lambda kv: kv[1].score(), reverse=True)
        if not peers:
            return
        chosen_idx = self._chooser.pick(self._have, set(self._in_flight.keys()), self._availability)
        if chosen_idx is None:
            return
        # choose a peer that likely has it
        for peer_key, ps in peers[: min(len(peers), self.cfg.max_peer_conns)]:
            if ps.score() < 0.15:
                continue
            remote = self._sim_net.resolve_peer(self.info_hash_hex, peer_key)
            if not remote:
                continue
            if not self._sim_net.peer_has_piece(self.info_hash_hex, peer_key, chosen_idx):
                continue
            self._in_flight[chosen_idx] = InFlightReq(idx=chosen_idx, peer_key=peer_key, sent_ms=now_ms())
            self._chooser.mark_hot(chosen_idx, 0.06)
            msg = {"t": "req_piece", "peer_key": self._local_peer.key, "idx": chosen_idx, "at_ms": now_ms()}
            await self._sim_net.send(self.info_hash_hex, self._local_peer, remote, msg)
            return

    async def _tick_timeouts(self) -> None:
        while not self._stop.is_set():
            try:
                self._expire_in_flight()
            except asyncio.CancelledError:
                raise
            except Exception:
                LOG.exception("timeout tick failed")
            await asyncio.sleep(0.6 + random.random() * 0.3)

    def _expire_in_flight(self) -> None:
        dead: list[int] = []
        nowx = now_ms()
        for idx, req in self._in_flight.items():
            if nowx - req.sent_ms > int(self.cfg.request_timeout_s * 1000):
                dead.append(idx)
        for idx in dead:
            req = self._in_flight.pop(idx, None)
            if not req:
                continue
            self._chooser.mark_hot(idx, 0.14)
            ps = self._peer_stats.get(req.peer_key)
            if ps:
                ps.trust = clamp(ps.trust - 0.03, 0.0, 1.0)

    # --- receipt logic ---

    async def _emit_receipt(self, kind: str, piece_idx: int, piece_sha1: bytes) -> None:
        # digest ties piece, info-hash, and local peer key
        digest = sha256(
            stable_json(
                {
                    "v": 1,
                    "kind": kind,
                    "info_hash": self.info_hash_hex,
                    "piece": int(piece_idx),
                    "sha1": piece_sha1.hex(),
                    "peer": self._local_peer.key,
                }
            ).encode("utf-8")
        )
        receipt_id = "rcpt_" + secrets.token_hex(10)
        self.db.add_receipt(receipt_id, self.info_hash_hex, kind, piece_idx, self.cfg.receipt_amount, digest.hex())
        payload = {
            "op": "fileSeedProof",
            "info_hash": self.info_hash_hex,
            "piece": int(piece_idx),
            "digest_hex": digest.hex(),
            "amount": int(self.cfg.receipt_amount),
            "peer_key": self._local_peer.key,
        }
        tr = self.evm.submit(payload)
        self.db.set_receipt_status(receipt_id, "submitted", tr.tx_id)

    # --- peer book ---

    def _touch_peer(self, peer: PeerIdentity) -> None:
        ps = self._peer_stats.get(peer.key)
        if not ps:
            ps = PeerStats(seen_ms=now_ms(), trust=0.5 + random.random() * 0.08)
            self._peer_stats[peer.key] = ps
        ps.seen_ms = now_ms()
        # keep DB in sync
        self.db.peer_touch(self.info_hash_hex, peer.key, peer.addr, peer.port, ps.score(), flags=0)


# ---------------------------------------------------------------------------
# Simulation network (local)
# ---------------------------------------------------------------------------


class SimNetwork:
    _instance: "SimNetwork | None" = None

    @classmethod
    def get(cls) -> "SimNetwork":
        if not cls._instance:
            cls._instance = SimNetwork()
        return cls._instance

    def __init__(self):
        self._lock = threading.RLock()
        self._by_torrent: dict[str, dict[str, tuple[PeerIdentity, Swarm]]] = {}
        self._have_cache: dict[tuple[str, str], bytes] = {}

    def register(self, info_hash_hex: str, peer: PeerIdentity, swarm: Swarm) -> None:
        with self._lock:
            d = self._by_torrent.setdefault(info_hash_hex, {})
            d[peer.key] = (peer, swarm)

    def resolve_peer(self, info_hash_hex: str, peer_key: str) -> PeerIdentity | None:
        with self._lock:
            d = self._by_torrent.get(info_hash_hex) or {}
            v = d.get(peer_key)
            return v[0] if v else None

    async def broadcast(self, info_hash_hex: str, src: PeerIdentity, msg: dict[str, t.Any]) -> None:
        with self._lock:
            peers = list((self._by_torrent.get(info_hash_hex) or {}).values())
        for peer, swarm in peers:
            if peer.key == src.key:
                continue
            await self.send(info_hash_hex, src, peer, msg)

    def peer_has_piece(self, info_hash_hex: str, peer_key: str, idx: int) -> bool:
        with self._lock:
            b = self._have_cache.get((info_hash_hex, peer_key))
            if not b:
                return False
        pm = PieceMap.from_bytes(10_000, b)  # oversized; only first bytes are used
        try:
            return pm.have(idx)
        except Exception:
            return False

    async def send(self, info_hash_hex: str, src: PeerIdentity, dst: PeerIdentity, msg: dict[str, t.Any]) -> None:
        await asyncio.sleep(0.02 + random.random() * 0.09)
        with self._lock:
            d = self._by_torrent.get(info_hash_hex) or {}
            pair = d.get(dst.key)
        if not pair:
            return
        _, swarm = pair
        # keep have cache updated from announce messages
        if msg.get("t") == "announce":
            try:
                pm_b = b64d(t.cast(str, msg.get("have_b64", "")))
                with self._lock:
                    self._have_cache[(info_hash_hex, t.cast(str, msg.get("peer_key", "")))] = pm_b
            except Exception:
                pass
        resp = await swarm.on_message(src, msg)
        if resp and resp.get("t") == "piece":
            # deliver piece response back to requester
            with self._lock:
                req_pair = d.get(src.key)
            if req_pair:
                _, src_swarm = req_pair
                await asyncio.sleep(0.02 + random.random() * 0.07)
                await src_swarm.on_message(dst, resp)


# ---------------------------------------------------------------------------
# HTTP API
# ---------------------------------------------------------------------------


class ApiServer(http.server.ThreadingHTTPServer):
    daemon_threads = True


class ApiHandler(http.server.BaseHTTPRequestHandler):
    server: "KatyAppServer"  # type: ignore[assignment]

    def _send(self, status: int, obj: t.Any) -> None:
        raw = (stable_json(obj) + "\n").encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(raw)))
        self.end_headers()
        self.wfile.write(raw)

    def _read_json(self) -> dict[str, t.Any]:
        ln = int(self.headers.get("Content-Length", "0") or "0")
        if ln <= 0 or ln > 2_000_000:
            return {}
        raw = self.rfile.read(ln)
        try:
            return t.cast(dict[str, t.Any], json.loads(raw.decode("utf-8")))
        except Exception:
            return {}

    def log_message(self, fmt: str, *args: t.Any) -> None:
        LOG.info("api %s - %s", self.address_string(), fmt % args)

    def do_GET(self) -> None:
        try:
            self._route("GET")
        except Exception as e:
            LOG.error("api error: %s", e)
            self._send(500, {"ok": False, "error": str(e), "trace": traceback.format_exc()})

    def do_POST(self) -> None:
        try:
            self._route("POST")
        except Exception as e:
            LOG.error("api error: %s", e)
            self._send(500, {"ok": False, "error": str(e), "trace": traceback.format_exc()})

    def _route(self, method: str) -> None:
        u = urllib.parse.urlparse(self.path)
        path = u.path.rstrip("/") or "/"
        qs = urllib.parse.parse_qs(u.query)

        if method == "GET" and path == "/health":
            self._send(200, {"ok": True, "ts": utc_now().isoformat()})
            return

        if method == "GET" and path == "/torrents":
            self._send(200, {"ok": True, "torrents": self.server.app.list_torrents()})
            return

        if method == "GET" and path == "/swarm":
            ih = (qs.get("info_hash") or [""])[0]
            snap = self.server.app.swarm_snapshot(ih)
            if not snap:
                self._send(404, {"ok": False, "error": "not found"})
            else:
                self._send(200, {"ok": True, "swarm": snap})
            return

        if method == "GET" and path == "/peers":
            ih = (qs.get("info_hash") or [""])[0]
            peers = self.server.app.list_peers(ih)
            self._send(200, {"ok": True, "peers": peers})
            return

        if method == "GET" and path == "/receipts":
            ih = (qs.get("info_hash") or [""])[0]
            rs = self.server.app.list_receipts(ih)
            self._send(200, {"ok": True, "receipts": rs})
            return

        if method == "POST" and path == "/add_torrent":
            body = self._read_json()
            p = str(body.get("path", ""))
            if not p:
                self._send(400, {"ok": False, "error": "missing path"})
                return
            ih = self.server.app.add_torrent_from_path(p)
            self._send(200, {"ok": True, "info_hash": ih})
            return

        if method == "POST" and path == "/seed_dummy":
            body = self._read_json()
            ih = str(body.get("info_hash", ""))
            n = int(body.get("pieces", 3))
            self.server.app.seed_dummy_pieces(ih, n)
            self._send(200, {"ok": True})
            return

        self._send(404, {"ok": False, "error": "unknown endpoint"})


class KatyAppServer(ApiServer):
    def __init__(self, addr: tuple[str, int], app: "KatyTorrentzApp"):
        self.app = app
        super().__init__(addr, ApiHandler)


# ---------------------------------------------------------------------------
# App core
# ---------------------------------------------------------------------------


class KatyTorrentzApp:
    def __init__(self, data_dir: str, chain_id: int, contract_addr: str, signer_tag: str):
        self.data_dir = data_dir
        os.makedirs(self.data_dir, exist_ok=True)
        self.db = StateDB(os.path.join(self.data_dir, "katy.db"))
        self.evm = EVMClient(chain_id=chain_id, contract_address=contract_addr, signer_tag=signer_tag)
        self.cfg = SwarmConfig()
        self._swarms: dict[str, Swarm] = {}
        self._loop: asyncio.AbstractEventLoop | None = None

    def close(self) -> None:
        self.db.close()

    def list_torrents(self) -> list[dict[str, t.Any]]:
        return self.db.list_torrents()

    def list_peers(self, info_hash_hex: str) -> list[dict[str, t.Any]]:
        if not info_hash_hex:
            return []
        return self.db.list_peers(info_hash_hex)

    def list_receipts(self, info_hash_hex: str) -> list[dict[str, t.Any]]:
        if not info_hash_hex:
            return []
        return self.db.list_receipts(info_hash_hex)

    def swarm_snapshot(self, info_hash_hex: str) -> dict[str, t.Any] | None:
        s = self._swarms.get(info_hash_hex)
        if not s:
            return None
        out = s.stats_snapshot()
        out["recent_txs"] = [dataclasses.asdict(x) for x in self.evm.list_recent(limit=18)]
        return out

    def add_torrent_from_path(self, torrent_path: str) -> str:
        ti = parse_torrent_file(torrent_path)
        self.db.add_torrent(ti)
        ih = ti.info_hash.hex()
        if ih not in self._swarms:
            store = PieceStore(self.data_dir, ti.info_hash, ti.piece_length, ti.piece_count)
            self._swarms[ih] = Swarm(ti, self.db, store, self.evm, self.cfg)
        return ih

    def seed_dummy_pieces(self, info_hash_hex: str, pieces: int) -> None:
        trow = self.db.get_torrent(info_hash_hex)
        if not trow:
            raise TorrentError("torrent not found")
        raw_info = b64d(t.cast(str, trow["raw_info_b64"]))
        info = t.cast(dict[bytes, t.Any], bdecode(raw_info))
        # reconstruct TorrentInfo using stored data
        piece_length = int(trow["piece_length"])
        piece_count = int(trow["piece_count"])
        name = str(trow["name"])
        # pieces list is not stored in DB; for dummy seeding we generate pseudo pieces
        # that match the hash list in the original torrent. If that's not available,
        # we seed "verified=False" and let the user use a real torrent for full integrity.
        fake_pieces = [sha1(f"{info_hash_hex}:{i}".encode("utf-8")) for i in range(piece_count)]
        ti = TorrentInfo(
            name=name,
            piece_length=piece_length,
            pieces=fake_pieces,
            files=[FileEntry(path=name, length=int(trow["total_length"]))],
            info_hash=bytes.fromhex(info_hash_hex),
            raw_info_bencode=raw_info,
        )
        s = self._swarms.get(info_hash_hex)
        if not s:
            store = PieceStore(self.data_dir, ti.info_hash, ti.piece_length, ti.piece_count)
            s = Swarm(ti, self.db, store, self.evm, self.cfg)
            self._swarms[info_hash_hex] = s
        # write N pieces with deterministic content
        n = max(0, min(int(pieces), ti.piece_count))
        for i in range(n):
            data = (f"KatyTorrentz-piece-{i}-" + rand_hex(20)).encode("utf-8")
            s.store.write_piece(i, data[: ti.piece_length])
            s._have.set_have(i, True)
            self.db.update_piece(info_hash_hex, i, have=True, verified=False)

    async def start(self) -> None:
        self._loop = asyncio.get_running_loop()
        for s in self._swarms.values():
            await s.start()

    async def stop(self) -> None:
        for s in list(self._swarms.values()):
            await s.stop()


# ---------------------------------------------------------------------------
# CLI + runtime
# ---------------------------------------------------------------------------


def make_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(prog="KatyTorrentz", description="AI-ish torrent sharing app with an EVM settlement lane.")
    p.add_argument("--data-dir", default=os.path.join(os.getcwd(), "KatyTorrentzData"), help="data directory")
    p.add_argument("--host", default="127.0.0.1", help="api host")
    p.add_argument("--port", type=int, default=9877, help="api port")
    p.add_argument("--chain-id", type=int, default=8453, help="EVM chain id (dry mode)")
    p.add_argument("--contract", default="0x8b3D5aD3F0cE11a4aD7b09c6C7E1F3a2b4c5D6e7", help="contract address string")
    p.add_argument("--signer-tag", default="katy-signer-" + secrets.token_hex(6), help="signer label (dry mode)")
    p.add_argument("--load", action="append", default=[], help="path to .torrent to load on startup (repeatable)")
    p.add_argument("--log-level", default="INFO", help="DEBUG/INFO/WARN/ERROR")
