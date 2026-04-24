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
