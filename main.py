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
