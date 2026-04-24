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

