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
