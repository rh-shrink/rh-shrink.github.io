#!/usr/bin/env python3
"""Measure the Lean source of every first-parent commit of a git repository.

Usage: collect.py REPO DATA [--ref main] [--prefix src/]

REPO is a (bare) clone; DATA is the JSON file the site reads. Commits already in
DATA are skipped (all are measured again when DATA has another VERSION).
Statistics are computed once per blob, so consecutive commits cost only the
files they changed.
"""
import argparse
import json
import multiprocessing
import os
import re
import subprocess
import sys
import threading

# 2: declarations and imports inside comments are not counted; code lines per folder.
VERSION = 2
STAT_KEYS = ("bytes", "lines", "code", "theorems", "defs", "imports")

# possessive quantifiers (++, *+, ?+): no backtracking, a third faster on this source
DECL = re.compile(
    rb"^[ \t]*+(?:@\[[^\]\n]*+\][ \t]*+)?+"
    rb"(?:(?:public|private|protected|noncomputable|partial|unsafe|nonrec|meta|scoped|local)[ \t]++)*+"
    rb"(theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque|axiom)\b",
    re.M,
)
IMPORT = re.compile(rb"^(?:public[ \t]+)?(?:meta[ \t]+)?import[ \t]", re.M)
CODE_TOKEN = re.compile(rb'/-|--|"')
COMMENT_TOKEN = re.compile(rb"/-|-/")
STRING_END = re.compile(rb'(?:[^"\\]|\\.)*"', re.S)
NOT_NEWLINE = re.compile(rb"[^\n]")
# The first line of a file that is not part of its header (module, prelude, imports): Lean allows
# imports only there.
NOT_HEADER = re.compile(
    rb"^[ \t]*(?!(?:public[ \t]+)?(?:meta[ \t]+)?import\b|module\b|prelude\b)\S", re.M)


def without_comments(text: bytes) -> bytes:
    """The text with every comment (--, nested /- -/) blanked out, newlines kept."""
    spans, pos, depth, start, n = [], 0, 0, 0, len(text)
    while pos < n:
        m = (COMMENT_TOKEN if depth else CODE_TOKEN).search(text, pos)
        if not m:
            if depth:
                spans.append((start, n))  # unclosed comment
            break
        tok, pos = m.group(), m.end()
        if tok == b"/-":
            if not depth:
                start = m.start()
            depth += 1
        elif tok == b"-/":
            depth -= 1
            if not depth:
                spans.append((start, pos))
        elif tok == b"--":
            nl = text.find(b"\n", pos)
            pos = n if nl < 0 else nl
            spans.append((m.start(), pos))
        else:  # a string: skip it, comment markers in it are text
            if text[m.start() - 1 : m.start()] == b"'" and text[pos : pos + 1] == b"'":
                continue  # the character literal '"'
            s = STRING_END.match(text, pos)
            pos = s.end() if s else n
    out = bytearray(text)
    for a, b in spans:
        out[a:b] = NOT_NEWLINE.sub(b" ", text[a:b])
    return bytes(out)


def header(text: bytes) -> bytes:
    """The header of a file, comments blanked out, from a prefix of the file: long enough when
    it holds a complete line that is not part of the header."""
    k = 4096
    while True:
        part = without_comments(text[:k])
        m = NOT_HEADER.search(part)
        if m and (k >= len(text) or part.find(b"\n", m.start()) >= 0):
            return part[: m.start()]
        if k >= len(text):
            return part
        k *= 8


def blob_stats(text: bytes) -> list:
    lines = text.count(b"\n") + (1 if text and not text.endswith(b"\n") else 0)
    code = without_comments(text)
    kinds = [m.group(1) for m in DECL.finditer(code)]
    # code lines: the lines with something but white space (translate and split run in C)
    parts = code.translate(None, b" \t\r\f\v").split(b"\n")
    end = NOT_HEADER.search(code)
    theorems = sum(k in (b"theorem", b"lemma") for k in kinds)
    return [
        len(text),
        lines,
        len(parts) - parts.count(b""),
        theorems,
        len(kinds) - theorems,
        len(IMPORT.findall(code, 0, end.start() if end else len(code))),
    ]


def git(repo, *args, **kw):
    return subprocess.run(
        ["git", "-C", repo, *args], check=True, stdout=subprocess.PIPE, **kw
    ).stdout


def lean_blobs(repo, sha, prefix):
    """(folder, blob id) of each .lean file under prefix; the folder is the first one below
    prefix, "" for files directly in it."""
    out = git(repo, "ls-tree", "-r", "-z", "--full-tree", sha, "--", prefix)
    blobs = []
    for entry in out.split(b"\0"):
        if not entry:
            continue
        meta, path = entry.split(b"\t", 1)
        _, kind, blob = meta.split()
        if kind == b"blob" and path.endswith(b".lean"):
            rest = path.decode()[len(prefix):]
            blobs.append((rest.split("/")[0] if "/" in rest else "", blob.decode()))
    return blobs


def read_blobs(repo, blobs):
    """Yield (blob id, contents) using one `git cat-file --batch`."""
    proc = subprocess.Popen(
        ["git", "-C", repo, "cat-file", "--batch"],
        stdin=subprocess.PIPE, stdout=subprocess.PIPE,
    )
    def feed():
        for b in blobs:
            proc.stdin.write(b.encode() + b"\n")
        proc.stdin.close()

    threading.Thread(target=feed, daemon=True).start()
    for _ in blobs:
        header = proc.stdout.readline().split()
        size = int(header[2])
        data = proc.stdout.read(size)
        proc.stdout.read(1)
        yield header[0].decode(), data
    proc.wait()


def stats_of(item):
    blob, text = item
    return blob, blob_stats(text)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("repo")
    ap.add_argument("data")
    ap.add_argument("--ref", default="main")
    ap.add_argument("--prefix", default="src/")
    args = ap.parse_args()

    data = {"commits": []}
    if os.path.exists(args.data):
        with open(args.data) as f:
            data = json.load(f)
    if data.get("version") != VERSION:
        data = {"version": VERSION, "commits": []}
    known = {c["sha"] for c in data["commits"]}

    cache = {}

    log = git(args.repo, "log", "--first-parent", "--reverse",
              "--format=%H%x00%cI%x00%s", args.ref).decode()
    new = [l.split("\0") for l in log.splitlines()]
    new = [c for c in new if c[0] not in known]
    print(f"{len(new)} new commit(s)", file=sys.stderr)

    pool = multiprocessing.Pool()  # files are measured on all cores
    for sha, date, subject in new:
        files = lean_blobs(args.repo, sha, args.prefix)
        blobs = [b for _, b in files]
        missing = sorted(set(blobs) - cache.keys())
        for blob, stats in pool.imap_unordered(stats_of, read_blobs(args.repo, missing), chunksize=64):
            cache[blob] = stats
        totals = [sum(cache[b][i] for b in blobs) for i in range(len(STAT_KEYS))]
        code = STAT_KEYS.index("code")
        dirs = {}
        for folder, b in files:
            dirs[folder] = dirs.get(folder, 0) + cache[b][code]
        pr = re.match(r"Merge pull request #(\d+)", subject)
        entry = {"sha": sha, "date": date, "subject": subject,
                 "pr": int(pr.group(1)) if pr else None, "files": len(blobs)}
        entry.update(zip(STAT_KEYS, totals))
        entry["dirs"] = dict(sorted(dirs.items()))
        data["commits"].append(entry)
        print(f"{sha[:8]} {entry['lines']:>10} lines {len(missing):>6} new blobs",
              file=sys.stderr)

    pool.close()
    with open(args.data, "w") as f:
        json.dump(data, f, separators=(",", ":"))
        f.write("\n")


if __name__ == "__main__":
    main()
