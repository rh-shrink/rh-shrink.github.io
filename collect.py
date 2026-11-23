#!/usr/bin/env python3
"""Measure the Lean source of every first-parent commit of a git repository.

Usage: collect.py REPO DATA [--ref main] [--prefix src/]

REPO is a (bare) clone; DATA is the JSON file the site reads. Commits already in
DATA are skipped (all are measured again when DATA has another VERSION).
Statistics are computed once per blob, so consecutive commits cost only the
files they changed.
"""
import argparse
import bisect
import collections
import hashlib
import json
import multiprocessing
import os
import re
import subprocess
import sys
import threading

# 2: declarations and imports inside comments are not counted; code lines per folder.
# 3: heartbeat overrides, omega/nlinarith, declaration lengths, repeated theorem statements.
# 4: finer declaration lengths.
VERSION = 4
STAT_KEYS = ("bytes", "lines", "code", "theorems", "defs", "imports", "heartbeats", "arith",
             "statements")
# Declaration lengths in code lines: bin k holds LENGTH_EDGES[k] up to the next edge (exclusive);
# 1 to 7 one by one, then four bins per doubling (8, 10, 12, 14, 16, 20, ...); the last is open.
LENGTH_EDGES = [1, 2, 3, 4, 5, 6, 7] + [o * f // 4 for o in (8, 16, 32, 64, 128, 256, 512, 1024, 2048)
                                         for f in (4, 5, 6, 7)] + [4096]
LENGTH_BINS = len(LENGTH_EDGES)

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
THEOREM = re.compile(
    rb"^[ \t]*+(?:@\[[^\]\n]*+\][ \t]*+)?+"
    rb"(?:(?:public|private|protected|noncomputable|partial|unsafe|nonrec|meta|scoped|local)[ \t]++)*+"
    rb"(?:theorem|lemma)[ \t]+[^\s:({\[]+",
    re.M,
)
HEARTBEATS = re.compile(rb"\bset_option[ \t]+maxHeartbeats\b")
ARITH = re.compile(rb"\b(?:omega|nlinarith)\b")
WHITE = re.compile(rb"\s+")
SHORTEST_STATEMENT = 30  # shorter statements (": a = a") repeat naturally

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


def statement(code: bytes, pos: int):
    """The statement of the theorem whose name ends at pos: up to ":=", white space normalised;
    None if not found within 3000 bytes or shorter than SHORTEST_STATEMENT."""
    rest = code[pos : pos + 3000]
    cut = rest.find(b":=")
    s = WHITE.sub(b" ", rest[:cut]).strip() if cut > 0 else b""
    return s if len(s) >= SHORTEST_STATEMENT else None


def blob_stats(text: bytes):
    """The STAT_KEYS counts followed by LENGTH_BINS declaration-length counts, and the hashes of
    the theorem statements (stable: the same in every process)."""
    lines = text.count(b"\n") + (1 if text and not text.endswith(b"\n") else 0)
    code = without_comments(text)
    decls = list(DECL.finditer(code))
    kinds = [m.group(1) for m in decls]
    # code lines: the lines with something but white space (translate and split run in C)
    parts = code.translate(None, b" \t\r\f\v").split(b"\n")
    end = NOT_HEADER.search(code)
    theorems = sum(k in (b"theorem", b"lemma") for k in kinds)
    # each declaration's code lines: from its line (DECL matches at a line start) to the next
    # declaration or the end, counted in C like the code lines
    lengths = [0] * LENGTH_BINS
    starts = [m.start() for m in decls] + [len(code)]
    for a, b in zip(starts, starts[1:]):
        seg = code[a:b].translate(None, b" \t\r\f\v").split(b"\n")
        lengths[bisect.bisect_right(LENGTH_EDGES, max(len(seg) - seg.count(b""), 1)) - 1] += 1
    hashes = []
    for m in THEOREM.finditer(code):
        s = statement(code, m.end())
        if s:
            hashes.append(int.from_bytes(hashlib.blake2b(s, digest_size=8).digest(), "big"))
    counts = [
        len(text),
        lines,
        len(parts) - parts.count(b""),
        theorems,
        len(kinds) - theorems,
        len(IMPORT.findall(code, 0, end.start() if end else len(code))),
        len(HEARTBEATS.findall(code)),
        len(ARITH.findall(code)),
        len(hashes),
    ]
    return counts + lengths, tuple(hashes)


def summary(stats):
    """The counts of a commit from the blob_stats of its files: STAT_KEYS, "lengths" and
    "repeats" (theorem statements that repeat an earlier one word for word)."""
    total = [sum(col) for col in zip(*(s for s, _ in stats))]
    seen = collections.Counter(h for _, hs in stats for h in hs)
    out = dict(zip(STAT_KEYS, total))
    out["lengths"] = total[len(STAT_KEYS):]
    out["length_edges"] = LENGTH_EDGES
    out["repeats"] = sum(seen.values()) - len(seen)
    return out


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
    import numpy as np  # here, not above: the workflow imports this module without numpy

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
    data["length_edges"] = LENGTH_EDGES
    known = {c["sha"] for c in data["commits"]}

    cache = {}

    log = git(args.repo, "log", "--first-parent", "--reverse",
              "--format=%H%x00%cI%x00%s", args.ref).decode()
    new = [l.split("\0") for l in log.splitlines()]
    new = [c for c in new if c[0] not in known]
    print(f"{len(new)} new commit(s)", file=sys.stderr)

    pool = multiprocessing.Pool()  # files are measured on all cores
    # The totals of a commit are kept from one commit to the next: only the files that changed
    # (as pairs of folder and blob) are added or taken away. So are its theorem statements, and
    # the code lines and files of each folder.
    present, statements = collections.Counter(), collections.Counter()
    width = len(STAT_KEYS) + LENGTH_BINS
    totals = np.zeros(width, dtype=np.int64)
    code = STAT_KEYS.index("code")
    dirs, dir_files = collections.Counter(), collections.Counter()
    for sha, date, subject in new:
        files = lean_blobs(args.repo, sha, args.prefix)
        blobs = [b for _, b in files]
        missing = sorted(set(blobs) - cache.keys())
        for blob, (counts, hashes) in pool.imap_unordered(stats_of, read_blobs(args.repo, missing), chunksize=64):
            cache[blob] = (np.array(counts, dtype=np.int64), hashes)
        now = collections.Counter(files)
        for change, sign in ((now - present, 1), (present - now, -1)):
            for (folder, b), k in change.items():
                counts, hashes = cache[b]
                totals += sign * k * counts
                dirs[folder] += sign * k * int(counts[code])
                dir_files[folder] += sign * k
                if not dir_files[folder]:
                    del dirs[folder], dir_files[folder]
                for h in hashes:
                    statements[h] += sign * k
                    if not statements[h]:
                        del statements[h]
        present = now
        pr = re.match(r"Merge pull request #(\d+)", subject)
        entry = {"sha": sha, "date": date, "subject": subject,
                 "pr": int(pr.group(1)) if pr else None, "files": len(blobs)}
        entry.update(zip(STAT_KEYS, totals.tolist()))
        entry["lengths"] = totals[len(STAT_KEYS):].tolist()
        entry["repeats"] = sum(statements.values()) - len(statements)
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
