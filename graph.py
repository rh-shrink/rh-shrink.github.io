#!/usr/bin/env python3
"""The import graph of the Lean modules of a commit, for the modularity pictures of the site.

Usage: graph.py REPO OUT.json [--ref main] [--prefix src/] [--package NAME.] [--only]

Writes, for the first first-parent commit ("original") and the last one ("now"):
- profile: the number of modules at each import depth (depth 0: imports no module of the
  project; otherwise one more than the deepest module it imports), so its length is the
  longest import chain;
- reach: for every module, the number of modules that import it directly or indirectly, i.e.
  that are rebuilt when it changes (exact), sorted, sampled for the chart;
- matrix: imports between modules, the modules in path order (so grouped by folder), counted
  in BINS x BINS cells.
Only imports of modules of the project count (not Mathlib and other dependencies).

With --only, just the commit REF, as "now" (used once for Mathlib, the comparison on the site:
graph.py MATHLIB site/mathlib.json --ref HEAD --prefix Mathlib/ --package Mathlib. --only).
"""
import argparse
import json
import re
import sys
import time

import numpy as np

from collect import git, header, read_blobs

IMPORT_LINE = re.compile(
    rb"^(?:public[ \t]+)?(?:meta[ \t]+)?import[ \t]+(?:all[ \t]+)?([^\n]*)", re.M)
VERSION = 2  # of the output; the workflow computes it again when this changes
BINS = 160
SAMPLES = 400


def modules(repo, sha, prefix, package=""):
    """Module names below prefix (path order) and the project modules each imports (indices);
    imports name a module as package + its name."""
    out = git(repo, "ls-tree", "-r", "-z", "--full-tree", sha, "--", prefix)
    paths, blobs = [], []
    for entry in out.split(b"\0"):
        if entry:
            meta, path = entry.split(b"\t", 1)
            _, kind, blob = meta.split()
            if kind == b"blob" and path.endswith(b".lean"):
                paths.append(path.decode())
                blobs.append(blob.decode())
    order = sorted(range(len(paths)), key=lambda i: paths[i])
    paths = [paths[i] for i in order]
    blobs = [blobs[i] for i in order]
    names = [p[len(prefix):-len(".lean")].replace("/", ".") for p in paths]
    index = {package + n: i for i, n in enumerate(names)}
    texts = dict(read_blobs(repo, sorted(set(blobs))))
    imports = []
    for b in blobs:
        found = set()
        for m in IMPORT_LINE.finditer(header(texts[b])):
            for name in m.group(1).decode().split():
                if name in index:
                    found.add(index[name])
        imports.append(sorted(found))
    return names, imports


def depths(imports):
    """Import depth of each module (Kahn's algorithm on the import graph)."""
    n = len(imports)
    importers = [[] for _ in range(n)]
    missing = [len(js) for js in imports]
    for i, js in enumerate(imports):
        for j in js:
            importers[j].append(i)
    depth = [0] * n
    ready = [i for i in range(n) if not missing[i]]
    done = 0
    while ready:
        j = ready.pop()
        done += 1
        for i in importers[j]:
            depth[i] = max(depth[i], depth[j] + 1)
            missing[i] -= 1
            if not missing[i]:
                ready.append(i)
    if done != n:
        sys.exit("import cycle")
    return depth


def reach(imports, depth, chunk=16384):
    """For each module, the number of modules that import it directly or indirectly (exact).

    Bit sets over a chunk of the modules at a time: the set of a module is itself and the sets of
    the modules importing it, which are deeper, so the depths are processed from the deepest. The
    chunks are taken in order of depth: the bits of a chunk only reach modules less deep than its
    deepest module, so the deeper levels are skipped."""
    n = len(imports)
    src = np.array([i for i, js in enumerate(imports) for _ in js], dtype=np.int64)
    dst = np.array([j for js in imports for j in js], dtype=np.int64)
    depth = np.array(depth)
    # the edges into each depth, sorted by the imported module
    by_level = {}
    order = np.lexsort((dst, depth[dst]))
    src, dst = src[order], dst[order]
    bounds = np.searchsorted(depth[dst], np.arange(depth.max() + 2))
    for d in range(depth.max() + 1):
        a, b = bounds[d], bounds[d + 1]
        if a < b:
            s, t = src[a:b], dst[a:b]
            starts = np.flatnonzero(np.r_[True, t[1:] != t[:-1]])
            by_level[d] = (s, t[starts], starts)
    count = np.zeros(n, dtype=np.int64)
    by_depth = np.argsort(depth, kind="stable")
    for c0 in range(0, n, chunk):
        members = by_depth[c0 : c0 + chunk]
        k = len(members)
        words = (k + 63) // 64
        bits = np.zeros((n, words), dtype=np.uint64)
        own = np.arange(k)
        bits[members, own // 64] = np.left_shift(np.uint64(1), (own % 64).astype(np.uint64))
        top = depth[members].max()
        for d in sorted((d for d in by_level if d < top), reverse=True):
            s, targets, starts = by_level[d]
            bits[targets] |= np.bitwise_or.reduceat(bits[s], starts, axis=0)
        count += np.bitwise_count(bits).sum(axis=1, dtype=np.int64)
    return count - 1  # not the module itself


def summary(names, imports):
    t = time.time()
    depth = depths(imports)
    t_depth = time.time() - t
    t = time.time()
    r = reach(imports, depth)
    t_reach = time.time() - t
    n = len(names)
    profile = np.bincount(depth).tolist()
    rank = np.argsort(-r, kind="stable")
    picks = np.unique(np.linspace(0, n - 1, min(SAMPLES, n)).round().astype(int))
    src = np.array([i for i, js in enumerate(imports) for _ in js], dtype=np.int64)
    dst = np.array([j for js in imports for j in js], dtype=np.int64)
    cell = (src * BINS // n) * BINS + dst * BINS // n
    cells = np.bincount(cell, minlength=BINS * BINS)
    nz = np.flatnonzero(cells)
    # what each bin holds, for the popups: the folders (two levels) of its first and last module
    def where(i):
        return ".".join(names[i].split(".")[:2])
    labels = []
    for b in range(BINS):
        lo, hi = -(-b * n // BINS), -(-(b + 1) * n // BINS) - 1
        labels.append(where(lo) if where(lo) == where(hi) else f"{where(lo)} … {where(hi)}")
    folders = []
    for i, name in enumerate(names):
        top = name.split(".")[0] if "." in name else ""
        if not folders or folders[-1]["name"] != top:
            folders.append({"name": top, "start": i})
    for f, g in zip(folders, folders[1:] + [{"start": n}]):
        f["end"] = g["start"]
    print(f"{n} modules, {len(src)} imports, depth {len(profile)}; "
          f"depths {t_depth:.1f}s, reach {t_reach:.1f}s", file=sys.stderr)
    return {
        "modules": n,
        "imports": int(len(src)),
        "profile": profile,
        "reach": {
            "mean": float(r.mean()),
            "unused": int((r == 0).sum()),  # imported by no module
            "rank": picks.tolist(),
            "count": r[rank[picks]].tolist(),
            "name": [names[i] for i in rank[picks]],
        },
        "matrix": {"bins": BINS, "labels": labels,
                   "cells": [[int(c // BINS), int(c % BINS), int(cells[c])] for c in nz]},
        "folders": folders,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("repo")
    ap.add_argument("out")
    ap.add_argument("--ref", default="main")
    ap.add_argument("--prefix", default="src/")
    ap.add_argument("--package", default="")
    ap.add_argument("--only", action="store_true")
    args = ap.parse_args()
    shas = git(args.repo, "log", "--first-parent", "--reverse", "--format=%H", args.ref).decode().split()
    result = {"version": VERSION}
    for key, sha in (("now", shas[-1]),) if args.only else (("original", shas[0]), ("now", shas[-1])):
        names, imports = modules(args.repo, sha, args.prefix, args.package)
        result[key] = {"sha": sha, **summary(names, imports)}
    with open(args.out, "w") as f:
        json.dump(result, f, separators=(",", ":"))
        f.write("\n")


if __name__ == "__main__":
    main()
