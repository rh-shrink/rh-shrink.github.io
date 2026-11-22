#!/usr/bin/env python3
"""The import graph of the Lean modules of a commit, for the modularity pictures of the site.

Usage: graph.py REPO OUT.json [--ref main] [--prefix src/] [--package NAME.] [--only]

Writes, for the first first-parent commit ("original") and the last one ("now"):
- matrix: imports between modules, the modules in path order (so grouped by folder), counted
  in BINS x BINS cells;
- build: an ideal build on as many cores as needed, each module starting as soon as the modules
  it imports are built and taking time proportional to its code lines (an assumption: real
  build times depend mostly on the proofs): the total work, the shortest possible build (span),
  the number of modules building at each of SAMPLES moments, and the module of the longest
  import chain building then;
- tree: the folders, LEVELS deep, with their code lines, modules and when they are built in
  the ideal build (as shares of the span).
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

from collect import git, header, read_blobs, without_comments

IMPORT_LINE = re.compile(
    rb"^(?:public[ \t]+)?(?:meta[ \t]+)?import[ \t]+(?:all[ \t]+)?([^\n]*)", re.M)
VERSION = 3  # of the output; the workflow computes it again when this changes
BINS = 160
SAMPLES = 300
LEVELS = 4
SMALLEST = 0.0005  # folders with a smaller share of the code lines are left out of the tree


def modules(repo, sha, prefix, package=""):
    """Module names below prefix (path order), the project modules each imports (indices) and
    the code lines of each; imports name a module as package + its name."""
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
    lines = {}
    for b, text in texts.items():
        parts = without_comments(text).translate(None, b" \t\r\f\v").split(b"\n")
        lines[b] = len(parts) - parts.count(b"")
    imports = []
    for b in blobs:
        found = set()
        for m in IMPORT_LINE.finditer(header(texts[b])):
            for name in m.group(1).decode().split():
                if name in index:
                    found.add(index[name])
        imports.append(sorted(found))
    return names, imports, [lines[b] for b in blobs]


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


def simulate(imports, depth, cost):
    """Start and end of each module in the ideal build: it starts when the last module it imports
    ends. The modules are taken by depth, so all that a module imports has ended before."""
    n = len(imports)
    depth = np.array(depth)
    cost = np.array(cost, dtype=float)
    src = np.array([i for i, js in enumerate(imports) for _ in js], dtype=np.int64)
    dst = np.array([j for js in imports for j in js], dtype=np.int64)
    order = np.lexsort((src, depth[src]))  # the edges by the depth of the importing module
    src, dst = src[order], dst[order]
    edge_bounds = np.searchsorted(depth[src], np.arange(depth.max() + 2))
    by_depth = np.argsort(depth, kind="stable")
    node_bounds = np.searchsorted(depth[by_depth], np.arange(depth.max() + 2))
    start, end = np.zeros(n), np.zeros(n)
    for d in range(depth.max() + 1):
        a, b = edge_bounds[d], edge_bounds[d + 1]
        if a < b:
            s = src[a:b]
            firsts = np.flatnonzero(np.r_[True, s[1:] != s[:-1]])
            start[s[firsts]] = np.maximum.reduceat(end[dst[a:b]], firsts)
        nodes = by_depth[node_bounds[d] : node_bounds[d + 1]]
        end[nodes] = start[nodes] + cost[nodes]
    return start, end


def summary(names, imports, cost):
    t = time.time()
    depth = depths(imports)
    start, end = simulate(imports, depth, cost)
    t_build = time.time() - t
    n = len(names)
    work, span = float(sum(cost)), float(end.max())
    moments = (np.arange(SAMPLES) + 0.5) / SAMPLES * span
    running = (np.searchsorted(np.sort(start), moments, "right")
               - np.searchsorted(np.sort(end), moments, "right"))
    # the longest import chain, from its last module back: each one's latest-ending import
    chain = [int(np.argmax(end))]
    while imports[chain[-1]]:
        chain.append(max(imports[chain[-1]], key=lambda j: end[j]))
    chain.reverse()
    chain_end = end[chain]
    at = np.minimum(np.searchsorted(chain_end, moments, "right"), len(chain) - 1)
    # the folders, LEVELS deep: code lines, modules, middle of their build (weighted by code
    # lines), first start and last end, as shares of the span
    agg = {}
    for i, name in enumerate(names):
        parts = name.split(".")[:-1]
        for k in range(1, min(LEVELS, len(parts)) + 1):
            a = agg.setdefault("/".join(parts[:k]), [0, 0, 0.0, span, 0.0])
            a[0] += cost[i]
            a[1] += 1
            a[2] += cost[i] * (start[i] + end[i]) / 2
            a[3] = min(a[3], start[i])
            a[4] = max(a[4], end[i])
    tree = [[path, a[0], a[1], round(a[2] / a[0] / span if a[0] else a[3] / span, 4),
             round(a[3] / span, 4), round(a[4] / span, 4)]
            for path, a in sorted(agg.items()) if a[0] >= SMALLEST * work]
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
    print(f"{n} modules, {len(src)} imports; work {work:.0f}, span {span:.0f} code lines "
          f"({work / span:.0f}x); build {t_build:.1f}s; {len(tree)} folders", file=sys.stderr)
    return {
        "modules": n,
        "imports": int(len(src)),
        "build": {"work": work, "span": span, "running": running.tolist(),
                  "chain": [names[i] for i in chain], "at": at.tolist()},
        "tree": tree,
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
        names, imports, cost = modules(args.repo, sha, args.prefix, args.package)
        result[key] = {"sha": sha, **summary(names, imports, cost)}
    with open(args.out, "w") as f:
        json.dump(result, f, separators=(",", ":"))
        f.write("\n")


if __name__ == "__main__":
    main()
