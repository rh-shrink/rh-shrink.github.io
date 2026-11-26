#!/usr/bin/env python3
"""The import graph of the Lean modules of a commit, for the modularity pictures of the site.

Usage: graph.py REPO OUT.json [--ref main] [--prefix FOLDER/] [--package NAME.] [--only] [--reuse OLD.json]

Writes, for the first first-parent commit that collect.py measures ("original") and the last one
("now"), with the source folder found as collect.py finds it (or --prefix):
- matrix: imports between modules, the modules in path order (so grouped by folder), counted
  in BINS x BINS cells;
- build: an ideal build on as many cores as needed, each module starting as soon as the modules
  it imports are built and taking time proportional to its code lines (an assumption: real
  build times depend mostly on the proofs): the total work, the shortest possible build (span),
  the number of modules building at each of SAMPLES moments, and the module of the import
  chain with the most code lines building then.
Only imports of modules of the project count (not Mathlib and other dependencies).

With --reuse, the "original" of OLD.json is taken over when it is of this VERSION and commit (it
never changes). With --only, just the commit REF, as "now", together with the counts collect.py makes for the
project's commits ("text"; used once for Mathlib, the comparison on the site:
graph.py MATHLIB site/mathlib.json --ref HEAD --prefix Mathlib/ --package Mathlib. --only).
"""
import argparse
import json
import re
import sys
import time

import numpy as np

from collect import (blob_stats, code_lines, git, header, lean_blobs, lean_files, read_blobs, source_dir,
                     summary as text_summary, without_comments)

IMPORT_LINE = re.compile(
    rb"^(?:public[ \t]+)?(?:meta[ \t]+)?import[ \t]+(?:all[ \t]+)?([^\n]*)", re.M)
VERSION = 7  # of the output; the workflow computes it again when this changes
BINS = 160
SAMPLES = 300


def modules(repo, sha, prefix, package=""):
    """Module names below prefix (path order), the project modules each imports (indices) and
    the code lines of each; imports name a module as package + its name."""
    files = lean_files(repo, sha, prefix)
    paths, blobs = [p for p, _ in files], [b for _, b in files]
    order = sorted(range(len(paths)), key=lambda i: paths[i])
    paths = [paths[i] for i in order]
    blobs = [blobs[i] for i in order]
    names = [p[len(prefix):-len(".lean")].replace("/", ".") for p in paths]
    index = {package + n: i for i, n in enumerate(names)}
    texts = dict(read_blobs(repo, sorted(set(blobs))))
    lines = {}
    for b, text in texts.items():
        lines[b] = code_lines(without_comments(text))
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
    # the import chain with the most code lines, from its last module back: each one's
    # latest-ending import
    chain = [int(np.argmax(end))]
    while imports[chain[-1]]:
        chain.append(max(imports[chain[-1]], key=lambda j: end[j]))
    chain.reverse()
    chain_end = end[chain]
    at = np.minimum(np.searchsorted(chain_end, moments, "right"), len(chain) - 1)
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
          f"({work / span:.0f}x); build {t_build:.1f}s", file=sys.stderr)
    return {
        "modules": n,
        "imports": int(len(src)),
        "build": {"work": work, "span": span, "running": running.tolist(),
                  "chain": [names[i] for i in chain], "at": at.tolist()},
        "matrix": {"bins": BINS, "labels": labels,
                   "cells": [[int(c // BINS), int(c % BINS), int(cells[c])] for c in nz]},
        "folders": folders,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("repo")
    ap.add_argument("out")
    ap.add_argument("--ref", default="main")
    ap.add_argument("--prefix", help="the folder to read in every commit, e.g. Mathlib/ "
                    "(default: the srcDir of each commit's lakefile, as in collect.py)")
    ap.add_argument("--package", default="")
    ap.add_argument("--only", action="store_true")
    ap.add_argument("--reuse")
    args = ap.parse_args()
    shas = git(args.repo, "log", "--first-parent", "--reverse", "--format=%H", args.ref).decode().split()
    result = {"version": VERSION}
    old = {}
    if args.reuse:
        try:
            with open(args.reuse) as f:
                old = json.load(f)
        except (OSError, ValueError):
            pass
    def prefix(sha):
        return args.prefix if args.prefix is not None else source_dir(args.repo, sha)

    # the commits collect.py measures: with a source folder holding .lean files
    def measured(sha):
        p = prefix(sha)
        return p is not None and bool(lean_files(args.repo, sha, p))

    first = next((sha for sha in shas if measured(sha)), None)
    if first is None or not measured(shas[-1]):
        sys.exit("no Lean source in the first or the last commit")
    for key, sha in (("now", shas[-1]),) if args.only else (("original", first), ("now", shas[-1])):
        if key == "original" and old.get("version") == VERSION and old.get("original", {}).get("sha") == sha:
            result[key] = old["original"]
            continue
        names, imports, cost = modules(args.repo, sha, prefix(sha), args.package)
        result[key] = {"sha": sha, **summary(names, imports, cost)}
        if args.only:
            blobs = [b for _, b in lean_blobs(args.repo, sha, prefix(sha))]
            result[key]["text"] = text_summary([blob_stats(t) for _, t in read_blobs(args.repo, blobs)])
    with open(args.out, "w") as f:
        json.dump(result, f, separators=(",", ":"))
        f.write("\n")


if __name__ == "__main__":
    main()
