# RH proof size

Size of the Lean source of [leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)
per commit on `main`: <https://rh-shrink.github.io>. Unofficial.

- `collect.py` counts lines, declarations, files and imports with regular expressions over the
  file contents in git (no Lean). The page lists exactly what is counted.
- `.github/workflows/update.yml` runs it every 15 minutes and deploys `site/` to GitHub Pages.
