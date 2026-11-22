#!/usr/bin/env python3
"""Draw the link preview of the site (Open Graph image, 1200 x 630) from its data.

Usage: card.py DATA OUT.png

The headline number of the page and the code lines relative to the original, as a step line.
"""
import json
import os
import sys
from datetime import datetime, timezone

from PIL import Image, ImageDraw, ImageFont

W, H, SCALE = 1200, 630, 2  # drawn at twice the size, then reduced: smooth lines
BG, BORDER, GRID = "#fcfcfb", "#e4e3df", "#ecebe7"
TEXT, SECONDARY, MUTED, BLUE = "#0b0b0b", "#52514e", "#7a7974", "#2a78d6"

FONTS = {  # the first that exists; the runner has DejaVu, a Mac has Helvetica
    "regular": ["/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf", "/System/Library/Fonts/Helvetica.ttc"],
    "bold": ["/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf", "/System/Library/Fonts/Helvetica.ttc"],
}


def font(kind, size):
    size *= SCALE
    for path in FONTS[kind]:
        if os.path.exists(path):
            return ImageFont.truetype(path, size, index=1 if kind == "bold" and path.endswith(".ttc") else 0)
    return ImageFont.load_default(size)


def main():
    commits = json.load(open(sys.argv[1]))["commits"]
    first, last = commits[0], commits[-1]
    img = Image.new("RGB", (W * SCALE, H * SCALE), BG)
    d = ImageDraw.Draw(img)
    s = lambda *v: [x * SCALE for x in v]

    # Text, left
    title = font("bold", 46)
    d.text(s(72, 64), "RH proof size", font=title, fill=TEXT)
    badge_x = 72 + d.textlength("RH proof size", font=title) / SCALE + 18
    small = font("regular", 20)
    bw = d.textlength("unofficial", font=small) / SCALE + 24
    d.rounded_rectangle(s(badge_x, 76, badge_x + bw, 108), radius=16 * SCALE, outline=BORDER, width=2 * SCALE)
    d.text(s(badge_x + 12, 80), "unofficial", font=small, fill=SECONDARY)
    d.text(s(72, 132), "leanprover-community/riemann-hypothesis", font=font("regular", 22), fill=MUTED)
    d.text(s(68, 218), f"{100 * last['code'] / first['code']:.1f}%", font=font("bold", 132), fill=TEXT)
    d.text(s(72, 384), "of the original code lines left", font=font("regular", 30), fill=SECONDARY)
    when = datetime.fromisoformat(last["date"]).astimezone(timezone.utc).strftime("%b %-d, %H:%M UTC")
    d.text(s(72, 548), f"rh-shrink.github.io · last commit {when}", font=font("regular", 20), fill=MUTED)

    # Code lines relative to the original, right: a fixed 0-100% axis as on the page
    x0, x1, y0, y1 = 700, 1128, 120, 540  # plot area; y0 is 100%, y1 is 0%
    for pct in (0, 50, 100):
        y = y1 - (y1 - y0) * pct / 100
        d.line(s(x0, y, x1, y), fill=GRID, width=2 * SCALE)
        label = f"{pct}%"
        d.text(s(x0 - 12 - d.textlength(label, font=small) / SCALE, y - 12), label, font=small, fill=MUTED)
    ts = [datetime.fromisoformat(c["date"]).timestamp() for c in commits]
    span = (ts[-1] - ts[0]) or 1
    pts = []
    for t, c in zip(ts, commits):
        x = x0 + (x1 - x0) * (t - ts[0]) / span
        y = y1 - (y1 - y0) * min(c["code"] / first["code"], 1)
        if pts:
            pts.append((x, pts[-1][1]))  # a step at each commit
        pts.append((x, y))
    area = [(x0, y1)] + pts + [(x1, y1)]
    tint = Image.new("RGBA", img.size)
    ImageDraw.Draw(tint).polygon([(x * SCALE, y * SCALE) for x, y in area], fill=(42, 120, 214, 30))
    img.paste(tint, (0, 0), tint)
    d.line([(x * SCALE, y * SCALE) for x, y in pts], fill=BLUE, width=4 * SCALE, joint="curve")
    d.text(s(x0, y1 + 14), "Code lines", font=small, fill=SECONDARY)

    img.resize((W, H), Image.LANCZOS).save(sys.argv[2], optimize=True)


if __name__ == "__main__":
    main()
