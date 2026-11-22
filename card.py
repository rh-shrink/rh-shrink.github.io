#!/usr/bin/env python3
"""Draw the link preview of the site (Open Graph image, 1200 x 630) from its data.

Usage: card.py DATA OUT.png

The headline number of the page, centred, and the code lines relative to the original as a\nstep line across the bottom.
"""
import json
import os
import sys
from datetime import datetime, timezone

from PIL import Image, ImageDraw, ImageFont

W, H, SCALE = 1200, 630, 2  # drawn at twice the size, then reduced: smooth lines
ZOOM = 0.7  # the drawing, shrunk around the centre: a margin all round, whatever an app crops
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

    # Everything that matters is centred, inside the middle square (x 285-915): some apps crop
    # the preview to a square or another narrower shape around the middle.
    def centred(y, text, f, fill):
        d.text(((W / 2) * SCALE - d.textlength(text, font=f) / 2, y * SCALE), text, font=f, fill=fill)

    title, small = font("bold", 40), font("regular", 18)
    tw = d.textlength("RH proof size", font=title) / SCALE
    bw = d.textlength("unofficial", font=small) / SCALE + 22
    x = W / 2 - (tw + 14 + bw) / 2
    d.text(s(x, 36), "RH proof size", font=title, fill=TEXT)
    bx = x + tw + 14
    d.rounded_rectangle(s(bx, 46, bx + bw, 76), radius=15 * SCALE, outline=BORDER, width=2 * SCALE)
    d.text(s(bx + 11, 50), "unofficial", font=small, fill=SECONDARY)
    centred(92, "leanprover-community/riemann-hypothesis", font("regular", 20), MUTED)
    centred(138, f"{100 * last['code'] / first['code']:.1f}%", font("bold", 120), TEXT)
    centred(284, "of the original code lines left", font("regular", 28), SECONDARY)
    when = datetime.fromisoformat(last["date"]).astimezone(timezone.utc).strftime("%b %-d, %H:%M UTC")
    centred(588, f"rh-shrink.github.io · last commit {when}", font("regular", 18), MUTED)

    # Code lines relative to the original, a band across the bottom: a fixed 0-100% axis as on
    # the page (cropped at the sides in a square preview, which only shortens the time axis)
    x0, x1, y0, y1 = 40, 1160, 360, 560  # plot area; y0 is 100%, y1 is 0%
    for pct in (0, 50, 100):
        y = y1 - (y1 - y0) * pct / 100
        d.line(s(x0, y, x1, y), fill=GRID, width=2 * SCALE)
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
    card = Image.new("RGB", (W, H), BG)
    w, h = round(W * ZOOM), round(H * ZOOM)
    card.paste(img.resize((w, h), Image.LANCZOS), ((W - w) // 2, (H - h) // 2))
    card.save(sys.argv[2], optimize=True)


if __name__ == "__main__":
    main()
