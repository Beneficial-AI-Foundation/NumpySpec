#!/usr/bin/env python3
"""remove_right_margin.py

Blank-out the rightmost margin of every page in a PDF.

Usage
-----
$ python remove_right_margin.py input.pdf output.pdf [--margin-pt 90]

The default margin width is 90 pt (≈1.25 in), appropriate for *Numerical Recipes in C*.
"""

from __future__ import annotations

import argparse
from pathlib import Path

from PyPDF2 import PdfReader, PdfWriter
from reportlab.pdfgen import canvas

# Optional, heavy dependency but gives fine-grained layout access.
try:
    from pdfminer.high_level import extract_pages  # type: ignore
    from pdfminer.layout import LTTextContainer  # type: ignore

    _PDFMINER_AVAILABLE = True
except ModuleNotFoundError:  # pragma: no cover – optional
    _PDFMINER_AVAILABLE = False

# -----------------------------------------------------------------------------
# Helpers
# -----------------------------------------------------------------------------


def build_full_margin_overlay(
    width_pt: float, height_pt: float, x0: float
) -> PdfReader:
    """Return a single-page PDF whitewashed from *x0* → page right edge."""

    from io import BytesIO

    packet = BytesIO()
    c = canvas.Canvas(packet, pagesize=(width_pt, height_pt))

    # Draw white rectangle covering the margin area.
    c.setFillColorRGB(1.0, 1.0, 1.0)
    c.setStrokeColorRGB(1.0, 1.0, 1.0)
    c.rect(x0, 0.0, width_pt - x0, height_pt, stroke=0, fill=1)
    c.save()
    packet.seek(0)

    return PdfReader(packet)


def build_fine_overlay(
    width_pt: float,
    height_pt: float,
    bboxes: list[tuple[float, float, float, float]],
) -> PdfReader:
    """Overlay that whites out *exactly* the given bounding boxes.

    Each *bbox* is *(x0, y0, x1, y1)* in PDF points.
    """

    from io import BytesIO

    packet = BytesIO()
    c = canvas.Canvas(packet, pagesize=(width_pt, height_pt))
    c.setFillColorRGB(1.0, 1.0, 1.0)
    c.setStrokeColorRGB(1.0, 1.0, 1.0)

    for x0, y0, x1, y1 in bboxes:
        c.rect(x0, y0, x1 - x0, y1 - y0, stroke=0, fill=1)

    c.save()
    packet.seek(0)
    return PdfReader(packet)


def extract_margin_bboxes(
    page, page_width: float
) -> list[tuple[float, float, float, float]]:
    """Heuristic: return bounding boxes representing rotated side-text on *page*.

    Notes for *Numerical Recipes in C*:
    • Rotated words sit at x ≥ ~532 pt.
    • They are narrow (x1 - x0 ≤ 40 pt) and tall.
    The heuristic below captures those.
    """

    if not _PDFMINER_AVAILABLE:
        return []

    bboxes: list[tuple[float, float, float, float]] = []

    # Heuristic thresholds tuned for Numerical Recipes in C layout.
    THRESH_X0 = 400.0  # any container right of this is candidate annotation
    MAX_WIDTH = 20.0  # rotated characters are narrow in x-span

    for element in page:
        if isinstance(element, LTTextContainer):
            x0, y0, x1, y1 = element.bbox  # type: ignore[attr-defined]
            if x0 >= THRESH_X0 and (x1 - x0) <= MAX_WIDTH:
                # small padding
                PAD = 2.0
                bboxes.append((x0 - PAD, y0 - PAD, x1 + PAD, y1 + PAD))

    if not bboxes:
        return []

    # Take the union of all candidate boxes to get a single rectangle for annotation.
    xs0 = min(b[0] for b in bboxes)
    ys0 = min(b[1] for b in bboxes)
    xs1 = max(b[2] for b in bboxes)
    ys1 = max(b[3] for b in bboxes)

    return [(xs0, ys0, xs1, ys1)]


# -----------------------------------------------------------------------------
# Main routine
# -----------------------------------------------------------------------------


def remove_right_margin(
    input_pdf: Path,
    output_pdf: Path,
    margin_pt: float | None = None,
) -> None:
    reader = PdfReader(str(input_pdf))
    writer = PdfWriter()

    # Inspect first page to get page size (we assume all pages share it).
    media_box = reader.pages[0].mediabox
    width_pt: float = float(media_box.width)
    height_pt: float = float(media_box.height)

    for raw_page_layout, page in zip(
        extract_pages(str(input_pdf))
        if _PDFMINER_AVAILABLE
        else [None] * len(reader.pages),
        reader.pages,
    ):
        if margin_pt is not None:
            # Simple, rectangular mask.
            x0 = width_pt - margin_pt
            overlay_page = build_full_margin_overlay(width_pt, height_pt, x0).pages[0]
            page.merge_page(overlay_page)
        else:
            # Fine-grained detection via pdfminer.
            bboxes = (
                extract_margin_bboxes(raw_page_layout, width_pt)
                if raw_page_layout
                else []
            )

            if bboxes:
                overlay_page = build_fine_overlay(width_pt, height_pt, bboxes).pages[0]
                page.merge_page(overlay_page)

        writer.add_page(page)

    # Ensure output directory exists.
    output_pdf.parent.mkdir(parents=True, exist_ok=True)
    with output_pdf.open("wb") as fh:
        writer.write(fh)

    print(f"Written masked PDF → {output_pdf}")


# -----------------------------------------------------------------------------
if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Blank-out the right-hand margin of a PDF."
    )
    parser.add_argument("input", type=Path, help="source PDF")
    parser.add_argument("output", type=Path, help="destination PDF")

    mode_group = parser.add_mutually_exclusive_group()
    mode_group.add_argument(
        "--margin-pt",
        type=float,
        help="simple fixed-width mask (points). Overrides auto-mask mode.",
    )
    mode_group.add_argument(
        "--auto-mask",
        action="store_true",
        help="detect the sideways margin words (Numerical-Recipes style) and blank only those boxes (default).",
    )

    args = parser.parse_args()
    chosen_margin = args.margin_pt if args.margin_pt is not None else None
    remove_right_margin(args.input, args.output, chosen_margin)
