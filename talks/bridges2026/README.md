# Bridges 2026 Beamer slides

This directory contains a Beamer slide deck for a 20 minute Bridges 2026 talk on the pipeline

```text
SMT path synthesis -> maze completion -> 3D realization of woven mazes
```

The schedule slot is 30 minutes, but the deck is designed for a formal talk of about 20 minutes, leaving time for questions and room changeover.

## Build

The deck requires XeLaTeX, the Libertinus font family, and Iosevka
Curly. The Beamer source uses Libertinus Serif, Libertinus Sans,
Libertinus Mono, and Libertinus Math through system font names:

```tex
\usefonttheme{professionalfonts}
\usepackage{fontspec}
\usepackage{unicode-math}
\setmainfont{Libertinus Serif}
\setsansfont{Libertinus Sans}
\setmonofont{Libertinus Mono}
\setmathfont{Libertinus Math}
```

SMT-LIB listings use the system font `Iosevka Curly`.

Compile from this directory with either command:

```sh
make
make slides
```

Both commands run `latexmk -xelatex` and produce `slides.pdf`.

## Figure Sources

The slide deck uses deck-local assets under `figures/` so the talk can
be edited independently without changing the paper or extended report.
The PDF artwork was copied from `../../extended-report/figures/` where
corresponding files exist. Talk-specific TikZ diagrams were then added
alongside those copies. The main assets are:

- `pipeline.tex`, `tiles.tex`, `visual-motivation.tex`, and the
  `local-*.tex`, `parent-rank-chain.tex`, and
  `crossing-virtual-elements.tex` files for the pipeline and encoding
  diagrams.
- `s-pattern-grid.tex` and `s-sol-grid.tex`, generated from
  `../../problems/s-sol.txt`, for the target-pattern and tile-assignment
  grids shown after the title slide.
- `s-nocross-sol-grid.tex`, generated from `../../nocross/s-sol.txt`,
  for the planar tile assignment in the same comparison.
- `abnormal1.pdf` through `abnormal4.pdf` for local-constraint and crossing failure modes.
- `bigart-inter-sol.pdf` for the large woven example.
- `crossing-construction-npr.pdf` for the local 3D crossing construction.
- `crossed-s-npr.pdf` for the title-page rendering.
- `crossed-s-no-solution.pdf` and `crossed-s.pdf` for the maze pair
  shown with the pattern and tile assignment after the title slide.
- `s-no-solution.pdf` and `s.pdf` for the corresponding planar maze
  pair.
- `crossed-inf-npr.pdf` for the full 3D woven maze rendering.

The final-slide QR code, `arxiv-2607.09781.pdf`, was generated locally
with `qrencode` and points to the extended report at
`https://arxiv.org/abs/2607.09781`.

The text and numerical claims are taken from the conference paper and the extended report already present in this repository. The deck does not modify the paper, the extended report, or implementation code.
