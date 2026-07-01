# Opt Maze

This repository contains research code and manuscript sources for the
Bridges 2026 paper
[From Patterns to Maze Solutions: An SMT-Based Construction](https://archive.bridgesmathart.org/2026/bridges2026-37.html)
and its extended technical report.

It provides the SMT-based path-synthesis component of a
maze-generation pipeline: it constructs a maze solution path on a grid,
either as a planar self-avoiding path or as a layered path with
crossings for woven mazes. The repository also includes the source
files for the published conference paper and the extended technical
report.

Maze-construction code for turning synthesized paths into
two-dimensional, three-dimensional, or interactive mazes is maintained
in the companion repository
[txyyss/maze-construction](https://github.com/txyyss/maze-construction).

## Repository Layout

- `OptMaze/`, `OptMaze.lean`, `Main.lean`: Lean 4 implementation of
  the 0/1 matrix parser, SMT-LIB encoder, solver interface, and model
  parser.
- `paper/`: LaTeX source for the published Bridges 2026 conference
  paper.
- `extended-report/`: LaTeX source for the expanded technical report.
- `OptMaze.wl`: Wolfram/Mathematica helper code for exploration and
  visualization.
- `.github/workflows/lean_action_ci.yml`: GitHub Actions workflow for
  building the Lean project.

## Requirements

- Lean 4 and Lake, managed by the toolchain in `lean-toolchain`
  (`leanprover/lean4:v4.31.0`).
- An SMT solver executable. The command-line tool defaults to `z3`.
  Solvers without optimization support can be used with an explicit
  fixed coverage bound via `--min`.
- A TeX distribution with `latexmk` for building the paper and extended
  report.
- Optional: Wolfram/Mathematica for auxiliary exploration and
  visualization files.

## Building

Build the Lean executable with Lake:

```sh
lake build
```

The command-line interface is:

```sh
lake exe opt-maze [FLAGS] <input>
```

The input is a rectangular text file of `0` and `1` characters. The
`0` cells are the target pattern cells to be covered by the synthesized
path, while `1` cells are background cells.

Common options:

```sh
lake exe opt-maze --solver z3 pattern.txt
lake exe opt-maze --solver <solver-executable> --min 120 pattern.txt
lake exe opt-maze --nocross --solver z3 pattern.txt
```

For an input file `pattern.txt`, the tool writes:

- `pattern.smt2`: the generated SMT-LIB instance.
- `pattern.sol`: the raw solver output.
- `pattern.out`: the parsed model as a Mathematica-style list, when
  the instance is satisfiable.
- `pattern.log`: basic instance statistics and solver timing.

## Building the Manuscripts

The conference paper and the extended report can be built from their
respective directories:

```sh
cd paper
latexmk -pdf maze.tex

cd ../extended-report
latexmk -pdf maze-extended.tex
```

Generated LaTeX files and PDFs are ignored by git.

## Citation

If you use this repository, please cite the Bridges 2026 paper:

```bibtex
@inproceedings{Wang2026PatternsMazeSolutions,
  author    = {Shengyi Wang},
  title     = {From Patterns to Maze Solutions: An SMT-Based Construction},
  booktitle = {Proceedings of Bridges 2026: Mathematics and the Arts},
  pages     = {37--44},
  publisher = {Tessellations Publishing},
  address   = {Phoenix, AZ, USA},
  year      = {2026},
  isbn      = {9781938664533},
  issn      = {1099-6702},
  url       = {https://archive.bridgesmathart.org/2026/bridges2026-37.html}
}
```

See also `CITATION.cff`.

## License

The software in this repository is released under the MIT License; see
`LICENSE`.

The paper and extended-report sources, figures, and third-party
conference template files are included as scholarly artifacts. Reuse of
those materials may be subject to separate copyright, citation, or
publisher requirements.
