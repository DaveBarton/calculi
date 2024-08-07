# calculi

## “Use all your cores”

<!-- ![Lines of code](https://img.shields.io/tokei/lines/github/DaveBarton/calculi?label=lines%20of%20code) -->
![Code size in bytes](https://img.shields.io/github/languages/code-size/DaveBarton/calculi)
![License](https://img.shields.io/github/license/DaveBarton/calculi)
<!-- ![Hackage](https://img.shields.io/hackage/v/DaveBarton/calculi) -->

Pure mathematics is a rich source of cpu-intensive problems with very precise semantics.
Typically its algorithms and data structures are side-effect free, which makes them surprisingly
easy to parallelize efficiently in [Haskell](https://www.haskell.org/). Calculating
[Gröbner Bases](https://en.wikipedia.org/wiki/Gr%C3%B6bner_basis) is a good first example. So
far, we have implemented the improved Buchberger algorithm for the case of polynomials over
`ℤ/pℤ`, achieving near-linear speedups for up to at least 6 cores, and currently about 25x
speedups counting garbage collection, or 32x not counting gc, for 60 cores. The Buchberger
algorithm is not obviously or "embarrassingly" parallel, and we believe this is the first
successful attempt to parallelize it.

You can see some timings at [timings/timings.txt](timings/timings.txt). If you want to compile
and run these calculations on your machine, the quickest way is probably:

1. Download and install ghcup, ghc 9.4.8 or later, and cabal from
[GHCup](https://www.haskell.org/ghcup/) or
[Getting started - GHCup](https://www.haskell.org/ghcup/install/), if you haven't already.

2. [Download](archive/refs/heads/main.zip), or fork and clone, this repository (calculi).

3. `cd` into your `calculi` directory, and run <!-- `cabal bench` or -->
`cabal run time-gb -- +RTS -N6` with "6" replaced by the number of cores you want to use (we
suggest the number of physical performance cores on your machine minus 1 or 2, not counting
hyperthreading or efficiency cores). You can also run `cabal run time-gb -- --help` to see more
options.
