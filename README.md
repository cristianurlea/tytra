# TyTraCL (“Coordination Language”)

This is the compiler for the TyTra Coordination Language, part of the [TyTra](http://www.tytra.org.uk) flow for high-level FPGA programming. TyTraCL is a functional language, intended to express the dataflow of computations on vectors (arrays of fixed size) using map and fold.

The aim is to allow generation of variants of the program, calculate the cost and performance, and ultimately emit the TyTra-IR code to create the final HDL for the FPGA

For more details, please read the paper in `docs`.

## PREREQUISITES:

The essential prerequisites to build and cost programs with the TyTraCL compiler are:

- Working Haskell/Stack Installation
- Graphviz to explore the transformed AST Graph


## INSTALLATION:

  Clone the repository or otherwise download a snapshot:

    # `git clone` the repo

  Build using `stack`:

    # stack build

## HOW TO USE:

  Call the compiler binary, passing in a file path and one or more transformation names to apply.

    $  stack exec bigbird-exe <input_file> [cleanup | autopar | inline]"

  Example input programs are provided in `./test/hllExamples`

#### Haskell

The compiler is written in `Haskell`.

- [ghc >= 7.10 ](http://www.haskell.org) to compile
- Install the [Haskell Stack](https://docs.haskellstack.org/en/stable/README/)
