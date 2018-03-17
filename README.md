# Slepice

[![Build Status](https://travis-ci.org/frantisekfarka/slepice.svg?branch=master)](https://travis-ci.org/frantisekfarka/slepice)


Prototype type-inference engine for LF via proof-relevant resolution.

## Prerequisites

The following tools need to be available before building `slepice`:
- _Ocaml_ development environment
- _Coq_
- _Ott_ version 0.25 (https://github.com/ott-lang/ott)

A local copy of ``ott`` can be installed by running the ``configure`` script.

Documentation further requires _latex_ distribution available with
_latex-extra_ and _xcolor_ packages.


## Installation 

The command `make` builds the `slepice` binary. 
The command `make doc` builds documentation in the `doc/` subdirectory.


## Usage

```
usage: slepice <options> -sig <filename> -term <filenamen> [ -o <basename> ]

  -sig <filename>         Input signature
  -term <filename>        Input term
  -o <basename>           Output files basename
  -print-sig <false>      Print parsed signature
  -print-term <false>     Print parsed term
  -print <false>          Print parsed signature and term
  -help                   Display this list of options
  --help                  Display this list of options
```

The binary either displays the generated logic program and goal or, when a basename
is provided, it generates files `basename.prog` and `basename.g` with the generated 
program and the generated goal respectively.

## Documentation

The directory ``doc/`` contains html documentation generated from Coq and
the file ``slepice.pdf`` that contains an overview of Ott grammar.

## Examples

Run the following command:

```
./slepice \
    -sig examples/fromJust.sig \
    -term examples/fromJust.tt
```

