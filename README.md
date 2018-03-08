# Slepice

[![Build Status](https://travis-ci.org/frantisekfarka/slepice.svg?branch=master)](https://travis-ci.org/frantisekfarka/slepice)


Prototype type-inference engine for LF via proof-relevant resolution.

## Installation 

The command `make` builds the `main.native` binary in the `ocaml/` subdirectory.
The command `make doc` builds documentation in the `doc/` subdirectory.


## Usage

```
usage: slepice -sig <filename> -term <filenamen> [ -o <basename> ]

  -sig <filename>         Input signature
  -term <filename>        Input term
  -o <basename>           Output files basename
  -print-sig <false>      Print parsed signature
  -print-term <false>     Print parsed term
  -print <false>          Print parsed signature and term
  -help                   Display this list of options
  --help                  Display this list of options
```



