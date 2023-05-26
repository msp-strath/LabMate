# LabRat

LabRat is your friendly robotic assistant for writing meaningful
Matlab code.

At the moment, LabRat mostly parses Matlab code, but in the future, it
will also check if the code makes sense, and offer to generate code.

## Installation

You will need to have the `GHC` Haskell compiler and the `cabal` tool
on your system. To install, clone the repository, and execute

```shell
cabal install --overwrite-policy=always
```

This should give you a `labrat` executable to run.

## Usage

LabRat can either be given a file or a directory as an argument.

**Parsing individual files:** The invocation

```shell
labrat file.m
```

will parse the Matlab file `file.m` and print out the internal LabRat
parse tree for the file.

**Parsing directories:** The invocation

```shell
labrat dir
```

will parse all `.m` files in the directory `dir` and report how many
files were successfully parsed. Any parse errors will also be
reported.

If no argument is given to LabRat, this currently means the same as
`labrat .`, that is, LabRat will try to parse all Matlab files in the
current directory.
