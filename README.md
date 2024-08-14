# LabMate

LabMate is your friendly robotic assistant for writing meaningful
Matlab code.

## Installation

You will need to have the `GHC` Haskell compiler and the `cabal` tool
on your system. To install, clone the repository, and execute

```shell
cabal install --overwrite-policy=always
```

This should give you a `labmate` executable to run.

## Usage

LabMate is meant to work as a *transducer*: it converts an input file
into a possibly more informal output file. If the input file contains
*directives* (encoded as formally marked Matlab comments), the output
file will contain additional *responses*, either in the form of Matlab
comments again, or in the form of generated Matlab code.

**LabMate as a filter**: If LabMate is given no argument, it reads
from the standard input stream and writes to the standard output
stream. Thus LabMate can be invoked as follows:

```shell
cat infile.m | labmate
```

This functionality is useful for running LabMate as a "filter" in your
favourite text editor; see instructions for setting up an Emacs mode
that does this below.

**LabMate acting on a given file:** If LabMate is given a filename as
an argument, it will read from the given file, and output an updated
version of the file to standard output. Thus LabMate can also be
invoked as follows:

```shell
labmate infile.m > outfile.m
```

**LabMate acting on a given directory:** If LabMate is given a
directory name as input, it will try to parse all the Matlab files in
that directory, and report how well it succeeded. It will not actually
transduce the contents of the files. This mode can be useful for
verifying that LabMate at least understands the syntactic structure of
an existing codebase.

```shell
labmate examples/
```

## Other command line options

LabMate also understands the following command line options:

| Option       | Action                                          |
|--------------|-------------------------------------------------|
| --help       | Print help text, then exit                      |
| --verbose    | Print internal state of LabMate after execution |
| --no-version | Do not insert LabMate version number in output  |

## Emacs mode

The file [labmate.el](emacs/labmate.el) can be used to add basic
LabMate transducer functionality to the text editor Emacs. Add the
following to your `.emacs` file to enable it (where `PATH` is the path
to wherever you have stored `labmate.el`):

```elisp
(autoload 'labmate-mode "PATH/labmate.el" nil t)
(add-to-list 'auto-mode-alist '("\\.m\\'" . labmate-mode))

```

After doing so, opening a file with extension `.m` should
automatically start LabMate mode, which will give you syntax
highlighting of directives and responses. More importantly, you can
run LabMate on the current buffer by pressing `C-c C-l` (Control-C
followed by Control-L).
