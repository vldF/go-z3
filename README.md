go-z3 provides Go bindings for
the [Z3 SMT solver](https://github.com/Z3Prover/z3).

Installation
============

First, follow the instructions to
[download and install](https://github.com/Z3Prover/z3/blob/master/README.md)
the Z3 C library.

go-z3 requires Z3 version 4.7.1 or later.

If you installed the C library to a non-default location (such as a
directory under `$HOME`), set the following environment variables:

```sh
# For building:
export CGO_CFLAGS=-I$Z3PREFIX/include CGO_LDFLAGS=-L$Z3PREFIX/lib
# For running binaries (including tests):
export LD_LIBRARY_PATH=$Z3PREFIX/lib
```

Then download and build go-z3:

```sh
go get -u github.com/vldF/go-z3/z3
```

Documentation
=============

See [pkg.go.dev](https://pkg.go.dev/github.com/vldF/go-z3/z3).
