Gmp
===

[![GoDoc](https://godoc.org/github.com/ncw/gmp?status.svg)](https://godoc.org/github.com/ncw/gmp)
[![Build Status](https://travis-ci.org/ncw/gmp.svg?branch=master)](https://travis-ci.org/ncw/gmp)

This package provides a drop in replacement for Go's built in
[math/big](http://golang.org/pkg/math/big/) big integer package using
the [GNU Multiprecision Library](http://gmplib.org/) (GMP).

GMP is very much faster than Go's math/big however it is an external C
library with all the problems that entails (cgo, dependencies etc)

This library was made by taking the [cgo example of wrapping
GMP](http://golang.org/misc/cgo/gmp/gmp.go) from the Go source and
doing the following to it

* Copying the implementation from misc/cgo/gmp/gmp.go
* Copying the documentation from src/pkg/math/big/int.go
* Additional implementation of missing methods
* Bug fixes for existing implementations
* Making it passes the test suite from src/pkg/math/big/int_test.go
* Adding memory management
* Fix problems on 32 bit platforms when using `int64` values which don't fit into a `C.long`
* Implementing Rat support making it pass src/pkg/math/big/rat_test.go

See here for package docs

* https://godoc.org/github.com/ncw/gmp

Install
-------

Use go to install the library

    go get github.com/ncw/gmp

Usage
-----

See here for full package docs

* http://go.pkgdoc.org/github.com/ncw/gmp

To use as in a drop in replacement for math/big, replace

    import "math/big"

With

    import big "github.com/ncw/gmp"

Features that aren't part of math/big are clearly marked and if you
are using those, then I suggest you import as

    import "github.com/ncw/gmp"
    
Testing
-------

To run the tests use

    go test github.com/ncw/gmp

The tests have been copied from the tests for the math/big library in
the Go source and modified as little as possible so it should be 100%
compatible.

Differences
-----------

Here are the differences between math/big and this package

* `Int.Bits` and `Int.SetBits` not implemented
* `Rat.Num()` and `Rat.Denom()` return a copy not a reference, so
*  If you want to set them use the new methods `Rat.SetNum()` and `Rat.SetDenom()`


License
-------

As this contains a great deal of code copied from the Go source it is
licenced identically to the Go source itself - see the LICENSE file
for details.

Contact and support
-------------------

The project website is at:

* https://github.com/ncw/gmp

There you can file bug reports, ask for help or contribute patches.

Authors
-------

* [The Go team](http://golang.org/AUTHORS)
* Nick Craig-Wood <nick@craig-wood.com>

Contributors
------------

* Bert Gijsbers <gijhub@gmail.com>
