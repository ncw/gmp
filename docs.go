// Copyright 2009 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Package gmp implements multi-precision arithmetic (big numbers).
//
// This package provides a drop in replacement for Go's built in
// math/big integer package using the GNU Multiprecision Library (GMP)
// to implement the operations.
//
// GMP is very much faster than Go's math/big however it is an
// external C library with all the problems that entails (cgo,
// dependencies etc)
//
// The following numeric types are supported:
//
//      - Int   signed integers
//      - Rat   rational numbers are NOT yet supported
//
// Methods are typically of the form:
//
//      func (z *Int) Op(x, y *Int) *Int        (similar for *Rat)
//
// and implement operations z = x Op y with the result as receiver; if it
// is one of the operands it may be overwritten (and its memory reused).
// To enable chaining of operations, the result is also returned. Methods
// returning a result other than *Int or *Rat take one of the operands as
// the receiver.
//
package gmp
