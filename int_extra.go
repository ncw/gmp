// Copyright 2013 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Implement extra functionality not in big.Int

package gmp

/*
#cgo LDFLAGS: -lgmp
#include <gmp.h>
#include <stdlib.h>
*/
import "C"

// Sqrt sets x to the truncated integer part of the square root of x
//
// NB This is not part of big.Int
func (z *Int) Sqrt(x *Int) *Int {
	z.doinit()
	C.mpz_sqrt(&z.i[0], &x.i[0])
	return z
}
