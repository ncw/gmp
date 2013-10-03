// Copyright 2009 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Test extra functionality

package gmp

import (
	"testing"
)

func TestSqrt(t *testing.T) {
	a := NewInt(1)
	a_squared := NewInt(1)
	ten := NewInt(10)
	hundred := NewInt(100)
	root := new(Int)
	for i := 0; i < 50; i++ {
		root := root.Sqrt(a_squared)
		if root.Cmp(a) != 0 {
			t.Errorf("Sqrt failed got %d expecting %d", root, a)
		}
		a.Mul(a, ten)
		a_squared.Mul(a_squared, hundred)
	}
}
