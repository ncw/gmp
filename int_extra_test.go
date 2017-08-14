// Copyright 2009 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Test extra functionality

package gmp

import (
	"math/rand"
	"testing"
	"time"
)

type binaryFun func(a, b int64) bool
type ternaryFun func(a, b, c int64) bool

var random *rand.Rand
var perFuncTests []int

func init() {
	random = rand.New(rand.NewSource(time.Now().UnixNano()))
	perFuncTests = random.Perm(50)
}

func randoms(num int, bits int) <-chan int64 {
	channel := make(chan int64)
	go func(out chan<- int64) {
		for _, i := range random.Perm(num) {
			ran := random.Int63n(1<<uint(bits-1) - 1)
			if i&1 == 1 {
				ran = -ran
			}
			out <- ran
		}
		close(out)
	}(channel)
	return channel
}

func absi(i int64) int64 {
	if i < 0 {
		return -i
	}
	return i
}

func cmpi(a, b int64) int {
	if a < b {
		return -1
	}
	if a > b {
		return 1
	}
	return 0
}

func testBinary(t *testing.T, name string, fun binaryFun, maxBits int) {
	small := [...]int64{0, 1, -1, 2, -2, 3, -3}
	for _, x := range small {
		for _, y := range small {
			if !fun(x, y) {
				t.Errorf("%s failed for %v and %v", name, x, y)
			}
		}
	}
	for x := range randoms(10, maxBits) {
		for y := range randoms(10, maxBits) {
			if !fun(x, y) {
				t.Errorf("%s failed for %v and %v", name, x, y)
			}
		}
	}
}

func testTernary(t *testing.T, name string, fun ternaryFun) {
	small := [...]int64{0, 1, -1, 2, -2, 3, -3}
	for _, x := range small {
		for _, y := range small {
			for _, z := range small {
				if !fun(x, y, z) {
					t.Errorf("%s failed for %v, %v and %v", name, x, y, z)
				}
			}
		}
	}
	num, bits := 6, 30
	for x := range randoms(num, bits) {
		for y := range randoms(num, bits) {
			for z := range randoms(num, bits) {
				if !fun(x, y, z) {
					t.Errorf("%s failed for %v, %v and %v", name, x, y, z)
				}
			}
		}
	}
}

func TestSwap(t *testing.T) {
	fun := func(i, j int64) bool {
		a := NewInt(i)
		b := NewInt(j)
		a.Swap(b)
		return i == b.Int64() && j == a.Int64()
	}
	testBinary(t, "Swap", fun, 64)
}

func TestAddMul(t *testing.T) {
	fun := func(i, j, k int64) bool {
		a := NewInt(i)
		return a.AddMul(NewInt(j), NewInt(k)).Int64() == i+j*k
	}
	testTernary(t, "AddMul", fun)
}

func TestAddUint32(t *testing.T) {
	fun := func(i, j int64) bool {
		a := NewInt(i)
		k := uint32(j)
		return a.AddUint32(a, k).Int64() == i+int64(k)
	}
	testBinary(t, "AddUint32", fun, 62)
}

func TestSubUint32(t *testing.T) {
	fun := func(i, j int64) bool {
		a := NewInt(i)
		k := uint32(j)
		return a.SubUint32(a, k).Int64() == i-int64(k)
	}
	testBinary(t, "SubUint32", fun, 62)
}

func TestUint32Sub(t *testing.T) {
	fun := func(i, j int64) bool {
		a := NewInt(i)
		k := uint32(j)
		return a.Uint32Sub(k, a).Int64() == int64(k)-i
	}
	testBinary(t, "Uint32Sub", fun, 62)
}

func TestMulUint32(t *testing.T) {
	fun := func(i, j int64) bool {
		a := NewInt(i)
		k := uint32(j)
		return a.MulUint32(a, k).Int64() == i*int64(k)
	}
	testBinary(t, "MulUint32", fun, 30)
}

func TestMulInt32(t *testing.T) {
	fun := func(i, j int64) bool {
		a := NewInt(i)
		k := int32(j)
		return a.MulInt32(a, k).Int64() == i*int64(k)
	}
	testBinary(t, "MulInt32", fun, 30)
}

func TestAddMulUint32(t *testing.T) {
	fun := func(i, j, k int64) bool {
		a := NewInt(i)
		n := uint32(k)
		return a.AddMulUint32(NewInt(j), n).Int64() == i+j*int64(n)
	}
	testTernary(t, "AddMulUint32", fun)
}

func TestSubMul(t *testing.T) {
	fun := func(i, j, k int64) bool {
		a := NewInt(i)
		return a.SubMul(NewInt(j), NewInt(k)).Int64() == i-j*k
	}
	testTernary(t, "SubMul", fun)
}

func TestSubMulUint32(t *testing.T) {
	fun := func(i, j, k int64) bool {
		a := NewInt(i)
		n := uint32(k)
		return a.SubMulUint32(NewInt(j), n).Int64() == i-j*int64(n)
	}
	testTernary(t, "SubMulUint32", fun)
}

func TestCmpUint32(t *testing.T) {
	fun := func(i, j int64) bool {
		a := NewInt(i)
		k := uint32(j)
		return a.CmpUint32(k) == cmpi(i, int64(k))
	}
	testBinary(t, "CmpUint32", fun, 64)
}

func TestCmpInt32(t *testing.T) {
	fun := func(i, j int64) bool {
		a := NewInt(i)
		k := int32(j)
		return a.CmpInt32(k) == cmpi(i, int64(k))
	}
	testBinary(t, "CmpInt32", fun, 64)
}

func TestCmpAbs(t *testing.T) {
	fun := func(i, j int64) bool {
		a := NewInt(i)
		return a.CmpAbs(NewInt(j)) == cmpi(absi(i), absi(j))
	}
	testBinary(t, "CmpAbs", fun, 64)
}

func TestCmpAbsUint32(t *testing.T) {
	fun := func(i, j int64) bool {
		a := NewInt(i)
		k := uint32(j)
		return a.CmpAbsUint32(k) == cmpi(absi(i), int64(k))
	}
	testBinary(t, "CmpAbsUint32", fun, 64)
}

func TestUint32(t *testing.T) {
	for _ = range perFuncTests {
		var n = uint32(random.Int63())
		if NewInt(int64(n)).Uint32() != n {
			t.Errorf("Uint32 failed for %v", n)
		}
	}
}

func TestInt32(t *testing.T) {
	for _ = range perFuncTests {
		var n = int32(random.Int63())
		if NewInt(int64(n)).Int32() != n {
			t.Errorf("Int32 failed for %v", n)
		}
	}
}

func TestSqrt(t *testing.T) {
	a := NewInt(1)
	aSquared := NewInt(1)
	ten := NewInt(10)
	hundred := NewInt(100)
	root := new(Int)
	for _ = range perFuncTests {
		root := root.Sqrt(aSquared)
		if root.Cmp(a) != 0 {
			t.Errorf("Sqrt failed got %d expecting %d", root, a)
		}
		a.Mul(a, ten)
		aSquared.Mul(aSquared, hundred)
	}
}

func TestRoot(t *testing.T) {
  a := NewInt(1)
  aSquared := NewInt(1)
  ten := NewInt(10)
  hundred := NewInt(100)
  root := new(Int)
  for _ = range perFuncTests {
    root := root.Root(aSquared,2)
    if root.Cmp(a) != 0 {
      t.Errorf("Root failed got %d expecting %d", root, a)
    }
    a.Mul(a, ten)
    aSquared.Mul(aSquared, hundred)
  }
}