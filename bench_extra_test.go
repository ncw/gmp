package gmp

import (
	"testing"
)

func BenchmarkSwapO(bench *testing.B) {
	a := NewInt(1)
	b := NewInt(2)
	c := NewInt(0)
	for i := bench.N; i > 0; i-- {
		c.Set(a)
		a.Set(b)
		b.Set(c)
	}
}

func BenchmarkSwapX(bench *testing.B) {
	a := NewInt(1)
	b := NewInt(2)
	for i := bench.N; i > 0; i-- {
		a.Swap(b)
	}
}

func BenchmarkAddUintO(bench *testing.B) {
	a := NewInt(1)
	b := NewInt(2)
	for i := bench.N; i > 0; i-- {
		b.SetUint64(uint64(i))
		a.Add(a, b)
	}
}

func BenchmarkAddUintX(bench *testing.B) {
	a := NewInt(1)
	for i := bench.N; i > 0; i-- {
		a.AddUint32(a, uint32(i))
	}
}

func BenchmarkMulInt0(bench *testing.B) {
	a := NewInt(1)
	b := NewInt(2)
	for i := bench.N; i > 0; i-- {
		b.SetInt64(1)
		a.Mul(a, b)
	}
}

func BenchmarkMulIntX(bench *testing.B) {
	a := NewInt(1)
	for i := bench.N; i > 0; i-- {
		a.MulInt32(a, 1)
	}
}

func BenchmarkAddMulO(bench *testing.B) {
	a := NewInt(1)
	b := NewInt(2)
	c := NewInt(0)
	for i := bench.N; i > 0; i-- {
		a.Add(a, c)
		b.Mul(b, a)
	}
}

func BenchmarkAddMulX(bench *testing.B) {
	a := NewInt(1)
	b := NewInt(2)
	c := NewInt(0)
	for i := bench.N; i > 0; i-- {
		b.AddMul(a, c)
	}
}

func BenchmarkCmpIntO(bench *testing.B) {
	a := NewInt(1)
	b := NewInt(2)
	for i := bench.N; i > 0; i-- {
		a.SetInt64(int64(i))
		b.Cmp(a)
	}
}

func BenchmarkCmpIntX(bench *testing.B) {
	a := NewInt(1)
	for i := bench.N; i > 0; i-- {
		a.CmpInt32(int32(i))
	}
}

func BenchmarkCmpAbsO(bench *testing.B) {
	a := NewInt(1)
	b := NewInt(2)
	for i := bench.N; i > 0; i-- {
		a.Abs(a)
		b.Abs(b)
		a.Cmp(b)
	}
}

func BenchmarkCmpAbsX(bench *testing.B) {
	a := NewInt(1)
	b := NewInt(1)
	for i := bench.N; i > 0; i-- {
		a.CmpAbs(b)
	}
}

func BenchmarkGetIntO(bench *testing.B) {
	a := NewInt(1)
	for i := bench.N; i > 0; i-- {
		a.Int64()
	}
}

func BenchmarkGetIntX(bench *testing.B) {
	a := NewInt(1)
	for i := bench.N; i > 0; i-- {
		a.Int32()
	}
}

func BenchmarkGetUintO(bench *testing.B) {
	a := NewInt(1)
	for i := bench.N; i > 0; i-- {
		a.Uint64()
	}
}

func BenchmarkGetUintX(bench *testing.B) {
	a := NewInt(1)
	for i := bench.N; i > 0; i-- {
		a.Uint32()
	}
}
