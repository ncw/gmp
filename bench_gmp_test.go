package gmp

import (
	"testing"
)

// Make a n digit number
func nDigitNumberGmp(digits int64) *Int {
	x := NewInt(10)
	n := NewInt(digits)
	one := NewInt(1)
	x.Exp(x, n, nil)
	x.Sub(x, one)
	return x
}

func benchmarkGmpAddN(b *testing.B, digits int64) {
	x := nDigitNumberGmp(digits)
	y := nDigitNumberGmp(digits)
	z := NewInt(0)
	b.ResetTimer()
	b.StartTimer()
	for i := b.N - 1; i >= 0; i-- {
		z.Add(x, y)
	}
}

func BenchmarkGmpAdd1(b *testing.B) {
	benchmarkGmpAddN(b, 10)
}
func BenchmarkGmpAdd10(b *testing.B) {
	benchmarkGmpAddN(b, 10)
}
func BenchmarkGmpAdd100(b *testing.B) {
	benchmarkGmpAddN(b, 100)
}
func BenchmarkGmpAdd1000(b *testing.B) {
	benchmarkGmpAddN(b, 1000)
}
func BenchmarkGmpAdd10000(b *testing.B) {
	benchmarkGmpAddN(b, 10000)
}
func BenchmarkGmpAdd100000(b *testing.B) {
	benchmarkGmpAddN(b, 100000)
}
func BenchmarkGmpAdd1000000(b *testing.B) {
	benchmarkGmpAddN(b, 1000000)
}

func benchmarkGmpMulN(b *testing.B, digits int64) {
	x := nDigitNumberGmp(digits)
	y := nDigitNumberGmp(digits)
	z := NewInt(0)
	b.ResetTimer()
	b.StartTimer()
	for i := b.N - 1; i >= 0; i-- {
		z.Mul(x, y)
	}
}

func BenchmarkGmpMul1(b *testing.B) {
	benchmarkGmpMulN(b, 10)
}
func BenchmarkGmpMul10(b *testing.B) {
	benchmarkGmpMulN(b, 10)
}
func BenchmarkGmpMul100(b *testing.B) {
	benchmarkGmpMulN(b, 100)
}
func BenchmarkGmpMul1000(b *testing.B) {
	benchmarkGmpMulN(b, 1000)
}
func BenchmarkGmpMul10000(b *testing.B) {
	benchmarkGmpMulN(b, 10000)
}
func BenchmarkGmpMul100000(b *testing.B) {
	benchmarkGmpMulN(b, 100000)
}
func BenchmarkGmpMul1000000(b *testing.B) {
	benchmarkGmpMulN(b, 1000000)
}
