package gmp_test

import (
	"math/big"
	"testing"
)

// Make a n digit number
func nDigitNumberMathBig(digits int64) *big.Int {
	x := big.NewInt(10)
	n := big.NewInt(digits)
	one := big.NewInt(1)
	x.Exp(x, n, nil)
	x.Sub(x, one)
	return x
}

func benchmarkMathBigAddN(b *testing.B, digits int64) {
	x := nDigitNumberMathBig(digits)
	y := nDigitNumberMathBig(digits)
	z := big.NewInt(0)
	b.ResetTimer()
	b.StartTimer()
	for i := b.N - 1; i >= 0; i-- {
		z.Add(x, y)
	}
}

func BenchmarkMathBigAdd1(b *testing.B) {
	benchmarkMathBigAddN(b, 10)
}
func BenchmarkMathBigAdd10(b *testing.B) {
	benchmarkMathBigAddN(b, 10)
}
func BenchmarkMathBigAdd100(b *testing.B) {
	benchmarkMathBigAddN(b, 100)
}
func BenchmarkMathBigAdd1000(b *testing.B) {
	benchmarkMathBigAddN(b, 1000)
}
func BenchmarkMathBigAdd10000(b *testing.B) {
	benchmarkMathBigAddN(b, 10000)
}
func BenchmarkMathBigAdd100000(b *testing.B) {
	benchmarkMathBigAddN(b, 100000)
}
func BenchmarkMathBigAdd1000000(b *testing.B) {
	benchmarkMathBigAddN(b, 1000000)
}

func benchmarkMathBigMulN(b *testing.B, digits int64) {
	x := nDigitNumberMathBig(digits)
	y := nDigitNumberMathBig(digits)
	z := big.NewInt(0)
	b.ResetTimer()
	b.StartTimer()
	for i := b.N - 1; i >= 0; i-- {
		z.Mul(x, y)
	}
}

func BenchmarkMathBigMul1(b *testing.B) {
	benchmarkMathBigMulN(b, 10)
}
func BenchmarkMathBigMul10(b *testing.B) {
	benchmarkMathBigMulN(b, 10)
}
func BenchmarkMathBigMul100(b *testing.B) {
	benchmarkMathBigMulN(b, 100)
}
func BenchmarkMathBigMul1000(b *testing.B) {
	benchmarkMathBigMulN(b, 1000)
}
func BenchmarkMathBigMul10000(b *testing.B) {
	benchmarkMathBigMulN(b, 10000)
}
func BenchmarkMathBigMul100000(b *testing.B) {
	benchmarkMathBigMulN(b, 100000)
}
func BenchmarkMathBigMul1000000(b *testing.B) {
	benchmarkMathBigMulN(b, 1000000)
}
