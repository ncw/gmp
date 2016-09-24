// Copyright 2010 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// This file implements multi-precision rational numbers.

package gmp

/*
#include <gmp.h>
#include <stdlib.h>

// Macros
int __mpq_sgn(mpq_ptr op) {
	return mpq_sgn(op);
}
int __mpz_cmp_ui(mpz_ptr op, unsigned long n) {
	return mpz_cmp_ui(op, n);
}
mpz_ptr _mpq_numref(mpq_t op) {
    return mpq_numref(op);
}
mpz_ptr _mpq_denref(mpq_t op) {
    return mpq_denref(op);
}
// Sign of the numerator
int _mpq_num_sgn(mpq_t op) {
	return mpz_sgn(mpq_numref(op));
}

*/
import "C"

import (
	"encoding/binary"
	"errors"
	"fmt"
	"math"
	"runtime"
	"strings"
	"unsafe"
)

// A Rat represents a quotient a/b of arbitrary precision.
// The zero value for a Rat represents the value 0.
type Rat struct {
	i    C.mpq_t
	init bool
}

// Finalizer - release the memory allocated to the mpz
func ratFinalize(z *Rat) {
	if z.init {
		runtime.SetFinalizer(z, nil)
		C.mpq_clear(&z.i[0])
		z.init = false
	}
}

// Rat promises that the zero value is a 0, but in gmp
// the zero value is a crash.  To bridge the gap, the
// init bool says whether this is a valid gmp value.
// doinit initializes z.i if it needs it.
func (z *Rat) doinit() {
	if z.init {
		return
	}
	z.init = true
	C.mpq_init(&z.i[0])
	runtime.SetFinalizer(z, ratFinalize)
}

// Clear the allocated space used by the number
//
// This normally happens on a runtime.SetFinalizer call, but if you
// want immediate deallocation you can call it.
//
// NB This is not part of big.Rat
func (z *Rat) Clear() {
	ratFinalize(z)
}

// NewRat creates a new Rat with numerator a and denominator b.
func NewRat(a, b int64) *Rat {
	return new(Rat).SetFrac64(a, b)
}

// SetFloat64 sets z to exactly f and returns z.
// If f is not finite, SetFloat returns nil.
func (z *Rat) SetFloat64(f float64) *Rat {
	if math.IsNaN(f) || math.IsInf(f, 0) {
		return nil
	}
	z.doinit()
	C.mpq_set_d(&z.i[0], C.double(f))
	return z
}

// Float64Gmp returns the nearest float64 value for z and a bool indicating
// whether f represents z exactly. If the magnitude of z is too large to
// be represented by a float64, f is an infinity and exact is false.
// The sign of f always matches the sign of z, even if f == 0.
//
// NB This uses GMP which is fast but rounds differently to Float64
func (z *Rat) Float64Gmp() (f float64, exact bool) {
	z.doinit()
	f = float64(C.mpq_get_d(&z.i[0]))
	if !(math.IsNaN(f) || math.IsInf(f, 0)) {
		exact = new(Rat).SetFloat64(f).Cmp(z) == 0
	}
	return
}

// low64 returns the least significant 64 bits of natural number z.
func low64(z *Int) uint64 {
	// FIXME not wildy efficient!
	t := new(Int).SetUint64(0xffffffffffffffff)
	t.And(t, z)
	return t.Uint64()
}

// quotToFloat returns the non-negative IEEE 754 double-precision
// value nearest to the quotient a/b, using round-to-even in halfway
// cases.  It does not mutate its arguments.
// Preconditions: b is non-zero; a and b have no common factors.
func quotToFloat(a, b *Int) (f float64, exact bool) {
	// TODO(adonovan): specialize common degenerate cases: 1.0, integers.
	alen := a.BitLen()
	if alen == 0 {
		return 0, true
	}
	blen := b.BitLen()
	if blen == 0 {
		panic("division by zero")
	}

	// 1. Left-shift A or B such that quotient A/B is in [1<<53, 1<<55).
	// (54 bits if A<B when they are left-aligned, 55 bits if A>=B.)
	// This is 2 or 3 more than the float64 mantissa field width of 52:
	// - the optional extra bit is shifted away in step 3 below.
	// - the high-order 1 is omitted in float64 "normal" representation;
	// - the low-order 1 will be used during rounding then discarded.
	exp := alen - blen
	a2, b2 := new(Int).Set(a), new(Int).Set(b)
	if shift := 54 - exp; shift > 0 {
		a2.Lsh(a2, uint(shift))
	} else if shift < 0 {
		b2.Lsh(b2, uint(-shift))
	}

	// 2. Compute quotient and remainder (q, r).  NB: due to the
	// extra shift, the low-order bit of q is logically the
	// high-order bit of r.
	q, r := new(Int).DivMod(a2, b2, new(Int)) // (recycle a2)
	mantissa := low64(q)
	haveRem := r.Sign() != 0 // mantissa&1 && !haveRem => remainder is exactly half

	// 3. If quotient didn't fit in 54 bits, re-do division by b2<<1
	// (in effect---we accomplish this incrementally).
	if mantissa>>54 == 1 {
		if mantissa&1 == 1 {
			haveRem = true
		}
		mantissa >>= 1
		exp++
	}
	if mantissa>>53 != 1 {
		panic("expected exactly 54 bits of result")
	}

	// 4. Rounding.
	if -1022-52 <= exp && exp <= -1022 {
		// Denormal case; lose 'shift' bits of precision.
		shift := uint64(-1022 - (exp - 1)) // [1..53)
		lostbits := mantissa & (1<<shift - 1)
		haveRem = haveRem || lostbits != 0
		mantissa >>= shift
		exp = -1023 + 2
	}
	// Round q using round-half-to-even.
	exact = !haveRem
	if mantissa&1 != 0 {
		exact = false
		if haveRem || mantissa&2 != 0 {
			if mantissa++; mantissa >= 1<<54 {
				// Complete rollover 11...1 => 100...0, so shift is safe
				mantissa >>= 1
				exp++
			}
		}
	}
	mantissa >>= 1 // discard rounding bit.  Mantissa now scaled by 2^53.

	f = math.Ldexp(float64(mantissa), exp-53)
	if math.IsInf(f, 0) {
		exact = false
	}
	return
}

// Float64 returns the nearest float64 value for z and a bool indicating
// whether f represents z exactly. If the magnitude of z is too large to
// be represented by a float64, f is an infinity and exact is false.
// The sign of f always matches the sign of z, even if f == 0.
func (z *Rat) Float64() (f float64, exact bool) {
	a := z.Num()
	negative := false
	if a.Sign() < 0 {
		a.Neg(a)
		negative = true
	}
	b := z.Denom()
	f, exact = quotToFloat(a, b)
	if negative {
		f = -f
	}
	return
}

// SetNum sets the numerator of z returning z
//
// NB this isn't part of math/big which uses Num().Set() for this
// purpose. In gmp Num() returns a copy hence the need for a SetNum()
// method.
func (z *Rat) SetNum(a *Int) *Rat {
	z.doinit()
	a.doinit()
	C.mpq_set_num(&z.i[0], &a.i[0])
	C.mpq_canonicalize(&z.i[0])
	return z
}

// SetDenom sets the numerator of z returning z
//
// NB this isn't part of math/big which uses Num().Set() for this
// purpose. In gmp Num() returns a copy hence the need for a SetNum()
// method.
func (z *Rat) SetDenom(a *Int) *Rat {
	z.doinit()
	a.doinit()
	C.mpq_set_den(&z.i[0], &a.i[0])
	// If numerator is zero don't canonicalize
	if C._mpq_num_sgn(&z.i[0]) != 0 {
		C.mpq_canonicalize(&z.i[0])
	}
	return z
}

// SetFrac sets z to a/b and returns z.
func (z *Rat) SetFrac(a, b *Int) *Rat {
	z.doinit()
	a.doinit()
	b.doinit()
	// FIXME copying? or referencing?
	C.mpq_set_num(&z.i[0], &a.i[0])
	C.mpq_set_den(&z.i[0], &b.i[0])
	C.mpq_canonicalize(&z.i[0])
	return z
}

// SetFrac64 sets z to a/b and returns z.
func (z *Rat) SetFrac64(a, b int64) *Rat {
	z.doinit()
	if b == 0 {
		panic("division by zero")
	}
	// Detect overflow if running on 32 bits
	if a == int64(C.long(a)) && b == int64(C.long(b)) {
		if b < 0 {
			a = -a
			b = -b
		}
		C.mpq_set_si(&z.i[0], C.long(a), C.ulong(b))
		C.mpq_canonicalize(&z.i[0])
		if b < 0 {
			// This only happens when b = 1<<63
			z.Neg(z)
		}
	} else {
		// Slow path but will work on 32 bit architectures
		z.SetFrac(NewInt(a), NewInt(b))
	}
	return z
}

// SetInt sets z to x (by making a copy of x) and returns z.
func (z *Rat) SetInt(x *Int) *Rat {
	z.doinit()
	// FIXME copying? or referencing?
	C.mpq_set_z(&z.i[0], &x.i[0])
	return z
}

// SetInt64 sets z to x and returns z.
func (z *Rat) SetInt64(x int64) *Rat {
	z.SetFrac64(x, 1)
	return z
}

// Set sets z to x (by making a copy of x) and returns z.
func (z *Rat) Set(x *Rat) *Rat {
	if z != x {
		z.doinit()
		C.mpq_set(&z.i[0], &x.i[0])
	}
	return z
}

// Abs sets z to |x| (the absolute value of x) and returns z.
func (z *Rat) Abs(x *Rat) *Rat {
	z.doinit()
	C.mpq_abs(&z.i[0], &x.i[0])
	return z
}

// Neg sets z to -x and returns z.
func (z *Rat) Neg(x *Rat) *Rat {
	z.doinit()
	C.mpq_neg(&z.i[0], &x.i[0])
	return z
}

// Inv sets z to 1/x and returns z.
func (z *Rat) Inv(x *Rat) *Rat {
	z.doinit()
	x.doinit()
	if x.Sign() == 0 {
		panic("division by zero")
	}
	C.mpq_inv(&z.i[0], &x.i[0])
	return z
}

// Sign returns:
//
//	-1 if z <  0
//	 0 if z == 0
//	+1 if z >  0
//
func (z *Rat) Sign() int {
	z.doinit()
	return int(C.__mpq_sgn(&z.i[0]))
}

// IsInt returns true if the denominator of z is 1.
func (z *Rat) IsInt() bool {
	z.doinit()
	return C.__mpz_cmp_ui(C._mpq_denref(&z.i[0]), C.ulong(1)) == 0
}

// Num returns the numerator of z; it may be <= 0.  The result is a
// copy of z's numerator; it won't change if a new value is assigned
// to z, and vice versa.  The sign of the numerator corresponds to the
// sign of z.
//
// NB In math/big this is a reference to the numerator not a copy
func (z *Rat) Num() *Int {
	// Return an initialised *Int so we don't initialize or finalize it by accident
	z.doinit()
	res := new(Int)
	res.doinit()
	C.mpq_get_num(&res.i[0], &z.i[0])
	return res
}

// Denom returns the denominator of z; it is always > 0.  The result
// is a copy of z's denominator; it won't change if a new value is
// assigned to z, and vice versa.
//
// NB In math/big this is a reference to the denominator not a copy
func (z *Rat) Denom() *Int {
	// Return an initialised *Int so we don't initialize or finalize it by accident
	z.doinit()
	res := new(Int)
	res.doinit()
	C.mpq_get_den(&res.i[0], &z.i[0])
	return res
}

// Cmp compares z and y and returns:
//
//   -1 if z <  y
//    0 if z == y
//   +1 if z >  y
//
func (z *Rat) Cmp(y *Rat) (r int) {
	z.doinit()
	y.doinit()
	r = int(C.mpq_cmp(&z.i[0], &y.i[0]))
	if r < 0 {
		r = -1
	} else if r > 0 {
		r = 1
	}
	return
}

// Add sets z to the sum x+y and returns z.
func (z *Rat) Add(x, y *Rat) *Rat {
	x.doinit()
	y.doinit()
	z.doinit()
	C.mpq_add(&z.i[0], &x.i[0], &y.i[0])
	return z
}

// Sub sets z to the difference x-y and returns z.
func (z *Rat) Sub(x, y *Rat) *Rat {
	x.doinit()
	y.doinit()
	z.doinit()
	C.mpq_sub(&z.i[0], &x.i[0], &y.i[0])
	return z
}

// Mul sets z to the product x*y and returns z.
func (z *Rat) Mul(x, y *Rat) *Rat {
	x.doinit()
	y.doinit()
	z.doinit()
	C.mpq_mul(&z.i[0], &x.i[0], &y.i[0])
	return z
}

// Quo sets z to the quotient x/y and returns z.
// If y == 0, a division-by-zero run-time panic occurs.
func (z *Rat) Quo(x, y *Rat) *Rat {
	x.doinit()
	y.doinit()
	z.doinit()
	if y.Sign() == 0 {
		panic("division by zero")
	}
	C.mpq_div(&z.i[0], &x.i[0], &y.i[0])
	return z
}

func ratTok(ch rune) bool {
	return strings.IndexRune("+-/0123456789.eE", ch) >= 0
}

// Scan is a support routine for fmt.Scanner. It accepts the formats
// 'e', 'E', 'f', 'F', 'g', 'G', and 'v'. All formats are equivalent.
func (z *Rat) Scan(s fmt.ScanState, ch rune) error {
	tok, err := s.Token(true, ratTok)
	if err != nil {
		return err
	}
	if strings.IndexRune("efgEFGv", ch) < 0 {
		return errors.New("Rat.Scan: invalid verb")
	}
	if _, ok := z.SetString(string(tok)); !ok {
		return errors.New("Rat.Scan: invalid syntax")
	}
	return nil
}

// SetString sets z to the value of s and returns z and a boolean indicating
// success. s can be given as a fraction "a/b" or as a floating-point number
// optionally followed by an exponent. If the operation failed, the value of
// z is undefined but the returned value is nil.
func (z *Rat) SetString(s string) (*Rat, bool) {
	if len(s) == 0 {
		return nil, false
	}
	z.doinit()
	a := new(Int)
	b := new(Int)

	// check for a quotient
	sep := strings.Index(s, "/")
	if sep >= 0 {
		// FIXME Num and Denom are bust
		// if _, ok := z.Num().SetString(s[0:sep], 10); !ok {
		// 	return nil, false
		// }
		// if _, ok := z.Denom().SetString(s[sep+1:], 10); !ok {
		// 	return nil, false
		// }
		if _, ok := a.SetString(s[0:sep], 10); !ok {
			return nil, false
		}
		if _, ok := b.SetString(s[sep+1:], 10); !ok {
			return nil, false
		}
		z.SetFrac(a, b)
		C.mpq_canonicalize(&z.i[0])
		return z, true
	}

	// check for a decimal point
	sep = strings.Index(s, ".")
	// check for an exponent
	e := strings.IndexAny(s, "eE")
	exp := new(Int)
	if e >= 0 {
		if e < sep {
			// The E must come after the decimal point.
			return nil, false
		}
		if _, ok := exp.SetString(s[e+1:], 10); !ok {
			return nil, false
		}
		s = s[0:e]
	}
	if sep >= 0 {
		s = s[0:sep] + s[sep+1:]
		exp.Sub(exp, NewInt(int64(len(s)-sep)))
	}

	if _, ok := a.SetString(s, 10); !ok {
		return nil, false
	}
	absExp := new(Int).Abs(exp)
	powTen := new(Int).Exp(_Int10, absExp, nil)
	if exp.Sign() < 0 {
		b = powTen
	} else {
		a.Mul(a, powTen)
		b.SetInt64(1)
	}
	z.SetFrac(a, b)
	C.mpq_canonicalize(&z.i[0])

	return z, true
}

// string returns z in the base given
func (z *Rat) string(base int) string {
	if z == nil {
		return "<nil>"
	}
	z.doinit()
	p := C.mpq_get_str(nil, C.int(base), &z.i[0])
	s := C.GoString(p)
	C.free(unsafe.Pointer(p))
	return s
}

// String returns a string representation of z in the form "a/b" (even if b == 1).
func (z *Rat) String() string {
	s := z.string(10)
	if !strings.Contains(s, "/") {
		s += "/1"
	}
	return s
}

// RatString returns a string representation of z in the form "a/b" if b != 1,
// and in the form "a" if b == 1.
func (z *Rat) RatString() string {
	return z.string(10)
}

// FloatString returns a string representation of z in decimal form with prec
// digits of precision after the decimal point and the last digit rounded.
func (z *Rat) FloatString(prec int) string {
	if z.IsInt() {
		s := z.string(10)
		if prec > 0 {
			s += "." + strings.Repeat("0", prec)
		}
		return s
	}

	a := z.Num()
	a.Abs(a)
	b := z.Denom()
	q, r := new(Int).DivMod(a, b, new(Int))

	p := _Int1
	if prec > 0 {
		p = new(Int).Exp(_Int10, NewInt(int64(prec)), nil)
	}

	r.Mul(r, p)
	r2 := new(Int)
	r.DivMod(r, b, r2)

	// see if we need to round up
	r2.Add(r2, r2)
	if b.Cmp(r2) <= 0 {
		r.Add(r, _Int1)
		if r.Cmp(p) >= 0 {
			q.Add(q, _Int1)
			r.Sub(r, p)
		}
	}

	s := q.string(10)
	if z.Sign() < 0 {
		s = "-" + s
	}

	if prec > 0 {
		rs := r.string(10)
		leadingZeros := prec - len(rs)
		s += "." + strings.Repeat("0", leadingZeros) + rs
	}

	return s
}

// Gob codec version. Permits backward-compatible changes to the encoding.
const ratGobVersion byte = 1

// GobEncode implements the gob.GobEncoder interface.
func (z *Rat) GobEncode() ([]byte, error) {
	bufa := z.Num().Bytes()
	bufb := z.Denom().Bytes()
	buf := make([]byte, 1+4) // extra bytes for version and sign bit (1), and numerator length (4)
	buf = append(buf, bufa...)
	buf = append(buf, bufb...)
	const j = 1 + 4
	n := len(bufa)
	if int(uint32(n)) != n {
		// this should never happen
		return nil, errors.New("Rat.GobEncode: numerator too large")
	}
	binary.BigEndian.PutUint32(buf[1:5], uint32(n))
	b := ratGobVersion << 1 // make space for sign bit
	if z.Sign() < 0 {
		b |= 1
	}
	buf[0] = b
	return buf, nil
}

// GobDecode implements the gob.GobDecoder interface.
func (z *Rat) GobDecode(buf []byte) error {
	if len(buf) == 0 {
		return errors.New("Rat.GobDecode: no data")
	}
	b := buf[0]
	if b>>1 != ratGobVersion {
		return fmt.Errorf("Rat.GobDecode: encoding version %d not supported", b>>1)
	}
	const j = 1 + 4
	i := j + binary.BigEndian.Uint32(buf[j-4:j])
	num := new(Int).SetBytes(buf[j:i])
	den := new(Int).SetBytes(buf[i:])
	if b&1 != 0 {
		num.Neg(num)
	}
	z.SetFrac(num, den)
	return nil
}
