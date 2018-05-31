// Copyright 2009 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// This file implements signed multi-precision integers.

package gmp

// FIXME could we use Go's allocator (gmp can use a custom allocator)
// instead of using runtime.SetFinalizer to manage memory?

/*
#cgo LDFLAGS: -lgmp
#include <gmp.h>
#include <stdlib.h>

// gmp 5.0.0+ changed the type of the 3rd argument to mp_bitcnt_t,
// so, to support older versions, we wrap these two functions.
void _mpz_mul_2exp(mpz_ptr a, mpz_ptr b, unsigned long n) {
	mpz_mul_2exp(a, b, n);
}
void _mpz_div_2exp(mpz_ptr a, mpz_ptr b, unsigned long n) {
	mpz_div_2exp(a, b, n);
}
unsigned int _mpz_tstbit(mpz_ptr a, unsigned long n) {
	return mpz_tstbit(a, n);
}
void _mpz_clrbit(mpz_ptr a, unsigned long n) {
	mpz_clrbit(a, n);
}
void _mpz_setbit(mpz_ptr a, unsigned long n) {
	mpz_setbit(a, n);
}

// Macros made into functions
int _mpz_sgn(mpz_t op) {
	return mpz_sgn(op);
}
*/
import "C"

import (
	"errors"
	"fmt"
	"io"
	"math/rand"
	"runtime"
	"strings"
	"unicode"
	"unsafe"
)

// Some definited Ints for internal use only
var (
	_Int0  = NewInt(0)
	_Int1  = NewInt(1)
	_Int10 = NewInt(10)
)

// An Int represents a signed multi-precision integer.
// The zero value for an Int represents the value 0.
type Int struct {
	i    C.mpz_t
	init bool
}

// Finalizer - release the memory allocated to the mpz
func intFinalize(z *Int) {
	if z.init {
		runtime.SetFinalizer(z, nil)
		C.mpz_clear(&z.i[0])
		z.init = false
	}
}

// Int promises that the zero value is a 0, but in gmp
// the zero value is a crash.  To bridge the gap, the
// init bool says whether this is a valid gmp value.
// doinit initializes z.i if it needs it.
func (z *Int) doinit() {
	if z.init {
		return
	}
	z.init = true
	C.mpz_init(&z.i[0])
	runtime.SetFinalizer(z, intFinalize)
}

// Clear the allocated space used by the number
//
// This normally happens on a runtime.SetFinalizer call, but if you
// want immediate deallocation you can call it.
//
// NB This is not part of big.Int
func (z *Int) Clear() {
	intFinalize(z)
}

// Sign returns:
//
//	-1 if x <  0
//	 0 if x == 0
//	+1 if x >  0
//
func (z *Int) Sign() int {
	z.doinit()
	return int(C._mpz_sgn(&z.i[0]))
}

// SetInt64 sets z to x and returns z.
func (z *Int) SetInt64(x int64) *Int {
	z.doinit()
	// Test for truncation
	y := C.long(x)
	if int64(y) == x {
		C.mpz_set_si(&z.i[0], y)
	} else {
		negative := false
		if x < 0 {
			x = -x
			negative = true
		}
		C.mpz_import(&z.i[0], 1, 0, 8, 0, 0, unsafe.Pointer(&x))
		if negative {
			C.mpz_neg(&z.i[0], &z.i[0])
		}
	}
	return z
}

// SetUint64 sets z to x and returns z.
func (z *Int) SetUint64(x uint64) *Int {
	z.doinit()
	// Test for truncation
	y := C.ulong(x)
	if uint64(y) == x {
		C.mpz_set_ui(&z.i[0], y)
	} else {
		C.mpz_import(&z.i[0], 1, 0, 8, 0, 0, unsafe.Pointer(&x))
	}
	return z
}

// NewInt allocates and returns a new Int set to x.
func NewInt(x int64) *Int {
	return new(Int).SetInt64(x)
}

// Set sets z to x and returns z.
func (z *Int) Set(x *Int) *Int {
	z.doinit()
	C.mpz_set(&z.i[0], &x.i[0])
	return z
}

// Bits provides raw (unchecked but fast) access to x by returning its
// absolute value as a little-endian Word slice. The result and x share
// the same underlying array.
// Bits is intended to support implementation of missing low-level Int
// functionality outside this package; it should be avoided otherwise.
// func (z *Int) Bits() []Word {
// 	// FIXME not implemented
// 	return nil
// }

// SetBits provides raw (unchecked but fast) access to z by setting its
// value to abs, interpreted as a little-endian Word slice, and returning
// z. The result and abs share the same underlying array.
// SetBits is intended to support implementation of missing low-level Int
// functionality outside this package; it should be avoided otherwise.
// func (z *Int) SetBits(abs []Word) *Int {
// 	// FIXME not implemented
// 	return nil
// }

// Abs sets z to |x| (the absolute value of x) and returns z.
func (z *Int) Abs(x *Int) *Int {
	x.doinit()
	z.doinit()
	C.mpz_abs(&z.i[0], &x.i[0])
	return z
}

// Neg sets z to -x and returns z.
func (z *Int) Neg(x *Int) *Int {
	x.doinit()
	z.doinit()
	C.mpz_neg(&z.i[0], &x.i[0])
	return z
}

// Add sets z to the sum x+y and returns z.
func (z *Int) Add(x, y *Int) *Int {
	x.doinit()
	y.doinit()
	z.doinit()
	C.mpz_add(&z.i[0], &x.i[0], &y.i[0])
	return z
}

// Sub sets z to the difference x-y and returns z.
func (z *Int) Sub(x, y *Int) *Int {
	x.doinit()
	y.doinit()
	z.doinit()
	C.mpz_sub(&z.i[0], &x.i[0], &y.i[0])
	return z
}

// Mul sets z to the product x*y and returns z.
func (z *Int) Mul(x, y *Int) *Int {
	x.doinit()
	y.doinit()
	z.doinit()
	C.mpz_mul(&z.i[0], &x.i[0], &y.i[0])
	return z
}

// MulRange sets z to the product of all integers
// in the range [a, b] inclusively and returns z.
// If a > b (empty range), the result is 1.
func (z *Int) MulRange(a, b int64) *Int {
	switch {
	case a > b:
		return z.SetInt64(1) // empty range
	case a <= 0 && b >= 0:
		return z.SetInt64(0) // range includes 0
	}
	// a <= b && (b < 0 || a > 0)

	// Can use gmp factorial routine if a = 1 and b >= 1
	if a == 1 && b >= 1 {
		C.mpz_fac_ui(&z.i[0], C.ulong(b))
	} else {
		// Slow
		z.SetInt64(a)
		for i := a + 1; i <= b; i++ {
			C.mpz_mul_si(&z.i[0], &z.i[0], C.long(i))
		}
	}
	return z
}

// Binomial sets z to the binomial coefficient of (n, k) and returns z.
func (z *Int) Binomial(n, k int64) *Int {
	var a, b Int
	a.MulRange(n-k+1, n)
	b.MulRange(1, k)
	return z.Quo(&a, &b)
}

// Quo sets z to the quotient x/y for y != 0 and returns z.
// If y == 0, a division-by-zero run-time panic occurs.
// Quo implements truncated division (like Go); see QuoRem for more details.
func (z *Int) Quo(x, y *Int) *Int {
	x.doinit()
	y.doinit()
	z.doinit()
	C.mpz_tdiv_q(&z.i[0], &x.i[0], &y.i[0])
	return z
}

// Rem sets z to the remainder x%y for y != 0 and returns z.
// If y == 0, a division-by-zero run-time panic occurs.
// Rem implements truncated modulus (like Go); see QuoRem for more details.
func (z *Int) Rem(x, y *Int) *Int {
	x.doinit()
	y.doinit()
	z.doinit()
	C.mpz_tdiv_r(&z.i[0], &x.i[0], &y.i[0])
	return z
}

// QuoRem sets z to the quotient x/y and r to the remainder x%y
// and returns the pair (z, r) for y != 0.
// If y == 0, a division-by-zero run-time panic occurs.
//
// QuoRem implements T-division and modulus (like Go):
//
//	q = x/y      with the result truncated to zero
//	r = x - y*q
//
// (See Daan Leijen, ``Division and Modulus for Computer Scientists''.)
// See DivMod for Euclidean division and modulus (unlike Go).
//
func (z *Int) QuoRem(x, y, r *Int) (*Int, *Int) {
	x.doinit()
	y.doinit()
	r.doinit()
	z.doinit()
	C.mpz_tdiv_qr(&z.i[0], &r.i[0], &x.i[0], &y.i[0])
	return z, r
}

// Div sets z to the quotient x/y for y != 0 and returns z.
// If y == 0, a division-by-zero run-time panic occurs.
// Div implements Euclidean division (unlike Go); see DivMod for more details.
func (z *Int) Div(x, y *Int) *Int {
	x.doinit()
	y.doinit()
	z.doinit()
	switch y.Sign() {
	case 1:
		C.mpz_fdiv_q(&z.i[0], &x.i[0], &y.i[0])
	case -1:
		C.mpz_cdiv_q(&z.i[0], &x.i[0], &y.i[0])
	case 0:
		panic("Division by zero")
	}
	return z
}

// Mod sets z to the modulus x%y for y != 0 and returns z.
// If y == 0, a division-by-zero run-time panic occurs.
// Mod implements Euclidean modulus (unlike Go); see DivMod for more details.
func (z *Int) Mod(x, y *Int) *Int {
	x.doinit()
	y.doinit()
	z.doinit()
	switch y.Sign() {
	case 1:
		C.mpz_fdiv_r(&z.i[0], &x.i[0], &y.i[0])
	case -1:
		C.mpz_cdiv_r(&z.i[0], &x.i[0], &y.i[0])
	case 0:
		panic("Division by zero")
	}
	return z
}

// DivMod sets z to the quotient x div y and m to the modulus x mod y
// and returns the pair (z, m) for y != 0.
// If y == 0, a division-by-zero run-time panic occurs.
//
// DivMod implements Euclidean division and modulus (unlike Go):
//
//	q = x div y  such that
//	m = x - y*q  with 0 <= m < |q|
//
// (See Raymond T. Boute, ``The Euclidean definition of the functions
// div and mod''. ACM Transactions on Programming Languages and
// Systems (TOPLAS), 14(2):127-144, New York, NY, USA, 4/1992.
// ACM press.)
// See QuoRem for T-division and modulus (like Go).
//
func (z *Int) DivMod(x, y, m *Int) (*Int, *Int) {
	x.doinit()
	y.doinit()
	m.doinit()
	z.doinit()
	switch y.Sign() {
	case 1:
		C.mpz_fdiv_qr(&z.i[0], &m.i[0], &x.i[0], &y.i[0])
	case -1:
		C.mpz_cdiv_qr(&z.i[0], &m.i[0], &x.i[0], &y.i[0])
	case 0:
		panic("Division by zero")
	}
	return z, m
}

// Cmp compares z and y and returns:
//
//   -1 if z <  y
//    0 if z == y
//   +1 if z >  y
//
func (z *Int) Cmp(y *Int) (r int) {
	z.doinit()
	y.doinit()
	r = int(C.mpz_cmp(&z.i[0], &y.i[0]))
	if r < 0 {
		r = -1
	} else if r > 0 {
		r = 1
	}
	return
}

// string returns z in the base given
func (z *Int) string(base int) string {
	if z == nil {
		return "<nil>"
	}
	z.doinit()
	p := C.mpz_get_str(nil, C.int(base), &z.i[0])
	s := C.GoString(p)
	C.free(unsafe.Pointer(p))
	return s
}

// String returns the decimal representation of z.
func (z *Int) String() string {
	return z.string(10)
}

// Convert rune into base
//
// Note gmp says -ve bases make upper case
func baseForRune(ch rune) int {
	switch ch {
	case 'b':
		return 2
	case 'o':
		return 8
	case 'd', 's', 'v':
		return 10
	case 'x':
		return 16
	case 'X':
		return -16
	}
	return 0 // unknown format
}

// write count copies of text to s
func writeMultiple(s fmt.State, text string, count int) {
	if len(text) > 0 {
		b := []byte(text)
		for ; count > 0; count-- {
			_, _ = s.Write(b)
		}
	}
}

// Format is a support routine for fmt.Formatter. It accepts
// the formats 'b' (binary), 'o' (octal), 'd' (decimal), 'x'
// (lowercase hexadecimal), and 'X' (uppercase hexadecimal).
// Also supported are the full suite of package fmt's format
// verbs for integral types, including '+', '-', and ' '
// for sign control, '#' for leading zero in octal and for
// hexadecimal, a leading "0x" or "0X" for "%#x" and "%#X"
// respectively, specification of minimum digits precision,
// output field width, space or zero padding, and left or
// right justification.
//
func (z *Int) Format(s fmt.State, ch rune) {
	base := baseForRune(ch)

	// special cases
	switch {
	case base == 0:
		// unknown format
		_, _ = fmt.Fprintf(s, "%%!%c(gmp.Int=%s)", ch, z.String())
		return
	case z == nil:
		_, _ = fmt.Fprint(s, "<nil>")
		return
	}

	// determine sign character
	sign := ""
	switch {
	case z.Sign() < 0:
		sign = "-"
	case s.Flag('+'): // supersedes ' ' when both specified
		sign = "+"
	case s.Flag(' '):
		sign = " "
	}

	// determine prefix characters for indicating output base
	prefix := ""
	if s.Flag('#') {
		switch ch {
		case 'o': // octal
			prefix = "0"
		case 'x': // hexadecimal
			prefix = "0x"
		case 'X':
			prefix = "0X"
		}
	}

	// determine digits with base set by len(cs) and digit characters from cs
	digits := z.string(base)
	if digits[0] == '-' {
		digits = digits[1:]
	}

	// number of characters for the three classes of number padding
	var left int   // space characters to left of digits for right justification ("%8d")
	var zeroes int // zero characters (actually cs[0]) as left-most digits ("%.8d")
	var right int  // space characters to right of digits for left justification ("%-8d")

	// determine number padding from precision: the least number of digits to output
	precision, precisionSet := s.Precision()
	if precisionSet {
		switch {
		case len(digits) < precision:
			zeroes = precision - len(digits) // count of zero padding
		case digits == "0" && precision == 0:
			return // print nothing if zero value (z == 0) and zero precision ("." or ".0")
		}
	}

	// determine field pad from width: the least number of characters to output
	length := len(sign) + len(prefix) + zeroes + len(digits)
	if width, widthSet := s.Width(); widthSet && length < width { // pad as specified
		switch d := width - length; {
		case s.Flag('-'):
			// pad on the right with spaces; supersedes '0' when both specified
			right = d
		case s.Flag('0') && !precisionSet:
			// pad with zeroes unless precision also specified
			zeroes = d
		default:
			// pad on the left with spaces
			left = d
		}
	}

	// print number as [left pad][sign][prefix][zero pad][digits][right pad]
	writeMultiple(s, " ", left)
	writeMultiple(s, sign, 1)
	writeMultiple(s, prefix, 1)
	writeMultiple(s, "0", zeroes)
	writeMultiple(s, digits, 1)
	writeMultiple(s, " ", right)
}

// Scan is a support routine for fmt.Scanner; it sets z to the value of
// the scanned number. It accepts the formats 'b' (binary), 'o' (octal),
// 'd' (decimal), 'x' (lowercase hexadecimal), and 'X' (uppercase hexadecimal).
func (z *Int) Scan(s fmt.ScanState, ch rune) error {
	s.SkipSpace() // skip leading space characters
	base := 0
	switch ch {
	case 'b':
		base = 2
	case 'o':
		base = 8
	case 'd':
		base = 10
	case 'x', 'X':
		base = 16
	case 's', 'v':
		// let scan determine the base
	default:
		return errors.New("Int.Scan: invalid verb")
	}
	charset := "0123456789abcdef"
	if base != 0 {
		charset = charset[:base]
	}

	// Read the number into in
	in := make([]byte, 0, 16)
	var err error
	var n int
	for {
		ch, n, err = s.ReadRune()
		if err == io.EOF {
			break
		}
		if err != nil {
			return err
		}
		if n > 1 {
			// Wide character - must be the end
			err = s.UnreadRune()
			if err != nil {
				return err
			}
			break
		}
		ch = unicode.ToLower(ch)
		if len(in) == 0 {
			if ch == '+' {
				// Skip leading + as gmp doesn't understand them
				continue
			}
			if ch == '-' {
				goto ok
			}
		}
		if len(in) == 1 && base == 0 {
			if ch == 'b' || ch == 'x' {
				goto ok
			}
		}
		if !strings.ContainsRune(charset, ch) {
			// Bad character - end
			err = s.UnreadRune()
			if err != nil {
				return err
			}
			break
		}
	ok:
		in = append(in, byte(ch))
	}

	// Use GMP to convert it as it is very efficient for large numbers
	z.doinit()
	// null terminate for C
	in = append(in, 0)
	if C.mpz_set_str(&z.i[0], (*C.char)(unsafe.Pointer(&in[0])), C.int(base)) < 0 {
		return errors.New("Int.Scan: failed")
	}
	return nil
}

// Int64 returns the int64 representation of z.
// If z cannot be represented in an int64, the result is undefined.
func (z *Int) Int64() (y int64) {
	if !z.init {
		return
	}
	if C.mpz_fits_slong_p(&z.i[0]) != 0 {
		return int64(C.mpz_get_si(&z.i[0]))
	}
	// Undefined result if > 64 bits
	if z.BitLen() > 64 {
		return
	}
	C.mpz_export(unsafe.Pointer(&y), nil, -1, 8, 0, 0, &z.i[0])
	if z.Sign() < 0 {
		y = -y
	}
	return
}

// Uint64 returns the uint64 representation of z.
// If z cannot be represented in a uint64, the result is undefined.
func (z *Int) Uint64() (y uint64) {
	if !z.init {
		return
	}
	if C.mpz_fits_ulong_p(&z.i[0]) != 0 {
		return uint64(C.mpz_get_ui(&z.i[0]))
	}
	// Undefined result if > 64 bits
	if z.BitLen() > 64 {
		return
	}
	C.mpz_export(unsafe.Pointer(&y), nil, -1, 8, 0, 0, &z.i[0])
	return
}

// SetString sets z to the value of s, interpreted in the given base,
// and returns z and a boolean indicating success. If SetString fails,
// the value of z is undefined but the returned value is nil.
//
// The base argument must be 0 or a value from 2 through MaxBase. If the base
// is 0, the string prefix determines the actual conversion base. A prefix of
// ``0x'' or ``0X'' selects base 16; the ``0'' prefix selects base 8, and a
// ``0b'' or ``0B'' prefix selects base 2. Otherwise the selected base is 10.
//
func (z *Int) SetString(s string, base int) (*Int, bool) {
	z.doinit()
	if base != 0 && (base < 2 || base > 36) {
		return nil, false
	}
	// Skip leading + as mpz_set_str doesn't understand them
	if len(s) > 1 && s[0] == '+' {
		s = s[1:]
	}
	// mpz_set_str incorrectly parses "0x" and "0b" as valid
	if base == 0 && len(s) == 2 && s[0] == '0' && (s[1] == 'x' || s[1] == 'X' || s[1] == 'b' || s[1] == 'B') {
		return nil, false
	}
	p := C.CString(s)
	defer C.free(unsafe.Pointer(p))
	if C.mpz_set_str(&z.i[0], p, C.int(base)) < 0 {
		return nil, false
	}
	return z, true // err == io.EOF => scan consumed all of s
}

// SetBytes interprets buf as the bytes of a big-endian unsigned
// integer, sets z to that value, and returns z.
func (z *Int) SetBytes(buf []byte) *Int {
	z.doinit()
	if len(buf) == 0 {
		z.SetInt64(0)
	} else {
		C.mpz_import(&z.i[0], C.size_t(len(buf)), 1, 1, 1, 0, unsafe.Pointer(&buf[0]))
	}
	return z
}

// Bytes returns the absolute value of z as a big-endian byte slice.
func (z *Int) Bytes() []byte {
	b := make([]byte, 1+(z.BitLen()+7)/8)
	n := C.size_t(len(b))
	C.mpz_export(unsafe.Pointer(&b[0]), &n, 1, 1, 1, 0, &z.i[0])
	return b[0:n]
}

// BitLen returns the length of the absolute value of z in bits.
// The bit length of 0 is 0.
func (z *Int) BitLen() int {
	z.doinit()
	if z.Sign() == 0 {
		return 0
	}
	return int(C.mpz_sizeinbase(&z.i[0], 2))
}

// Exp sets z = x**y mod |m| (i.e. the sign of m is ignored), and returns z.
// If y <= 0, the result is 1; if m == nil or m == 0, z = x**y.
// See Knuth, volume 2, section 4.6.3.
func (z *Int) Exp(x, y, m *Int) *Int {
	x.doinit()
	y.doinit()
	z.doinit()
	if y.Sign() <= 0 {
		z.SetInt64(1)
		return z
	}
	if m == nil || m.Sign() == 0 {
		C.mpz_pow_ui(&z.i[0], &x.i[0], C.mpz_get_ui(&y.i[0]))
	} else {
		m.doinit()
		C.mpz_powm(&z.i[0], &x.i[0], &y.i[0], &m.i[0])
	}
	return z
}

// GCD sets z to the greatest common divisor of a and b, which both must
// be > 0, and returns z.
// If x and y are not nil, GCD sets x and y such that z = a*x + b*y.
// If either a or b is <= 0, GCD sets z = x = y = 0.
func (z *Int) GCD(x, y, a, b *Int) *Int {
	z.doinit()
	a.doinit()
	b.doinit()
	if a.Sign() <= 0 || b.Sign() <= 0 {
		z.SetInt64(0)
		if x != nil {
			x.SetInt64(0)
		}
		if y != nil {
			y.SetInt64(0)
		}
	} else if x == nil && y == nil {
		C.mpz_gcd(&z.i[0], &a.i[0], &b.i[0])
	} else {
		if x != nil {
			x.doinit()
		} else {
			x = _Int0
		}
		if y != nil {
			y.doinit()
		} else {
			y = _Int0
		}
		C.mpz_gcdext(&z.i[0], &x.i[0], &y.i[0], &a.i[0], &b.i[0])
	}
	return z
}

// ProbablyPrime performs n Miller-Rabin tests to check whether z is prime.
// If it returns true, z is prime with probability 1 - 1/4^n.
// If it returns false, z is not prime.
func (z *Int) ProbablyPrime(n int) bool {
	z.doinit()
	return int(C.mpz_probab_prime_p(&z.i[0], C.int(n))) > 0
}

// Rand sets z to a pseudo-random number in [0, n) and returns z.
func (z *Int) Rand(rnd *rand.Rand, n *Int) *Int {
	z.doinit()
	// Get rid of n <= 0 case
	if n.Sign() <= 0 {
		z.SetInt64(0)
		return z
	}
	// Make a copy of n if aliased
	t := n
	aliased := false
	if n == z {
		aliased = true
		t = new(Int).Set(n)
	}
	// Work out bit sizes and masks
	bits := n.BitLen()         // >= 1
	nwords := (bits + 31) / 32 // >= 1
	bitLengthOfMSW := uint(bits % 32)
	if bitLengthOfMSW == 0 {
		bitLengthOfMSW = 32
	}
	mask := uint32((1 << bitLengthOfMSW) - 1)
	words := make([]uint32, nwords)
	for {
		// Make a most significant first array of random bytes
		for i := 0; i < nwords; i++ {
			words[i] = rnd.Uint32()
		}
		// Mask out the top bits so this is only just bigger than n
		words[0] &= mask
		C.mpz_import(&z.i[0], C.size_t(len(words)), 1, 4, 0, 0, unsafe.Pointer(&words[0]))
		// Exit if z < n - should take ~1.5 iterations of loop on average
		if z.Cmp(t) < 0 {
			break
		}
	}
	if aliased {
		t.Clear()
	}
	return z
}

// ModInverse sets z to the multiplicative inverse of g in the group ℤ/pℤ (where
// p is a prime) and returns z.
func (z *Int) ModInverse(g, p *Int) *Int {
	g.doinit()
	p.doinit()
	z.doinit()
	C.mpz_invert(&z.i[0], &g.i[0], &p.i[0])
	return z
}

// Lsh sets z = x << n and returns z.
func (z *Int) Lsh(x *Int, n uint) *Int {
	x.doinit()
	z.doinit()
	C._mpz_mul_2exp(&z.i[0], &x.i[0], C.ulong(n))
	return z
}

// Rsh sets z = x >> n and returns z.
func (z *Int) Rsh(x *Int, n uint) *Int {
	x.doinit()
	z.doinit()
	C._mpz_div_2exp(&z.i[0], &x.i[0], C.ulong(n))
	return z
}

// Bit returns the value of the i'th bit of z. That is, it
// returns (z>>i)&1. The bit index i must be >= 0.
func (z *Int) Bit(i int) uint {
	z.doinit()
	return uint(C._mpz_tstbit(&z.i[0], C.ulong(i)))
}

// SetBit sets z to x, with x's i'th bit set to b (0 or 1).
// That is, if b is 1 SetBit sets z = x | (1 << i);
// if b is 0 SetBit sets z = x &^ (1 << i). If b is not 0 or 1,
// SetBit will panic.
func (z *Int) SetBit(x *Int, i int, b uint) *Int {
	if z != x {
		z.Set(x)
	}
	if b == 0 {
		C._mpz_clrbit(&z.i[0], C.ulong(i))
	} else {
		C._mpz_setbit(&z.i[0], C.ulong(i))
	}
	return z
}

// And sets z = x & y and returns z.
func (z *Int) And(x, y *Int) *Int {
	x.doinit()
	y.doinit()
	z.doinit()
	C.mpz_and(&z.i[0], &x.i[0], &y.i[0])
	return z
}

// AndNot sets z = x &^ y and returns z.
func (z *Int) AndNot(x, y *Int) *Int {
	x.doinit()
	y.doinit()
	z.doinit()
	t := z
	aliased := false
	if z == y || z == x {
		aliased = true
		t = new(Int).Set(y)
	}
	C.mpz_com(&t.i[0], &y.i[0])
	C.mpz_and(&z.i[0], &x.i[0], &t.i[0])
	if aliased {
		t.Clear()
	}
	return z
}

// Or sets z = x | y and returns z.
func (z *Int) Or(x, y *Int) *Int {
	x.doinit()
	y.doinit()
	z.doinit()
	C.mpz_ior(&z.i[0], &x.i[0], &y.i[0])
	return z
}

// Xor sets z = x ^ y and returns z.
func (z *Int) Xor(x, y *Int) *Int {
	x.doinit()
	y.doinit()
	z.doinit()
	C.mpz_xor(&z.i[0], &x.i[0], &y.i[0])
	return z
}

// Not sets z = ^x and returns z.
func (z *Int) Not(x *Int) *Int {
	x.doinit()
	z.doinit()
	C.mpz_com(&z.i[0], &x.i[0])
	return z
}

// Gob codec version. Permits backward-compatible changes to the encoding.
const intGobVersion byte = 1

// GobEncode implements the gob.GobEncoder interface.
func (z *Int) GobEncode() ([]byte, error) {
	buf := make([]byte, 2+(z.BitLen()+7)/8)
	n := C.size_t(len(buf) - 1)
	C.mpz_export(unsafe.Pointer(&buf[1]), &n, 1, 1, 1, 0, &z.i[0])
	b := intGobVersion << 1 // make space for sign bit
	if z.Sign() < 0 {
		b |= 1
	}
	buf[0] = b
	return buf[:n+1], nil
}

// GobDecode implements the gob.GobDecoder interface.
func (z *Int) GobDecode(buf []byte) error {
	if len(buf) == 0 {
		return errors.New("Int.GobDecode: no data")
	}
	b := buf[0]
	if b>>1 != intGobVersion {
		return fmt.Errorf("Int.GobDecode: encoding version %d not supported", b>>1)
	}
	z.SetBytes(buf[1:])
	if b&1 != 0 {
		C.mpz_neg(&z.i[0], &z.i[0])
	}
	return nil
}

// MarshalJSON implements the json.Marshaler interface.
func (z *Int) MarshalJSON() ([]byte, error) {
	// TODO(gri): get rid of the []byte/string conversions
	return []byte(z.String()), nil
}

// UnmarshalJSON implements the json.Unmarshaler interface.
func (z *Int) UnmarshalJSON(x []byte) error {
	// TODO(gri): get rid of the []byte/string conversions
	_, ok := z.SetString(string(x), 0)
	if !ok {
		return fmt.Errorf("math/big: cannot unmarshal %s into a *gmp.Int", x)
	}
	return nil
}
