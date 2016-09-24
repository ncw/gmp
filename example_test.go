// Copyright 2012 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package gmp

import (
	"fmt"
	"log"
)

// func ExampleRat_SetString() {
// 	r := new(big.Rat)
// 	r.SetString("355/113")
// 	fmt.Println(r.FloatString(3))
// 	// Output: 3.142
// }

func ExampleInt_SetString() {
	i := new(Int)
	i.SetString("644", 8) // octal
	fmt.Println(i)
	// Output: 420
}

// func ExampleRat_Scan() {
// 	// The Scan function is rarely used directly;
// 	// the fmt package recognizes it as an implementation of fmt.Scanner.
// 	r := new(Rat)
// 	_, err := fmt.Sscan("1.5000", r)
// 	if err != nil {
// 		log.Println("error scanning value:", err)
// 	} else {
// 		fmt.Println(r)
// 	}
// 	// Output: 3/2
// }

func ExampleInt_Scan() {
	// The Scan function is rarely used directly;
	// the fmt package recognizes it as an implementation of fmt.Scanner.
	i := new(Int)
	_, err := fmt.Sscan("18446744073709551617", i)
	if err != nil {
		log.Println("error scanning value:", err)
	} else {
		fmt.Println(i)
	}
	// Output: 18446744073709551617
}
