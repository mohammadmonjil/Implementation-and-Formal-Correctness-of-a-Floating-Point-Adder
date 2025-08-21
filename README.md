# Primitive Floating Point Adder in ACL2

## Summary

This project implements a **primitive floating point adder** for two IEEE-754 floating point numbers and formally proves its correctness in **ACL2 (version 8.6)**. I implemented this project to learn theorem proving under the guidance of Dr. Sandip Ray at University of Florida. 
The adder supports addition of numbers represented in sign–magnitude exponent form and bitvector mantissas.  
Correctness is proven by connecting the implementation with rational arithmetic through intermediate theorems.  

**Limitations:**  
- Lossless semantics only (no rounding modeled).  
- Modified IEEE format 

---

## Running the Project

The source files are in the `src/` folder. Run them in ACL2 (tested in ACL2 8.6) in the following order:

1. `fp.lisp`  (contains the adder and other functions)
2. `book-1.lisp`  
3. `book-2.lisp`  
4. `book-3.lisp`  
5. `book-4.lisp`  
6. `book-5.lisp`  
7. `book-6.lisp` (contains the final correctness theorem)

---

## Structure of IEEE Floating-Point Numbers

A floating-point number consists of three fields:

- **Sign bit (S)**  
  - 0 → positive  
  - 1 → negative  

- **Exponent (E)**  
  - Stored with a bias to allow both positive and negative exponents.  
  - For an exponent of width k: Bias = 2^(k−1) − 1  
  - Example: in single precision (8-bit exponent), Bias = 127  

- **Mantissa / Fraction (M)**  
  - Represents the significant digits of the number.  
  - Normalized numbers assume an implicit leading 1 before the binary point.  

The value of a floating point number is:  
`Value = (-1)^S * (1.F) * 2^(E - Bias)`

Zero is represented by putting 0 in both exponent and mantissa.

---

## Modifications in This Implementation

- Exponent is stored as a bitvector `[sign][magnitude]` instead of biased form.  
- Zero is represented as `[1][zero-vector]`.  
- Sign and mantissa are both represented as bitvectors.  

---

## Floating Point Adder Algorithm (Simplified)

1. **Denormalization**  
   - Add the hidden 1 in front of both mantissas to make them explicit.

2. **Exponent Alignment (Right-Shifter)**  
   - Compare the exponents.  
   - Right-shift the mantissa of the smaller exponent until both exponents match.

3. **Signed BitVector Addition**  
   - If signs are the same → add the mantissas.  
   - If signs differ → subtract smaller from larger and keep the sign of the larger.  
   - If the result is zero → return canonical zero.  

4. **Normalization**  
   - Ensure the mantissa has a leading 1.  
   - Shift right if overflow, or shift left if underflow.  
   - Adjust the exponent accordingly.  

5. **Pack Result**  
   - Return the final triple (Sign, Exponent, Mantissa).  

---

## Rational Semantics

To relate bitvector operations to real arithmetic, two rational interpretation functions were defined:

- **Rational_Normalized**: works on normalized mantissas (with implicit leading 1).  
- **Rational_Denormalized**: works on denormalized mantissas (with the hidden 1 restored explicitly).  

---

## Functions in the FP-Adder

- **Denormalization**  
  Restores the hidden 1, turning the fraction field into an integer mantissa.  

- **Right-Shifter**  
  Aligns exponents by right-shifting the smaller mantissa by the difference in exponents.  

- **Signed_BitVector_Adder**  
  Performs addition or subtraction of two signed magnitudes. Handles zero as a special case.  

- **Normalization**  
  Restores the invariant that the mantissa has a leading 1 and adjusts the exponent accordingly.  

---

## Intermediate Theorems

1. **Denormalization correctness**  
   Rational_Normalized(F) = Rational_Denormalized(Denormalization(F))  
   *Denormalization preserves value.*  

2. **Right-shift semantics**  
   Rational_Denormalized(Sign, RightShift(Mantissa, n), Exponent)  
   = Rational_Denormalized(Sign, Mantissa, Exponent) / 2^n  
   *Right-shifting corresponds to division by a power of two.*  

3. **Signed add/sub correctness**  
   Rational_Denormalized(Signed_BitVector_Adder(SignA, MantissaA, SignB, MantissaB), Exponent)  
   = Rational_Denormalized(SignA, MantissaA, Exponent) + Rational_Denormalized(SignB, MantissaB, Exponent)  
   *The signed bitvector adder corresponds exactly to rational addition when exponents are aligned.*  

4. **Normalization invariance**  
   Rational_Denormalized(F) = Rational_Normalized(Normalization(F))  
   *Normalization preserves value.*  

---

## How the Theorems Compose

- The input floats are first turned into Rational_Denormalized form using theorem (1).  
- Exponent alignment is justified by theorem (2).  
- Mantissa addition is justified by theorem (3).  
- Result normalization is justified by theorem (4).  

Chaining these steps together proves that the rational semantics of the FP-Adder matches real addition.

---

## Final Theorem

**Correctness of the Floating Point Adder:**  

Rational_Normalized(FP_Adder(A, B))  
= Rational_Normalized(A) + Rational_Normalized(B)

---
