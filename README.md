# Primitive Floating Point Adder in ACL2

## Summary

This project implements a **primitive floating point adder** for two IEEE-754 floating point numbers and formally proves its correctness in **ACL2 (version 8.6)**. I implemented this project to learn theorem proving under the guidance of Dr. Sandip Ray at University of Florida. 

Correctness is proven by showing that the rational number represented by the output of adder is the sum of the rational numbers represented by the input floating point numbers. 

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
![IEEE Floating Point Representation](https://github.com/mohammadmonjil/Implementation-and-Formal-Correctness-of-a-Floating-Point-Adder/blob/main/images/IEEE.png?raw=true)

A floating-point number consists of three fields:

- **Sign bit (S)**  
  - 0 → positive  
  - 1 → negative  

- **Exponent (E)**  
  - Stored with a bias to allow both positive and negative exponents.  
  - For an exponent of width k: ${Bias} = 2^{k-1} - 1$  
  - Example: in single precision (8-bit exponent), Bias = 127  

- **Mantissa / Fraction (M)**  
  - Represents the significant digits of the number.  
  - Normalized numbers assume an implicit leading 1 before the binary point.  

The value of a floating point number is:  
$Value = (-1)^S \times (1.F) \times 2^{E - Bias}$

In normalized form with implimcit 1 in front of mantissa, the rational number zero is treated as a special case. In IEEE 754, it is represented by putting all 0s in both exponent and mantissa.

---

## Modifications in This Implementation

- Exponent is stored as a bitvector $[sign][magnitude]$ instead of biased form.  
- The rational value zero is represented as $[1][zero-vector]$ in the exponent, value of mantissa is ignored.  


---

## Floating Point Adder Algorithm (Simplified)
- Input: two floating point number a,b. Output: floating point number c.
```
    A = [SA][ExpA][MantissaA]
    B = [SB][ExpB][MantissaB]
```
1. **Denormalization**  
Add the hidden 1 in front of both mantissas to make them explicit.

```
MantissaA = [1][MantissaA]
MantissaB = [1][MantissaB]
```

2. **Exponent Alignment**

```
If ExpA >= ExpB:  
   MantissaA = LeftShift(MantissaA, ExpA - ExpB)  
   MantissaB = RightShift(MantissaB, ExpA - ExpB)  
   ExpC = ExpA  

Else (if Exp(b) > Exp(a)):  
   MantissaB = LeftShift(MantissaB, ExpB - ExpA)  
   MantissaA = RightShift(MantissaA, ExpB - ExpA)  
   ExpC = ExpB
```

LeftShift adds traling zeros and RightShift adds leading zeros to the bitvector of the mantissa, so our operation is lossless (rounding not considered).

3. **Signed BitVector Addition**
   ```
       SignC, MantissaC = SignedBitVectorAdder(SignA, MantissaA, SignB, MantissaB)
       If signs are the same → add the mantissas and return the sign.  
       If signs differ → subtract smaller from larger and keep the sign of the larger.  
       If the result is zero → return canonical zero (ExpC = [1][zero-vector]).
   ```

5. **Normalization**
``` 
       Ensure the mantissa has a leading 1 and adjust the exponent accordingly.
       example: If Mantissa  = 0.00101, exp = 5 (in decimal), this is same as 1.01, exp = 2. After normalization step, Mantissa = 01 (leading 1 hidden), exp = 2
```
7. **Pack Result**  
   - Return the final triple (Sign, Exponent, Mantissa).  

---

## Rational Semantics

To relate bitvector operations to real arithmetic, two rational interpretation functions were defined:

$RationalNormalized(S, M, E) = (-1)^S \times \Big(1 + \sum_{i=1}^{k} M_i \cdot 2^{-i}\Big) \times 2^{E}$

$RationalDeNormalized(S, M, E) = (-1)^S \times \Big(M_0 \cdot 2^{0} + \sum_{i=1}^{k-1} M_i \cdot 2^{-(i+1)}\Big) \times 2^{E}$

**Rational_Normalized**: works on normalized mantissas (with implicit leading 1).  
**Rational_Denormalized**: works on denormalized mantissas (with the hidden 1 restored explicitly).  

## Intermediate Theorems
To prove the correctness of the floating point adder, a number of intermediate theorems relating to different operations of the algoritms were proved. The major theorems are as follows:

1. **Denormalization Invariance**
```
   Rational_Normalized(S,M,E) = Rational_Denormalized(Denormalization(S,M,E))  
```
Denormalization preserves the rational value represented by floating point number.

2. **Right-shift and Left-shift semantics**
```  
   Rational_Denormalized(Sign, RightShift(Mantissa, n), Exponent)  
   = Rational_Denormalized(Sign, Mantissa, Exponent) / 2^n

  Rational_Denormalized(Sign, LeftShift(Mantissa, n), Exponent)  
   = Rational_Denormalized(Sign, Mantissa, Exponent) 
```
   Right-shifting corresponds to division by a power of two. Left-shifting does not change the value. 

3. **Signed add/sub correctness**
```
   Rational_Denormalized(Signed_BitVector_Adder(SignA, MantissaA, SignB, MantissaB), Exponent)  
   = Rational_Denormalized(SignA, MantissaA, Exponent) + Rational_Denormalized(SignB, MantissaB, Exponent)
```
   The signed bitvector adder corresponds exactly to rational addition when exponents are aligned(or they have same exponent).  

4. **Normalization invariance**
```
   Rational_Denormalized(F) = Rational_Normalized(Normalization(F))
```
   Normalization preserves value.  

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
```
      Rational_Normalized(FP_Adder(A, B))  = Rational_Normalized(A) + Rational_Normalized(B)
```
