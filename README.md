# Project 3 - Scheme Interpreter Extension
## CSC 4101, Spring 2026

## Overview
This project extends the Project 2 Scheme interpreter by implementing rational
numbers and related built-in functions in Scheme (ini.scm).

## Rational Number Representation
Rational numbers are represented as 3-element lists:
  (rational numerator denominator)
e.g. 2/3 is stored as (rational 2 3)

All results are automatically simplified using GCD. If the denominator
reduces to 1, an integer is returned instead.

## Implemented Functions

### Type Predicates
- integer?, rational?, number?

### Integer Division
- quotient (via repeated subtraction)
- remainder

### Math Functions
- numerator, denominator, abs, gcd, lcm

### N-ary Arithmetic
- +, -, *, / (defined for one or more arguments)
- max, min

### N-ary Comparisons
- =, <, >, <=, >=

### Sign Predicates
- zero?, positive?, negative?

### Equality
- eqv?, equal?

### Association Lists
- assq, assv, assoc

### Write Function
- w: prints lists on one line, prints rationals in n/d notation

## References
- Euclid's Algorithm: https://en.wikipedia.org/wiki/Euclidean_algorithm
