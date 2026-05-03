; ini.scm - Project 3: Scheme Interpreter Extension
; Implements rational numbers and extended built-in functions

; ============================================================
; BASIC HELPERS (from Project 2, needed as foundation)
; ============================================================

(define (not x) (if x #f #t))

(define (caar x) (car (car x)))
(define (cadr x) (car (cdr x)))
(define (cdar x) (cdr (car x)))
(define (cddr x) (cdr (cdr x)))
(define (caaar x) (car (car (car x))))
(define (caadr x) (car (car (cdr x))))
(define (cadar x) (car (cdr (car x))))
(define (caddr x) (car (cdr (cdr x))))
(define (cdaar x) (cdr (car (car x))))
(define (cdadr x) (cdr (car (cdr x))))
(define (cddar x) (cdr (cdr (car x))))
(define (cdddr x) (cdr (cdr (cdr x))))
(define (cadddr x) (car (cdr (cdr (cdr x)))))

(define (list . args) args)

(define (length lst)
  (if (null? lst)
      0
      (b+ 1 (length (cdr lst)))))

(define (append lst1 lst2)
  (if (null? lst1)
      lst2
      (cons (car lst1) (append (cdr lst1) lst2))))

(define (reverse lst)
  (define (rev-helper lst acc)
    (if (null? lst)
        acc
        (rev-helper (cdr lst) (cons (car lst) acc))))
  (rev-helper lst '()))

(define (map f lst)
  (if (null? lst)
      '()
      (cons (f (car lst)) (map f (cdr lst)))))

(define (for-each f lst)
  (if (null? lst)
      #f
      (begin (f (car lst)) (for-each f (cdr lst)))))

; apply is handled natively by the interpreter

; ============================================================
; INTEGER ARITHMETIC PRIMITIVES
; These wrap the built-in Java operations (b+, b-, b*, b/)
; ============================================================

; integer arithmetic primitives wrapping Java built-ins
(define (int+ a b) (b+ a b))
(define (int- a b) (b- a b))
(define (int* a b) (b* a b))
(define (int-div a b) (b/ a b))  ; Java integer division, only used internally
(define (int= a b) (b= a b))
(define (int< a b) (b< a b))

; ============================================================
; QUOTIENT AND REMAINDER via repeated subtraction
; ============================================================

(define (quotient a b)
  ; use Java's built-in integer division via b/
  (int-div a b))

(define (remainder a b)
  ; remainder via: a - b * quotient(a, b)
  (int- a (int* b (quotient a b))))

; ============================================================
; GCD and LCM
; Euclid's algorithm reference: https://en.wikipedia.org/wiki/Euclidean_algorithm
; ============================================================

(define (gcd a b)
  ; make both positive first
  (define (gcd-pos a b)
    (if (int= b 0)
        a
        (gcd-pos b (remainder a b))))
  (gcd-pos (if (int< a 0) (int- 0 a) a)
           (if (int< b 0) (int- 0 b) b)))

(define (lcm a b)
  (define g (gcd a b))
  (if (int= g 0)
      0
      (int* (quotient (if (int< a 0) (int- 0 a) a) g)
            (if (int< b 0) (int- 0 b) b))))

; ============================================================
; RATIONAL NUMBER REPRESENTATION
; A rational is stored as (rational numerator denominator)
; ============================================================

(define (rational? x)
  (if (pair? x)
      (if (eq? (car x) 'rational)
          #t
          #f)
      #f))

(define (integer? x)
  (if (rational? x)
      #f
      (if (pair? x)
          #f
          (if (eq? x #t)
              #f
              (if (eq? x #f)
                  #f
                  (if (null? x)
                      #f
                      ; if it's not a bool, pair, or null, assume integer
                      ; (strings and symbols are not numbers)
                      (if (string? x)
                          #f
                          (if (symbol? x)
                              #f
                              #t))))))))

(define (number? x)
  (if (integer? x)
      #t
      (if (rational? x)
          #t
          #f)))

; ============================================================
; RATIONAL CONSTRUCTORS / ACCESSORS
; ============================================================

(define (numerator x)
  (if (rational? x)
      (cadr x)
      x))  ; integers have themselves as numerator

(define (denominator x)
  (if (rational? x)
      (caddr x)
      1))  ; integers have denominator 1

; make-rational: constructs a simplified rational number
; if denominator is 1 after simplification, returns integer
(define (make-rational n d)
  ; handle sign: keep sign in numerator
  (define neg (if (int< d 0) #t #f))
  (define abs-n (if (int< n 0) (int- 0 n) n))
  (define abs-d (if (int< d 0) (int- 0 d) d))
  (define g (gcd abs-n abs-d))
  (define sn (if neg
                 (int- 0 (quotient abs-n g))
                 (quotient abs-n g)))
  (define sd (quotient abs-d g))
  (if (int= sd 1)
      sn
      (list 'rational sn sd)))

; convert any number to rational form for arithmetic
(define (to-rational x)
  (if (rational? x)
      x
      (list 'rational x 1)))

; ============================================================
; ABS
; ============================================================

(define (abs x)
  (if (rational? x)
      (make-rational
        (if (int< (numerator x) 0) (int- 0 (numerator x)) (numerator x))
        (denominator x))
      (if (int< x 0) (int- 0 x) x)))

; ============================================================
; ARITHMETIC OPERATIONS: +, -, *, /
; Each handles integer and rational arguments
; ============================================================

; add two numbers
(define (add2 a b)
  (if (rational? a)
      (if (rational? b)
          ; rat + rat
          (make-rational
            (int+ (int* (numerator a) (denominator b))
                  (int* (numerator b) (denominator a)))
            (int* (denominator a) (denominator b)))
          ; rat + int
          (make-rational
            (int+ (numerator a) (int* b (denominator a)))
            (denominator a)))
      (if (rational? b)
          ; int + rat
          (make-rational
            (int+ (int* a (denominator b)) (numerator b))
            (denominator b))
          ; int + int
          (int+ a b))))

; subtract two numbers
(define (sub2 a b)
  (if (rational? a)
      (if (rational? b)
          (make-rational
            (int- (int* (numerator a) (denominator b))
                  (int* (numerator b) (denominator a)))
            (int* (denominator a) (denominator b)))
          (make-rational
            (int- (numerator a) (int* b (denominator a)))
            (denominator a)))
      (if (rational? b)
          (make-rational
            (int- (int* a (denominator b)) (numerator b))
            (denominator b))
          (int- a b))))

; multiply two numbers
(define (mul2 a b)
  (if (rational? a)
      (if (rational? b)
          (make-rational
            (int* (numerator a) (numerator b))
            (int* (denominator a) (denominator b)))
          (make-rational
            (int* (numerator a) b)
            (denominator a)))
      (if (rational? b)
          (make-rational
            (int* a (numerator b))
            (denominator b))
          (int* a b))))

; divide two numbers
(define (div2 a b)
  (if (rational? b)
      (mul2 a (list 'rational (denominator b) (numerator b)))
      (if (rational? a)
          (make-rational (numerator a) (int* (denominator a) b))
          (make-rational a b))))

; n-ary +
(define (+ . args)
  (if (null? args)
      0
      (if (null? (cdr args))
          (car args)
          (add2 (car args) (apply + (cdr args))))))

; n-ary - (one or more args)
(define (- . args)
  (if (null? args)
      (error "- requires at least one argument")
      (if (null? (cdr args))
          ; unary minus
          (sub2 0 (car args))
          (if (null? (cddr args))
              (sub2 (car args) (cadr args))
              (sub2 (car args) (apply + (cdr args)))))))

; n-ary *
(define (* . args)
  (if (null? args)
      1
      (if (null? (cdr args))
          (car args)
          (mul2 (car args) (apply * (cdr args))))))

; n-ary / (one or more args)
(define (/ . args)
  (if (null? args)
      (error "/ requires at least one argument")
      (if (null? (cdr args))
          (div2 1 (car args))
          (if (null? (cddr args))
              (div2 (car args) (cadr args))
              (div2 (car args) (apply * (cdr args)))))))

; ============================================================
; COMPARISON HELPERS
; Convert to common denominator for comparison
; ============================================================

; compare two numbers, returns -1, 0, or 1
(define (num-compare a b)
  (define na (numerator a))
  (define da (denominator a))
  (define nb (numerator b))
  (define db (denominator b))
  ; scale: na*db vs nb*da
  (define lhs (int* na db))
  (define rhs (int* nb da))
  (if (int= lhs rhs)
      0
      (if (int< lhs rhs)
          -1
          1)))

; ============================================================
; N-ARY COMPARISON OPERATIONS
; ============================================================

(define (= . args)
  (if (null? args)
      #t
      (if (null? (cdr args))
          #t
          (if (int= (num-compare (car args) (cadr args)) 0)
              (apply = (cdr args))
              #f))))

(define (< . args)
  (if (null? args)
      #t
      (if (null? (cdr args))
          #t
          (if (int= (num-compare (car args) (cadr args)) -1)
              (apply < (cdr args))
              #f))))

(define (> . args)
  (if (null? args)
      #t
      (if (null? (cdr args))
          #t
          (if (int= (num-compare (car args) (cadr args)) 1)
              (apply > (cdr args))
              #f))))

(define (<= . args)
  (if (null? args)
      #t
      (if (null? (cdr args))
          #t
          (if (int= (num-compare (car args) (cadr args)) 1)
              #f
              (apply <= (cdr args))))))

(define (>= . args)
  (if (null? args)
      #t
      (if (null? (cdr args))
          #t
          (if (int= (num-compare (car args) (cadr args)) -1)
              #f
              (apply >= (cdr args))))))

; ============================================================
; MAX AND MIN
; ============================================================

(define (max2 a b)
  (if (int= (num-compare a b) 1) a b))

(define (max . args)
  (if (null? (cdr args))
      (car args)
      (max2 (car args) (apply max (cdr args)))))

(define (min2 a b)
  (if (int= (num-compare a b) -1) a b))

(define (min . args)
  (if (null? (cdr args))
      (car args)
      (min2 (car args) (apply min (cdr args)))))

; ============================================================
; ZERO?, POSITIVE?, NEGATIVE?
; ============================================================

(define (zero? x)
  (if (rational? x)
      (int= (numerator x) 0)
      (int= x 0)))

(define (positive? x)
  (if (rational? x)
      (int< 0 (numerator x))
      (int< 0 x)))

(define (negative? x)
  (if (rational? x)
      (int< (numerator x) 0)
      (int< x 0)))

; ============================================================
; EQV? AND EQUAL?
; ============================================================

(define (eqv? a b)
  (if (rational? a)
      (if (rational? b)
          (if (int= (numerator a) (numerator b))
              (int= (denominator a) (denominator b))
              #f)
          #f)
      (if (rational? b)
          #f
          (eq? a b))))

(define (equal? a b)
  (if (pair? a)
      (if (pair? b)
          (if (equal? (car a) (car b))
              (equal? (cdr a) (cdr b))
              #f)
          #f)
      (if (pair? b)
          #f
          (eqv? a b))))

; ============================================================
; ASSOCIATION LIST OPERATIONS
; ============================================================

(define (assq key lst)
  (if (null? lst)
      #f
      (if (eq? key (caar lst))
          (car lst)
          (assq key (cdr lst)))))

(define (assv key lst)
  (if (null? lst)
      #f
      (if (eqv? key (caar lst))
          (car lst)
          (assv key (cdr lst)))))

(define (assoc key lst)
  (if (null? lst)
      #f
      (if (equal? key (caar lst))
          (car lst)
          (assoc key (cdr lst)))))

; ============================================================
; WRITE FUNCTION w
; Prints rational numbers as n/d, prints lists on one line
; ============================================================

(define (w x)
  (cond
    ((rational? x)
     (begin
       (display (numerator x))
       (display "/")
       (display (denominator x))))
    ((pair? x)
     (begin
       (display "(")
       (w (car x))
       (w-list-tail (cdr x))
       (display ")")))
    (else
     (display x))))

(define (w-list-tail x)
  (if (null? x)
      #f
      (if (pair? x)
          (begin
            (display " ")
            (w (car x))
            (w-list-tail (cdr x)))
          (begin
            (display " . ")
            (w x)))))

; ============================================================
; ADDITIONAL LIST UTILITIES
; ============================================================

(define (list? x)
  (if (null? x)
      #t
      (if (pair? x)
          (list? (cdr x))
          #f)))

(define (member x lst)
  (if (null? lst)
      #f
      (if (equal? x (car lst))
          lst
          (member x (cdr lst)))))

(define (memv x lst)
  (if (null? lst)
      #f
      (if (eqv? x (car lst))
          lst
          (memv x (cdr lst)))))

(define (memq x lst)
  (if (null? lst)
      #f
      (if (eq? x (car lst))
          lst
          (memq x (cdr lst)))))

(define (newline) (display "\n"))
