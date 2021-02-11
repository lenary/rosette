#lang racket

(require racket/syntax (only-in racket [< racket/<] [- racket/-] [and racket/and])
         (only-in "server.rkt" printf/current-server))

(provide (except-out (all-defined-out) quantified define-ops printf-smt))

; Prints all smt commands to current-output-port.
; To dump the printed SMT, use (output-smt #t).
(define-syntax-rule (printf-smt arg ...)
  (printf/current-server arg ...))

; Commands
(define (set-option opt val) (printf-smt "(set-option ~a ~a)\n" opt val))

(define (set-logic l)    (printf-smt "(set-logic ~a)\n" l))
(define (check-sat)      (printf-smt "(check-sat)\n"))
(define (get-model)      (printf-smt "(get-model)\n"))
(define (get-unsat-core) (printf-smt "(get-unsat-core)\n"))
(define (get-info kw)    (printf-smt "(get-info ~a)\n" kw))
(define (echo s)         (printf-smt "(echo \"~a\")\n" s))

(define (reset)          (printf-smt "(reset)\n"))
(define (push [n 1])     (printf-smt "(push ~a)\n" n))
(define (pop [n 1])      (printf-smt "(pop ~a)\n" n))

(define assert 
  (case-lambda [(e)     (printf-smt "(assert ~a)\n" e)]
               [(e id)  (printf-smt "(assert (! ~a :named ~a))\n" e id)]))

(define (minimize t)    (printf-smt "(minimize ~a)\n" t))
(define (maximize t)    (printf-smt "(maximize ~a)\n" t))

; Declarations and definitions
(define (declare-const id type)
  (printf-smt "(declare-const ~a ~a)\n" id type))

(define (declare-fun id domain range)
  (printf-smt "(declare-fun ~a ~a ~a)\n" id domain range))
                     
(define (define-const id type body)
  (printf-smt "(define-fun ~a () ~a ~a)\n" id type body))

(define (define-fun id args type body)
  (printf-smt "(define-fun ~a ~a ~a ~a)\n" id args type body))

; Applications of uninterpreted functions.
(define (app f . args)
  `(,f ,@args))

(define-syntax-rule (define-ops id ...)
  (define-values (id ...)
    (values (lambda e `(id ,@e)) ...)))

(define-syntax-rule (define-names id ...)
  (define-values (id ...)
    (values 'id ...)))

; Core theoryRosette: Add support for quantifiers
(define-names
  Bool
  true false)
(define-ops not and or xor => ite = distinct)
(define (<=> l r) (and (=> l r) (=> r l)))

; Bitvector theory
(define (BitVec size) `(_ BitVec ,size))
(define (bv val size)  (if (racket/< val 0)
                           (bvneg `(_ ,(format-symbol "bv~a" (racket/- val)) ,size))
                           `(_ ,(format-symbol "bv~a" val) ,size)))
(define-ops 
  bvnot bvand bvor bvxor 
  bvule bvult bvuge bvugt bvsle bvslt bvsge bvsgt
  bvneg bvadd bvsub bvmul bvsdiv bvudiv bvurem bvsrem bvsmod
  bvshl bvlshr bvashr concat) 

(define (extract i j s)
  `((_ extract ,i ,j) ,s))

(define (zero_extend i b)
  `((_ zero_extend ,i) ,b))

(define (sign_extend i b)
  `((_ sign_extend ,i) ,b))

; Int and Real theories
(define-names Int Real)
(define-ops
  + - * / div mod abs 
  < <= 
  is_int to_int to_real )

; Quantifiers
(define (quantified quantifier vars body)
  `(,quantifier ,vars ,body))

(define (forall vars body)
  (quantified 'forall vars body))

(define (exists vars body)
  (quantified 'exists vars body))

;; Float Theory
(define (FloatingPoint exp-size significand-size)
  `(_ FloatingPoint ,exp-size ,significand-size))

(define-names
  Float16
  Float32
  Float64
  Float128)

; FP Value Constructor
; TODO: make sure sign, exp, significand are the right number of bits
(define (fp sign exp significand)
  `(fp ,sign ,exp ,significand))

; Infinity
(define (+oo exp-size significand-size)
  `(_ +oo ,exp-size ,significand-size))
(define (-oo exp-size significand-size)
  `(_ -oo ,exp-size ,significand-size))

; Zeroes
(define (+zero exp-size significand-size)
  `(_ +zero ,exp-size ,significand-size))
(define (-zero exp-size significand-size)
  `(_ -zero ,exp-size ,significand-size))

; NaN
(define (NaN exp-size significand-size)
  `(_ NaN ,exp-size ,significand-size))

; Rounding Modes
(define-names
  RoundingMode
  roundNearestTiesToEven RNE
  roundNearestTiesToAway RNA
  roundTowardPositive    RTP
  roundTowardNegative    RTN
  roundTowardZero        RTZ)

(define-ops
  fp.abs fp.neg
  fp.add fp.sub
  fp.mul fp.div fp.rem fp.fma fp.sqrt
  fp.roundToIntegral
  fp.min fp.max
  fp.eq fp.leq fp.lt fp.geq fp.gt
  fp.isNormal
  fp.isSubnormal
  fp.isZero
  fp.isInfinite
  fp.isNaN
  fp.isNegative
  fp.isPositive
  fp.to_real)

(define (to_fp exp-size significand-size . args)
  `((_ to_fp ,exp-size ,significand-size) ,@args))
(define (to_fp_unsigned exp-size significand-size . args)
  `((_ to_fp_unsigned ,exp-size ,significand-size) ,@args))

(define (fp.to_ubv bv-size . args)
  `((_ fp.to_ubv ,bv-size) ,@args))
(define (fp.to_sbv bv-size . args)
  `((_ fp.to_sbv ,bv-size) ,@args))

