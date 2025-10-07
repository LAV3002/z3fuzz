; func 2
(define-fun mor ((lhs (_ BitVec 64)) (rhs (_ BitVec 64))) (_ BitVec 64) (bvor lhs rhs))
(define-fun mand ((lhs (_ BitVec 64)) (rhs (_ BitVec 64))) (_ BitVec 64) (bvand lhs rhs))
(define-fun mxor ((lhs (_ BitVec 64)) (rhs (_ BitVec 64))) (_ BitVec 64) (bvxor lhs rhs))

(define-fun madd ((lhs (_ BitVec 64)) (rhs (_ BitVec 64))) (_ BitVec 64) (bvadd lhs rhs))
(define-fun msub ((lhs (_ BitVec 64)) (rhs (_ BitVec 64))) (_ BitVec 64) (bvsub lhs rhs))
(define-fun mmul ((lhs (_ BitVec 64)) (rhs (_ BitVec 64))) (_ BitVec 64) (bvmul lhs rhs))
(define-fun msdiv ((lhs (_ BitVec 64)) (rhs (_ BitVec 64))) (_ BitVec 64) (bvsdiv lhs rhs))
(define-fun mudiv ((lhs (_ BitVec 64)) (rhs (_ BitVec 64))) (_ BitVec 64) (bvudiv lhs rhs))

(define-fun meq ((lhs (_ BitVec 64)) (rhs (_ BitVec 64))) (_ BitVec 64) (ite (= lhs rhs) (_ bv1 64) (_ bv0 64)))

(define-fun mult ((lhs (_ BitVec 64)) (rhs (_ BitVec 64))) (_ BitVec 64) (ite (bvult lhs rhs) (_ bv1 64) (_ bv0 64)))
(define-fun mule ((lhs (_ BitVec 64)) (rhs (_ BitVec 64))) (_ BitVec 64) (ite (bvule lhs rhs) (_ bv1 64) (_ bv0 64)))
(define-fun muge ((lhs (_ BitVec 64)) (rhs (_ BitVec 64))) (_ BitVec 64) (ite (bvuge lhs rhs) (_ bv1 64) (_ bv0 64)))
(define-fun mugt ((lhs (_ BitVec 64)) (rhs (_ BitVec 64))) (_ BitVec 64) (ite (bvugt lhs rhs) (_ bv1 64) (_ bv0 64)))

(define-fun mslt ((lhs (_ BitVec 64)) (rhs (_ BitVec 64))) (_ BitVec 64) (ite (bvslt lhs rhs) (_ bv1 64) (_ bv0 64)))
(define-fun msle ((lhs (_ BitVec 64)) (rhs (_ BitVec 64))) (_ BitVec 64) (ite (bvsle lhs rhs) (_ bv1 64) (_ bv0 64)))
(define-fun msge ((lhs (_ BitVec 64)) (rhs (_ BitVec 64))) (_ BitVec 64) (ite (bvsge lhs rhs) (_ bv1 64) (_ bv0 64)))
(define-fun msgt ((lhs (_ BitVec 64)) (rhs (_ BitVec 64))) (_ BitVec 64) (ite (bvsgt lhs rhs) (_ bv1 64) (_ bv0 64)))

(define-fun msrem ((lhs (_ BitVec 64)) (rhs (_ BitVec 64))) (_ BitVec 64) (bvsrem lhs rhs))
(define-fun msmod ((lhs (_ BitVec 64)) (rhs (_ BitVec 64))) (_ BitVec 64) (bvsmod lhs rhs))
(define-fun murem ((lhs (_ BitVec 64)) (rhs (_ BitVec 64))) (_ BitVec 64) (bvurem lhs rhs))

(define-fun mshl ((lhs (_ BitVec 64)) (rhs (_ BitVec 64))) (_ BitVec 64) (bvshl lhs rhs))
(define-fun mlshr ((lhs (_ BitVec 64)) (rhs (_ BitVec 64))) (_ BitVec 64) (bvlshr lhs rhs))
(define-fun mashr ((lhs (_ BitVec 64)) (rhs (_ BitVec 64))) (_ BitVec 64) (bvashr lhs rhs))

(define-fun mmix ((lhs (_ BitVec 64)) (rhs (_ BitVec 64))) (_ BitVec 64) (concat ((_ extract 31 0) lhs) ((_ extract 63 32) rhs)))

; func 1

(define-fun mnot ((lhs (_ BitVec 64))) (_ BitVec 64) (bvnot lhs))

; symbols

(declare-fun SV1 () (_ BitVec 64))
(declare-fun SV2 () (_ BitVec 64))
(declare-fun SV3 () (_ BitVec 64))
(declare-fun SV4 () (_ BitVec 64))

; body

(define-fun T6 () (_ BitVec 64) ( mor SV1 SV2 ))
(define-fun T5 () (_ BitVec 64) ( mnot T6 ))
(define-fun T4 () (_ BitVec 64) ( mnot SV1 ))
(define-fun T3 () (_ BitVec 64) ( mnot SV1 ))
(define-fun T2 () (_ BitVec 64) ( mand T3 T4 ))
(define-fun T1 () (_ BitVec 64) ( meq T2 T5 ))
(define-fun T0 () (_ BitVec 64) ( mnot T1 ))

; epilog

(assert (= T0 (_ bv1 64)))
(check-sat)
