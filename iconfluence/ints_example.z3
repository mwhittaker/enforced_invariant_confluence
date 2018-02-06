; x = MaxInt(name='x')
; y = MaxInt(name='y')
; tmp = MaxInt(name='tmp')
;
; incr:
;   x = x + 1
;   y = y + 1
;
; swap
;   tmp.assign(x)
;   x.assign(y)
;   y.assign(tmp)
;
; Invariants:
;   x == y

; oracle = Oracle()
; x = oracle.Int()
; y = oracle.Set(IntSort())
;
;
; def txn():
;   tmp = x + oracle.One()
;   x = x + y
;   y = ....
;
;  x = x + y
;  x = x + xrr
;
; oracle.check()


(define-fun max ((x Int) (y Int)) Int
    (ite (>= x y) x y)
)

(define-fun set_union ((x Int) (y Int)) Int
    (ite (>= x y) x y)
)

; 1. Commutativity ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; incr, swap
(push)
(declare-const x Int)
(declare-const y Int)
(declare-const tmp Int)
(declare-const x_incr_swap_1 Int)
(declare-const x_incr_swap_2 Int)
(declare-const y_incr_swap_1 Int)
(declare-const y_incr_swap_2 Int)
(declare-const tmp_incr_swap_1 Int)
(declare-const tmp_incr_swap_2 Int)
(declare-const x_swap_incr_1 Int)
(declare-const x_swap_incr_2 Int)
(declare-const y_swap_incr_1 Int)
(declare-const y_swap_incr_2 Int)
(declare-const tmp_swap_incr_1 Int)
(declare-const tmp_swap_incr_2 Int)

; incr -> swap
(assert (= x_incr_swap_1 (+ x 1)))
(assert (= y_incr_swap_1 (+ y 1)))
(assert (= tmp_incr_swap_1 x_incr_swap_1))
(assert (= x_incr_swap_2 y_incr_swap_1))
(assert (= y_incr_swap_2 tmp_incr_swap_1))

; swap -> incr
(assert (= tmp_swap_incr_1 x))
(assert (= x_swap_incr_1 y))
(assert (= y_swap_incr_1 tmp_swap_incr_1))
(assert (= x_swap_incr_2 (+ x_swap_incr_1 1)))
(assert (= y_swap_incr_2 (+ y_swap_incr_1 1)))

(assert (not (and (= x_incr_swap_2 x_swap_incr_2)
                  (= y_incr_swap_2 y_swap_incr_2))))
(check-sat)
(pop)

; 2. Join is Application ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; incr, swap
(push)
(declare-const x Int)
(declare-const y Int)
(declare-const x_incr_1 Int)
(declare-const y_incr_1 Int)
(declare-const tmp_swap_1 Int)
(declare-const x_swap_1 Int)
(declare-const y_swap_1 Int)
(declare-const x_joined Int)
(declare-const y_joined Int)
(declare-const x_incr_swap_1 Int)
(declare-const y_incr_swap_1 Int)

; incr join swap
(assert (= x_incr_1 (+ x 1)))
(assert (= y_incr_1 (+ y 1)))
(assert (= tmp_swap_1 x))
(assert (= x_swap_1 y))
(assert (= y_swap_1 tmp_swap_1))
(assert (= x_joined (max x_incr_1 x_swap_1)))
(assert (= y_joined (max y_incr_1 y_swap_1)))

; incr(swap)
(assert (= x_incr_swap_1 (+ x_swap_1 1)))
(assert (= y_incr_swap_1 (+ y_swap_1 1)))

(assert (not (and (= x_joined x_incr_swap_1) (= y_joined y_incr_swap_1))))
(check-sat)
(pop)

; 3. 1-DI-confluence ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(push)
(declare-const x Int)
(declare-const y Int)
(declare-const x_incr_1 Int)
(declare-const y_incr_1 Int)
(declare-const tmp_swap_1 Int)
(declare-const x_swap_1 Int)
(declare-const y_swap_1 Int)
(declare-const x_joined Int)
(declare-const y_joined Int)

(assert (= x_incr_1 (+ x 1)))
(assert (= y_incr_1 (+ y 1)))
(assert (= tmp_swap_1 x))
(assert (= x_swap_1 y))
(assert (= y_swap_1 tmp_swap_1))
(assert (= x_joined (max x_incr_1 x_swap_1)))
(assert (= y_joined (max y_incr_1 y_swap_1)))

(define-fun initial_invariant () Bool (= x y))
(define-fun incr_invariant () Bool (= x_incr_1 y_incr_1))
(define-fun swap_invariant () Bool (= x_swap_1 y_swap_1))
(define-fun joined_invariant () Bool (= x_swap_1 y_swap_1))
(assert (not (=> (and initial_invariant incr_invariant swap_invariant) joined_invariant)))
(check-sat)
(pop)
