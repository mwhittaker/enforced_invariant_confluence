;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define-fun intmax ((x Int) (y Int)) Int
  (ite (< x y) y x))
(declare-fun decl_intmax (Int Int) Int)
(assert (forall ((x Int) (y Int)) (= (intmax x y) (decl_intmax x y))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Pair
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(declare-datatypes (A B) ((Pair (pair (first A) (second B)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Option
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(declare-datatypes (A) ((Option none (some (x A)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Sets
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define-sort Elt () Int)
(define-sort Set () (Array Elt Bool))

(define-fun set_empty () Set
  ((as const Set) false))

(define-fun set_mem ((s Set) (x Elt)) Bool
  (select s x))

(define-fun set_add ((s Set) (x Elt)) Set
  (store s x true))

(define-fun set_intersect ((s1 Set) (s2 Set)) Set
  ((_ map and) s1 s2))

(define-fun set_union ((s1 Set) (s2 Set)) Set
  ((_ map or) s1 s2))

(define-fun set_complement ((s Set)) Set
  ((_ map not) s))

(define-fun set_diff ((s1 Set) (s2 Set)) Set
  (set_intersect s1 (set_complement s2)))

(define-fun set_subset ((s1 Set) (s2 Set)) Bool
  (= set_empty (set_diff s1 s2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; State-based G-Set
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define-sort GSet () Set)

(define-fun gset_query ((xs GSet)) Set
  xs)

(define-fun gset_add ((xs GSet) (x Elt)) GSet
  (set_add xs x))

(define-fun gset_merge ((xs GSet) (ys GSet)) GSet
  (set_union xs ys))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; State-based 2P-Set
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(declare-datatypes () ((TwoPSet (twopset (a GSet) (r GSet)))))

(define-fun twopset_query ((xs TwoPSet)) Set
  (set_diff (a xs) (r xs)))

(define-fun twopset_add ((xs TwoPSet) (x Elt)) TwoPSet
  (twopset (set_add (a xs) x) (r xs)))

(define-fun twopset_remove ((xs TwoPSet) (x Elt)) TwoPSet
  (twopset (a xs) (set_add (r xs) x)))

(define-fun twopset_merge ((xs TwoPSet) (ys TwoPSet)) TwoPSet
  (twopset (gset_merge (a xs) (a ys)) (gset_merge (r xs) (r ys))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; State-based LWW-Set
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define-sort IntMap () (Array Elt Int))

; http://stackoverflow.com/questions/19258074/mapping-user-defined-functions-in-z3
(define-fun intmap_merge ((xs IntMap) (ys IntMap)) IntMap
  ((_ map decl_intmax) xs ys))

(declare-datatypes () ((LWWSet (lwwset (a IntMap) (r IntMap)))))

(define-fun lwwset_query ((xs LWWSet)) Set
  ((_ map (> (Int Int) Int)) (a xs) (r xs)))

(define-fun lwwset_add ((xs LWWSet) (x Elt)) LWWSet
  (lwwset (store (a xs) x (+ (intmax (select (a xs) x) (select (r xs) x)) 1))
          (r xs)))

(define-fun lwwset_remove ((xs LWWSet) (x Elt)) LWWSet
  (lwwset (a xs)
          (store (r xs) x (+ (intmax (select (a xs) x) (select (r xs) x)) 1))))

(define-fun lwwset_merge ((xs LWWSet) (ys LWWSet)) LWWSet
  (lwwset (intmap_merge (a xs) (a ys)) (intmap_merge (r xs) (r ys))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(declare-const xs (LWWSet))
(declare-const ys (LWWSet))
(declare-const x1 (Elt))
(declare-const y1 (Elt))
(declare-const x2 (Elt))
(declare-const y2 (Elt))

(define-fun conjecture () Bool
  (=>
  (and
  (and (subset (lwwset_query xs) (lwwset_query ys))
       (subset (lwwset_query (lwwset_add xs x1)) (lwwset_query (lwwset_add ys y1))))
       (subset (lwwset_query (lwwset_add xs x2)) (lwwset_query (lwwset_add ys y2))))
       (subset (lwwset_query (lwwset_merge (lwwset_add xs x1) (lwwset_add xs x2)))
               (lwwset_query (lwwset_merge (lwwset_add ys y1) (lwwset_add ys y2))))
  )
)

(assert (not conjecture))

(check-sat)
(get-model)
