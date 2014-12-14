(ns wbtree.tree
  (:use     [clj-tuple])
  (:require [wbtree.util :as util])
  (:require [clojure.zip :as zip]))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def +delta+ 3)
(def +gamma+ 2)



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn xcompare [x y]
  (if (= (type x) (type y))
    (if (instance? Comparable x)
      (compare x y)
      (compare (hash x) (hash y)))
    (compare (hash (type x)) (hash (type y)))))

(defn xcompare< [x y]
  (neg? (xcompare x y)))

(defn xcompare> [x y]
  (pos? (xcompare x y)))

(defn xcompare= [x y]
  (zero? (xcompare x y)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(def %leaf% nil)

(defn leaf [] %leaf%)


(defn null []
  (leaf))

(defn null? [n]
  (= n (leaf)))

(defn node [k v l r x]
  (tuple k v l r x))

(defn node? [thing]
  (= (type thing) clj_tuple.Tuple5))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn -k [[k _ _ _ _]]
  k)

(defn -v [[_ v _ _ _]]
  v)

(defn -l [[_ _ l _ _]]
  l)

(defn -r [[_ _ _ r _]]
  r)

(defn -x [[_ _ _ _ x]]
  x)

(defn -kv [[k v _ _ _]]
  (tuple k v))

(defn -lr [[_ _ l r _]]
  (tuple l r))

(defn -kvlr [[k v l r _]]
  (tuple k v l r))



(defmacro kv [[ksym vsym] n & body]
  `(let [[~ksym ~vsym _ _ _] ~n] 
     ~@body))


(defmacro kvlr [[ksym vsym lsym rsym] n & body]
  `(let [[~ksym ~vsym ~lsym ~rsym _] ~n]
     ~@body))


(defmacro kvlrx [[ksym vsym lsym rsym xsym] n & body]
  `(let [[~ksym ~vsym ~lsym ~rsym ~xsym] ~n]
     ~@body))



(defn node-call [n f]
  (apply f (-kvlr n)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn node-size [n]
  (if (null? n)
    0
    (-x n)))

(defn node-weight [n]
  (inc (node-size n)))


(defn node-cons-enum
  ([n] (node-cons-enum n (list)))
  ([n enum]
     (if (null? n)
       enum
       (kvlr [k v l r] n
         (node-cons-enum l (list (tuple k v) r enum))))))


(defn node-create [k v l r]
  (node k v l r (+ 1 (node-size l) (node-size r))))


(defn node-singleton [k v]
  (node-create k v (null) (null) ))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn rotate-single-left [ak av x r]
  (node-call r
    (fn [bk bv y z]
      (node-create bk bv
        (node-create ak av x y) z))))


(defn rotate-double-left [ak av x r]
  (node-call r
    (fn [ck cv b z]
      (node-call b
        (fn [bk bv y1 y2]
          (node-create bk bv
            (node-create ak av x y1)
            (node-create ck cv y2 z)))))))


(defn rotate-single-right [bk bv l z]
  (node-call l
    (fn [ak av x y]
      (node-create ak av x (node-create bk bv y z)))))


(defn rotate-double-right [ck cv l z]
  (node-call l
    (fn [ak av x b]
      (node-call b
        (fn [bk bv y1 y2]
          (node-create bk bv
            (node-create ak av x y1)
            (node-create ck cv y2 z)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn node-join [k v l r]
  (let [lw (node-weight l)
        rw (node-weight r)]
    (cond
      (> rw (* +delta+ lw)) (let [rlw (node-weight (-l r))
                                  rrw (node-weight (-r r))]
                              (if (< rlw (* +gamma+ rrw))
                                (rotate-single-left k v l r)
                                (rotate-double-left k v l r)))
      (> lw (* +delta+ rw)) (let [llw (node-weight (-l l))
                                  lrw (node-weight (-r l))]
                              (if (< lrw (* +gamma+ llw))
                                (rotate-single-right k v l r)
                                (rotate-double-right k v l r)))
      true                  (node-create k v l r))))


(defn node-add
  ([n k] (node-add n k k))
  ([n k v]
     (if (null? n)
       (node-singleton k v)
       (node-call n
         (fn [key val l r]
           (cond
             (xcompare< k key) (node-join key val (node-add l k v) r)
             (xcompare> k key) (node-join key val l (node-add r k v))
             true              (node-create key v l r)))))))


(defn node-concat3 [k v l r]
  (cond
    (null? l) (node-add r k v)
    (null? r) (node-add l k v)
    true      (let [lw (node-weight l)
                    rw (node-weight r)]
                (cond
                  (< (* +delta+ lw) rw) (node-call r
                                          (fn [k2 v2 l2 r2]
                                            (node-join k2 v2
                                              (node-concat3 k v l l2) r2)))
                  (< (* +delta+ rw) lw) (node-call l
                                          (fn [k1 v1 l1 r1]
                                            (node-join k1 v1 l1
                                              (node-concat3 k v r1 r))))
                  true                  (node-create k v l r)))))


(defn node-least [n]
  (cond
    (null? n)   (util/exception "least: empty tree")
    (null? (-l n)) n
    true           (node-least (-l n))))


(defn node-greatest [n]
  (cond
    (null? n)   (util/exception "greatest: empty tree")
    (null? (-r n)) n
    true           (node-greatest (-r n))))


(defn node-remove-least [n]
  (cond
    (null? n)       (util/exception "remove-least: empty tree")
    (null? (-l n))  (-r n)
    true            (node-join (-k n) (-v n)
                      (node-remove-least (-l n)) (-r n))))


(defn node-remove-greatest [n]
  (cond
    (null? n)       (util/exception "remove-greatest: empty tree")
    (null? (-r n))  (-l n)
    true            (node-join (-k n) (-v n) (-l n)
                      (node-remove-greatest (-r n)))))


(defn node-concat2 [l r]
  (cond
    (null? l) r
    (null? r) l
    true      (node-call (node-least r)
                (fn [k v _ _]
                  (node-join k v l (node-remove-least r))))))


(defn node-concat [n1 n2]
  (cond
    (null? n1) n2
    (null? n2) n1
    true       (let [minimum (node-least n2)]
                 (node-concat3 (-k minimum) (-v minimum) n1
                   (node-remove-least n2)))))


(defn node-remove [n k]
  (if (null? n)
    (null)
    (node-call n
      (fn [key val l r]
        (cond
          (xcompare< k key) (node-join key val (node-remove 1 k) r)
          (xcompare> k key) (node-join key val l (node-remove k r))
          true              (node-concat2 l r))))))


(defn node-find [n k]
  (letfn [(srch [this best]
            (cond
              (null? this)            best
              (xcompare< k (-k this)) (srch (-l this) best)
              true                    (srch (-r this) this)))]
    (let [best (srch n nil)]
      (when best
        (when-not (xcompare< (-k best) k)
          best)))))


(defn node-inorder-fold [f base n]
  (letfn [(fold [base n]
            (if (null? n)
              base
              (kvlr [k v l r] n
                (fold (f k v (fold base r)) l))))]
    (fold base node)))


(defn node-reverse-fold [f base n]
  (letfn [(fold [base n]
            (if (null? n)
              base
              (kvlr [k v l r] n
                (fold (f k v (fold base l)) r))))]
    (fold base node)))


(defn node-iter [n f]
  (if (null? n)
    nil
    (kvlr [_ _ l r] n
      (node-iter l f)
      (f n)
      (node-iter r f))))


(defn for-all-nodes [n p f]
  (node-iter n (fn [n] (when (p n) (f n)))))


(defn node-split-lesser [n k]
  (cond
    (null? n)            (null)
    (xcompare< k (-k n)) (node-split-lesser (-l n) k)
    (xcompare> k (-k n)) (node-concat3 (-k n) (-v n) (-l n)
                           (node-split-lesser (-r n) k))
    true                 (-l n)))


(defn node-split-greater [n k]
  (cond
    (null? n)            (null)
    (xcompare> k (-k n)) (node-split-greater (-r n) k)
    (xcompare< k (-k n)) (node-concat3 (-k n) (-v n)
                           (node-split-greater (-l n) k) (-r n))
    true                 (-r n)))


(defn node-split [n k]
  (if (null? n)
    [nil nil nil]
    (kvlr [ak v l r] n
      (let [c (xcompare k ak)]
        (cond
          (zero? c) [l (list k v) r]
          (neg?  c) (let [[ll pres rl] (node-split l k)]
                      [ll pres (node-concat3 ak v rl r)])
          (pos?  c) (let [[lr pres rr] (node-split r k)]
                      [(node-concat3 ak v l lr) pres rr]))))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn node-union [n1 n2]
  (cond
    (null? n1) n2
    (null? n2) n1
    true       (kvlr [ak av l r] n2
                 (let [l1 (node-split-lesser n1 ak)
                       r1 (node-split-greater n1 ak)]
                   (node-concat3 ak av
                     (node-union l1 l)
                     (node-union r1 r))))))


(defn node-intersection [n1 n2]
  (cond
    (null? n1) (null)
    (null? n2) (null)
    true       (kvlr [ak av l r] n2
                 (let [l1 (node-split-lesser n1 ak)
                       r1 (node-split-greater n1 ak)]
                   (if (node-find n1 ak)
                     (node-concat3 ak av
                       (node-intersection l1 l)
                       (node-intersection r1 r))
                     (node-concat
                       (node-intersection l1 l)
                       (node-intersection r1 r)))))))


(defn node-difference [n1 n2]
  (cond
    (null? n1) (null)
    (null? n2) n2
    true       (kvlr [ak _ l r] n2
                 (let [l1 (node-split-lesser n1 ak)
                       r1 (node-split-greater n1 ak)]
                   (node-concat
                     (node-difference l1 l)
                     (node-difference r1 r))))))


(defn node-subset? [super sub]
  (letfn [(subset? [n1 n2]
            (or (null? n1)
              (and (<= (node-size n1) (node-size n2))
                (kvlr [k1 _ l1 r1] n1
                  (kvlr [k2 _ l2 r2] n2
                    (let [c (xcompare k1 k2)]
                      (cond
                        (neg? c) (and
                                   (subset?   l1 l2)
                                   (node-find n2 k1)
                                   (subset?   r1 n2))
                        (pos? c) (and
                                   (subset?   r1 r2)
                                   (node-find n2 k1)
                                   (subset?   l1 n2))
                        true     (and
                                   (subset? l1 l2)
                                   (subset? r1 r2)))))))))]
    (let [res (or (null? sub) (subset? sub super))]
      (if res true false))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn node-at-rank [n index]
  (letfn [(srch [n index]
            (kvlr [_ _ l r] n
              (let [lsize (node-size l)]
                (cond
                  (< index lsize) (srch l index)
                  (> index lsize) (srch r (- index (inc lsize)))
                  true            n))))]
    (if-not (and (<= 0 index) (< index (node-size n)))
      (util/exception "index out of range")
      (srch n index))))


(defn node-rank
  ([n k] (node-rank n k 0))
  ([n k rank]
     (cond
       (null? n)            nil
       (xcompare< k (-k n)) (node-rank (-l n) k rank)
       (xcompare> k (-k n)) (node-rank (-r n) k
                              (+ 1 rank (node-size (-l n))))
       true                 (+ rank (node-size (-l n))))))
  
    


