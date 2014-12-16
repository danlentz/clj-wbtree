(ns wbtree.tree
  (:use     [clj-tuple])
  (:require [wbtree.util :as util]))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Weight Balanced Functional Binary Tree (Hirai-Yamamoto Tree)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; This is an implementation of a weight-balanced binary tree data
;;  structure based on the following references:
;;
;; --  Adams (1992)
;;     'Implementing Sets Efficiently in a Functional Language'
;;     Technical Report CSTR 92-10, University of Southampton.
;;
;; --  Hirai and Yamamoto (2011)
;;     'Balancing Weight-Balanced Trees'
;;     Journal of Functional Programming / 21 (3):
;;     Pages 287-307
;;
;; --  Oleg Kiselyov
;;     'Towards the best collection API, A design of the overall optimal
;;     collection traversal interface'
;;     <http://pobox.com/~oleg/ftp/papers/LL3-collections-enumerators.txt>
;;
;; --  Nievergelt and Reingold (1972)
;;     'Binary Search Trees of Bounded Balance'
;;     STOC '72 Proceedings
;;     4th Annual ACM symposium on Theory of Computing
;;     Pages 137-142 
;;
;; --  Driscoll, Sarnak, Sleator, and Tarjan (1989)
;;     'Making Data Structures Persistent'
;;     Journal of Computer and System Sciences Volume 38 Issue 1, February 1989
;;     18th Annual ACM Symposium on Theory of Computing
;;     Pages 86-124
;;
;; --  MIT Scheme weight balanced tree as reimplemented by Yoichi Hirai
;;     and Kazuhiko Yamamoto using the revised non-variant algorithm recommended
;;     integer balance parameters from (Hirai/Yamomoto 2011).
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Weight Balancing Constants
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  
;; +delta+:
;;   The primary balancing rotation parameter that is used for the
;;   determination whether two subtrees of a node are in balance or
;;   require adjustment by means of a rotation operation.  The specific
;;   rotation to be performed is determined by +gamma+.

(def +delta+ 3)

;; +gamma+:
;;   The secondary balancing rotation parameter that is used for the
;;   determination of whether a single or double rotation operation should
;;   occur, once it has been decided based on +delta+ that a rotation is
;;   indeed required.

(def +gamma+ 2)



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Universal Comparator
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
;; Storage Model
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(def %leaf% nil)

(defn leaf [] %leaf%)


(defn null
  "a value which satisfies null?"
  []
  (leaf))

(defn null? [n]
  (= n (leaf)))

(defn node [k v l r x]
  (tuple k v l r x))

(defn node? [thing]
  (= (type thing) clj_tuple.Tuple5))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Constituent Accessors
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



(defmacro kv
  "destructure node n: key value"
  [[ksym vsym] n & body]
  `(let [[~ksym ~vsym _ _ _] ~n] 
     ~@body))


(defmacro kvlr
  "destructure node n: key value left right"
  [[ksym vsym lsym rsym] n & body]
  `(let [[~ksym ~vsym ~lsym ~rsym _] ~n]
     ~@body))


(defmacro kvlrx
  "destructure node n: key value left right size"
  [[ksym vsym lsym rsym xsym] n & body]
  `(let [[~ksym ~vsym ~lsym ~rsym ~xsym] ~n]
     ~@body))


(defn node-call 
  "apply f to the destructured constituent values of n.
   f is a function taking four parameters: K, V, L, and R,
   where K is the key of NODE, V is the value of NODE, L is the left
   subtree of NODE, and R is the right subtree of NODE."
  [n f]
  (apply f (-kvlr n)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Fundamental Node Operations
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn node-size [n]
  (if (null? n)
    0
    (-x n)))


(defn node-weight
  "returns node weight as appropriate for rotation calculations using
   the 'revised non-variant algorithm' for weight balanced binary tree."
  [n]
  (inc (node-size n)))


(defn node-cons-enum
  "Efficient mechanism to accomplish partial enumeration of
   tree-structure into a seq representation without incurring the
   overhead of operating over the entire tree.  Used internally for
   implementation of higher-level collection api routines"
  ([n] (node-cons-enum n nil))
  ([n enum]
     (if (null? n)
       enum
       (kvlr [k v l r] n
         (node-cons-enum l (list n r enum))))))


(defn node-cons-enum-reverse
  ([n] (node-cons-enum-reverse n nil))
  ([n enum]
     (if (null? n)
       enum
       (kvlr [k v l r] n
         (node-cons-enum-reverse r (list n l enum))))))


(defn node-enum-first [enum]
  (when (seq enum)
    (first enum)))


(defn node-enum-rest  [enum]
  (when (seq enum)
    (let [[x1 x2 x3] enum]
      (when-not (and (nil? x2) (nil? x3))
        (node-cons-enum x2 x3)))))


(defn node-enum-prior [enum]
  (when (seq enum)
    (let [[x1 x2 x3] enum]
      (when-not (and (nil? x2) (nil? x3))
        (node-cons-enum-reverse x2 x3)))))


(defn node-create
  "Join left and right subtrees at root k/v.
  Assumes all keys in l < k < all keys in r."
  [k v l r]
  (node k v l r (+ 1 (node-size l) (node-size r))))


(defn node-singleton 
  "Create and return a newly allocated weight balanced
  tree containing a single association, that value V with key K."
  [k v]
  (node-create k v (null) (null) ))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Tree Rotations
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn rotate-single-left
  "Perform a single left rotation, moving Y, the left subtree of the
  right subtree of A, into the left subtree (shown below).  This must
  occur in order to restore proper balance when the weight of the left
  subtree of node A is less then the weight of the right subtree of
  node A multiplied by rotation coefficient +delta+ and the weight of
  the left subtree of node B is less than the weight of the right subtree
  of node B multiplied by rotation coefficient +gamma+
 
                ,---,                                  ,---,
                | A |                                  | B |
                :---:                                  :---:
               :     :                                :     :
          ,---:       :---,                      ,---:       :---, 
          | X |       | B |           =>         | A |       | Z | 
          '---'       :---:                      :---:       '---'
                 ,---:     :---,            ,---:     :---,
                 | Y |     | Z |            | X |     | Y |
                 '---'     '---'            '---'     '---'
  "
  [ak av x r]
  (node-call r
    (fn [bk bv y z]
      (node-create bk bv
        (node-create ak av x y) z))))



(defn rotate-double-left
  "Perform a double left rotation, moving Y1, the left subtree of the
  left subtree of the right subtree of A, into the left subtree (shown
  below).  This must occur in order to restore proper balance when the
  weight of the left subtree of node A is less then the weight of the
  right subtree of node A multiplied by rotation coefficient +delta+
  and the weight of the left subtree of node B is greater than or equal
  to the weight of the right subtree of node B multiplied by rotation
  coefficient +gamma+.
  
                ,---,                                    ,---,             
                | A |                                    | B |             
             ___:---:___                             ____:---:____          
        ,---:           :---,                   ,---:             :---,       
        | X |           | C |                   | A |             | C |       
        '---'           :---:         =>        :---:             :---:
                   ,---:     :---,         ,---:     :---,   ,---:     :---,  
                   | B |     | Z |         | X |     | y1|   | y2|     | Z |  
                   :---:     '---'         '---'     '---'   '---'     '---'
              ,---:     :---,   
              | y1|     | y2|  
              '---'     '---'
  "
  [ak av x r]
  (node-call r
    (fn [ck cv b z]
      (node-call b
        (fn [bk bv y1 y2]
          (node-create bk bv
            (node-create ak av x y1)
            (node-create ck cv y2 z)))))))


(defn rotate-single-right
  "Perform a single right rotation, moving Y, the right subtree of the
  left subtree of B, into the right subtree (shown below).  This must
  occur in order to restore proper balance when the weight of the right
  subtree of node B is less then the weight of the left subtree of
  node B multiplied by rotation coefficient +delta+ and the weight of the
  right subtree of node A is less than the weight of the left subtree
  of node A multiplied by rotation coefficient +gamma+.
  
                ,---,                                  ,---,             
                | B |                                  | A |             
                :---:                                  :---:             
               :     :                                :     :            
          ,---:       :---,                      ,---:       :---,       
          | A |       | Z |          =>          | X |       | B |       
          :---:       '---'                      '---'       :---:       
     ,---:     :---,                                    ,---:     :---,  
     | X |     | Y |                                    | Y |     | Z |  
     '---'     '---'                                    '---'     '---'  
  "
  [bk bv l z]
  (node-call l
    (fn [ak av x y]
      (node-create ak av x (node-create bk bv y z)))))


(defn rotate-double-right
  "Perform a double right rotation, moving Y2, the right subtree of
  the right subtree of the left subtree of C, into the right
  subtree (shown below).  This must occur in order to restore proper
  balance when the weight of the right subtree of node C is less then
  the weight of the left subtree of node C multiplied by rotation
  coefficient +delta+ and the weight of the right subtree of node B
  is greater than or equal to the weight of the left subtree of node B
  multiplied by rotation coefficient +gamma+.
  
                ,---,                                    ,---,             
                | C |                                    | B |             
             ___:---:___                             ____:---:____          
        ,---:           :---,                   ,---:             :---,       
        | A |           | Z |                   | A |             | C |       
        :---:           '---'        =>         :---:             :---:
   ,---:     :---,                         ,---:     :---,   ,---:     :---,  
   | X |     | B |                         | X |     | y1|   | y2|     | Z |  
   '---'     :---:                         '---'     '---'   '---'     '---'
        ,---:     :---,   
        | y1|     | y2|  
        '---'     '---'
  "
  [ck cv l z]
  (node-call l
    (fn [ak av x b]
      (node-call b
        (fn [bk bv y1 y2]
          (node-create bk bv
            (node-create ak av x y1)
            (node-create ck cv y2 z)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Fundamental Tree Operations
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn node-join
  "Join left and right subtrees at root k/v, performing a single or
  double rotation to balance the resulting tree, if needed.  Assumes
  all keys in l < k < all keys in r, and the relative weight balance
  of the left and right subtrees is such that no more than one
  single/double rotation will result in each subtree being less than
  +delta+ times the weight of the other."
  [k v l r]
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


(defn node-least 
  "Return the node containing the minimum key of the tree rooted at n"
  [n]
  (cond
    (null? n)   (util/exception "least: empty tree")
    (null? (-l n)) n
    true           (node-least (-l n))))


(defn node-greatest
  "Return the node containing the minimum key of the tree rooted at n"
  [n]
  (cond
    (null? n)   (util/exception "greatest: empty tree")
    (null? (-r n)) n
    true           (node-greatest (-r n))))


(defn node-remove-least
  "Return a tree the same as the one rooted at n, with the node
  containing the minimum key removed. See node-least."
  [n]
  (cond
    (null? n)       (util/exception "remove-least: empty tree")
    (null? (-l n))  (-r n)
    true            (node-join (-k n) (-v n)
                      (node-remove-least (-l n)) (-r n))))


(defn node-remove-greatest
  "Return a tree the same as the one rooted at n, with the node
  containing the maximum key removed. See node-greatest."
  [n]
  (cond
    (null? n)       (util/exception "remove-greatest: empty tree")
    (null? (-r n))  (-l n)
    true            (node-join (-k n) (-v n) (-l n)
                      (node-remove-greatest (-r n)))))


(defn node-concat2
  "Join two trees, the left rooted at l, and the right at r,
  performing a single balancing operation on the resulting tree, if
  needed. Assumes all keys in l are smaller than all keys in r, and
  the relative balance of l and r is such that no more than one rotation
  operation will be required to balance the resulting tree"
  [l r]
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
          (xcompare< k key) (node-join key val (node-remove l k) r)
          (xcompare> k key) (node-join key val l (node-remove k r))
          true              (node-concat2 l r))))))


(defn node-find
  "Find k (if exists) in only d comparisons (d is depth of tree)
   rather than the traditional compare/low compare/high which takes on
   avg (* 1.5 (- d 1))"
  [n k]
  (letfn [(srch [this best]
            (cond
              (null? this)            best
              (xcompare< k (-k this)) (srch (-l this) best)
              true                    (srch (-r this) this)))]
    (let [best (srch n nil)]
      (when best
        (when-not (xcompare< (-k best) k)
          best)))))


(defn node-fold-left
  "Fold-left (reduce) the collection from least to greatest."
  [f base n]
  (letfn [(fold [base n]
            (if (null? n)
              base
              (kvlr [_ _ l r] n
                (fold (f (fold base l) n) r))))]
    (fold base n)))


(defn node-fold-right
  "Fold-right (reduce) the collection from greatest to least."
  [f base n]
  (letfn [(fold [base n]
            (if (null? n)
              base
              (kvlr [_ _ l r] n
                (fold (f (fold base r) n) l))))]
    (fold base n)))


(defn node-iter
  "For the side-effect, apply f to each node of the tree rooted at n"
  [n f]
  (if (null? n)
    nil
    (kvlr [_ _ l r] n
      (node-iter l f)
      (f n)
      (node-iter r f))))


(defn for-all-nodes
  "For the side-effect, apply f to each node of the tree rooted at
  n for which the predicate function returns a logically true value"
  [n p f]
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


(defn node-split
  "returns a triple (l present r) where: l is the set of elements of
  n that are < k, r is the set of elements of n that are > k, present
  is false if n contains no element equal to k, or (k v) if n contains
  an element with key equal to k"
  [n k]
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
;; Fundamental Set Operations
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn node-set-union [n1 n2]
  (cond
    (null? n1) n2
    (null? n2) n1
    true       (kvlr [ak av l r] n2
                 (let [l1 (node-split-lesser n1 ak)
                       r1 (node-split-greater n1 ak)]
                   (node-concat3 ak av
                     (node-set-union l1 l)
                     (node-set-union r1 r))))))



(defn node-set-intersection [n1 n2]
  (cond
    (null? n1) (null)
    (null? n2) (null)
    true       (kvlr [ak av l r] n2
                 (let [l1 (node-split-lesser n1 ak)
                       r1 (node-split-greater n1 ak)]
                   (if (node-find n1 ak)
                     (node-concat3 ak av
                       (node-set-intersection l1 l)
                       (node-set-intersection r1 r))
                     (node-concat
                       (node-set-intersection l1 l)
                       (node-set-intersection r1 r)))))))



(defn node-set-difference [n1 n2]
  (cond
    (null? n1) (null)
    (null? n2) n2
    true       (kvlr [ak _ l r] n2
                 (let [l1 (node-split-lesser n1 ak)
                       r1 (node-split-greater n1 ak)]
                   (node-concat
                     (node-set-difference l1 l)
                     (node-set-difference r1 r))))))



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



(defn node-set-compare 
  "return 3-way ordinal comparison of the trees n1 and n2 with the following
  return-value semantics:

   -1  -> n1 is LESS-THAN    n2
    0  -> n1 is EQAL-TO      n2
   +1  -> n1 is GREATER-THAN n2"
  [n1 n2] 
  (loop [e1 (node-cons-enum n1 nil)
         e2 (node-cons-enum n2 nil)]      
    (cond
      (and (nil? e1) (nil? e2))  0
      (nil? e1)                 -1
      (nil? e2)                  1
      true                       (let [[v1 r1 ee1] e1
                                       [v2 r2 ee2] e2
                                       c (xcompare (-k v1) (-k v2))]
                                   (if-not (zero? c)
                                     c
                                     (recur
                                       (node-cons-enum r1 ee1)
                                       (node-cons-enum r2 ee2)))))))
                                     


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Fundamental Vector Operations
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn node-nth 
  "Return nth node from the beginning of the ordered tree rooted at n."
  [n index]
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
  "Return the rank (sequential position) of a given KEY within the
  ordered tree rooted at n."
  ([n k] (node-rank n k 0))
  ([n k rank]
     (cond
       (null? n)            nil
       (xcompare< k (-k n)) (node-rank (-l n) k rank)
       (xcompare> k (-k n)) (node-rank (-r n) k
                              (+ 1 rank (node-size (-l n))))
       true                 (+ rank (node-size (-l n))))))
  
    
(defn node-vec
  "Return a (lon-lazy) vector of all nodes in tree rooted at n in
  the order they occur."
  [n]
  (node-fold-left conj [] n))

    
(defn node-vec-reverse
  "Return a (lon-lazy) vector of all nodes in tree rooted at n in
  reverse order."
  [n]
  (node-fold-right conj [] n))


(defn node-key-vec
  "Return a (lon-lazy) vector of all keys in tree rooted at n
  in the order they occur."
  [n]
  (node-fold-left #(conj %1 (-k %2)) [] n))


(defn node-key-vec-reverse
  "Return a (lon-lazy) vector of all keys in tree rooted at n
  in reverse-order."
  [n]
  (node-fold-right #(conj %1 (-k %2)) [] n))


(defn node-value-vec
  "Return a (lon-lazy) vector of all values in tree rooted at n
  in the order they occur."
  [n]
  (node-fold-left #(conj %1 (-v %2)) [] n))


(defn node-value-vec-reverse
  "Return a (lon-lazy) vector of all values in tree rooted at n
  in reverse-order."
  [n]
  (node-fold-right #(conj %1 (-v %2)) [] n))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Fundamental Seq Operations
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn- node-enum-seq [enum]
  (lazy-seq
    (when-not (nil? enum)
      (cons (node-enum-first enum)
        (node-enum-seq (node-enum-rest enum))))))

(defn- node-enum-seq-reverse [enum]
  (lazy-seq
    (when-not (nil? enum)
      (cons (node-enum-first enum)
        (node-enum-seq-reverse (node-enum-prior enum))))))


(defn node-seq
  "Return a (lazy) seq of nodes in tree rooted at n in the order they occur."
  [n]
  (node-enum-seq (node-cons-enum n)))


(defn node-seq-reverse
  "Return a (lazy) seq of nodes in tree rooted at n in reverse order."
  [n]
  (node-enum-seq-reverse (node-cons-enum-reverse n)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Misc
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn- make-integer-tree
  ([size]           (reduce node-add (null) (range size)))
  ([start end]      (reduce node-add (null) (range start end)))
  ([start end step] (reduce node-add (null) (range start end step))))


(defn- make-integer-set
  ([size]           (reduce conj #{} (range size)))
  ([start end]      (reduce conj #{} (range start end)))
  ([start end step] (reduce conj #{} (range start end step))))


(defn- make-integer-sorted-set
  ([size]           (reduce conj (sorted-set) (range size)))
  ([start end]      (reduce conj (sorted-set) (range start end)))
  ([start end step] (reduce conj (sorted-set) (range start end step))))


;; (def i10 (make-integer-tree 10))
;; (def i30 (make-integer-tree 20 30))
;; (def i   (make-integer-tree 30))

;; (map first (node-seq i))
;;   => (0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24
;;       25 26 27 28 29)

;; (map first (node-seq-reverse i))
;;   => (29 28 27 26 25 24 23 22 21 20 19 18 17 16 15 14 13 12 11 10 9 8
;;       7 6 5 4 3 2 1 0)


