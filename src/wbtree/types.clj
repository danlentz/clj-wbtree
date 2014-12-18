(ns wbtree.types
  (:use     [clj-tuple])
  (:require [wbtree.tree :as tree])
  (:require [wbtree.util :as util]))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Common Interface
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(definterface IOrderedCollection
  (getRoot          []))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Ordered Set Collection
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(deftype OrderedSet [root _meta]

  IOrderedCollection
  (getRoot [_]
    root)

  clojure.lang.IMeta
  (meta [_]
    _meta)

  clojure.lang.IObj
  (withMeta [_ m]
    (new OrderedSet root m))
  
  clojure.lang.Indexed
  (nth [_ i]
    (tree/-k
      (tree/node-nth root i)))

  clojure.lang.Seqable
  (seq [_]
    (map tree/-k (tree/node-seq root)))

  clojure.lang.Reversible
  (rseq [_]
    (map tree/-k (tree/node-seq-reverse root)))

  clojure.lang.ILookup
  (valAt [_ k not-found]
    (if-let [found (tree/node-find root k)]
      (tree/-k found)
      not-found))
  (valAt [this k]
    (.valAt this k nil))

  clojure.lang.IFn
  (invoke [this k not-found]
    (.valAt this k not-found))
  (invoke [this k]
    (.valAt this k nil))

  java.lang.Comparable
  (compareTo [this o]
    (if (identical? this o)
      0
      (if (instance? IOrderedCollection o)                      
        (tree/node-set-compare root (.getRoot o))
        (util/exception "unsupported comparison: " this o))))

  java.util.Collection
  (toArray [_]
    (object-array (tree/node-key-vec root)))
  (add [_ o]
    (util/exception UnsupportedOperationException))
  (addAll [_ o]
    (util/exception UnsupportedOperationException))
  (remove [_ o]
    (util/exception UnsupportedOperationException))
  (removeAll [_ o]
    (util/exception UnsupportedOperationException))
  (retainAll [_ o]
    (util/exception UnsupportedOperationException))

  java.util.Set
  (size [_]
    (tree/node-size root))
  (isEmpty [_]
    (tree/null? root))
  (iterator [this]
    (clojure.lang.SeqIterator. (seq this)))
  (containsAll [this s]
    (every? #(.contains this %) s))

  
  clojure.lang.IPersistentSet
  (equiv [this o]
    (if (identical? this o)
      0
      (if (instance? IOrderedCollection o)                      
        (zero? (tree/node-set-compare root (.getRoot o)))
        (if (set? o)
          (zero? (.equiv (set (tree/node-key-vec root)) o))
          (util/exception "unsupported comparison: " this o)))))
  (count [_]
    (tree/node-size root))
  (empty [_]
    (->OrderedSet (tree/null) {}))
  (contains [_ k]
    (if (tree/node-find root k)
      true
      false))
  (disjoin [this k]
    (->OrderedSet (tree/node-remove root k) _meta))
  (cons [this k]
    (->OrderedSet (tree/node-add root k) _meta))
  )


(defmethod print-method OrderedSet [s w]
  ((get (methods print-method) clojure.lang.IPersistentSet) s w))


(defn ordered-set
  ([]
     (ordered-set []))
  ([coll]
     (->OrderedSet (reduce tree/node-add (tree/null) coll) {})))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Ordered Map Collection
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (deftype OrderedMap [root]
;;   IOrderedCollection
;;   (getRoot [_]
;;     root))
