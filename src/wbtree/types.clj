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
    (new OrderedSet (tree/null) {}))
  (contains [_ k]
    (if (tree/node-find root k)
      true
      false))
  (disjoin [this k]
    (new OrderedSet (tree/node-remove root k) _meta))
  (cons [this k]
    (new OrderedSet (tree/node-add root k) _meta))
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

(defn pair [k v]
  (new clojure.lang.MapEntry k v))


(deftype OrderedMap [root _meta]

  IOrderedCollection
  (getRoot [_]
    root)

  clojure.lang.IMeta
  (meta [_]
    _meta)

  clojure.lang.IObj
  (withMeta [_ m]
    (new OrderedMap root m))
  
  clojure.lang.Indexed
  (nth [_ i]
    (tree/-kv
      (tree/node-nth root i)))
  
  clojure.lang.MapEquivalence

  clojure.lang.Counted
  (count [this]
    (tree/node-size root))
  
  clojure.lang.Seqable
  (seq [_]
    (map tree/-kv (tree/node-seq root)))

  clojure.lang.Reversible
  (rseq [_]
    (map tree/-kv (tree/node-seq-reverse root)))

  clojure.lang.ILookup
  (valAt [_ k not-found]
    (if-let [found (tree/node-find root k)]
      (tree/-v found)
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

  clojure.lang.Associative
  (containsKey [_ k]
    (not (nil? (tree/node-find root k))))
  (entryAt [_ k]
    (when-let [x (tree/node-find root k)]
      (tree/-kv x)))
  (assoc [_ k v]
    (new OrderedMap (tree/node-add root k v) _meta))
  (empty [this]
    (new OrderedMap (tree/null) {}))

  java.util.Map
  (get [this k]
    (.valAt this k))
  (isEmpty [_]
    (tree/null? root))
  (size [_]
    (tree/node-size root))
  (keySet [_]
    (set (tree/node-key-vec root)))
  (put [_ _ _]
    (throw (UnsupportedOperationException.)))
  (putAll [_ _]
    (throw (UnsupportedOperationException.)))
  (clear [_]
    (throw (UnsupportedOperationException.)))
  (values [_]
    (map tree/-v (tree/node-seq root)))
  (entrySet [this]
    (set (seq this)))
  (iterator [this]
    (clojure.lang.SeqIterator. (seq this)))

  clojure.lang.IPersistentCollection
  (equiv [this x]
    (and (map? x) (= x (into {} this))))

  (cons [this o]
    (if (map? o)
      (reduce #(apply assoc %1 %2) this o)
      (.assoc this (nth o 0) (nth o 1))))
  
  clojure.lang.IPersistentMap
  (assocEx [this k v]
    (if (contains? this k)
      (throw (Exception. "Key or value already present"))
      (assoc this k v)))
  (without [_ k]
    (new OrderedMap (tree/node-remove root k) _meta)))




(defmethod print-method OrderedMap [m w]
  ((get (methods print-method) clojure.lang.IPersistentMap) m w))


(defn ordered-map
  ([]
     (ordered-map []))
  ([coll]
     (->OrderedMap (reduce (fn [acc [k v]]
                             (tree/node-add acc k v))
                     (tree/null) (seq coll))
       {})))




;; (ordered-map)
;;  => {}

;; (seq (ordered-map [[:b "b"] [:c "c"] [:a "a"] [:d "d"]]))
;;  => ([:a "a"] [:b "b"] [:c "c"] [:d "d"])

;; (ordered-map {:a "a", :b "b", :c "c", :d "d"})
;;  => {:a "a", :b "b", :c "c", :d "d"}

;; (-> (ordered-map) (assoc :b "b") (assoc :a "a") (assoc :c "c"))
;;  => {:a "a", :b "b", :c "c"}

;; ((ordered-map {:a "a", :b "b", :c "c", :d "d"}) :c)
;;  => "c"

;; ((ordered-map {:a "a", :b "b", :c "c", :d "d"}) :z ::not-found)
;;  => :wbtree.types/not-found
