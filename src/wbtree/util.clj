(ns wbtree.util
  (:require [clojure.pprint :as pp])
  (:require [clojure.repl]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Control Flow
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
(defmacro returning
  "Compute a return value, then execute other forms for side effects.
  Like prog1 in common lisp, or a (do) that returns the first form."
  [value & forms]
  `(let [value# ~value]
     ~@forms
     value#))

(defmacro returning-bind 
  "Compute a return value, bind that value to provided sym, then
  execute other forms for side effects within the lexical scope of
  that binding.  The return value of a returning-bind block will be
  the value computed by retn-form.  Similar in concept to Paul
  Graham's APROG1, or what is commonly found in CL libraries as
  PROG1-BIND.  This macro is especially handy when one needs to
  interact with stateful resources such as io.

  Example:

    (returning-bind [x (inc 41)]
      (println :returning x)
      (println 3.141592654))

  PRINTS:   :returning 42
            3.141592654
  RETURNS:  42"
  [[sym retn-form] & body]
      `(let [val# ~retn-form
             ~sym val#]
         ~@body
         val#))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Collections
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn indexed
  "Returns a lazy sequence of [index, item] pairs, where items come
  from 's' and indexes count up from zero.
  (indexed '(a b c d))  =>  ([0 a] [1 b] [2 c] [3 d])"
  [s]
  (map vector (range) s))

(defn positions
  "Returns a lazy sequence containing the positions at which pred
   is true for items in coll."
  [pred coll]
  (for [[idx elt] (indexed coll) :when (pred elt)] idx))

(defn split-vec
  "Split the given vector at the provided offsets using subvec. Supports
  negative offsets."
  [v & ns]
  (let [ns (map #(if (neg? %) (+ % (count v)) %) ns)]
    (lazy-seq
     (if-let [n (first ns)]
       (cons (subvec v 0 n)
             (apply split-vec
                    (subvec v n)
                    (map #(- % n) (rest ns))))
       (list v)))))

(defn knit
  "Takes a list of functions (f1 f2 ... fn) and returns a new function F.
  F takes a collection of size n (x1 x2 ... xn) and returns a vector
      [(f1 x1) (f2 x2) ... (fn xn)]."
  [& fs]
  (fn [arg-coll] split-vec    (vec (map #(% %2) fs arg-coll))))

(defn rmerge
  "Recursive merge of the provided maps."
  [& maps]
  (if (every? map? maps)
    (apply merge-with rmerge maps)
    (last maps)))

(defn mappend
  "maps elements in list and finally appends all resulted lists."
  [f & seqs]
  (apply concat (apply map f seqs)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Namespace Introspection
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn ns-docs
  "Prints docs for all public symbols in given namespace
   http://blog.twonegatives.com/post/42435179639/ns-docs
   https://gist.github.com/timvisher/4728530"
  [ns-symbol]
  (dorun 
   (map (comp #'clojure.repl/print-doc meta)
        (->> ns-symbol 
             ns-publics 
             sort 
             vals))))

(defn symbolic-name-from-var
  [var]
  (clojure.string/join "/" ((juxt (comp str :ns) :name) (meta var))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Timing and Performance Metric
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defmacro with-timing [& body]
  `(let [start# (System/nanoTime)  ret# ~(cons 'do body)]
     [ret# (/ (double (- (System/nanoTime) start#)) 1000000.0)]))

(defmacro avg-timing [iter & body]
  `(let [iter# ~iter]
      (/ (reduce +
            (map second
              (repeatedly iter#
                 #(let [start# (System/nanoTime) ret# ~(cons 'do body)]
                    [ret# (/ (double (- (System/nanoTime) start#))
                            1000000.0)]))))
           iter#)))

(defmacro run-and-measure-timing [expr]
  `(let [start-time# (System/currentTimeMillis)
         response# ~expr
         end-time# (System/currentTimeMillis)]
     {:time-taken (- end-time# start-time#)
      :response response#
      :start-time start-time#
      :end-time end-time#}))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Debugging
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro wrap-fn [name args & body]
  `(let [old-fn# (var-get (var ~name))
         new-fn# (fn [& p#] 
                   (let [~args p#] 
                     (do ~@body)))
         wrapper# (fn [& params#]
                    (if (= ~(count args) (count params#))
                      (apply new-fn# params#)
                      (apply old-fn# params#)))] 
     (alter-var-root (var ~name) (constantly wrapper#))))


(defmacro ppmx [form]
  `(do
     (pp/cl-format *out*  ";;; Macroexpansion:~%~% ~S~%~%;;; First Step~%~%"
       '~form)
     (pp/pprint (macroexpand-1 '~form))
     (pp/cl-format *out*  "~%;;; Full expansion:~%~%")
     (pp/pprint (macroexpand '~form))
     (println "")))


;;;
;;; From: The Joy of Clojure
;;;

(defn contextual-eval [ctx expr]
  (eval
    `(let [~@(mapcat (fn [[k v]] [k `'~v]) ctx)]
       ~expr)))

(defmacro local-context []
  (let [symbols (keys &env)]
    (zipmap (map (fn [sym] `(quote ~sym)) symbols) symbols)))

(defn readr [prompt exit-code]
  (let [input (clojure.main/repl-read prompt exit-code)]
    (if (= input ::r)
      exit-code
      input)))

(defmacro break []
  `(clojure.main/repl
     :prompt #(print "debug=> ")
     :read   readr
     :eval   (partial contextual-eval (local-context))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; IO
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn lines-of-file [file-name]
  (line-seq
    (java.io.BufferedReader.
      (java.io.InputStreamReader.
        (java.io.FileInputStream. file-name)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Exceptions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defmacro exception [& [param & more :as params]] 
  (if (class? param) 
    `(throw (new ~param (str ~@(interpose " " more)))) 
    `(throw (Exception. (str ~@(interpose " " params))))))


(defmacro ignore-exceptions [& body]
  `(try
     ~@body
     (catch Exception e# nil)))





;; (defn to-byte-array [x]
;;   (let [baos (ByteArrayOutputStream.)
;;         oos (ObjectOutputStream. baos)]
;;     (pr oos x)
;;     (.close oos)
;;     (.toByteArray baos)))  
