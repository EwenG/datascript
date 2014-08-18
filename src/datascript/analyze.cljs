(ns datascript.analyze
  (:require
    [clojure.set :as set]
    [clojure.walk :as walk]
    [datascript.core :as dc]
    [datascript.query :as dq])
  (:require-macros [datascript :refer [case-tree]]))

(defn pattern->index-keys
  [[e a v tx added :as pattern]]
  (case-tree [e a (some? v) tx]
             [[:eavt e a v] ;; e a v tx
              [:eavt e a v] ;; e a v _
              [:eavt e a] ;; e a _ tx
              [:eavt e a] ;; e a _ _
              [:eavt e] ;; e _ v tx
              [:eavt e] ;; e _ v _
              [:eavt e] ;; e _ _ tx
              [:eavt e] ;; e _ _ _
              [:avet a v] ;; _ a v tx
              [:avet a v] ;; _ a v _
              [:avet a] ;; _ a _ tx
              [:avet a] ;; _ a _ _
              [] ;; _ _ v tx
              [] ;; _ _ v _
              [] ;; _ _ _ tx
              []])) ;; _ _ _ _


(defn- parse-where [where]
  (let [source (first where)]
    (if (and (symbol? source)
             (= \$ (-> source name first)))
      [(first where) (next where)]
      ['$ where])))



(defn- context-resolve-val [context sym]
  (when-let [rel (first (filter #(contains? (:attrs %) sym) (:rels context)))]
    (map #(aget % ((:attrs rel) sym)) (:tuples rel))))

(defn- bind-symbol [sym context]
  (cond
    (= '_ sym) [nil]
    (symbol? sym) (or (context-resolve-val context sym) [nil])
    :else [sym]))

(defn cart [colls]
  (if (empty? colls)
    '(())
    (for [x (first colls)
          more (cart (rest colls))]
      (cons x more))))

(defn- bind-symbols [form context]
   (let [bound-symbols (map #(bind-symbol % context) form)]
     (cart bound-symbols)))

(defn- analyze-call [[f & args] context]
  (let [bound-args (bind-symbols args context)
        f (or (get dq/built-ins f)
              (dq/context-resolve-val context f))]
    (set (map #(into [f] %) bound-args))))

(defn- index-keys
  [source where context]
  (let [index-keys (map pattern->index-keys (bind-symbols where context))
         keys (map #(vec (cons source (filter (complement nil?) %))) index-keys)
         keys (filter not-empty keys)]
    (set keys)))

(defn -resolve-clause [context clause]
  (condp dq/looks-like? clause
    '[[*]]                                                  ;; predicate [(pred ?a ?b ?c)]
    (dq/filter-by-pred context clause)

    '[[*] _]                                                ;; function [(fn ?a ?b) ?res]
    (update-in context [:calls] set/union (analyze-call (first clause) context))

    '[*] ;; pattern
    (let [[source where] (parse-where clause)
          found (index-keys source where context)]
      (update-in context [:index-keys] set/union found))))



(defn solve-rule [context clause]
  (let [final-attrs     (filter dq/free-var? clause)
        final-attrs-map (zipmap final-attrs (range))
        ;;         clause-cache    (atom {}) ;; TODO
        solve           (fn [prefix-context clauses]
                          (reduce -resolve-clause prefix-context clauses))
        empty-rels?     (fn [context]
                          (some #(empty? (:tuples %)) (:rels context)))]
    (loop [stack (list {:prefix-clauses []
                        :prefix-context (assoc context :rels [])
                        :clauses        [clause]
                        :used-args      {}
                        :pending-guards {}})
           rel   (dq/Relation. final-attrs-map [])
           index-keys #{}]
      (if-let [frame (first stack)]
        (let [[clauses [rule-clause & next-clauses]] (split-with #(not (dq/rule? context %)) (:clauses frame))]
          (if (nil? rule-clause)

            ;; no rules --> expand, collect, sum
            (let [context (solve (:prefix-context frame) clauses)
                  tuples  (dq/-collect context final-attrs)
                  new-rel (dq/Relation. final-attrs-map tuples)]
              (recur (next stack) (dq/sum-rel rel new-rel)
                     (set/union index-keys (-> context :index-keys))))

            ;; has rule --> add guards --> check if dead --> expand rule --> push to stack, recur
            (let [[rule & call-args]     rule-clause
                  guards                 (dq/rule-gen-guards rule-clause (:used-args frame))
                  [active-gs pending-gs] (dq/split-guards (concat (:prefix-clauses frame) clauses)
                                                       (concat guards (:pending-guards frame)))]
              (if (some #(= % '[(-differ?)]) active-gs) ;; trivial always false case like [(not= [?a ?b] [?a ?b])]

                                                        ;; this branch has no data, just drop it from stack
                (recur (next stack) rel index-keys)

                (let [prefix-clauses (concat clauses active-gs)
                      prefix-context (solve (:prefix-context frame) prefix-clauses)]
                  (if (empty-rels? prefix-context)

                    ;; this branch has no data, just drop it from stack
                    (recur (next stack) rel (set/union index-keys (-> prefix-context :index-keys)))

                    ;; need to expand rule to branches
                    (let [used-args  (assoc (:used-args frame) rule
                                                               (conj (get (:used-args frame) rule []) call-args))
                          branches   (dq/expand-rule rule-clause context used-args)]
                      (recur (concat
                               (for [branch branches]
                                 {:prefix-clauses prefix-clauses
                                  :prefix-context prefix-context
                                  :clauses        (dq/concatv branch next-clauses)
                                  :used-args      used-args
                                  :pending-guards pending-gs})
                               (next stack))
                             rel
                             (set/union index-keys (-> context :index-keys))))))))))
        [rel index-keys]))))

(defn resolve-clause [context clause]
  (if (dq/rule? context clause)
    (let [[source rule] (if (dq/source? (first clause))
                          [(first clause) (next clause)]
                          ['$ clause])
          source (get-in context [:sources source])
          [rel cc] (solve-rule (assoc context :sources {'$ source}) rule)
          context (update-in context [:index-keys] set/union cc)]
      (update-in context [:rels] dq/collapse-rels rel))
    (-resolve-clause context clause)))

(defn -q->index-keys [context clauses]
  (reduce resolve-clause context clauses))


(defn analyze-q [q & inputs]
  (let [q         (if (sequential? q) (dq/parse-query q) q)
        find      (dq/find-attrs q)
        ins       (:in q '[$])
        wheres    (:where q)
        context   (-> (dq/Context. [] {} {})
                      (dq/parse-ins ins inputs))
        result-context (-> context
                           (-q->index-keys wheres))
        process-index-keys (fn [index-keys] (set (map #(assoc % 0 (get (:sources result-context) (first %)))
                                                      (filter #(> (count %) 1) index-keys))))
        index-keys (-> (:index-keys result-context) identity process-index-keys)]
    {:index-keys index-keys :calls (or (:calls result-context) #{})}))

(comment

  (load-namespace 'datascript)

  (let [q '[:find ?e
            :in $ ?n
            :where [?e :name ?n]]]
    (analyze-q q (datascript/empty-db) "re"))

  (let [db [                  [5 :follow 3]
                              [1 :follow 2] [2 :follow 3] [3 :follow 4] [4 :follow 6]
                              [2         :follow           4]]]
    (analyze-q '[:find ?e1 ?e2
           :in $ %
           :where (follow ?e1 ?e2)]
         db
         '[[(follow ?x ?y)
            [?x :follow ?y]]]))

  (let [db (-> (datascript/empty-db)
               (datascript/with [ { :db/id 1, :name  "Ivan", :age   15 }
                         { :db/id 2, :name  "Petr", :age   37 }
                         { :db/id 3, :name  "Ivan", :age   37 }]))]

    (analyze-q '[:find ?attr ?value
                   :in $ ?e [?attr ...]
                   :where [?e ?attr ?value]]
                 "NA" 1 [:name :age]))

  (analyze-q '[:find  ?e1 ?e2 ?e3
                 :where [?e1 :age ?a1]
                 [?e2 :age ?a2]
                 [?e3 :age ?a3]
                 [(+ ?a1 ?a2) ?a12]
                 [(= ?a12 ?a3)]]
               "NA")

  (analyze-q '[:find  ?e2
                 :in    $ ?e1 %
                 :where (follow ?e1 ?e2)]
               "NA"
               1
               '[[(follow ?e2 ?e1)
                  [?e2 :follow ?e1]]
                 [(follow ?e2 ?e1)
                  [?e2 :follow ?t]
                  [?t  :follow ?e1]]])


  )

;TODO Check how datomic works => Database function call during transaction. --- Predicates in query (do the position in where clauses matter?)