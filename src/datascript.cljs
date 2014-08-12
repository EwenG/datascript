(ns datascript
  (:require
    [clojure.set :as set]
    [clojure.walk :as walk]
    [cljs.reader :refer [read-string]]
    [datascript.btset :refer [btset-by slice]])
  (:require-macros [datascript :refer [combine-cmp case-tree]]))

(defrecord Datom [e a v tx added]
  Object
  (toString [this]
    (pr-str this)))

(extend-type Datom
  IHash
  (-hash [d] (or (.-__hash d)
                 (set! (.-__hash d) (hash-coll [(.-e d) (.-a d) (.-v d)]))))
  IEquiv
  (-equiv [d o] (and (= (.-e d) (.-e o)) (= (.-a d) (.-a o)) (= (.-v d) (.-v o))))
  ISeqable
  (-seq [d] (list (.-e d) (.-a d) (.-v d) (.-tx d) (.-added d))))

(defn- some? [x] (not (nil? x)))

(defn pattern->index-keys
  [[e a v tx added :as pattern]]
  (case-tree [e a (some? v) tx]
             [[:eavt e a v]   ;; e a v tx
              [:eavt e a v]   ;; e a v _
              [:eavt e a]     ;; e a _ tx
              [:eavt e a]     ;; e a _ _
              [:eavt e]       ;; e _ v tx
              [:eavt e]       ;; e _ v _
              [:eavt e]       ;; e _ _ tx
              [:eavt e]       ;; e _ _ _
              [:avet a v]     ;; _ a v tx
              [:avet a v]     ;; _ a v _
              [:avet a]       ;; _ a _ tx
              [:avet a]       ;; _ a _ _
              []              ;; _ _ v tx
              []              ;; _ _ v _
              []              ;; _ _ _ tx
              []]))           ;; _ _ _ _

;;;;;;;;;; Searching

(defprotocol ISearch
  (-search [data pattern]))

(defn- compare-key [k o1 o2]
  (let [k1 (get o1 k)
        k2 (get o2 k)]
    (if (and (some? k1) (some? k2))
      (let [t1 (type k1)
            t2 (type k2)]
        (if (= t1 t2)
          (compare k1 k2)
          (compare t1 t2)))
      0)))

(defn- cmp-val [o1 o2]
  (if (and (some? o1) (some? o2))
    (let [t1 (type o1)
          t2 (type o2)]
      (if (= t1 t2)
        (compare o1 o2)
        (compare t1 t2)))
    0))

(defn- cmp [o1 o2]
  (if (and o1 o2)
    (compare o1 o2)
    0))

(defn- cmp-datoms-eavt [d1 d2]
  (combine-cmp
    (cmp     (.-e d1) (.-e d2))
    (cmp     (.-a d1) (.-a d2))
    (cmp-val (.-v d1) (.-v d2))
    (cmp     (.-tx d1) (.-tx d2))))

(defn- cmp-datoms-aevt [d1 d2]
  (combine-cmp
    (cmp     (.-a d1) (.-a d2))
    (cmp     (.-e d1) (.-e d2))
    (cmp-val (.-v d1) (.-v d2))
    (cmp     (.-tx d1) (.-tx d2))))

(defn- cmp-datoms-avet [d1 d2]
  (combine-cmp
    (cmp     (.-a d1) (.-a d2))
    (cmp-val (.-v d1) (.-v d2))
    (cmp     (.-e d1) (.-e d2))
    (cmp     (.-tx d1) (.-tx d2))))

(defrecord DB [schema eavt aevt avet max-eid max-tx]
  Object
  (toString [this]
    (pr-str* this))
    
  ISearch
  (-search [_ [e a v tx]]
    (case-tree [e a (some? v) tx] [
      (slice eavt (Datom. e a v tx nil))                 ;; e a v tx
      (slice eavt (Datom. e a v nil nil))                ;; e a v _
      (->> (slice eavt (Datom. e a nil nil nil))         ;; e a _ tx
           (filter #(= tx (.-tx %))))
      (slice eavt (Datom. e a nil nil nil))              ;; e a _ _
      (->> (slice eavt (Datom. e nil nil nil nil))       ;; e _ v tx
           (filter #(and (= v (.-v %)) (= tx (.-tx %)))))
      (->> (slice eavt (Datom. e nil nil nil nil))       ;; e _ v _
           (filter #(= v (.-v %))))
      (->> (slice eavt (Datom. e nil nil nil nil))       ;; e _ _ tx
           (filter #(= tx (.-tx %))))
      (slice eavt (Datom. e nil nil nil nil))            ;; e _ _ _
      (->> (slice avet (Datom. nil a v nil nil))         ;; _ a v tx
           (filter #(= tx (.-tx %))))
      (slice avet (Datom. nil a v nil nil))              ;; _ a v _
      (->> (slice avet (Datom. nil a nil nil nil))       ;; _ a _ tx
           (filter #(= tx (.-tx %))))
      (slice avet (Datom. nil a nil nil nil))            ;; _ a _ _
      (filter #(and (= v (.-v %)) (= tx (.-tx %))) eavt) ;; _ _ v tx
      (filter #(= v (.-v %)) eavt)                       ;; _ _ v _
      (filter #(= tx (.-tx %)) eavt)                     ;; _ _ _ tx
      eavt])))                                           ;; _ _ _ _
  
(defrecord TxReport [db-before db-after tx-data tempids])

(defn multival? [db attr]
  (= (get-in db [:schema attr :db/cardinality]) :db.cardinality/many))

(defn ref? [db attr]
  (= (get-in db [:schema attr :db/valueType]) :db.type/ref))

(defn- match-tuple [tuple pattern]
  (every? true?
    (map #(or (nil? %2) (= %1 %2)) tuple pattern)))

(defn- search [data pattern]
  (cond
    (satisfies? ISearch data)
      (-search data pattern)
    (or (satisfies? ISeqable data)
        (array? data))
      (filter #(match-tuple % pattern) data)))


;;;;;;;;;; Transacting

(defn- current-tx [report]
  (inc (get-in report [:db-before :max-tx])))

(defn- next-eid [db]
  (inc (:max-eid db)))

(defn- advance-max-eid [db eid]
  (cond-> db
    (> eid (:max-eid db))
      (assoc :max-eid eid)))

(defn- allocate-eid
  ([report eid]
     (update-in report [:db-after] advance-max-eid eid))
  ([report e eid]
     (-> report
       (assoc-in [:tempids e] eid)
       (update-in [:db-after] advance-max-eid eid))))

(defn- with-datom [db datom]
  (if (.-added datom)
    (-> db
      (update-in [:eavt] conj datom)
      (update-in [:aevt] conj datom)
      (update-in [:avet] conj datom)
      (advance-max-eid (.-e datom)))
    (let [removing (first (-search db [(.-e datom) (.-a datom) (.-v datom)]))]
      (-> db
        (update-in [:eavt] disj removing)
        (update-in [:aevt] disj removing)
        (update-in [:avet] disj removing)))))

(defn- transact-report [report datom]
  (-> report
      (update-in [:db-after] with-datom datom)
      (update-in [:tx-data] conj datom)))

(defn- explode [db entity]
  (let [eid (:db/id entity)]
    (for [[a vs] (dissoc entity :db/id)
          v      (if (and (sequential? vs)
                          (multival? db a))
                   vs [vs])]
      [:db/add eid a v])))

(defn- transact-add [report [_ e a v]]
  (let [tx      (current-tx report)
        db      (:db-after report)
        datom   (Datom. e a v tx true)]
    (if (multival? db a)
      (if (empty? (-search db [e a v]))
        (transact-report report datom)
        report)
      (if-let [old-datom (first (-search db [e a]))]
        (if (= (.-v old-datom) v)
          report
          (-> report
            (transact-report (Datom. e a (.-v old-datom) tx false))
            (transact-report datom)))
        (transact-report report datom)))))

(defn- transact-retract-datom [report d]
  (let [tx (current-tx report)]
    (transact-report report (Datom. (.-e d) (.-a d) (.-v d) tx false))))

(defn- transact-entities [db-begin report [entity & entities :as es]]
  (let [db (:db-after report)]
    (cond
      (nil? entity)
        (-> report
            (update-in [:db-after :max-tx] inc))

      (map? entity)
        (if (:db/id entity)
          (recur db-begin report (concat (explode db entity) entities))
          (let [eid    (next-eid db)
                entity (assoc entity :db/id eid)]
            (recur db-begin (allocate-eid report eid)
                   (concat [entity] entities))))

      :else
        (let [[op e a v] entity]
          (cond
            (= op :db.fn/call)
              (let [[_ f & args] entity]
                (recur db-begin report (concat (apply f db-begin args) entities)))

            (neg? e)
              (if-let [eid (get-in report [:tempids e])]
                (recur db-begin report (concat [[op eid a v]] entities))
                (recur db-begin (allocate-eid report e (next-eid db)) es))

            (and (ref? db a) (neg? v))
              (if-let [vid (get-in report [:tempids v])]
                (recur db-begin report (concat [[op e a vid]] entities))
                (recur db-begin (allocate-eid report v (next-eid db)) es))

            (= op :db/add)
              (recur db-begin (transact-add report entity) entities)

            (= op :db/retract)
              (if-let [old-datom (first (-search db [e a v]))]
                (recur db-begin (transact-retract-datom report old-datom) entities)
                (recur db-begin report entities))

            (= op :db.fn/retractAttribute)
              (let [datoms (-search db [e a])]
                (recur db-begin (reduce transact-retract-datom report datoms) entities))

            (= op :db.fn/retractEntity)
              (let [datoms (-search db [e])]
                (recur db-begin (reduce transact-retract-datom report datoms) entities)))))))

;; QUERIES

(defn- parse-where [where]
  (let [source (first where)]
    (if (and (symbol? source)
             (= \$ (-> source name first)))
      [(first where) (next where)]
      ['$ where])))

(defn- bind-symbol [sym scope]
  (cond
    (= '_ sym)    nil
    (symbol? sym) (get scope sym nil)
    :else         sym))

(defn- bind-symbols [form scope]
  (map #(bind-symbol % scope) form))

(defn- search-datoms [source where scope]
  (search (bind-symbol source scope)
          (bind-symbols where scope)))

(defn- index-keys
  [source where scope]
  (let [keys (vec (cons source (filter (complement nil?) (pattern->index-keys (bind-symbols where scope)))))]
    (if (not-empty keys)
      (set [keys])
      #{})))

(defn- populate-scope [scope where datom]
  (->>
    (map #(when (and (symbol? %1)
                     (not (contains? scope %1)))
            [%1 %2])
      where
      datom)
    (remove nil?)
    (into scope)))

(defn- -differ? [& xs]
  (let [l (count xs)]
    (not= (take (/ l 2) xs) (drop (/ l 2) xs))))

(def ^:private built-ins { '= =, '== ==, 'not= not=, '!= not=, '< <, '> >, '<= <=, '>= >=, '+ +, '- -, '* *, '/ /, 'quot quot, 'rem rem, 'mod mod, 'inc inc, 'dec dec, 'max max, 'min min,
                           'zero? zero?, 'pos? pos?, 'neg? neg?, 'even? even?, 'odd? odd?, 'true? true?, 'false? false?, 'nil? nil?,
                           '-differ? -differ?})

(defn- call [[f & args] scope]
  (let [bound-args (bind-symbols args scope)
        f          (or (built-ins f) (scope f))]
    (apply f bound-args)))

(defn- analyze-call [[f & args] scope]
  (let [bound-args (bind-symbols args scope)
        f          (or (built-ins f) (scope f))]
    (into [f] bound-args)))

(defn- looks-like? [pattern form]
  (cond
    (= '_ pattern)
      true
    (= '[*] pattern)
      (sequential? form)
    (sequential? pattern)
      (and (sequential? form)
           (= (count form) (count pattern))
           (every? (fn [[pattern-el form-el]] (looks-like? pattern-el form-el))
                   (map vector pattern form)))
    (symbol? pattern)
      (= form pattern)
    :else ;; (predicate? pattern)
      (pattern form)))

(defn- collect [f coll]
  (persistent! (reduce #(reduce conj! %1 (f %2)) (transient #{}) coll)))

(defn- bind-rule-branch [branch call-args context]
  (let [[[rule & local-args] & body] branch
        replacements (zipmap local-args call-args)
        ;; replacing free vars to unique symbols
        seqid        (:__depth context 0)
        bound-body   (walk/postwalk #(if (and (symbol? %)
                                              (= \? (-> % name first)))
                                       (or (replacements %)
                                           (symbol (str (name %) "__auto__" seqid)))
                                       %)
                                     body)]
    ;; recursion breaker
    ;; adding condition that call args cannot take same values as they took in any previous call to this rule
    (concat
      (for [prev-call-args (get context rule)]
        [(concat ['-differ?] call-args prev-call-args)])
      bound-body)))

(defn- -q [in+sources wheres scope]
  (cond
    (not-empty in+sources) ;; parsing ins
      (let [[in source] (first in+sources)]
        (condp looks-like? in
          '[_ ...] ;; collection binding [?x ...]
            (collect #(-q (concat [[(first in) %]] (next in+sources)) wheres scope) source)

          '[[*]]   ;; relation binding [[?a ?b]]
            (collect #(-q (concat [[(first in) %]] (next in+sources)) wheres scope) source)

          '[*]     ;; tuple binding [?a ?b]
            (recur (concat
                     (zipmap in source)
                     (next in+sources))
                   wheres
                   scope)
          '%       ;; rules
            (let [rules (if (string? source) (read-string source) source)]
              (recur (next in+sources)
                     wheres
                     (assoc scope :__rules (group-by ffirst rules))))

          '_       ;; regular binding ?x
            (recur (next in+sources)
                   wheres
                   (assoc scope in source))))

    (not-empty wheres) ;; parsing wheres
      (let [where (first wheres)]

        ;; rule (rule ?a ?b ?c)
        (if-let [rule-branches (get (:__rules scope) (first where))]
          (let [[rule & call-args] where
                next-scope (-> scope
                             (update-in [:__rules_ctx rule] conj call-args)
                             (update-in [:__rules_ctx :__depth] inc))
                next-wheres (next wheres)]
            (collect
              #(-q nil
                   (concat (bind-rule-branch % call-args (:__rules_ctx scope)) next-wheres)
                   next-scope)
              rule-branches))

          (condp looks-like? where
            '[[*]] ;; predicate [(pred ?a ?b ?c)]
              (when (call (first where) scope)
                (recur nil (next wheres) scope))

            '[[*] _] ;; function [(fn ?a ?b) ?res]
              (let [res (call (first where) scope)]
                (recur [[(second where) res]] (next wheres) scope))

            '[*] ;; pattern
              (let [[source where] (parse-where where)
                    found          (search-datoms source where scope)]
                (collect #(-q nil (next wheres) (populate-scope scope where %)) found))
            )))

   :else ;; reached bottom
      #{(mapv scope (:__find scope))}
    ))

;; Computes a map from datasources satisfying ISearch to the set of
;; index key sequences for that source implied by the query
(defn- -q->index-keys [in+sources wheres scope]
  (cond
   (not-empty in+sources) ;; parsing ins
   (let [[in source] (first in+sources)]
     (condp looks-like? in
       '[_ ...] ;; collection binding [?x ...]
       (apply (partial merge-with set/union) (map #(-q->index-keys (concat [[(first in) %]] (next in+sources)) wheres scope) source))

       '[[*]]   ;; relation binding [[?a ?b]]
       (apply (partial merge-with set/union) (map #(-q->index-keys (concat [[(first in) %]] (next in+sources)) wheres scope) source))

       '[*]     ;; tuple binding [?a ?b]
       (recur (concat
               (zipmap in source)
               (next in+sources))
              wheres
              scope)
       '%       ;; rules
       (recur (next in+sources)
              wheres
              (assoc scope :__rules (group-by ffirst source)))

       '_                                                   ;; regular binding ?x
       (recur (next in+sources)
                       wheres
                       (assoc scope in source))))

   (not-empty wheres) ;; parsing wheres
   (let [where (first wheres)]

     ;; rule (rule ?a ?b ?c)
     (if-let [rule-branches (get (:__rules scope) (first where))]
       (let [[rule & call-args] where
             next-scope (-> scope
                            (update-in [:__rules_ctx rule] conj call-args)
                            (update-in [:__rules_ctx :__depth] inc))
             next-wheres (next wheres)]
         (apply (partial merge-with set/union)
                (map #(-q->index-keys nil
                                      (concat (bind-rule-branch % call-args (:__rules_ctx scope)) next-wheres)
                                      next-scope) rule-branches))
         )

       (condp looks-like? where
         '[[*]] ;; predicate [(pred ?a ?b ?c)]
         (if (= '-differ? (ffirst where))
           (when (call (first where) scope)
             (recur nil (next wheres) scope))
           (recur nil (next wheres) scope))

         '[[*] _] ;; function [(fn ?a ?b) ?res]
         (if (= '-differ? (ffirst where))
           (when (call (first where) scope)
             (recur nil (next wheres) scope))
           #_(-q->index-keys nil (next wheres) scope)
           (update-in (-q->index-keys nil (next wheres) scope)
                      [:calls]
                      conj (analyze-call (first where) scope)))

         '[*] ;; pattern
         (let [[source where] (parse-where where)
               found          (index-keys source where scope)]
           #_(set/union (-q->index-keys nil (next wheres) scope) found)
           (update-in (-q->index-keys nil (next wheres) scope)
                      [:index-keys]
                      set/union found))
         )))

   :else ;; reached bottom
   {:index-keys #{} :calls #{}}
   ))

;; AGGREGATES

(def ^:private built-in-aggregates {
  'distinct (comp vec distinct)
  'min    (fn
            ([coll] (reduce min coll))
            ([n coll]
              (vec
                (reduce (fn [acc x]
                          (cond
                            (< (count acc) n) (sort (conj acc x))
                            (< x (last acc))  (sort (conj (butlast acc) x))
                            :else             acc))
                        [] coll))))
  'max    (fn
            ([coll] (reduce max coll))
            ([n coll]
              (vec
                (reduce (fn [acc x]
                          (cond
                            (< (count acc) n) (sort (conj acc x))
                            (> x (first acc)) (sort (conj (next acc) x))
                            :else             acc))
                        [] coll))))
  'sum    #(reduce + 0 %)
  'rand   (fn
            ([coll] (rand-nth coll))
            ([n coll] (vec (repeatedly n #(rand-nth coll)))))
  'sample (fn [n coll]
            (vec (take n (shuffle coll))))
  'count  count})

(defn- aggr-group-key [find result]
  (mapv (fn [val sym]
          (if (sequential? sym) nil val))
        result
        find))

(defn- -aggregate [find scope results]
  (mapv (fn [sym val i]
          (if (sequential? sym)
            (let [[f & args] sym
                  vals (map #(get % i) results)
                  args (concat
                        (bind-symbols (butlast args) scope)
                        [vals])
                  f    (or (built-in-aggregates f) (scope f))]
              (apply f args))
            val))
        find
        (first results)
        (range)))

(defn- aggregate [query scope results]
  (let [find (concat (:find query) (:with query))]
    (->> results
         (group-by #(aggr-group-key find %))
         (mapv (fn [[_ results]] (-aggregate (:find query) scope results))))))

(defn- parse-query [query]
  (loop [parsed {}, key nil, qs query]
    (if-let [q (first qs)]
      (if (keyword? q)
        (recur parsed q (next qs))
        (recur (update-in parsed [key] (fnil conj []) q) key (next qs)))
      parsed)))

;; SUMMING UP

;; Returns the set of "index paths" used by the query.
;; Example query:
;; (d/analyze-q '[:find  ?e ?e2 ?n
;;                :where [?e :name "Ivan"]
;;                       [?e :age ?a]
;;                       [?e2 :age ?a]
;;                       [?e2 :name ?n]] db)
;;
;; analyze-q results: #{[db :av :name "Ivan"][db :av :age][db :av :name]}
(defn analyze-q [query & sources]
  (let [query        (cond-> query
                             (sequential? query) parse-query)
        ins->sources (zipmap (:in query '[$]) sources)
        find         (concat
                      (map #(if (sequential? %) (last %) %) (:find query))
                      (:with query))
        analyze-result (-q->index-keys ins->sources (:where query) {:__find find})
        process-index-keys (fn [index-keys] (set (map #(assoc % 0 (ins->sources (first %)))
                                            (filter #(> (count %) 1) index-keys))))]
    (update-in analyze-result [:index-keys] process-index-keys)))


(defn q [query & sources]
  (let [query        (if (sequential? query) (parse-query query) query)
        ins->sources (zipmap (:in query '[$]) sources)
        find         (concat
                       (map #(if (sequential? %) (last %) %) (:find query))
                       (:with query))
        results      (-q ins->sources (:where query) {:__find find})]
    (cond->> results
      (:with query)
        (mapv #(subvec % 0 (count (:find query))))
      (not-empty (filter sequential? (:find query)))
        (aggregate query ins->sources))))

(defn entity [db eid]
  (when-let [datoms (not-empty (-search db [eid]))]
    (reduce (fn [entity datom]
              (let [a (.-a datom)
                    v (.-v datom)]
                (if (multival? db (.-a datom))
                  (update-in entity [a] (fnil conj []) v)
                  (assoc entity a v))))
            { :db/id eid } datoms)))

(def ^:const tx0 0x20000000)

(defn empty-db [& [schema]]
  (DB. schema
       (btset-by cmp-datoms-eavt)
       (btset-by cmp-datoms-aevt)
       (btset-by cmp-datoms-avet)
       0
       tx0))

(defn create-conn [& [schema]]
  (atom (empty-db schema)
        :meta { :listeners  (atom {})}))

(defn- datom->index-keys
  [{:keys [e a v t added]}]
  #{[:eavt e]
    [:eavt e a]
    [:eavt e a v]
    [:avet a]
    [:avet a v]})

(defn transact [db entities]
  (transact-entities db (with-meta (TxReport. db db [] {}) (meta entities)) entities))

(defn with [db entities]
  (:db-after (transact db entities)))

(defn -transact! [conn entities]
  (let [report (atom nil)]
    (swap! conn (fn [db]
                  (let [r (transact db entities)]
                    (reset! report r)
                    (:db-after r))))
    @report))

#_(defn transact! [conn entities]
  (let [report (-transact! conn entities)]
    (doseq [[_ callback] @(:listeners (meta conn))]
      (callback report))
    (when (not-empty @(:q-listeners (meta conn)))
      (let [tx-index-keys (reduce set/union #{} (map datom->index-keys (:tx-data report)))]
        (doseq [[key {:keys [index-keys callback]}] @(:q-listeners (meta conn))]
          (when (not-empty (set/intersection index-keys tx-index-keys)) (callback report)))))
    report))

#_(defn transact! [conn entities]
  (let [report (-transact! conn entities)]
    (doseq [[_ callback] @(:listeners (meta conn))]
      (callback report))
    (when (not-empty (-> @(:q-listeners (meta conn)) :index-keys))
      (let [tx-index-keys (reduce set/union #{} (map datom->index-keys (:tx-data report)))
            all-callbacks (atom #{})]
        (doseq [single-index-keys tx-index-keys]
          (when-let [callbacks (-> @(:q-listeners (meta conn))
                                   :index-keys
                                   (get single-index-keys))]
            (swap! all-callbacks into callbacks)))
        (doseq [callback @all-callbacks]
          (callback report))))
    report))

(defprotocol IPublish
  (publish [this report]))

(extend-type function
  IPublish
  (publish [this report]
    (this report)))

(defn transact! [conn entities]
  (let [report (-transact! conn entities)]
    (let [listeners (:listeners (meta conn))]
      (when (not-empty (-> @listeners :callbacks->index-keys))
        (let [tx-index-keys (reduce set/union #{} (map datom->index-keys (:tx-data report)))
              all-index-keys-callbacks (-> @listeners
                                   :index-keys->callbacks
                                   :all-index-keys)
              all-callbacks (atom (into #{} all-index-keys-callbacks))]
          (doseq [single-index-keys tx-index-keys]
            (when-let [callbacks (-> @listeners
                                     :index-keys->callbacks
                                     (get single-index-keys))]
              (swap! all-callbacks into callbacks)))
          (doseq [callback @all-callbacks]
            (publish callback report)))))
    report))

(comment
  (let [conn    (create-conn)
        q '[:find ?e ?n :where [?e :name ?n]]
        q2 '[:find ?e ?n :where [?e :name2 ?n]]
        callback #(.log js/console (str "callback " (:tx-data %)))
        c (async/chan)]
    (go-loop [ch c]
             (when-let [val (async/<! ch)]
               (callback val)
               (recur ch))
             (async/close! ch))
    #_(listen! conn callback (-> (analyze-q q conn) :index-keys))
    #_(listen! conn callback (into (-> (analyze-q q2 conn) :index-keys)
                                 (-> (analyze-q q conn) :index-keys)))

    (listen! conn c (-> (analyze-q q conn) :index-keys))

    (transact! conn [[:db/add -1 :name "Alex"]
                     [:db/add -2 :name "Boris"]])

    #_@(:listeners (meta conn))

    )


  )


(defn revert! [conn tx-data]
  (transact! conn (with-meta (map (fn [{:keys [e a v t added]}] [(if added :db/retract :db/add) e a v]) tx-data) {:type :revert})))

#_(defn listen!
  ([conn callback] (listen! conn (rand) callback))
  ([conn key callback]
     (swap! (:listeners (meta conn)) assoc key callback)
   key)
  ([conn callback q sources]
   (listen! conn (rand) callback q sources))
  ([conn key callback q sources]
   (let [index-keys (set (map (comp vec rest) (filter #(= @conn (first %)) (apply analyze-q q sources))))]
     (swap! (:q-listeners (meta conn)) assoc key {:index-keys index-keys :callback callback})
     key)))

#_(defn listen!
  ([conn callback] (listen! conn (rand) callback))
  ([conn key callback]
   (swap! (:listeners (meta conn)) assoc key callback)
   key)
  ([conn key callback all-index-keys]
   (let [index-keys (set (map (comp vec rest) (filter #(= conn (first %)) all-index-keys)))]
     (swap! (:q-listeners (meta conn)) assoc key {:index-keys index-keys :callback callback})
     key)))


#_(defn listen!
  ([conn callback] (listen! conn (rand) callback))
  ([conn key callback]
   (swap! (:listeners (meta conn)) assoc key callback)
   key)
  ([conn key callback all-index-keys]
   (let [index-keys (set (map (comp vec rest) (filter #(= conn (first %)) all-index-keys)))
         add-callback (fn [q-listeners]
                        (let [q-listeners (atom q-listeners)]
                          (doseq [single-index-keys index-keys]
                            (swap! q-listeners update-in
                                   [:index-keys single-index-keys]
                                   (comp set conj) callback))
                          @q-listeners))
         add-callback-key (fn [q-listeners]
                            (assoc q-listeners key {:index-keys index-keys :callback callback}))]
     (swap! (:q-listeners (meta conn)) (comp add-callback-key add-callback))
     key)))

(defn clean-index-key->callback [listeners index-key]
  (if (empty? (-> listeners
                  :index-keys->callbacks
                  (get index-key)))
    (update-in listeners [:index-keys->callbacks] dissoc index-key)
    listeners))

(defn rem-index-key->callback [listeners index-key callback]
  (-> (update-in listeners [:index-keys->callbacks index-key]
                  disj callback)
      (clean-index-key->callback index-key)))

(defn add-index-key->callback [listeners index-key callback ]
  (update-in listeners [:index-keys->callbacks index-key]
             (comp set conj) callback))

(defn rem-index-keys->callback [listeners index-keys callback]
  (reduce #(rem-index-key->callback %1 %2 callback) listeners index-keys))

(defn add-index-keys->callback [listeners index-keys callback]
  (reduce #(add-index-key->callback %1 %2 callback) listeners index-keys))

(defn add-callback->index-keys [listeners index-keys callback]
  (assoc-in listeners [:callbacks->index-keys callback] index-keys))

(defn rem-callback->index-keys [listeners callback]
  (update-in listeners [:callbacks->index-keys] dissoc callback))

(defn listen!
  ([conn callback] (let [listeners (:listeners (meta conn))
                         index-keys (-> @listeners
                                        :callbacks->index-keys
                                        (get callback))
                         rem-index-keys->callback-fn (if (and index-keys (not= #{:all-index-keys} index-keys))
                                                       #(rem-index-keys->callback % index-keys callback)
                                                       identity)
                         add-index-keys->callback-fn #(add-index-keys->callback % #{:all-index-keys} callback)
                         add-callback->index-keys #(add-callback->index-keys % #{:all-index-keys} callback)]
                     (swap! listeners (comp add-callback->index-keys
                                            add-index-keys->callback-fn
                                            rem-index-keys->callback-fn))))
  ([conn callback index-keys]
   (let [listeners (:listeners (meta conn))
         index-keys (set (map (comp vec rest) (filter #(= conn (first %)) index-keys)))
         old-index-keys (-> @listeners
                        :callbacks->index-keys
                        (get callback))
         diff-index-keys (clojure.data/diff old-index-keys index-keys)
         rem-index-keys (first diff-index-keys)
         add-index-keys (second diff-index-keys)
         rem-index-keys->callback-fn #(rem-index-keys->callback % rem-index-keys callback)
         add-index-keys->callback-fn #(add-index-keys->callback % add-index-keys callback)
         add-callback->index-keys #(add-callback->index-keys % index-keys callback)]
     (swap! listeners (comp add-callback->index-keys
                            add-index-keys->callback-fn
                            rem-index-keys->callback-fn)))))


(defn disj-pred [s pred]
  (clojure.set/difference s (clojure.set/select pred s)))

#_(defn unlisten!
  ([conn key]
   (swap! (:listeners (meta conn)) dissoc key)
   (let [rem-callback (fn [q-listeners]
                        (let [index-keys (-> (get q-listeners key) :index-keys)
                              q-listeners (atom q-listeners)]
                          (doseq [single-index-keys index-keys]
                            (swap! q-listeners update-in
                                   [:index-keys single-index-keys]
                                   disj-pred #(= key (:key %)))
                            (when (empty? (-> (:index-keys @q-listeners)
                                              (get single-index-keys)))
                              (swap! q-listeners update-in
                                     [:index-keys]
                                     dissoc single-index-keys)))
                          @q-listeners))
         rem-callback-key (fn [q-listeners]
                            (dissoc q-listeners key))]
     (swap! (:q-listeners (meta conn)) (comp rem-callback-key rem-callback))))
  ([conn key all-index-keys]
   (let [rem-callback (fn [q-listeners]
                        (let [q-listeners (atom q-listeners)]
                          (doseq [single-index-keys all-index-keys]
                            (swap! q-listeners update-in
                                   [:index-keys single-index-keys]
                                   disj-pred #(= key (:key %)))
                            (when (empty? (-> (:index-keys @q-listeners)
                                              (get single-index-keys)))
                              (swap! q-listeners update-in
                                     [:index-keys]
                                     dissoc single-index-keys)))
                          @q-listeners))
         rem-callback-key (fn [q-listeners]
                            (let [q-listeners (atom q-listeners)]
                              (swap! q-listeners update-in [key :index-keys] clojure.set/difference all-index-keys)
                              (when (empty? (-> (get @q-listeners key) :index-keys))
                                (swap! q-listeners dissoc key))
                              @q-listeners))]
     (swap! (:q-listeners (meta conn)) (comp rem-callback-key rem-callback)))))

(defn unlisten! [conn callback]
  (let [listeners (:listeners (meta conn))
        old-index-keys (-> @listeners
                           :callbacks->index-keys
                           (get callback))
        rem-index-keys->callback-fn #(rem-index-keys->callback % old-index-keys callback)
        rem-callback->index-keys #(rem-callback->index-keys % callback)]
    (swap! listeners (comp rem-callback->index-keys
                           rem-index-keys->callback-fn))))



(defn- components->pattern [index cs]
  (case index
    :eavt (Datom. (nth cs 0 nil) (nth cs 1 nil) (nth cs 2 nil) (nth cs 3 nil) nil)
    :aevt (Datom. (nth cs 1 nil) (nth cs 0 nil) (nth cs 2 nil) (nth cs 3 nil) nil)
    :avet (Datom. (nth cs 2 nil) (nth cs 0 nil) (nth cs 1 nil) (nth cs 3 nil) nil)))

(defn datoms [db index & cs]
  (slice (get db index) (components->pattern index cs)))

(defn seek-datoms [db index & cs]
  (slice (get db index) (components->pattern index cs) (Datom. nil nil nil nil nil)))

;; printing and reading
;; #datomic/DB {:schema <map>, :datoms <vector of [e a v tx]>}

(extend-type Datom
  IPrintWithWriter
  (-pr-writer [d w opts]
    (pr-sequential-writer w pr-writer "#datascript/Datom [" " " "]" opts [(.-e d) (.-a d) (.-v d) (.-tx d) (.-added d)])))

(defn datom-from-reader [[e a v tx added]]
  (Datom. e a v tx added))

(extend-type DB
  IPrintWithWriter
  (-pr-writer [db w opts]
    (-write w "#datascript/DB {")
    (-write w ":schema ")
    (pr-writer (.-schema db) w opts)
    (-write w ", :datoms ")
    (pr-sequential-writer w
      (fn [d w opts]
        (pr-sequential-writer w pr-writer "[" " " "]" opts [(.-e d) (.-a d) (.-v d) (.-tx d)]))
      "[" " " "]" opts (.-eavt db))
    (-write w "}")))

(defn db-from-reader [{:keys [schema datoms]}]
  (let [datoms (map (fn [[e a v tx]] (Datom. e a v tx true)) datoms)]
    (DB. schema
         (apply btset-by cmp-datoms-eavt datoms)
         (apply btset-by cmp-datoms-aevt datoms)
         (apply btset-by cmp-datoms-avet datoms)
         (reduce max 0 (map :e datoms))
         (reduce max tx0 (map :tx datoms)))))



