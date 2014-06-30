(ns datascript
  (:require
    [clojure.set :as set]
    [clojure.walk :as walk]
    [cljs.reader :refer [read-string]]
    [loom.graph :as g]
    [loom.attr :as attr]
    [loom.alg :as alg]))

(defn cartesian-product
  "All the ways to take one item from each sequence"
  [& seqs]
  (let [v-original-seqs (vec seqs)
        step
        (fn step [v-seqs]
          (let [increment
                (fn [v-seqs]
                  (loop [i (dec (count v-seqs)), v-seqs v-seqs]
                    (if (= i -1) nil
                                 (if-let [rst (next (v-seqs i))]
                                   (assoc v-seqs i rst)
                                   (recur (dec i) (assoc v-seqs i (v-original-seqs i)))))))]
            (when v-seqs
              (cons (mapv first v-seqs)
                    (lazy-seq (step (increment v-seqs)))))))]
    (when (every? seq seqs)
      (lazy-seq (step v-original-seqs)))))

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

(defprotocol ISearch
  (-search [data pattern]))

(defrecord DB [schema ea av max-eid max-tx]
  ISearch
  (-search [db [e a v tx added :as pattern]]
    (cond->>
      (case [(when e :+) (when a :+) (when v :+)]
        [:+  nil nil]
          (->> (get-in db [:ea e]) vals (apply concat))
        [nil :+  nil]
          (->> (get-in db [:av a]) vals (apply concat))
        [:+  :+  nil]
          (get-in db [:ea e a])
        [nil :+  :+]
          (get-in db [:av a v])
        [:+  :+  :+]
          (->> (get-in db [:ea e a])
               (filter #(= v (.-v %)))))
     tx    (filter #(= tx (.-tx %)))
     added (filter #(= added (.-added %))))))

(defrecord TxReport [db-before db-after tx-data tempids])

(defn multival? [db attr]
  (= (get-in db [:schema attr :db/cardinality]) :db.cardinality/many))

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

(defn- transact-datom [db datom]
  (if (.-added datom)
    (-> db
      (update-in [:ea (.-e datom) (.-a datom)] (fnil conj #{}) datom)
      (update-in [:av (.-a datom) (.-v datom)] (fnil conj #{}) datom))
    (-> db
      (update-in [:ea (.-e datom) (.-a datom)] disj datom)
      (update-in [:av (.-a datom) (.-v datom)] disj datom))))

(defn- -resolve-eid [eid db]
  (- (.-max-eid db) eid))

(defn- resolve-eid [db d]
  (if (neg? (.-e d))
    (update-in d [:e] -resolve-eid db)
    d))

(defn- entity->ops [db entity]
  (cond
    (map? entity)
      (let [eid (:db/id entity)]
        (for [[a vs] (dissoc entity :db/id)
              v      (if (and (sequential? vs)
                              (multival? db a))
                       vs
                       [vs])]
          [:db/add eid a v]))
    (= (first entity) :db.fn/call)
      (let [[_ f & args] entity]
        (mapcat #(entity->ops db %) (apply f db args)))
    :else
      [entity]))

(defn- op->tx-data [db [op e a v]]
  (let [tx (inc (.-max-tx db))]
    (case op
      :db/add
        (if (= :db.cardinality/many (get-in db [:schema a :db/cardinality]))
          (when (empty? (-search db [e a v]))
            [(->Datom e a v tx true)])
          (if-let [old-datom (first (-search db [e a]))]
            (when (not= (.-v old-datom) v)
              [(->Datom e a (.-v old-datom) tx false)
               (->Datom e a v tx true)])
            [(->Datom e a v tx true)]))
      :db/retract
        (when-let [old-datom (first (-search db [e a v]))]
          [(->Datom e a v tx false)])
      :db.fn/retractAttribute
        (let [datoms (-search db [e a])]
          (map #(assoc % :tx tx :added false) datoms))
      :db.fn/retractEntity
        (let [datoms (-search db [e])]
          (map #(assoc % :tx tx :added false) datoms))
      )))

(defn- entity->tx-data [db entity]
  (->> (entity->ops db entity)
       (mapcat #(op->tx-data db %))))

(defn- -with [db tx-data]
  (->
    (reduce transact-datom db tx-data)
    (update-in [:max-tx] inc)
    (assoc      :max-eid (reduce max (.-max-eid db) (map :e tx-data)))))


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
    :else sym))

(defn- bind-symbol2 [sym scope]
  (cond
    (= '_ sym) [nil]
    (symbol? sym) (get scope sym [nil])
    :else [sym]))

(defn- bind-symbols [form scope]
  (map #(bind-symbol % scope) form))

(defn- bind-symbols2 [form scope]
  (map #(bind-symbol2 % scope) form))

(defn- search-datoms [source where scope]
  (search (bind-symbol source scope)
          (bind-symbols where scope)))

(defn- search-datoms2 [source where scope]
  (mapcat #(search (bind-symbol source scope) %)
          (apply cartesian-product (bind-symbols2 where scope))))

(defn- populate-scope [scope where datom]
  (->>
    (map #(when (and (symbol? %1)
                     (not (contains? scope %1)))
            [%1 %2])
      where
      datom)
    (remove nil?)
    (into scope)))

(defn- populate-scope2 [scope where datom]
  (->>
    (map #(when (and (symbol? %1)
                     (not (contains? scope %1)))
           [%1 [%2]])
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

(defn- call2 [[f & args] scope]
  (let [bound-args (bind-symbols2 args scope)
        f          (or (built-ins f) (scope f))]
    (mapv #(apply f %) (apply cartesian-product bound-args))))

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
  (reduce #(set/union %1 (f %2)) #{} coll))

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




(defn bind-in+source-helper [in+sources]
  (let [[in source] (first in+sources)]
    #_(prn (str in " ++++ " source " ---- "))
    (condp looks-like? in
      '[[*]] (recur [[(first in) (mapv first source)]])
      '[*] (map #(zipmap in %) source) #_(zipmap in source))))

(defn bind-in+source [in+sources]
  (let [[in source] in+sources]
    #_(prn (str in " ++++ " source " ---- "))
    (condp looks-like? in
      '[_ ...] (bind-in+source-helper [[[(first in)] (mapv (fn [x] [x]) source)]])
      '[[*]] (bind-in+source-helper [[[(first in)] (mapv (fn [x] [x]) source)]])
      '[*] (bind-in+source-helper [[in (mapv (fn [x] [x]) source)]])
      '% (let [rules (if (string? source) (read-string source) source)]
           [{:__rules (group-by ffirst rules)}])
      '_ [{in source}])))

(defn handle-sources [in+sources scope]
  )



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
                    found          (search-datoms source where scope)
                    #__ #_(.log js/console (str "!!!!!!!!!!!  " found))]
                (collect #(-q nil (next wheres) (populate-scope scope where %)) found))
            )))
   
   :else ;; reached bottom
   #{(mapv scope (:__find scope))}
   ))





(defn remove-nodes+attrs [graph & nodes]
  (let [graph (if (:attrs graph)
                (loop [graph graph
                       [node & rest] nodes]
                  (if (nil? node)
                    graph
                    (recur (attr/remove-attr graph node :attrs)
                           rest)))
                graph)]
    (g/remove-nodes* graph nodes)))

(defn add-attrs-for-nodes [g nodes attrs]
  (loop [graph g
         nodes nodes
         attrs attrs]
    (if-let [node (first nodes)]
      (let [attr (first attrs)
            graph (attr/add-attr graph node :attrs attr)]
        (recur graph (rest nodes) (rest attrs)))
      graph)))

(defn wheres->branch [wheres]
  (let [graph (g/digraph)
        nodes (map (fn [] (gensym ::node)) wheres)
        graph (g/add-nodes* graph nodes)
        edges (map (fn [x y] [x y]) nodes (rest nodes))
        graph (g/add-edges* graph edges)]
    (add-attrs-for-nodes graph nodes (map (fn [s] {:where s}) wheres))))

(defn rule->where-graph [where-rule rules previous-calls]
  (let [rule-branches (get rules (first where-rule))]
    (let [[rule & call-args] where-rule
          new-previous-calls (-> previous-calls
                                 (update-in [:__rules_ctx rule] conj call-args)
                                 (update-in [:__rules_ctx :__depth] inc))]
      (->> rule-branches (map #(bind-rule-branch % call-args (:__rules_ctx previous-calls)))
           (map wheres->branch)
           (concat [new-previous-calls])))))

(defn node->branches [graph node branches]
  (let [predecessors (g/predecessors graph node)
        successors (g/successors graph node)
        branch-edges (mapcat g/edges branches)
        branch-nodes (mapcat g/nodes branches)
        first-nodes (map (comp first g/nodes) branches)
        last-nodes (map (comp last g/nodes) branches)]
    (let [graph (remove-nodes+attrs graph node)
          graph (g/add-edges* graph branch-edges)
          graph (g/add-nodes* graph branch-nodes)
          p-edges (for [p predecessors
                        b first-nodes]
                    [p b])
          s-edges (for [s successors
                        b last-nodes]
                    [b s])
          graph (g/add-edges* graph (concat p-edges s-edges))
          attrs (apply merge (concat (:attrs graph) (map :attrs branches)))
          graph (assoc graph :attrs attrs)]
      graph)))



(defn rule-nodes->branches [graph nodes rules previous-calls]
  (for [node nodes
        :let [rule (:where (attr/attr graph node :attrs))
              [new-previous-calls & branches] (rule->where-graph rule rules previous-calls)]]
    [node branches new-previous-calls]))


(defn expand-rules [graph rules]
  (loop [graph graph
         [node & rest] (map (fn [n] [n {}])
                            (g/nodes graph))]
    (if (nil? node)
      graph
      (let [[node prev-calls] node]
        (if-let [where (:where (attr/attr graph node :attrs))]
          (if-let [rule-branches (get rules (first where))]
            (let [[new-prev-calls & branches] (rule->where-graph where rules prev-calls)
                  new-graph (node->branches graph node branches)
                  new-nodes (mapcat g/nodes branches)
                  new-nodes (map (fn [n] [n new-prev-calls]) new-nodes)]
              (recur new-graph (concat new-nodes rest)))
            (recur graph rest))
          (recur graph rest))))))

(defn build-request-graph [in+sources wheres find]
  (let [graph (g/digraph)
        find-node (gensym ::node)
        sources (map first in+sources)
        source-nodes (map (fn [] (gensym ::node)) sources)
        graph (g/add-edges* graph [[find-node (first source-nodes)]])
        s-edges (map (fn [x y] [x y]) source-nodes (rest source-nodes))
        graph (g/add-edges* graph s-edges)
        where-nodes (map (fn [] (gensym ::node)) wheres)
        graph (g/add-edges* graph [[(last source-nodes) (first where-nodes)]])
        w-edges (map (fn [x y] [x y]) where-nodes (rest where-nodes))
        graph (g/add-edges* graph w-edges)
        graph (attr/add-attr graph find-node :attrs {:find find})
        graph (add-attrs-for-nodes graph source-nodes (map (fn [s] {:source s}) sources))
        graph (add-attrs-for-nodes graph where-nodes (map (fn [s] {:where s}) wheres))]
    graph))

(defn execute-query [graph in+sources wheres]
  (loop [graph graph
         [node & rest] (alg/bf-traverse graph)]
    (if (nil? node)
      graph
      (let [attrs (attr/attr graph node :attrs)
            new-attrs
            (cond
              (:find attrs) (assoc attrs :envs (list {:find (:find attrs)}))
              (:source attrs) (let [sources (bind-in+source
                                              [(:source attrs) (get in+sources (:source attrs))])
                                    pred-envs (mapcat #(:envs (attr/attr graph % :attrs))
                                                      (g/predecessors graph node))
                                    envs (for [pred-env pred-envs
                                               source sources]
                                           (merge pred-env source))]
                                (assoc attrs :envs envs))
              (:where attrs) nil)]
        (recur (attr/add-attr graph node :attrs new-attrs) rest)))))


#_(condp looks-like? where
  '[[*]] ;; predicate [(pred ?a ?b ?c)]
  (when (call (first where) scope)
    (recur nil (next wheres) scope))

  '[[*] _] ;; function [(fn ?a ?b) ?res]
  (let [res (call (first where) scope)]
    (recur [[(second where) res]] (next wheres) scope))

  '[*] ;; pattern
  (let [[source where] (parse-where where)
        found          (search-datoms source where scope)
        #__ #_(.log js/console (str "!!!!!!!!!!!  " found))]
    (collect #(-q nil (next wheres) (populate-scope scope where %)) found))
  )


(defn- -q2 [in+sources wheres scope]
  (cond
    (not-empty in+sources) ;; parsing ins
    (let [[in source] (first in+sources)]
      (condp looks-like? in
        '[_ ...] ;; collection binding [?x ...]
        (recur (next in+sources) wheres (into scope [[(first in) source]]))

        '[[*]]   ;; relation binding [[?a ?b]]
        (recur (next in+sources) wheres (into scope [[(first in) source]]))

        '[*]     ;; tuple binding [?a ?b]
        #_(recur (concat
                 (zipmap in source)
                 (next in+sources))
               wheres
               scope)
        (recur (next in+sources)
               wheres
               (into scope (mapv (fn [i s] [i [s]]) in source)))
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
          (when (call2 (first where) scope)
            (recur nil (next wheres) scope))

          '[[*] _] ;; function [(fn ?a ?b) ?res]
          (let [res (call2 (first where) scope)]
            (recur nil (next wheres) (into scope [[(second where) res]])))

          '[*] ;; pattern
          (let [[source where] (parse-where where)
                found          (search-datoms2 source where scope)
                #__ #_(.log js/console (str "!!!!!!!!!!!  " found))]
            (collect #(-q2 nil (next wheres) (populate-scope2 scope where %)) found))
          )))

    :else ;; reached bottom
    #_#{(mapv scope (:__find scope))}
    (->> (mapv scope (:__find scope))
         (apply cartesian-product)
         set)))



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

(defn q2 [query & sources]
  (let [query        (if (sequential? query) (parse-query query) query)
        ins->sources (zipmap (:in query '[$]) sources)
        find         (concat
                       (map #(if (sequential? %) (last %) %) (:find query))
                       (:with query))
        query-graph      (build-request-graph ins->sources (:where query) find)
        run-graph (execute-query query-graph ins->sources (:where query))]
    #_(cond->> results
             (:with query)
             (mapv #(subvec % 0 (count (:find query))))
             (not-empty (filter sequential? (:find query)))
             (aggregate query ins->sources))
    run-graph))

(defn entity [db eid]
  (when-let [attrs (not-empty (get-in db [:ea eid]))]
    (merge { :db/id eid }
           (for [[attr datoms] attrs
                 :when (not-empty datoms)]
             (if (multival? db attr)
               [attr (mapv :v datoms)]
               [attr (.-v (first datoms))])))))


(def ^:const tx0 0x20000000)

(defn empty-db [& [schema]]
  (DB. schema {} {} 0 tx0))

(defn create-conn [& [schema]]
  (atom (empty-db schema)
        :meta { :listeners  (atom {}) }))

(defn transact [db entities]
  (let [raw-datoms (mapcat #(entity->tx-data db %) entities)
        datoms     (map #(resolve-eid db %) raw-datoms)
        tempids    (->> raw-datoms
                     (filter #(neg? (.-e %)))
                     (map #(vector (.-e %) (-resolve-eid (.-e %) db)))
                     (into {}))]
    (TxReport. db (-with db datoms) datoms tempids)))

(defn with [db entities]
  (:db-after (transact db entities)))

(defn -transact! [conn entities]
  (let [report (atom nil)]
    (swap! conn (fn [db]
                  (let [r (transact db entities)]
                    (reset! report r)
                    (:db-after r))))
    @report))

(defn transact! [conn entities]
  (let [report (-transact! conn entities)]
    (doseq [[_ callback] @(:listeners (meta conn))]
      (callback report))
    report))
           
(defn listen!
  ([conn callback] (listen! conn (rand) callback))
  ([conn key callback]
     (swap! (:listeners (meta conn)) assoc key callback)
     key))

(defn unlisten! [conn key]
  (swap! (:listeners (meta conn)) dissoc key))