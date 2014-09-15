(ns datascript
  (:require
    [datascript.core :as dc]
    [datascript.query :as dq]
    (datascript.analyze :as da)
    [datascript.btset :as btset]
    [clojure.data]
    [clojure.set :as set])
  (:require-macros [datascript :refer [case-tree]]))

;; SUMMING UP

(def q dq/q)

(def analyze-q da/analyze-q)

(defn entity [db eid]
  (when-let [datoms (not-empty (dc/-search db [eid]))]
    (reduce (fn [entity datom]
              (let [a (.-a datom)
                    v (.-v datom)]
                (if (dc/multival? db (.-a datom))
                  (update-in entity [a] (fnil conj []) v)
                  (assoc entity a v))))
            { :db/id eid } datoms)))

(def ^:const tx0 0x20000000)

(defn empty-db [& [schema]]
  (dc/DB. schema
       (btset/btset-by dc/cmp-datoms-eavt) 
       (btset/btset-by dc/cmp-datoms-aevt)
       (btset/btset-by dc/cmp-datoms-avet)
       0
       tx0))

(defn create-conn [& [schema]]
  (atom (empty-db schema)
        :meta { :listeners  (atom {}) }))

(defn transact [db entities]
  (dc/transact-entities (dc/TxReport. db db [] {}) entities))

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
    report))

(defprotocol IPublish
  (publish [this report]))
(extend-type function
  IPublish
  (publish [this report]
    (this report)))



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

(defn- datom->index-keys
  [{:keys [e a v t added]}]
  #{[:eavt e]
    [:eavt e a]
    [:eavt e a v]
    [:avet a]
    [:avet a v]})

(defprotocol IndexKeys
  (get-index-keys
    [this]
    [this a]
    [this a b]
    [this a b c]
    [this a b c d]
    [this a b c d e]
    [this a b c d e f]
    [this a b c d e f g]
    [this a b c d e f g h]
    [this a b c d e f g h i]
    [this a b c d e f g h i j]
    [this a b c d e f g h i j k]
    [this a b c d e f g h i j k l]
    [this a b c d e f g h i j k l m]
    [this a b c d e f g h i j k l m n]
    [this a b c d e f g h i j k l m n o]
    [this a b c d e f g h i j k l m n o p]
    [this a b c d e f g h i j k l m n o p q]
    [this a b c d e f g h i j k l m n o p q s]
    [this a b c d e f g h i j k l m n o p q s t]
    [this a b c d e f g h i j k l m n o p q s t rest]))

(defn wrap-query [query wrap-fn]
  (reify
    cljs.core/IFn
    (-invoke [this data]
      (-> (query data)
          wrap-fn))
    IndexKeys
    (get-index-keys [this conn]
      (get-index-keys query conn))))

(defn analyze-calls->index-keys [{:keys [index-keys calls]}]
  (let [calls-index-keys (for [[fct & params] calls]
                           (when (implements? IndexKeys fct)
                             (apply get-index-keys fct params)))]
    (apply set/union (conj calls-index-keys index-keys))))

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
           
#_(defn listen!
  ([conn callback] (listen! conn (rand) callback))
  ([conn key callback]
     (swap! (:listeners (meta conn)) assoc key callback)
     key))

#_(defn unlisten! [conn key]
  (swap! (:listeners (meta conn)) dissoc key))

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
  ([conn callback]
   (let [listeners (:listeners (meta conn))
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

(defn unlisten! [conn callback]
  (let [listeners (:listeners (meta conn))
        old-index-keys (-> @listeners
                           :callbacks->index-keys
                           (get callback))
        rem-index-keys->callback-fn #(rem-index-keys->callback % old-index-keys callback)
        rem-callback->index-keys #(rem-callback->index-keys % callback)]
    (swap! listeners (comp rem-callback->index-keys
                           rem-index-keys->callback-fn))))

(defn- components->pattern [index [c0 c1 c2 c3]]
  (case index
    :eavt (dc/Datom. c0 c1 c2 c3 nil)
    :aevt (dc/Datom. c1 c0 c2 c3 nil)
    :avet (dc/Datom. c2 c0 c1 c3 nil)))

(defn datoms [db index & cs]
  (btset/slice (get db index) (components->pattern index cs)))

(defn seek-datoms [db index & cs]
  (btset/slice (get db index) (components->pattern index cs) (dc/Datom. nil nil nil nil nil)))

;; printing and reading
;; #datomic/DB {:schema <map>, :datoms <vector of [e a v tx]>}

(extend-type dc/Datom
  IPrintWithWriter
  (-pr-writer [d w opts]
    (pr-sequential-writer w pr-writer "#datascript/Datom [" " " "]" opts [(.-e d) (.-a d) (.-v d) (.-tx d) (.-added d)])))

(defn datom-from-reader [[e a v tx added]]
  (dc/Datom. e a v tx added))

(extend-type dc/DB
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
  (let [datoms (map (fn [[e a v tx]] (dc/Datom. e a v tx true)) datoms)]
    (dc/DB. schema
         (apply btset/btset-by dc/cmp-datoms-eavt datoms)
         (apply btset/btset-by dc/cmp-datoms-aevt datoms)
         (apply btset/btset-by dc/cmp-datoms-avet datoms)
         (reduce max 0 (map :e datoms))
         (reduce max tx0 (map :tx datoms)))))
