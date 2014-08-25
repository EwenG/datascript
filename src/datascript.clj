(ns datascript)

(defmacro combine-cmp [& comps]
  (loop [comps (reverse comps)
         res   0]
    (if (not-empty comps)
      (recur
        (next comps)
        `(let [c# ~(first comps)]
           (if (== 0 c#)
             ~res
             c#)))
      res)))

(defn- -case-tree [queries variants]
  (if queries
    (let [v1 (take (/ (count variants) 2) variants)
          v2 (drop (/ (count variants) 2) variants)]
      (list 'if (first queries)
        (-case-tree (next queries) v1)
        (-case-tree (next queries) v2)))
    (first variants)))

(defmacro case-tree [qs vs]
  (-case-tree qs vs))

(defmacro defquery [name params query & sources]
  (let [cache-key? (= :cache params)
        params (if cache-key? (first sources) params)
        params (into '[_] params)                           ;Add the first argument to a Protocol method call
        query (if cache-key? (second sources) query)
        sources (if cache-key? (nthrest sources 2) sources)
        cache? (if cache-key? query false)]
    (if cache?
      `(let [cached-query# (cljs.core/atom #{})]
         (def ~name
           (reify cljs.core/IFn
             (~'-invoke ~'[_] (cljs.core/deref cached-query#))
             (~'-invoke ~params (cljs.core/reset! cached-query# (datascript/q ~query ~@sources)))
             datascript/IndexKeys
             (~'get-index-keys ~params (~'-> (datascript/analyze-q ~query ~@sources)
                                        datascript/analyze-calls->index-keys)))))
      `(def ~name
         (reify cljs.core/IFn
           (~'-invoke ~params (datascript/q ~query ~@sources))
           datascript/IndexKeys
           (~'get-index-keys ~params (~'-> (datascript/analyze-q ~query ~@sources)
                                      datascript/analyze-calls->index-keys)))))))


