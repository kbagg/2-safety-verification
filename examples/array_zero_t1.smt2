;; for (int i = 0; i < N; i++)
;;    a[i] = 0
;;
;; for (int i = 0; i < N; i++)
;;    assert (a[i] <= 0);

(declare-rel L1 (Int Int (Array Int Int)) )
(declare-rel L2 (Int Int (Array Int Int)) )

(declare-rel Error () )

(declare-var i Int)
(declare-var j Int)
(declare-var n Int)
(declare-var A (Array Int Int))
(declare-var B (Array Int Int))

(rule (L1 0 n A))

(rule (=> (and (L1 i n A) )
         (< i n)
         (L1 (+ i 1) n (store A i 0))))

(rule (=> (and (L1 i n A) (not (< i n)))
         (L2 0 n A)))

;; Need to find a lemma
;; forall j :: 0 <= j < n -> a[j] <= 0
(rule (=> (and (L2 0 n A) (<= 0 j) (< j n) (not (<= (select A j) 0))) Error))


(query Error)
