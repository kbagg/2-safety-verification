;; I'm following the example1.smt2 sent by sir as that matches closely to secure information flow verification using self-composition (the assertion is at the end and the assumption at the beginning). The self-composed program starts from the next line.
;; assume(h' != h);
;; z = 1;
;; if (h) {x = 1;}
;; else {x = z;}
;; l = x + y;
;; z' = 1;
;; if (h') {x' = 1;}
;; else {x' = z';}
;; l' = x' + y';
;; assert(l' == l);

(set-logic HORN)

;; Inv(z, h, x, l, y, z', h', x', l', y')

(declare-fun Inv (Int Int Int Int Int Int Int Int Int Int) Bool)
(assert
  (forall ((A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int))
          (=> (and (= A 1) (= F 1) (not (= B G)) (= E J))
             (Inv A B C D E F G H I J)))
  )

(assert
  (forall ((A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (C1 Int) (D1 Int) (H1 Int) (I1 Int))
          (=>
            (and (Inv A B C D E F G H I J) (= C1 (ite (= B 0) 1 A)) (= H1 (ite (= G 0) 1 F)) (= D1 (+ C1 E)) (= I1 (+ H1 J)) (not (= D1 I1)))
            false
            )
          )
  )

(check-sat)
(get-model)