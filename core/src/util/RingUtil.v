Require Import Vector.

Section UTIL.

Open Scope Matrix_scope.

Variable n: nat.

Add Ring MRing: (mat_ring n).
Add Ring VRing: (vec_ring n).

Property ring_util_1: forall (v1 v2: Vector n) A1 B1 A3 B3,
(v1 |* A1 |+| v1 |* B1) |+| (v2 |* A3 |+| v2 |* B3) = (v1 |* A1 |+| v2 |* A3) |+| (v1 |* B1 |+| v2 |* B3).
Proof. intros; ring. Qed.

Property ring_util_2: forall (v1 v2: Vector n) A1 B1 A2 B2,
(A1 *| v1 |+| B1 *| v1) |+| (A2 *| v2 |+| B2 *| v2) = (A1 *| v1 |+| A2 *| v2) |+| (B1 *| v1 |+| B2 *| v2).
Proof. intros; ring. Qed.

Property ring_util_3: forall (v1 v2 w1 w2: Vector n) A1 A3,
(v1 |* A1 |+| w1 |* A1) |+| (v2 |* A3 |+| w2 |* A3) = (v1 |* A1 |+| v2 |* A3) |+| (w1 |* A1 |+| w2 |* A3).
Proof. intros; ring. Qed.

Property ring_util_4: forall (v1 v2 w1 w2: Vector n) A1 A2,
(A1 *| v1 |+| A1 *| w1) |+| (A2 *| v2 |+| A2 *| w2) = (A1 *| v1 |+| A2 *| v2) |+| (A1 *| w1 |+| A2 *| w2).
Proof. intros; ring. Qed.

Property ring_util_5: forall (v1 v2: Vector n) A1 A2 A3 A4 B1 B3,
((v1 |* A1) |* B1 |+| (v1 |* A2) |* B3) |+| ((v2 |* A3) |* B1 |+| (v2 |* A4) |* B3) = ((v1 |* A1) |* B1 |+| (v2 |* A3) |* B1) |+| ((v1 |* A2) |* B3 |+| (v2 |* A4) |* B3).
Proof. intros; ring. Qed.

Property ring_util_6: forall (v1 v2: Vector n) A1 A2 B1 B2 B3 B4,
(A1 *| (B1 *| v1) |+| A2 *| (B3 *| v1)) |+| (A1 *| (B2 *| v2) |+| A2 *| (B4 *| v2)) = (A1 *| (B1 *| v1) |+| A1 *| (B2 *| v2)) |+| (A2 *| (B3 *| v1) |+| A2 *| (B4 *| v2)).
Proof. intros; ring. Qed.

End UTIL.
