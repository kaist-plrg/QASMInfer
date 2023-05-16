Require Import Operator.

Definition cnot13: Matrix.
Proof.
  refine ((Qcnot 3 0 2 _ _ _).1). lia. lia. lia.
Defined.

Fact cnot0_0: Minner cnot13 0 0 = 1.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot0_1: Minner cnot13 0 1 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot0_2: Minner cnot13 0 2 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot0_3: Minner cnot13 0 3 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot0_4: Minner cnot13 0 4 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot0_5: Minner cnot13 0 5 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot0_6: Minner cnot13 0 6 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot0_7: Minner cnot13 0 7 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot1_0: Minner cnot13 1 0 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot1_1: Minner cnot13 1 1 = 1.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot1_2: Minner cnot13 1 2 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot1_3: Minner cnot13 1 3 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot1_4: Minner cnot13 1 4 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot1_5: Minner cnot13 1 5 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot1_6: Minner cnot13 1 6 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot1_7: Minner cnot13 1 7 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot2_0: Minner cnot13 2 0 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot2_1: Minner cnot13 2 1 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot2_2: Minner cnot13 2 2 = 1.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot2_3: Minner cnot13 2 3 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot2_4: Minner cnot13 2 4 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot2_5: Minner cnot13 2 5 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot2_6: Minner cnot13 2 6 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot2_7: Minner cnot13 2 7 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot3_0: Minner cnot13 3 0 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot3_1: Minner cnot13 3 1 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot3_2: Minner cnot13 3 2 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot3_3: Minner cnot13 3 3 = 1.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot3_4: Minner cnot13 3 4 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot3_5: Minner cnot13 3 5 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot3_6: Minner cnot13 3 6 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot3_7: Minner cnot13 3 7 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot4_0: Minner cnot13 4 0 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot4_1: Minner cnot13 4 1 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot4_2: Minner cnot13 4 2 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot4_3: Minner cnot13 4 3 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot4_4: Minner cnot13 4 4 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot4_5: Minner cnot13 4 5 = 1.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot4_6: Minner cnot13 4 6 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot4_7: Minner cnot13 4 7 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot5_0: Minner cnot13 5 0 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot5_1: Minner cnot13 5 1 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot5_2: Minner cnot13 5 2 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot5_3: Minner cnot13 5 3 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot5_4: Minner cnot13 5 4 = 1.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot5_5: Minner cnot13 5 5 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot5_6: Minner cnot13 5 6 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot5_7: Minner cnot13 5 7 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot6_0: Minner cnot13 6 0 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot6_1: Minner cnot13 6 1 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot6_2: Minner cnot13 6 2 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot6_3: Minner cnot13 6 3 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot6_4: Minner cnot13 6 4 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot6_5: Minner cnot13 6 5 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot6_6: Minner cnot13 6 6 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot6_7: Minner cnot13 6 7 = 1.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot7_0: Minner cnot13 7 0 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot7_1: Minner cnot13 7 1 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot7_2: Minner cnot13 7 2 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot7_3: Minner cnot13 7 3 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot7_4: Minner cnot13 7 4 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot7_5: Minner cnot13 7 5 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot7_6: Minner cnot13 7 6 = 1.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact cnot7_7: Minner cnot13 7 7 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
