Require Import Operator.

Definition swap13: Matrix.
Proof.
  refine ((Qswap 3 0 2 _ _).1). lia. lia.
Defined.

Fact swap0_0: Minner swap13 0 0 = 1.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap0_1: Minner swap13 0 1 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap0_2: Minner swap13 0 2 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap0_3: Minner swap13 0 3 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap0_4: Minner swap13 0 4 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap0_5: Minner swap13 0 5 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap0_6: Minner swap13 0 6 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap0_7: Minner swap13 0 7 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap1_0: Minner swap13 1 0 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap1_1: Minner swap13 1 1 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap1_2: Minner swap13 1 2 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap1_3: Minner swap13 1 3 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap1_4: Minner swap13 1 4 = 1.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap1_5: Minner swap13 1 5 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap1_6: Minner swap13 1 6 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap1_7: Minner swap13 1 7 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap2_0: Minner swap13 2 0 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap2_1: Minner swap13 2 1 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap2_2: Minner swap13 2 2 = 1.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap2_3: Minner swap13 2 3 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap2_4: Minner swap13 2 4 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap2_5: Minner swap13 2 5 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap2_6: Minner swap13 2 6 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap2_7: Minner swap13 2 7 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap3_0: Minner swap13 3 0 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap3_1: Minner swap13 3 1 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap3_2: Minner swap13 3 2 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap3_3: Minner swap13 3 3 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap3_4: Minner swap13 3 4 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap3_5: Minner swap13 3 5 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap3_6: Minner swap13 3 6 = 1.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap3_7: Minner swap13 3 7 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap4_0: Minner swap13 4 0 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap4_1: Minner swap13 4 1 = 1.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap4_2: Minner swap13 4 2 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap4_3: Minner swap13 4 3 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap4_4: Minner swap13 4 4 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap4_5: Minner swap13 4 5 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap4_6: Minner swap13 4 6 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap4_7: Minner swap13 4 7 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap5_0: Minner swap13 5 0 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap5_1: Minner swap13 5 1 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap5_2: Minner swap13 5 2 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap5_3: Minner swap13 5 3 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap5_4: Minner swap13 5 4 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap5_5: Minner swap13 5 5 = 1.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap5_6: Minner swap13 5 6 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap5_7: Minner swap13 5 7 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap6_0: Minner swap13 6 0 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap6_1: Minner swap13 6 1 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap6_2: Minner swap13 6 2 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap6_3: Minner swap13 6 3 = 1.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap6_4: Minner swap13 6 4 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap6_5: Minner swap13 6 5 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap6_6: Minner swap13 6 6 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap6_7: Minner swap13 6 7 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap7_0: Minner swap13 7 0 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap7_1: Minner swap13 7 1 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap7_2: Minner swap13 7 2 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap7_3: Minner swap13 7 3 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap7_4: Minner swap13 7 4 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap7_5: Minner swap13 7 5 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap7_6: Minner swap13 7 6 = 0.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.
Fact swap7_7: Minner swap13 7 7 = 1.
Proof. simpl. unfold Mmult_inner. simpl. lca. Qed.