Require Import Coq.Lists.List.

Inductive bool_expr : Type :=
   | b_true : bool_expr
   | b_false : bool_expr
   | b_equal : bool_expr -> bool_expr -> bool_expr.

Inductive eval_bool : bool_expr -> bool -> Prop :=
   | bool_true : eval_bool b_true true
   | bool_false : eval_bool b_false false
   | bool_equal_true : forall a b, eval_bool a true /\ eval_bool b true -> eval_bool (b_equal a b) true
   | bool_equal_false : forall a b, eval_bool a false /\ eval_bool b false -> eval_bool (b_equal a b) true.

Inductive body_tm : Type :=
   | btm_one : body_tm
   | btm_tensor : body_tm -> body_tm -> body_tm
   | btm_constraint : bool_expr -> body_tm
   | btm_fact : nat -> body_tm.

Inductive head_tm : Type :=
   | head_one : head_tm
   | head_tensor : head_tm -> head_tm -> head_tm
   | head_fact : nat -> head_tm.

Inductive rule_tm : Type :=
   | rtm_lolli : body_tm -> head_tm -> rule_tm.

Inductive match0 : list nat -> body_tm -> list nat -> Prop :=
   | Match_One : match0 nil btm_one nil
   | Match_Tensor : forall ctx1 ctx2 a b end1 end2, match0 ctx1 a end1 -> match0 ctx2 b end2 -> match0 (app ctx1 ctx2) (btm_tensor a b) (app end1 end2)
   | Match_Fact : forall p, match0 (p :: nil) (btm_fact p) (p :: nil)
   | Match_Constraint: forall c, eval_bool c true -> match0 nil (btm_constraint c) nil.

(** match1 remain past_consumed body total_consumed **)
Inductive match1 : list nat -> list nat -> (list body_tm) -> list nat -> Prop :=
   | Match1_One : forall delta xi xi' ls, match1 delta xi ls xi' -> match1 delta xi (btm_one :: ls) xi'
   | Match1_Tensor : forall delta xi a b ls xi', match1 delta xi (a :: b :: ls) xi' -> match1 delta xi (btm_tensor a b :: ls) xi'
   | Match1_Fact : forall delta' xi p xi' ls, match1 delta' (p :: xi) ls xi' -> match1 (p :: delta') xi (btm_fact p :: ls) xi'
   | Match1_Constraint : forall delta bexp xi ls xi', eval_bool bexp true -> match1 delta xi ls xi' -> match1 delta xi (btm_constraint bexp :: ls) xi'
   | Match1_End : forall delta xi, match1 delta xi nil xi.

Inductive derive0 : list head_tm -> list nat -> list nat -> Prop :=
   | Derive_One : forall ctx ls final, derive0 ls ctx final -> derive0 (head_one :: ls) ctx final
   | Derive_Fact : forall ctx ls p final, derive0 ls (p :: ctx) final -> derive0 (head_fact p :: ls) ctx final
   | Derive_Tensor : forall ctx ls a b final, derive0 (a :: b :: ls) ctx final -> derive0 (head_tensor a b :: ls) ctx final
   | Derive_End : forall final, derive0 nil final final.

Inductive apply0 : list nat -> rule_tm -> list nat -> list nat -> list nat -> Prop :=
   | Apply0 : forall body head ctx_deleted ctx_maintain ctx_new, match0 ctx_deleted body ctx_deleted -> derive0 (head :: nil) nil ctx_new -> apply0 (ctx_deleted ++ ctx_maintain) (rtm_lolli body head) ctx_maintain ctx_new ctx_deleted.

Example simple_match1 :
   match0 (1 :: 2 :: 3 :: nil) (btm_tensor (btm_tensor (btm_fact 1) (btm_fact 2)) (btm_fact 3)) (1 :: 2 :: 3 :: nil).
Proof.
assert (1 :: 2 :: 3 :: nil = (1 :: 2 :: nil) ++ 3 :: nil).
auto.

rewrite H.
apply Match_Tensor.
assert ((1 :: nil) ++ 2 :: nil = 1 :: 2 :: nil).
auto.

rewrite <- H0.
apply Match_Tensor.
apply Match_Fact.

apply Match_Fact.

apply Match_Fact.
Qed.

Lemma match0_same :
   forall a, exists ctx1 ctx2, match0 ctx1 a ctx2 -> ctx1 = ctx2.
Proof.
intro a.
induction a.
exists nil.
exists nil.
intro H.
auto.

inversion IHa1.
inversion IHa2.
inversion H.
inversion H0.
exists (x1 ++ x2).
exists (x1 ++ x2).
intro A.
auto.

exists nil.
exists nil.
auto.

exists (n :: nil).
exists (n :: nil).
auto.
Qed.

Example apply0_example1:
   apply0 (1 :: 2 :: 3 :: nil) (rtm_lolli (btm_tensor (btm_fact 1) (btm_fact 2)) (head_tensor (head_tensor (head_fact 5) (head_fact 6)) (head_one))) (3 :: nil) (6 :: 5 :: nil) (1 :: 2 :: nil).
   assert (1 :: 2 :: 3 :: nil = (1 :: 2 :: nil) ++ 3 :: nil).
   auto.

   rewrite H.
   apply Apply0.
   assert (1 :: 2 :: nil = (1 :: nil) ++ 2 :: nil).
   auto.

   rewrite H0.
   apply Match_Tensor.
   apply Match_Fact.

   apply Match_Fact.
   apply Derive_Tensor.
   apply Derive_Tensor.
   apply Derive_Fact.
   apply Derive_Fact.
   apply Derive_One.
   apply Derive_End.
   Qed.

Theorem match1_subset:
   forall xi a xi' delta, match1 delta xi a xi' -> exists xi2, xi2 ++ xi = xi'.
Proof.
   intros.
   induction H.
   inversion IHmatch1.
   exists x.
   auto.

   inversion IHmatch1.
   exists x.
   auto.

   inversion IHmatch1.
   simpl in H0.
   exists (p :: xi).
   simpl.
   auto.
   rewrite <- H0.
   admit.

   inversion IHmatch1.
   exists x.
   auto.

   exists nil.
   simpl.
   auto.
Qed.

Theorem match1_add:
   forall delta1 xi1 ls xi', match1 delta1 xi1 ls xi' -> forall delta2 xi2, match1 (delta1 ++ delta2) (xi1 ++ xi2) ls (xi' ++ xi2).
Proof.
   intros delta1 xi1 ls xi'.
   intros H.
   induction H.
   simpl.
   intros.
   apply Match1_One.
   auto.

   intros.
   apply Match1_Tensor.
   auto.

   intros.
   simpl.
   apply Match1_Fact.
   auto.
   apply IHmatch1.

   intros.
   apply Match1_Constraint.
   auto.

   auto.

   intros.
   apply Match1_End.
Qed.

Theorem match1_merge:
   forall delta1 xi1 a xi1', match1 delta1 xi1 a xi1' -> forall delta2 b xi2 xi2', match1 delta2 xi2 b xi2' -> match1 (delta2 ++ delta1) (xi1 ++ xi2) (a ++ b) (xi1' ++ xi2').
Proof.
   intros delta1 xi1 a xi1'.
   intros H.
   induction H.
   simpl.
   intros.
   apply Match1_One.
   auto.

   intros.
   simpl.
   apply Match1_Tensor.
   auto.
   simpl.
   apply IHmatch1.
   auto.

   intros.
   simpl.
   simpl.
   assert (delta2 ++ p :: delta' = p :: delta' ++ delta2).
   admit.

   rewrite H1.
   apply Match1_Fact.
   assert (delta2 ++ delta' = delta' ++ delta2).
   admit.

   rewrite <- H2.
   apply IHmatch1.
   auto.

   intros.
   simpl.
   apply Match1_Constraint.
   auto.

   auto.

   simpl.
   intros.
   apply match1_add with (delta2 := delta) (xi2 := xi) in H.
   assert (xi ++ xi2 = xi2 ++ xi).
   admit.

   rewrite H0.
   assert (xi ++ xi2' = xi2' ++ xi).
   admit.

   rewrite H1.
   auto.
Qed.

Theorem match_completeness:
   forall delta a, match0 delta a delta -> match1 delta nil (a :: nil) delta.
Proof.
   intros.
   induction H.
   simpl.
   apply Match1_One.
   auto.
   apply Match1_End.

   simpl.
   apply Match1_Tensor.
   assert (a :: b :: nil = (a :: nil) ++ b :: nil).
   admit.

   rewrite H1.
   apply
   match1_merge
   with (delta1 := end1) (xi1 := nil) (a := a :: nil) (xi1' := end1)
   in IHmatch0_2.
   simpl.
   auto.
   simpl in IHmatch0_2.
   auto.
   assert (end1 ++ end2 = end2 ++ end1).
   admit.

   rewrite H2.
   auto.
   rewrite <- H2.
   rewrite H2.
   rewrite <- H2 in |- * at 1.
   auto.
   rewrite <- H2 in |- * at 1.
   rewrite H2 in |- * at 1.
   auto.

   simpl.
   auto.

   apply Match1_Fact.
   apply Match1_End.

   apply Match1_Constraint.
   auto.

   auto.
   apply Match1_End.
Qed.

