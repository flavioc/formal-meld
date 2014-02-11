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

(* cont [rules] ctx xi *)
Inductive cont : Type :=
   | continuation : list rule_tm -> list nat -> cont.

Definition empty_continuation := continuation nil nil.

Inductive match0 : list nat -> body_tm -> list nat -> Prop :=
   | Match_One : match0 nil btm_one nil
   | Match_Tensor : forall ctx1 ctx2 a b end1 end2, match0 ctx1 a end1 -> match0 ctx2 b end2 -> match0 (app ctx1 ctx2) (btm_tensor a b) (app end1 end2)
   | Match_Fact : forall p, match0 (p :: nil) (btm_fact p) (p :: nil)
   | Match_Constraint: forall c, eval_bool c true -> match0 nil (btm_constraint c) nil.

(** match1 remain past_consumed body continuation total_consumed **)
Inductive match1 : list nat -> list nat -> (list body_tm) -> cont -> head_tm -> list nat -> Prop :=
   | Match1_One : forall delta xi xi' ls c h, match1 delta xi ls c h xi' -> match1 delta xi (btm_one :: ls) c h xi'
   | Match1_Tensor : forall delta xi a b ls xi' c h, match1 delta xi (a :: b :: ls) c h xi' -> match1 delta xi (btm_tensor a b :: ls) c h xi'
   | Match1_Fact : forall delta delta' xi p xi' ls c h, In p delta -> delta = p :: delta' -> match1 delta' (p :: xi) ls c h xi' -> match1 delta xi (btm_fact p :: ls) c h xi'
   | Match1_FactFail : forall delta xi p xi' ls nr nrs orig h, ~ In p delta -> cont1 (continuation (nr :: nrs) orig) xi' -> match1 delta xi (btm_fact p :: ls) (continuation (nr :: nrs) orig) h xi'
   | Match1_Constraint : forall delta bexp xi ls xi' c h, eval_bool bexp true -> match1 delta xi ls c h xi' -> match1 delta xi (btm_constraint bexp :: ls) c h xi'
   | Match1_End : forall delta xi c h, derive1 (h :: nil) delta xi delta (empty_continuation) xi delta -> match1 delta xi nil c h xi
with do1 : list nat -> list rule_tm -> list nat -> Prop :=
   | Do1_Rule : forall delta rules xi rule, apply1 delta rule (continuation rules delta) xi -> do1 delta (rule :: rules) xi
with cont1 : cont -> list nat -> Prop :=
   | Cont1_Next : forall r rs xi' delta, do1 delta (r ::rs) xi' -> cont1 (continuation (r :: rs) delta) xi'
with apply1 : list nat -> rule_tm -> cont -> list nat -> Prop :=
(** apply1 delta rule cont xi *)
   | Apply1_Rule : forall delta body head c xi, match1 delta nil (body :: nil) c head xi -> apply1 delta (rtm_lolli body head) c xi
(* derive1 head delta xi new cont xi' finalnew *)
with derive1 : list head_tm -> list nat -> list nat -> list nat -> cont -> list nat -> list nat -> Prop :=
   | Derive1_One : forall delta new ls xi c xi' final, derive1 ls delta xi new c xi' final -> derive1 (head_one :: ls) delta xi new c xi' final
   | Derive1_Fact : forall ls delta p xi c new xi' final, derive1 ls delta xi (p :: new) c xi' final -> derive1 (head_fact p :: ls) delta xi new c xi' final
   | Derive1_Tensor : forall ls delta a b xi c new xi' final, derive1 (a :: b :: ls) delta xi new c xi' final -> derive1 (head_tensor a b :: ls) delta xi new c xi' final
   | Derive1_End : forall delta xi c new , derive1 nil delta xi new c xi new.

(* derive0 head delta new xi final *)
Inductive derive0 : list head_tm -> list nat -> list nat -> list nat -> list nat -> Prop :=
   | Derive_One : forall ls delta new xi final, derive0 ls delta new xi final -> derive0 (head_one :: ls) delta new xi final
   | Derive_Fact : forall delta ls p new xi final, derive0 ls delta (p :: new) xi final -> derive0 (head_fact p :: ls) delta new xi final
   | Derive_Tensor : forall delta ls a b xi new final, derive0 (a :: b :: ls) delta new xi final -> derive0 (head_tensor a b :: ls) delta new xi final
   | Derive_End : forall delta new xi, derive0 nil delta new xi new.


(* apply0 delta rule delta' xi *)
Inductive apply0 : list nat -> rule_tm -> list nat -> list nat -> Prop :=
   | Apply0_Rule : forall body head ctx_deleted ctx_maintain ctx_new xi, match0 ctx_deleted body ctx_deleted -> derive0 (head :: nil) ctx_maintain nil xi ctx_new -> apply0 (ctx_deleted ++ ctx_maintain) (rtm_lolli body head) ctx_new (ctx_deleted ++ xi).

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

   (*
Example apply0_example2:
   apply0 ((1 :: nil) ++ nil) (rtm_lolli (btm_fact 1) head_one) nil ((1 :: nil) ++ nil).
   Proof.

   *)

Example apply0_example1:
   apply0 (1 :: 2 :: 3 :: nil) (rtm_lolli (btm_tensor (btm_fact 1) (btm_fact 2)) (head_tensor (head_tensor (head_fact 5) (head_fact 6)) (head_one))) (6 :: 5 :: nil) (1 :: 2 :: nil).
   Proof.
   assert (1 :: 2 :: 3 :: nil = (1 :: 2 :: nil) ++ (3 :: nil)).
    simpl.
     auto.

      rewrite H.
      assert (1 :: 2 :: nil = (1 :: 2 :: nil) ++ nil).
       auto.

        rewrite H0.
        apply Apply0_Rule.
         assert (1 :: 2 :: nil = (1 :: nil) ++ 2 :: nil).
           auto.

             rewrite H1.
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
   forall xi a xi' delta h, match1 delta xi a (continuation nil nil) h xi' -> exists xi2, xi2 ++ xi = xi'.
Proof.
   remember (continuation nil nil) as c.
   intros.
   induction H.
    auto.

     auto.

      apply IHmatch1 in Heqc.
       inversion Heqc.
        exists (p :: x).
         simpl.
          admit.

           inversion Heqc.

            auto.

             exists nil.
              auto.
Qed.

   (*
Theorem match1_add:
   forall delta1 xi1 ls xi' h, match1 delta1 xi1 ls empty_continuation h xi' -> forall delta2 xi2, match1 (delta1 ++ delta2) (xi1 ++ xi2) ls empty_continuation h (xi' ++ xi2).
Proof.
   intros delta1 xi1 ls xi' h.
   intros H.
   remember (empty_continuation) as c in H.
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
   apply Match1_Fact with (delta' := delta' ++ delta2).
   rewrite H0.
   auto.
   simpl.
   auto.

   simpl.
   auto.
   rewrite H0.
   auto.

   apply IHmatch1.
   auto.
    inversion Heqc.

   intros.
   apply Match1_Constraint.
   auto.

   auto.

   intros.
   apply Match1_End.
Qed.

Theorem match1_merge:
   forall delta1 xi1 a xi1' h, match1 delta1 xi1 a empty_continuation h xi1' -> forall delta2 b xi2 xi2', match1 delta2 xi2 b empty_continuation h xi2' -> match1 (delta2 ++ delta1) (xi1 ++ xi2) (a ++ b) empty_continuation h (xi1' ++ xi2').
Proof.
   intros delta1 xi1 a xi1' h.
   intros H.
   remember empty_continuation as c in H.
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
   auto.

   intros.
   simpl.
   apply Match1_Fact with (delta' := delta' ++ delta2).
    rewrite H0.
    admit.
    rewrite H0.
    admit.
    apply IHmatch1 with (delta2 := delta2) (b := b) (xi2 := xi2) (xi2' := xi2')
       in Heqc.
          simpl Heqc.
             assert (delta' ++ delta2 = delta2 ++ delta').
                 admit.

                     rewrite H3.
                         apply Heqc.

                            auto.
                            inversion Heqc.

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
   forall delta a h, match0 delta a delta -> match1 delta nil (a :: nil) empty_continuation h delta.
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

    apply Match1_Fact with (delta' := nil).
    simpl.
    auto.
    auto.

   apply Match1_End.

   apply Match1_Constraint.
   auto.

   auto.
   apply Match1_End.
Qed.
*)

Theorem match_cont_theorem:
   forall delta xi a c xi' deltany h, match1 delta xi a c h xi' -> match1 delta xi a (continuation nil deltany) h xi' \/ cont1 c xi'.
Proof.
intros.
induction H.
inversion IHmatch1.
left.
apply Match1_One.
auto.

right.
auto.

inversion IHmatch1.
left.
apply Match1_Tensor.
auto.

right.
auto.

inversion IHmatch1.
left.
apply Match1_Fact with (delta' := delta').
auto.

auto.

auto.

right.
auto.

right.
auto.

inversion IHmatch1.
left.
apply Match1_Constraint.
auto.

auto.

right.
auto.

left.
apply Match1_End.
auto.
Qed.

Theorem apply1_cont_theorem:
   forall delta rule c xi' deltany, apply1 delta rule c xi' -> apply1 delta rule (continuation nil deltany) xi' \/ cont1 c xi'.
Proof.
intros.
induction H.
apply match_cont_theorem with (deltany := deltany) in H.
inversion H.
 left.
  apply Apply1_Rule.
   auto.

    right.
     auto.
Qed.

Theorem do_cont_theorem:
   forall rules delta xi, do1 delta rules xi -> exists r, In r rules /\ do1 delta (r :: nil) xi.
Proof.
induction rules.
intros.
inversion H.

intros.
inversion H.
apply apply1_cont_theorem with (deltany := delta) in H4.
inversion H4.
exists a.
split.
simpl.
auto.

apply Do1_Rule.
auto.

inversion H5.
rewrite H6.
rewrite H6 in H9.
apply IHrules in H9.
inversion H9.
exists x.
inversion H10.
split.
simpl.
right.
auto.

auto.
Qed.

Theorem derive_soundness:
   forall a delta xi xi' delta1 delta' c, derive1 a delta xi delta1 c xi' delta' -> derive0 a delta delta1 xi' delta'.
Proof.
   intros.
   induction H.
   apply Derive_One.
   auto.

   apply Derive_Fact.
   auto.

   apply Derive_Tensor.
   auto.

   apply Derive_End.
Qed.

Theorem derive1_includes_delta1:
   forall a delta xi xi' delta1 delta' c, derive1 a delta xi delta1 c xi' delta' -> exists other, delta' = delta1 ++ other.
   intros.
   induction H.
   inversion IHderive1.
   exists x.
   auto.

   inversion IHderive1.
   exists (p :: x).
   admit.

   inversion IHderive1.
   exists x.
   auto.

   exists nil.
   simpl.
   rewrite app_nil_r.
   auto.
Qed.

(*
Theorem match_soundness:
   forall delta others a xi xi', delta = xi' ++ others /\ match1 delta xi (a :: nil) empty_continuation (xi ++ xi') -> match0 xi' a xi'.
Proof.
*)
