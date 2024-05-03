From FirstProject Require Import Maps Imp.
From Coq Require Import Lists.List. Import ListNotations.

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".


(* ================================================================= *)
(** ** Evaluation as a Relation *)

(** We'll use the notation [st1 / q1 =[ c ]=> st2 / q2 / r] for the [ceval] relation:
    [st1 / q1 =[ c ]=> st2 / q2 / r] means that executing program [c] in a starting
    state [st1] with continuations [q1] results in an ending state [st2] with unexplored
    continuations [q2]. Moreover the result of the computation will be [r].*)

(* Type of result *)
Inductive result : Type :=
| Success
| Fail.

(* Notation that we use *)
Reserved Notation "st1 '/' q1 '=[' c ']=>' st2 '/' q2 '/' r"
(at level 40,
 q1 constr at next level,
 c custom com at level 99, 
 st2 constr at next level,
 q2 constr at next level,
 r constr at next level).

(* 
3. TODO: Define the relational semantics (ceval) to support the required constructs.
*)

Inductive ceval : com -> state -> list (state * com) -> 
          result -> state -> list (state * com) -> Prop :=
| E_Skip : forall st q,
 st / q =[ skip ]=> st / q / Success

| E_Asg  : forall st a1 n q x,
  aeval st a1 = n ->
  st / q =[ x := a1 ]=> (x !-> n; st) / q / Success

| E_Seq : forall c c' st st' st'' q q' q'' r,
  st / q =[ c ]=> st' / q' / Success ->
  st' / q' =[ c' ]=> st'' / q'' / r ->
  st / q =[ c ; c' ]=> st'' / q'' / r

| E_IfTrue : forall st st' b c c' q q',
  beval st b = true ->
  st / q =[ c ]=> st' / q' / Success ->
  st / q =[ if b then c else c' end ]=> st' / q' / Success

| E_IfFalse : forall st st' b c c' q q',
  beval st b = false ->
  st / q =[ c' ]=> st' / q' / Success ->
  st / q =[ if b then c else c' end ]=> st' / q' / Success

| E_WE : forall b st c q,
  beval st b = false ->
  st / q =[ while b do c end ]=> st / q / Success

| E_WL : forall st st' st'' b c q q' q'',
  beval st b = true ->
  st / q =[ c ]=> st' / q' / Success ->
  st' / q' =[ while b do c end ]=> st'' / q'' / Success ->
  st / q =[ while b do c end ]=> st'' / q'' / Success

| E_NDet : forall st st' q q' c c' r,
  st / q =[ c ]=> st' / q' / r ->
  st / q =[ c !! c' ]=> st' / ((st,c') :: q') / r

| E_NDet2 : forall st st' q q' c c' r,
  st / q =[ c' ]=> st' / q' / r ->
  st / q =[ c !! c' ]=> st' / ((st,c) :: q') / r

| E_GuardTrue : forall st st' b c q q',
  beval st b = true ->
  st / q =[ c ]=> st' / q' / Success ->
  st / q =[ b -> c ]=> st' / q' / Success

| E_FalseEmpty : forall st st' b c,
  beval st b = false ->
  st / [] =[ b -> c ]=> st' / [] / Fail

| E_GuardFalse : forall st st' st'' st''' d b c q q' q'',
  beval st b = false ->
  st' / q =[ d ]=> st'' / q' / Success ->
  st'' / q' =[ b -> c ]=> st''' / q'' / Success ->
  st / ((st', d) :: q) =[  b -> c  ]=> st''' / q'' / Success
(* TODO. Hint: follow the same structure as shown in the chapter Imp *)
where "st1 '/' q1 '=[' c ']=>' st2 '/' q2 '/' r" := (ceval c st1 q1 r st2 q2).


(**
  3.1. TODO: Use the new relational semantics to prove the examples
             ceval_example_if, ceval_example_guard1, ceval_example_guard2,
             ceval_example_guard3 and ceval_example_guard4.
*)

Example ceval_example_if:
empty_st / [] =[
X := 2;
if (X <= 1)
  then Y := 3
  else Z := 4
end
]=> (Z !-> 4 ; X !-> 2) / [] / Success.
Proof.
  eapply E_Seq.
    - apply E_Asg. reflexivity.
    - apply E_IfFalse.
      -- reflexivity.
      -- apply E_Asg. reflexivity.
Qed.


Example ceval_example_guard1:
empty_st / [] =[
   X := 2;
   (X = 1) -> X:=3
]=> (empty_st) / [] / Fail.
Proof.
  eapply E_Seq.
    - apply E_Asg. reflexivity.
    - apply E_FalseEmpty. reflexivity.
Qed. 

Example ceval_example_guard2:
empty_st / [] =[
   X := 2;
   (X = 2) -> X:=3
]=> (X !-> 3 ; X !-> 2) / [] / Success.
Proof.
  eapply E_Seq.
  - apply E_Asg. reflexivity.
  - apply E_GuardTrue.
  -- reflexivity.
  -- apply E_Asg. reflexivity.
Qed. 

Example ceval_example_guard3: exists q,
empty_st / [] =[
   (X := 1 !! X := 2);
   (X = 2) -> X:=3
]=> (X !-> 3) / q / Success.
Proof.
 eexists.
 eapply E_Seq.
  - apply E_NDet2.
    apply E_Asg. reflexivity.
  - apply E_GuardTrue.
    -- reflexivity.
    -- assert ((X!->3 ; X!->2)=(X!->3)) by (apply t_update_shadow).
       rewrite <- H.
       apply E_Asg. reflexivity.
Qed.
    
Example ceval_example_guard4: exists q,
empty_st / [] =[
   (X := 1 !! X := 2);
   (X = 2) -> X:=3
]=> (X !-> 3) / q / Success.
Proof.
eexists.
eapply E_Seq.
  - apply E_NDet2. apply E_Asg. reflexivity.
  - eapply E_GuardTrue; try reflexivity.
    -- assert ((X!->3 ; X!->2)=(X!->3)) by (apply t_update_shadow).
       rewrite <- H.
       apply E_Asg.
       reflexivity.
Qed.



(* 3.2. Behavioral equivalence *)

Definition cequiv_imp (c1 c2 : com) : Prop := 
forall (st1 st2 : state) q1 q2 result,
(st1 / q1 =[ c1 ]=> st2 / q2 / result) ->
exists q3, 
(st1 / q1 =[ c2 ]=> st2 / q3 / result).

Definition cequiv (c1 c2 : com) : Prop :=
cequiv_imp c1 c2 /\ cequiv_imp c2 c1.

Infix "==" := cequiv (at level 99).


(**
  3.2. TODO: Prove the properties below.
*)

Lemma cequiv_ex1:
<{ X := 2; X = 2 -> skip }> == 
<{ X := 2 }>.
Proof.
split.
  - eexists.
    inversion H; subst.
    inversion H2; subst; simpl in H2.
    inversion H8; subst; simpl in H8.
    inversion H10; subst; simpl in H10.
    -- eapply E_Asg. reflexivity.
    -- discriminate.
    -- discriminate.
  - eexists.
    inversion H; subst.
    eapply E_Seq.
      -- apply E_Asg. reflexivity.
      -- simpl. apply E_GuardTrue.
        --- reflexivity.
        --- apply E_Skip.
Qed.

Lemma cequiv_ex2:
<{ (X := 1 !! X := 2); X = 2 -> skip }> == 
<{ X := 2 }>.
Proof.
split.
  - unfold cequiv_imp. intros.
    inversion H; subst.
    inversion H2; subst; simpl in H2. 
    inversion H9; subst; simpl in H9.
    inversion H8; subst; simpl in H8.
    inversion H11; subst; simpl in H11.
    (* Choice 1 - Guard true *)
    -- discriminate.
    (* Choice 1 - Guard false *)
    -- inversion H14; subst. 
       inversion H4; subst.
       inversion H5; subst.
       eexists.
       eapply Asg. reflexivity.
    -- inversion H9; subst; simpl in H9.
       inversion H8; subst.
       eexists.
      (* Choice 2 - Guard true *)
      --- inversion H11; subst.
          inversion H3; subst.
          eapply E_Asg. reflexivity.
      (* Choice 2 - Guard false *)
      --- discriminate.  
  - eexists.
    inversion H; subst; simpl in H.
    simpl.
    eapply E_Seq.
    -- eapply E_NDet2. 
       eapply E_Asg. reflexivity.
    -- eapply E_GuardTrue; 
       try reflexivity.
       eapply E_Skip.
Qed.


Lemma choice_idempotent: forall c,
<{ c !! c }> == <{ c }>.
Proof.
  split; unfold cequiv_imp; intros.
  - inversion H; subst; eexists; eassumption.
  - inversion H; subst; eexists; apply E_NDet; eassumption.
Qed.

Lemma choice_comm: forall c1 c2,
<{ c1 !! c2 }> == <{ c2 !! c1 }>.
Proof.
  split; unfold cequiv_imp; intros.
  - inversion H; subst. 
    -- eexists. 
       eapply E_NDet2. 
       eassumption.
    -- eexists. 
       eapply E_NDet. 
       eassumption.
  - inversion H; subst. 
    -- eexists. 
       eapply E_NDet2. 
       eassumption.
    -- eexists. 
       eapply E_NDet. 
       eassumption.
Qed.

Lemma choice_assoc: forall c1 c2 c3,
<{ (c1 !! c2) !! c3 }> == <{ c1 !! (c2 !! c3) }>.
Proof.
split; unfold cequiv_imp; intros.
  - inversion H; subst.
    inversion H7; subst.
    -- eexists.  
       eapply E_NDet.
       eassumption.
    -- eexists.
       eapply E_NDet2.
       eapply E_NDet. 
       eassumption.
    -- eexists.
       eapply E_NDet2.
       eapply E_NDet2.
       eassumption.
  - inversion H; subst.
    -- eexists.
       eapply E_NDet.
       eapply E_NDet.
       eassumption.
    -- inversion H7; subst.
      --- eexists.
          eapply E_NDet.
          eapply E_NDet2.
          eassumption.
      --- eexists.
          eapply E_NDet2.
          eassumption.   
Qed.


Lemma choice_seq_distr_l: forall c1 c2 c3,
<{ c1 ; (c2 !! c3)}> == <{ (c1;c2) !! (c1;c3) }>.
Proof.
  split; unfold cequiv_imp; intros.
  - inversion H; subst.
    inversion H8; subst.
    -- eexists.
       apply E_NDet.
       eapply E_Seq;
       eassumption.
    -- eexists. 
       apply E_NDet2.
       eapply E_Seq;
       eassumption.
  - inversion H; subst.
    inversion H7; subst.
    -- eexists.
       eapply E_Seq;
       try eassumption.
      --- eapply E_NDet.
          eassumption.
    -- inversion H7; subst.
       eexists.
       eapply E_Seq.
      ---  eassumption.
      ---  apply E_NDet2.
           eassumption.
Qed.

Lemma choice_congruence: forall c1 c1' c2 c2',
c1 == c1' -> c2 == c2' ->
<{ c1 !! c2 }> == <{ c1' !! c2' }>.
Proof.
  split; intros s1 s2 q1 q2 r H3; inversion H3; subst; 
  repeat(apply H in H9; induction H9; eexists; apply E_NDet; apply H1);
  repeat(apply H0 in H9; induction H9; eexists; apply E_NDet2; apply H1).
Qed.