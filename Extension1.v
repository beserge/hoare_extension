
Set Warnings "-notation-overridden,-parsing".

From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
Import ListNotations.

(*MAPS *)
Definition total_map (A : Type) := string -> A.

Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).



Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.

Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if eqb_string x x' then v else m x'.

Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).

Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).

Definition empty_st := (_ !-> 0).

(*imp*)
Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string)              (* <--- NEW *)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).


Definition state := total_map nat.

(*
Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.
 *)

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x                                (* <--- NEW *)
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2  => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => (aeval st a1) =? (aeval st a2)
  | BLe a1 a2   => (aeval st a1) <=? (aeval st a2)
  | BNot b1     => negb (beval st b1)
  | BAnd b1 b2  => andb (beval st b1) (beval st b2)
  end.

Definition bool_to_bexp (b : bool) : bexp :=
  if b then BTrue else BFalse.
(*Coercion bool_to_bexp : bool >-> bexp.*)

Bind Scope imp_scope with aexp.
Bind Scope imp_scope with bexp.
Delimit Scope imp_scope with imp.



Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Notation "x + y" := (APlus x y) (at level 50, left associativity) : imp_scope.
Notation "x - y" := (AMinus x y) (at level 50, left associativity) : imp_scope.
Notation "x * y" := (AMult x y) (at level 40, left associativity) : imp_scope.
Notation "x <= y" := (BLe x y) (at level 70, no associativity) : imp_scope.
Notation "x = y" := (BEq x y) (at level 70, no associativity) : imp_scope.
Notation "x && y" := (BAnd x y) (at level 40, left associativity) : imp_scope.
Notation "'~' b" := (BNot b) (at level 75, right associativity) : imp_scope.

Inductive com : Type :=
  | CSkip
  | CAss (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com)
  | CLoop (a : aexp) (c : com).


Bind Scope imp_scope with com.
Notation "'SKIP'" :=
   CSkip : imp_scope.
Notation "x '::=' a" :=
  (CAss x a) (at level 60) : imp_scope.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity) : imp_scope.
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity) : imp_scope.
Notation "'TEST' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity) : imp_scope.
Notation "'LOOP' a 'DO' c 'END'" :=
  (CLoop a c) (at level 70, right associativity) : imp_scope.

Reserved Notation "st '=[' c ']=>' st'"
                  (at level 40).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ SKIP ]=> st
  | E_Ass  : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x ::= a1 ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ;; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ WHILE b DO c END ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ WHILE b DO c END ]=> st'' ->
      st  =[ WHILE b DO c END ]=> st''
  | E_LoopZero : forall (st:state) (a:aexp)  (c:com),
    aeval st a = 0 -> 
    st =[ LOOP a DO c END ]=> st
  | E_LoopMore : forall st st' st'' a c v,
      aeval st a = v ->
      v > 0 ->
    st =[ c ]=> st' -> 
    st' =[ LOOP (ANum (pred v)) DO c END ]=> st'' ->
    st =[ LOOP a DO c END ]=> st''

  where "st =[ c ]=> st'" := (ceval c st st').



Example ex1: forall x c, (x) =[ LOOP (ANum 0) DO c END ]=> (x).

Proof.
  intros. apply E_LoopZero. reflexivity.
Qed.

(*Example ex2: (X !-> 0; empty_st) =[ LOOP 4 DO X ::= X + 1 END ]=> (X !-> 4; X !-> 3; X !-> 2; X !-> 1; X !-> 0; empty_st).

Proof.  
  repeat
   (try (eapply E_LoopMore; try reflexivity; try apply le_plus_l; try (apply E_Ass; reflexivity));  
   try (apply E_LoopZero; reflexivity)). 
 Qed. 


Example ex3: (X !-> 4; empty_st) =[ LOOP X DO X ::= X + 1 END ]=> (X !-> 8; X !-> 7; X !-> 6; X !-> 5; X !-> 4; empty_st).
Proof.
  repeat
   (try (eapply E_LoopMore; try reflexivity; try apply le_plus_l; try (apply E_Ass; reflexivity));  
   try (apply E_LoopZero; reflexivity)). 
 Qed. 
*)
(* TODO: We should probably try to prove that our rule doesn't break the other rules, as well as its general correctness *)

Theorem ceval_deterministic: forall c st st1 st2,
     st =[ c ]=> st1  ->
     st =[ c ]=> st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  induction E1;
           intros st2 E2; inversion E2; subst.
  - (* E_Skip *) reflexivity.
  - (* E_Ass *) reflexivity.
  - (* E_Seq *)
    assert (st' = st'0) as EQ1.
    { (* Proof of assertion *) apply IHE1_1; assumption. }
    subst st'0.
    apply IHE1_2. assumption.
  - (* E_IfTrue, b1 evaluates to true *)
      apply IHE1. assumption.
  - (* E_IfTrue,  b1 evaluates to false (contradiction) *)
      rewrite H in H5. discriminate H5.
  - (* E_IfFalse, b1 evaluates to true (contradiction) *)
      rewrite H in H5. discriminate H5.
  - (* E_IfFalse, b1 evaluates to false *)
      apply IHE1. assumption.
  - (* E_WhileFalse, b1 evaluates to false *)
    reflexivity.
  - (* E_WhileFalse, b1 evaluates to true (contradiction) *)
    rewrite H in H2. discriminate H2.
  - (* E_WhileTrue, b1 evaluates to false (contradiction) *)
    rewrite H in H4. discriminate H4.
  - (* E_WhileTrue, b1 evaluates to true *)
      assert (st' = st'0) as EQ1.
      { (* Proof of assertion *) apply IHE1_1; assumption. }
      subst st'0.
      apply IHE1_2. assumption.  
  - reflexivity.
  - Admitted.



(* Hoare *)

Definition Assertion := state -> Prop.

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Notation "P ->> Q" := (assert_implies P Q)
                      (at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.

Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) : hoare_spec_scope.

Definition hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st',
     st =[ c ]=> st'  ->
     P st  ->
     Q st'.

Notation "{{ P }}  c  {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level)
  : hoare_spec_scope.


Theorem hoare_post_true : forall (P Q : Assertion) c,
  (forall st, Q st) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros st st' Heval HP.
  apply H.  Qed.

Theorem hoare_pre_false : forall (P Q : Assertion) c,
  (forall st, ~ (P st)) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros st st' Heval HP.
  unfold not in H. apply H in HP.
  inversion HP.  Qed.

Definition assn_sub X a P : Assertion :=
  fun (st : state) =>
    P (X !-> aeval st a ; st).

Notation "P [ X |-> a ]" := (assn_sub X a P)
  (at level 10, X at next level).


Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} X ::= a {{Q}}.
Proof.
  unfold hoare_triple.
  intros Q X a st st' HE HQ.
  inversion HE. subst.
  unfold assn_sub in HQ. assumption.  Qed.

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q c Hhoare Himp.
  intros st st' Hc HP. apply (Hhoare st st').
  assumption. apply Himp. assumption. Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P Q Q' c Hhoare Himp.
  intros st st' Hc HP.
  apply Himp.
  apply (Hhoare st st').
  assumption. assumption. Qed.

Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
  {{P'}} c {{Q'}} ->
  P ->> P' ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q Q' c Hht HPP' HQ'Q.
  apply hoare_consequence_pre with (P' := P').
  apply hoare_consequence_post with (Q' := Q').
  assumption. assumption. assumption.  Qed.

Theorem hoare_skip : forall P,
     {{P}} SKIP {{P}}.
Proof.
  intros P st st' H HP. inversion H. subst.
  assumption.  Qed.

Theorem hoare_seq : forall P Q R c1 c2,
     {{Q}} c2 {{R}} ->
     {{P}} c1 {{Q}} ->
     {{P}} c1;;c2 {{R}}.
Proof.
  intros P Q R c1 c2 H1 H2 st st' H12 Pre.
  inversion H12; subst.
  apply (H1 st'0 st'); try assumption.
  apply (H2 st st'0); assumption. Qed.

Definition bassn b : Assertion :=
  fun st => (beval st b = true).

Lemma bexp_eval_true : forall b st,
  beval st b = true -> (bassn b) st.
Proof.
  intros b st Hbe.
  unfold bassn. assumption.  Qed.

Lemma bexp_eval_false : forall b st,
  beval st b = false -> ~ ((bassn b) st).
Proof.
  intros b st Hbe contra.
  unfold bassn in contra.
  rewrite -> contra in Hbe. inversion Hbe.  Qed.

Theorem hoare_while : forall P b c,
  {{fun st => P st /\ bassn b st}} c {{P}} ->
  {{P}} WHILE b DO c END {{fun st => P st /\ ~ (bassn b st)}}.
Proof.
  intros P b c Hhoare st st' He HP.
  (* Like we've seen before, we need to reason by induction
     on [He], because, in the "keep looping" case, its hypotheses
     talk about the whole loop instead of just [c]. *)
  remember (WHILE b DO c END)%imp as wcom eqn:Heqwcom.
  induction He;
    try (inversion Heqwcom); subst; clear Heqwcom.
  - (* E_WhileFalse *) 
    split. assumption. apply bexp_eval_false. assumption.
  - (* E_WhileTrue *)
    apply IHHe2. reflexivity.
    apply (Hhoare st st'). assumption.
      split. assumption. apply bexp_eval_true. assumption.
Qed.

(*TODO*)

Lemma loop_skip :  forall (n:aexp) (st:state),
  st =[ LOOP n DO SKIP END ]=> st.

Proof.
  intro. induction n.
  - intro. induction n.  
    + eapply E_LoopZero. reflexivity.
    + eapply E_LoopMore. 
      apply E.
  -  eapply E_LoopMore. apply E. apply gt_Sn_O.
    apply E_Skip.     
    simpl. 

    apply IHn0. (* why the implication in IHn0? Don't we simply assume st =[ LOOP n DO SKIP END ]=> st?
                    clearly via E,  aeval st n = n0 !=  aeval st n = S n0 *)



Lemma loop : forall  (v:nat) (n:aexp) (st:state) (c:com) , st =[ LOOP n DO c END ]=> st ->
              aeval st n = v
              -> st =[ LOOP (ANum v) DO c END ]=> st.
Proof.
  induction v.
  - intros. eapply E_LoopZero;auto.
  - induction n.
    + intros. simpl in H0. rewrite H0 in H. apply H.
    + intros.  eapply E_LoopMore in H.
      ;auto.  apply gt_Sn_O.
      apply E_Skip. 
      simpl. apply IHv. apply H.
      
      simpl.   simpl in H0. rewrite H0 in H. apply H.
    eapply E_LoopMore;auto.
    apply gt_Sn_O. apply E_Skip. 
    simpl. eapply IHv. apply H.
    


Example ex4 : forall P X,  {{P}} LOOP X DO SKIP END {{P}}.

Proof.
  intros. intros st st' cmd H. induction (aeval st X0) eqn:E.
  - assert (st = st'). eapply E_LoopZero in E.
  { eapply ceval_deterministic. apply E. apply cmd. }
  rewrite <- H0. apply H.
  - eapply E_LoopMore in E.
    + assert (st' = st). { eapply ceval_deterministic. apply cmd. apply E. }
    rewrite H0. apply H.
    + apply gt_Sn_O.
    + apply E_Skip.
    + simpl.  


(*E_LoopMore : forall st st' st'' a c v,
      aeval st a = v ->
      v > 0 ->
    st =[ c ]=> st' -> 
    st' =[ LOOP (pred v) DO c END ]=> st'' ->
    st =[ LOOP a DO c END ]=> st''*)


Theorem hoare_loop : forall P e c,
  {{P}} c {{P}} ->
  {{P}} LOOP e DO c END {{P}}.
Proof.
  intros. intros st st' cmd H'. unfold hoare_triple in H.
  induction (aeval st e) eqn:E.
  - assert (st = st').
    { eapply ceval_deterministic. apply (E_LoopZero st e c) in E. apply E. apply cmd. }
    rewrite <- H0. apply H'.
  - eapply E_LoopMore in E.
    + admit.  
    + apply gt_Sn_O.
    + 


Theorem hoare_loop : forall P e c t,
  (forall z, {{fun st => P st /\ (st t) = z}} c;; t ::= t - 1 {{fun st => P st /\ st t = (z - 1)}}) ->
  {{fun st => P st /\ st t = e}} LOOP e DO c END {{fun st => P st /\ (st t) = 0}}.

Proof.
  intros. intros st st' cmd H'. induction e eqn:E.
  - assert (st = st'). { eapply ceval_deterministic. -

Proof. 
  intros. intros st st' cmd H'. remember (LOOP e DO c END)%imp as cmd'.
  induction cmd; try (inversion Heqcmd'); subst; clear Heqcmd'.
  - apply H'.
  - apply (E_LoopMore st st' st'' e c)in H0 .
    + 

    + apply cmd1. 
    + apply cmd2.




