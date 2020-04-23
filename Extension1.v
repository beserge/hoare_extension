
Set Warnings "-notation-overridden,-parsing".

From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
Import ListNotations.
(*Require Import Maps. *)

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

Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
    (x !-> v ; m) x = v.
Proof.
  Admitted. 

Theorem t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
    x1 <> x2 ->
    (x1 !-> v ; m) x2 = m x2.
Proof.
Admitted.

Lemma t_update_shadow : forall (A : Type) (m : total_map A) x v1 v2,
    (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof.
Admitted.

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
Definition T : string := "T".


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

(*
st =[ LOOP a DO c END ]=> st' iff st=[ c;c;...;c] => st'
where c is composed (eval st a) times.
*)

Example ex1: forall x c, (x) =[ LOOP (ANum 0) DO c END ]=> (x).

Proof.
  intros. apply E_LoopZero. reflexivity.
Qed.

Example ex2: (X !-> 0; empty_st) =[ LOOP (ANum 4) DO X ::= (AId X) + (ANum 1) END ]=> (X !-> 4; X !-> 3; X !-> 2; X !-> 1; X !-> 0; empty_st).

Proof.  
  repeat
   (try (eapply E_LoopMore; try reflexivity; try apply le_plus_l; try (apply E_Ass; reflexivity));  
   try (apply E_LoopZero; reflexivity)). 
 Qed. 


Example ex3: (X !-> 4; empty_st) =[ LOOP (AId X) DO X ::= (AId X) + (ANum 1) END ]=> (X !-> 8; X !-> 7; X !-> 6; X !-> 5; X !-> 4; empty_st).
Proof.
  repeat
   (try (eapply E_LoopMore; try reflexivity; try apply le_plus_l; try (apply E_Ass; reflexivity));  
   try (apply E_LoopZero; reflexivity)). 
 Qed. 

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


Theorem hoare_if : forall P Q b c1 c2,
  {{fun st => P st /\ bassn b st}} c1 {{Q}} ->
  {{fun st => P st /\ ~ (bassn b st)}} c2 {{Q}} ->
  {{P}} TEST b THEN c1 ELSE c2 FI {{Q}}.
Proof.
  intros P Q b c1 c2 HTrue HFalse st st' HE HP.
  inversion HE; subst.
  - (* b is true *)
    apply (HTrue st st').
      assumption.
      split. assumption.
      apply bexp_eval_true. assumption.
  - (* b is false *)
    apply (HFalse st st').
      assumption.
      split. assumption.
      apply bexp_eval_false. assumption. Qed.


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

Lemma loop_zero: forall st st' c,
  st =[ LOOP (ANum 0) DO c END ]=> st' ->
  st= st'.

Proof.
 intros. assert (aeval st (ANum 0) = 0). reflexivity. 
 eapply E_LoopZero in H0. eapply ceval_deterministic.
 apply H0. apply H.
Qed.

Lemma loop_skip_ANum : forall n st, 
   st =[ LOOP (ANum n) DO SKIP END ]=> st.

Proof.
  intros. induction n.
  - eapply E_LoopZero. reflexivity.
  - eapply E_LoopMore. reflexivity.
    apply gt_Sn_O. apply E_Skip.
    apply IHn.
Qed.

Lemma aexp_loop : forall c a st st',
  st =[ LOOP ANum (aeval st a) DO c END ]=> st' <-> st =[ LOOP a DO c END ]=> st'.

Proof.
  intros. split. - intros. inversion H.
  + subst. simpl in H4. eapply E_LoopZero in H4. apply H4.
  + subst. simpl in H7. simpl in H3. remember (aeval st a).
    apply Nat.eq_sym_iff in Heqn. eapply E_LoopMore in Heqn.
    * apply Heqn.
    * apply H3.
    * apply H4.
    * apply H7.
  - intros. inversion H.
    + subst. rewrite H4. eapply E_LoopZero. reflexivity.
    + subst. remember (aeval st a). eapply E_LoopMore.
      * apply Heqn.
      * rewrite <- Heqn. apply H3.
      * apply H4.
      * simpl. rewrite <- Heqn. apply H7.
Qed.

Theorem loop_skip_general :  forall (n:aexp) (st:state),
  st =[ LOOP n DO SKIP END ]=> st.

Proof.
  intros. induction n eqn:E;
  try (apply aexp_loop; apply loop_skip_ANum).
Qed.


Lemma loop : forall  (v:nat) (n:aexp) (st st':state) (c:com) , st =[ LOOP n DO c END ]=> st' ->
              aeval st n = v
              -> st =[ LOOP (ANum v) DO c END ]=> st'.

Proof.
  intros. rewrite <- H0. apply aexp_loop. apply H.
Qed. 

Example ex4 : forall P X,  {{P}} LOOP X DO SKIP END {{P}}.

Proof.
  intros P e st st' H H'. assert (st' = st).
  { eapply ceval_deterministic. apply H. apply loop_skip_general. }
  rewrite H0. apply H'.
Qed.


Lemma hoare_loop_ANum : forall P n c, 
  {{P}} c {{P}} ->
  {{P}} LOOP (ANum n) DO c END {{P}}.

Proof.
  intros. induction n. 
    + intros st st' H' H0. apply loop_zero in H'. rewrite <- H'. apply H0.
    + unfold hoare_triple. intros.
    unfold hoare_triple in H. unfold hoare_triple in IHn.
    remember (aeval st (ANum (S n))). 
    apply Nat.eq_sym_iff in Heqn0. inversion H0.
    * subst. apply H1.
    * subst. simpl in H9. eapply IHn. apply H9. eapply H.
    { apply H6. }
    { apply H1. }
Qed.

Theorem hoare_loop_simple : forall P e c,
  {{P}} c {{P}} ->
  {{P}} LOOP e DO c END {{P}}.

(*TODO automate this proof, too repetitive*)

Proof. 
  intros.
  induction e.
  - apply hoare_loop_ANum. apply H.
  - unfold hoare_triple. intros. apply aexp_loop in H0.
    remember (aeval st (AId x)). eapply hoare_loop_ANum. apply H.
    apply H0. apply H1.
  - unfold hoare_triple. intros. apply aexp_loop in H0.
    remember (aeval st (e1 + e2)). eapply hoare_loop_ANum. apply H.
    apply H0. apply H1.
  - unfold hoare_triple. intros. apply aexp_loop in H0.
    remember (aeval st (e1 - e2)). eapply hoare_loop_ANum. apply H.
    apply H0. apply H1.
  - unfold hoare_triple. intros. apply aexp_loop in H0.
    remember (aeval st (e1 * e2)). eapply hoare_loop_ANum. apply H.
    apply H0. apply H1. 
Qed.


Example ex5 : forall P X,  {{P}} LOOP X DO SKIP END {{P}}.

Proof.
  intros. apply hoare_loop_simple. apply hoare_skip.
Qed.


Theorem hoare_loop : forall a P c t ,
    (forall z, {{P  [ t |-> (ANum z)]}}
                 c
               {{P  [ t |-> (ANum(z - 1))]}})
    ->
    {{P [  t |-> (ANum a) ]}}
      LOOP (ANum a) DO c END
    {{P [t |-> (ANum 0)]}}.

Proof.
  intros a. induction a.
  - intros. unfold hoare_triple. intros. apply loop_zero in H0. rewrite <- H0. apply H1.
  - intros. unfold hoare_triple. intros. inversion H0; subst.
    + inversion H6.
    + simpl in H9. eapply H in H6. apply IHa in H. unfold hoare_triple in H. eapply H.
      * apply H9.
      * apply H6 in H1. simpl in H1. rewrite Nat.sub_0_r in H1. apply H1.
Qed.

(*
Theorem hoare_loop1 : forall a P c ,
    (forall z, {{fun st => P st /\    st T = z}}
                 c
               {{fun st => P st /\  st T =z - 1}})
    ->
    {{fun st => P st /\   st T = aeval st a  }}
      LOOP a DO c END
    {{fun st => P st /\  st T = 0}}.
Proof.
admit.
  (*intros a. induction a.
  -eapply hoare_loop.
  -intros. apply
*)
Admitted.
*)



Definition prog1 :=
{{ (fun st => st X + st T = 4) [ T |->  ANum 4] }}
            (CLoop (ANum 4)
               (CSeq
                 (CAss   X (APlus (AId X) (ANum 1)))            
                 (CAss  T  (AMinus (AId T) (ANum 1)))
               )
               )
{{ (fun st =>  st X + st T = 4) [T |-> ANum 0]}}             
.


Lemma lemma_aux_prog1 : forall z,
{{(fun st => st X + st T = 4) [ T |->  ANum z] }}
(CSeq (CAss   X (APlus (AId X) (ANum 1))) (CAss  T  (AMinus (AId T) (ANum 1))))
{{(fun st => st X + st T = 4) [ T |->  ANum (z-1)] }}
.
Proof.
  induction z.
  - simpl. apply hoare_seq with (Q:= (fun st => st X + st T = 3 )[ T |->  ANum 0]).
    + apply hoare_consequence_pre with (P':= (fun st : string -> nat => st X + st T = 4) [T |-> ANum 0] [T |-> AId T- ANum 1] ). apply hoare_asgn. unfold assert_implies.
      admit.
    + apply hoare_consequence_pre with (P':= (fun st : string -> nat => st X + st T = 3) [T |-> ANum 0] [X |-> AId X+ ANum 1] ). apply hoare_asgn. unfold assert_implies.
      intros. unfold assn_sub in H. simpl in H. rewrite t_update_eq in H. assert (T <> X). { admit. }
      eapply t_update_neq in H0. rewrite H0 in H.
      unfold assn_sub; simpl. rewrite t_update_eq.
      assert (T <> X). { admit. } eapply t_update_neq in H1. rewrite H1. rewrite t_update_eq. admit. (* Problem here *)
  - simpl. apply hoare_seq with (Q:= (fun st => st X + st T = 3 )[ T |->  ANum (z-0)]).
    + apply
        hoare_consequence_pre with (P':= (fun st : string -> nat => st X + st T = 4) [T |-> ANum (z-0)] [T |-> AId T- ANum 1] ). apply hoare_asgn. unfold assert_implies.
      admit.
     + apply hoare_consequence_pre with (P':= (fun st : string -> nat => st X + st T = 3) [T |-> ANum (z-0)] [X |-> AId X+ ANum 1] ). apply hoare_asgn. unfold assert_implies.
      admit.
Admitted.


Theorem prog1_proof :
  prog1.
Proof.
  unfold prog1.
  apply hoare_loop.   
  apply lemma_aux_prog1. 
Qed.

(* Undecorated Examples *)

(* Multiplication *)

(* 

forall x,y

{ X = 0 }
LOOP y DO
X := X + x
END.
{ X = x*y }

*)

Theorem loop_mult :
{{ (fun st => st X  = (4 - aeval st (AId T)) * 3) [ T |-> ANum 4] }} 
LOOP ANum 4 DO
X ::= AId X + ANum 3;;
T ::= AId T - ANum 1
END
{{ (fun st => st X = (4 - (aeval st (AId T))) * 3) [T |-> ANum 0] }}.
(* ->> { st X = 3 * 4 } *)

Proof.
  intros. apply hoare_loop. induction z.
  -  admit. (* unfold assn_sub. simpl. eapply hoare_seq.
    + apply hoare_asgn.
    + eapply hoare_asgn. *)
  - unfold assn_sub. simpl.
  Admitted.

Theorem loop_factorial :
(* X ::= 1;; *)
{{ (fun st => st X  = fact (5 - st T)) [ T |-> ANum 4] }} 
LOOP ANum 4 DO
X ::= AId X * (ANum 5 - AId T);;
T ::= AId T - ANum 1
END
{{ (fun st => st X  = fact (5 - st T)) [T |-> ANum 0] }}.

Proof.
  Admitted.

(*
 forall z. {{P /\ t=z}} c {{P /\ t=z-1}}.
---------------------------------
 {{P /\ t=e }} LOOP e DO c END {{P} /\ t=0 }.
*)


(*
forall st_k, k<= 4
st_k[t->k]  X:=X+1;; t=t-1 st_k'[t->k-1]
  
st  LOOP 4 DO X:=X+1 END st'


st X:=X+1 st_k1 X::X+1 st_k2 X:=X+1 st_k3  X:=X+1 st_k4=st' *)


(*Decorations*)

(*forall r. {{P }} c {{Q}} : Nat -> (Assertion -> dcom ) *)

Inductive dcom : Type :=
  | DCSkip :  Assertion -> dcom
  | DCSeq : dcom -> dcom -> dcom
  | DCAsgn : string -> aexp ->  Assertion -> dcom
  | DCIf : bexp ->  Assertion -> dcom ->  Assertion -> dcom -> Assertion-> dcom
  | DCWhile : bexp -> Assertion -> dcom -> Assertion -> dcom
  | DCLoop  : aexp -> Assertion ->  dcom -> Assertion  -> dcom      (* New *)  
 (* | DCLoop  : aexp -> (nat -> Assertion * Assertion) -> dcom -> Assertion  -> dcom *)
  | DCPre : Assertion -> dcom -> dcom
  | DCPost : dcom -> Assertion -> dcom.
                                    
Inductive    decorated : Type :=
  | Decorated : Assertion -> dcom -> decorated.



(*Definition prog1 :=

( Decorated (fun st => True /\ st T = 4)
            (DCLoop (ANum 4)
                    (fun st => st X + st T = 4 )
             (
               DCSeq
                 (DCAsgn   X (APlus (AId X) (ANum 1))
                           (fun st => st X + st T = 3 ))
                 (DCAsgn  T  (AMinus (AId T) (ANum 1))
                          (fun st => st X + st T = 4  ))
             )
    (fun st => st X + st T= 4 /\ st T= 0)
    )
).
*)
Delimit Scope default with default.

Notation "'SKIP' {{  P  }}"
      := (DCSkip P)
      (at level 10) : dcom_scope.

Notation "l '::=' a {{ P }}"
      := (DCAsgn  l a P)
           (at level 60, a at next level) : dcom_scope.

Notation "'WHILE' b 'DO' {{ Pbody }} d 'END' {{ Ppost }}"
      := (DCWhile b Pbody d Ppost)
      (at level 80, right associativity) : dcom_scope.

Notation "'LOOP' a 'DO' {{ Pbody }}  d 'END' {{ Ppost }}"      (* New *)
  := (DCLoop a Pbody d  Ppost)
  (at level 80, right associativity) : dcom_scope.

Notation "'TEST' b 'THEN' {{ P }} d 'ELSE' {{ P' }} d' 'FI' {{ Q }}"
      := (DCIf b P d P' d' Q)
      (at level 80, right associativity)  : dcom_scope.
Notation "'->>' {{ P }} d"
      := (DCPre P d)
      (at level 90, right associativity)  : dcom_scope.
Notation "d '->>' {{ P }}"
      := (DCPost d P)
      (at level 80, right associativity)  : dcom_scope.
Notation " d ;; d' "
      := (DCSeq d d')
      (at level 80, right associativity)  : dcom_scope.
Notation "{{ P }} d"
      := (Decorated P d)
      (at level 90)  : dcom_scope.

Delimit Scope dcom_scope with dcom.
Open Scope dcom_scope.

Example dec0 :=
  SKIP {{ fun st => True }}.
Example dec1 :=
  WHILE (BTrue) DO {{ fun st => True }} SKIP {{ fun st => True }} END
  {{ fun st => True }}.

Example dec2 :=
  LOOP (ANum(4)) DO {{fun st => True}}  SKIP {{ fun st => True }}   END
  {{ fun st => True }}.


Set Printing All.

Example dec_while : decorated :=
  {{ fun st => True }} 
  WHILE ~(AId X = ANum 0)
  DO
    {{ fun st => True /\ st X <> 0}}
    X ::= AId X - ANum 1
    {{ fun _ => True }}
  END
  {{ fun st => True /\ st X = 0}} ->>
  {{ fun st => st X = 0 }}.

Example dec_loop : decorated :=
    {{ fun st => st X + st T = 4 }}
      LOOP (ANum(4))
      DO
       {{fun st => st X + st T = 4  }}
      X ::= AId X + ANum 1
      {{  fun st => st X + st T = 4  }}

  {{ fun st => True }} 
  LOOP (ANum(4))
  DO
    {{ fun z => (fun st => st X + st T = 4  /\ st T = z)}}
    X ::= AId X + ANum 1
    {{  fun st => st X + st T = 4  /\ st T = 1}}
    WITH
    {{ fun z =>  (fun st => st X + st T = 4  /\ st T = z-1)}}

  END
    {{ fun st => st X + st T = 4  }}                       
.

Example seq_dec (z:nat) : decorated :=
      {{ (fun st => st X + st T = 4  /\ st T = z)}}
      X ::= AId X + ANum 1
      {{  fun st => st X + st T = 4  /\ st T = z}};;
      T ::= AId T - ANum 1
      {{  fun st => st X + st T = 4  /\ st T = z-1}}
.


Example dec_loop_complete : decorated :=
    {{ fun st => st X + st T = 4}}
      LOOP (ANum(4))
      DO
      {{fun st => st X + st T = 4}}
      X ::= AId X + ANum 1
      {{  fun st => st X + st T = 4 }};;
      T ::= AId T - ANum 1
      {{  fun st => st X + st T = 4 }}
  END
    {{fun st => st X + st T = 4  }}                       
.


Set Printing All.
(* Multiplication *)
(*
{True}

X ::= m
Y ::= n

{ X = m * (n - z) /\ (z = (n-1) } ->
{ X = m * 1 }
LOOP X
{ X = m * (n - z}
DO X = X + Y
{ }
END
{ X = m * (n - z) /\ z = 0} ->
{ X = m * n }

Loop invariant:
Something like x = m * (n - z)
*)

Example loop_mult : decorated := 
{{ fun st => True }}
X ::= ANum 4
{{ fun st => True }} ;;
>>>>>>> 724a3ef938ed5e8f78fd5141514245985ca7ed89


(* Multiplication *)


(* Exponentiation (assumes mult)

X ::= m
E ::= n
{True}
{ X = X ^ (E - z) /\ z = (E - 1)}
LOOP E
{ X = X ^ (E -z) }
DO X = X * X
END
{ X = X ^ (E - z) /\ z = 0} ->
{ X = X ^ E }


loop invariant: X = X ^ (E - Z)
*)


(* Tetration (assumes exp.) 
X ::= m
B ::= X
E ::= n
{True}
{ X = m }
LOOP E
DO X = B ^ X
END
{ X = X ^^ E }

*)

(* bitwise OR (Coq binary?)

*)


(** It is easy to go from a [dcom] to a [com] by erasing all
    annotations. *)

Fixpoint extract (d : dcom) : com :=
  match d with
  | DCSkip _           => SKIP
  | DCSeq d1 d2        => (extract d1 ;; extract d2)
  | DCAsgn X a _       => X ::= a
  | DCIf b _ d1 _ d2 _ => TEST b THEN extract d1 ELSE extract d2 FI
  | DCWhile b _ d _    => WHILE b DO extract d END
  | DCLoop  a _ d _     => CLoop a (extract d)
  | DCPre _ d          => extract d
  | DCPost d _         => extract d
  end.

Definition extract_dec (dec : decorated) : com :=
  match dec with
  | Decorated P d => extract d
  end.

Fixpoint post (d : dcom) : Assertion :=
  match d with
  | DCSkip P                => P
  | DCSeq d1 d2             => post d2
  | DCAsgn X a Q            => Q
  | DCIf  _ _ d1 _ d2 Q     => Q
  | DCWhile b Pbody c Ppost => Ppost
  | DCLoop a  Pbody c Ppost       => Ppost (* New *)
  | DCPre _ d               => post d
  | DCPost c Q              => Q
  end.

Definition pre_dec (dec : decorated) : Assertion :=
  match dec with
  | Decorated P d => P
  end.

Definition post_dec (dec : decorated) : Assertion :=
  match dec with
  | Decorated P d => post d
  end.

Definition dec_correct (dec : decorated) :=
  {{pre_dec dec}} (extract_dec dec) {{post_dec dec}}.

(* TODO *)

Check forall (r:nat), True.

(** ** Extracting Verification Conditions *)

Fixpoint verification_conditions (P : Assertion) (d : dcom) : Prop :=
  match d with
  | DCSkip Q =>
      (P ->> Q)
  | DCSeq d1 d2 =>
      verification_conditions P d1
      /\ verification_conditions (post d1) d2
  | DCAsgn X a Q =>
      (P ->> Q [X |-> a])
  | DCIf b P1 d1 P2 d2 Q =>
      ((fun st => P st /\ bassn b st) ->> P1)
      /\ ((fun st => P st /\ ~ (bassn b st)) ->> P2)
      /\ (post d1 ->> Q) /\ (post d2 ->> Q)
      /\ verification_conditions P1 d1
      /\ verification_conditions P2 d2
  | DCWhile b Pbody d Ppost =>
      (* post d is the loop invariant and the initial
         precondition *)
      (P ->> post d)
      /\ ((fun st => post d st /\ bassn b st) ->> Pbody)
      /\ ((fun st => post d st /\ ~(bassn b st)) ->> Ppost)
      /\ verification_conditions Pbody d
  | DCLoop a Pbody d Ppost => forall r,   
    ((fun st => P st) ->> (fun st => Pbody st /\ st T = aeval st a))
    /\ ((fun st => Pbody st /\  st T = r ) ->> Pbody)
    /\ ((fun st => Pbody st /\  st T = 0 ) ->> Ppost)
      /\ (post d ->>(fun st => Pbody st /\  st T = r-1 ))
      /\ verification_conditions Pbody d
  | DCPre P' d =>
      (P ->> P') /\ verification_conditions P' d
  | DCPost d Q =>
      verification_conditions P d /\ (post d ->> Q)
  end.

Theorem verification_correct : forall d P,
  verification_conditions P d -> {{P}} (extract d) {{post d}}.
Proof.
  induction d; intros P H; simpl in *.
  - (* Skip *)
    eapply hoare_consequence_pre.
      apply hoare_skip.
      assumption.
  - (* Seq *)
    destruct H as [H1 H2].
    eapply hoare_seq.
      apply IHd2. apply H2.
      apply IHd1. apply H1.
  - (* Asgn *)
    eapply hoare_consequence_pre.
      apply hoare_asgn.
      assumption.
  - (* If *)
    destruct H as [HPre1 [HPre2 [Hd1 [Hd2 [HThen HElse]]]]].
    apply IHd1 in HThen. clear IHd1.
    apply IHd2 in HElse. clear IHd2.
    apply hoare_if.
      + eapply hoare_consequence_post with (Q':=post d1); eauto.
         eapply hoare_consequence_pre; eauto.
      + eapply hoare_consequence_post with (Q':=post d2); eauto.
         eapply hoare_consequence_pre; eauto.
  - (* While *)
    destruct H as [Hpre [Hbody1 [Hpost1  Hd]]].
    eapply hoare_consequence_pre; eauto.
    eapply hoare_consequence_post; eauto.
    apply hoare_while.
    eapply hoare_consequence_pre; eauto.
  - (* Loop *)
    eapply hoare_consequence_pre; eauto.
    eapply hoare_consequence_post; eauto.
    apply hoare_loop1;auto.  intro.
    destruct (H z) as [Hpre [Hbody1 [Hpost1 [Hpost2 Hd]]]]; auto.
    eapply hoare_consequence_pre; eauto.
    eapply hoare_consequence_post;  eauto.
    destruct (H 0) as [Hpre [Hbody1 [Hpost1 [Hpost2 Hd]]]]; auto.
    destruct (H 0) as [Hpre [Hbody1 [Hpost1 [Hpost2 Hd]]]]; auto.
  -  (* Pre *)
    destruct H as [HP Hd].
    eapply hoare_consequence_pre. apply IHd. apply Hd. assumption.
  - (* Post *)
    destruct H as [Hd HQ].
    eapply hoare_consequence_post. apply IHd. apply Hd. assumption.
Qed.


Definition verification_conditions_dec (dec : decorated) : Prop :=
  match dec with
  | Decorated P d => verification_conditions P d
  end.

Lemma verification_correct_dec : forall dec,
  verification_conditions_dec dec -> dec_correct dec.
Proof.
  intros [P d]. apply verification_correct.
Qed.

(** The propositions generated by [verification_conditions] are fairly
    big, and they contain many conjuncts that are essentially trivial. *)

Eval simpl in (verification_conditions_dec dec_while).
(**

   ===>
    (((fun _ : state => True) ->> (fun _ : state => True)) /\
     ((fun st : state => True /\ bassn (~(X = 0)) st) ->>
      (fun st : state => True /\ st X <> 0)) /\
     ((fun st : state => True /\ ~ bassn (~(X = 0)) st) ->>
      (fun st : state => True /\ st X = 0)) /\
      (fun st : state => True /\ st X <> 0) ->>
      (fun _ : state => True) [X |-> X - 1]) /\
      (fun st : state => True /\ st X = 0) ->> 
      (fun st : state => st X = 0)   
*)

(** In principle, we could work with such propositions using just the
    tactics we have so far, but we can make things much smoother with
    a bit of automation.  We first define a custom [verify] tactic
    that uses [split] repeatedly to turn all the conjunctions into
    separate subgoals and then uses [omega] and [eauto] (described in
    chapter [Auto] in _Logical Foundations_) to deal with as many
    of them as possible. *)

Tactic Notation "verify" :=
  apply verification_correct;
  repeat split;
  simpl; unfold assert_implies;
  unfold bassn in *; unfold beval in *; unfold aeval in *;
  unfold assn_sub; intros;
  repeat rewrite t_update_eq;
  repeat (rewrite t_update_neq; [| (intro X; inversion X)]);
  simpl in *;
  repeat match goal with [H : _ /\ _ |- _] => destruct H end;
  repeat rewrite not_true_iff_false in *;
  repeat rewrite not_false_iff_true in *;
  repeat rewrite negb_true_iff in *;
  repeat rewrite negb_false_iff in *;
  repeat rewrite eqb_eq in *;
  repeat rewrite eqb_neq in *;
  repeat rewrite leb_iff in *;
  repeat rewrite leb_iff_conv in *;
  try subst;
  repeat
    match goal with
      [st : state |- _] =>
        match goal with
          [H : st _ = _ |- _] => rewrite -> H in *; clear H
        | [H : _ = st _ |- _] => rewrite <- H in *; clear H
        end
    end;
  try eauto; try omega.

(** What's left after [verify] does its thing is "just the interesting
    parts" of checking that the decorations are correct. For very
    simple examples, [verify] sometimes even immediately solves the
    goal (provided that the annotations are correct!). *)

Theorem dec_while_correct :
  dec_correct dec_while.
Proof. verify.
       admit. admit. 
Admitted.

Theorem dec1_correct :
  dec_correct (Decorated (fun st => True) dec1).
Proof. verify.
Qed.

Example dec3 (r:nat) :=
  LOOP (ANum(4)) DO {{fun st => st T =r }}  T::= (AId T) - (ANum 1) {{ fun st => st T= r-1}}   END
  {{ fun st => True }}.


Theorem dec2_correct : forall r,
  dec_correct (Decorated (fun st => True /\ st T =4) (dec3 r)).
Proof. intro. verify.
admit. 
Qed.


(** Another example (formalizing a decorated program we've seen
    before): *)

Example subtract_slowly_dec (m : nat) (p : nat) : decorated :=
    {{ fun st => st X = m /\ st Z = p }} ->>
    {{ fun st => st Z - st X = p - m }}
  WHILE ~(X = 0)
  DO   {{ fun st => st Z - st X = p - m /\ st X <> 0 }} ->>
       {{ fun st => (st Z - 1) - (st X - 1) = p - m }}
     Z ::= Z - 1
       {{ fun st => st Z - (st X - 1) = p - m }} ;;
     X ::= X - 1
       {{ fun st => st Z - st X = p - m }}
  END
    {{ fun st => st Z - st X = p - m /\ st X = 0 }} ->>
    {{ fun st => st Z = p - m }}.

Theorem subtract_slowly_dec_correct : forall m p,
  dec_correct (subtract_slowly_dec m p).
Proof. intros m p. verify. (* this grinds for a bit! *) Qed.

(* ================================================================= *)
(** ** Examples *)

(** In this section, we use the automation developed above to verify
    formal decorated programs corresponding to most of the informal
    ones we have seen. *)

(* ----------------------------------------------------------------- *)
(** *** Swapping Using Addition and Subtraction *)

Definition swap : com :=
  X ::= X + Y;;
  Y ::= X - Y;;
  X ::= X - Y.

Definition swap_dec m n : decorated :=
   {{ fun st => st X = m /\ st Y = n}} ->>
   {{ fun st => (st X + st Y) - ((st X + st Y) - st Y) = n
                /\ (st X + st Y) - st Y = m }}
  X ::= X + Y
   {{ fun st => st X - (st X - st Y) = n /\ st X - st Y = m }};;
  Y ::= X - Y
   {{ fun st => st X - st Y = n /\ st Y = m }};;
  X ::= X - Y
   {{ fun st => st X = n /\ st Y = m}}.

Theorem swap_correct : forall m n,
  dec_correct (swap_dec m n).
Proof. intros; verify. Qed.

(* ----------------------------------------------------------------- *)
(** *** Simple Conditionals *)

Definition if_minus_plus_com :=
  (TEST X <= Y
    THEN Z ::= Y - X
    ELSE Y ::= X + Z
  FI)%imp.

Definition if_minus_plus_dec :=
  {{fun st => True}}
  TEST X <= Y  THEN
      {{ fun st => True /\ st X <= st Y }} ->>
      {{ fun st => st Y = st X + (st Y - st X) }}
    Z ::= Y - X
      {{ fun st => st Y = st X + st Z }}
  ELSE
      {{ fun st => True /\ ~(st X <= st Y) }} ->>
      {{ fun st => st X + st Z = st X + st Z }}
    Y ::= X + Z
      {{ fun st => st Y = st X + st Z }}
  FI
  {{fun st => st Y = st X + st Z}}.

Theorem if_minus_plus_correct :
  dec_correct if_minus_plus_dec.
Proof. verify. Qed.

Definition if_minus_dec :=
  {{fun st => True}}
  TEST X <= Y THEN
      {{fun st => True /\ st X <= st Y }} ->>
      {{fun st => (st Y - st X) + st X = st Y
               \/ (st Y - st X) + st Y = st X}}
    Z ::= Y - X
      {{fun st => st Z + st X = st Y \/ st Z + st Y = st X}}
  ELSE
      {{fun st => True /\ ~(st X <= st Y) }} ->>
      {{fun st => (st X - st Y) + st X = st Y
               \/ (st X - st Y) + st Y = st X}}
    Z ::= X - Y
      {{fun st => st Z + st X = st Y \/ st Z + st Y = st X}}
  FI
    {{fun st => st Z + st X = st Y \/ st Z + st Y = st X}}.

Theorem if_minus_correct :
  dec_correct if_minus_dec.
Proof. verify. Qed.

(* ----------------------------------------------------------------- *)
(** *** Division *)

Definition div_mod_dec (a b : nat) : decorated :=
  {{ fun st => True }} ->>
  {{ fun st => b * 0 + a = a }}
  X ::= a
  {{ fun st => b * 0 + st X = a }};;
  Y ::= 0
  {{ fun st => b * st Y + st X = a }};;
  WHILE b <= X DO
    {{ fun st => b * st Y + st X = a /\ b <= st X }} ->>
    {{ fun st => b * (st Y + 1) + (st X - b) = a }}
    X ::= X - b
    {{ fun st => b * (st Y + 1) + st X = a }};;
    Y ::= Y + 1
    {{ fun st => b * st Y + st X = a }}
  END
  {{ fun st => b * st Y + st X = a /\ ~(b <= st X) }} ->>
  {{ fun st => b * st Y + st X = a /\ (st X < b) }}.

Theorem div_mod_dec_correct : forall a b,
  dec_correct (div_mod_dec a b).
Proof. intros a b. verify.
  rewrite mult_plus_distr_l. omega.
Qed.
