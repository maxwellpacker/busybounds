From BusyCoq Require Import Bounds.Definitions.
From BusyCoq Require Import Individual992.
From Coq Require Import Lia.

Lemma mstep0_refl: forall tm c c',
  c = c' ->
  c -[ tm ]->> 0 / c'.
Proof. intros. subst c'. auto. Qed.

Lemma mstep_refl: forall tm c1 c1' n1 c2 c2' n2,
  c1 -[ tm ]->> n1 / c1' ->
  c1 = c2 ->
  c1' = c2' ->
  n1 = n2 ->
  c2 -[ tm ]->> n2 / c2'.
Proof. intros. subst c1. subst c1'. subst n1. auto. Qed.

Ltac finish_mstep := apply mstep0_refl; try (reflexivity || lia_refl).

Ltac mydo x tac :=
  match x with
  | O => idtac
  | S ?n => (tac) ; (mydo n tac)
  end.

Ltac mstep1 := eapply multistep_S; [prove_step | simpl_tape].

Ltac mstep n := mydo n mstep1; try finish_mstep.

Ltac mstep_apply H :=
  match type of H with
  | ?a -[ ?b ]->> ?c / ?d =>
    apply mstep_refl with (c1 := a) (tm := b) (n1 := c) (c1' := d); auto
  | _ => idtac "mstep_apply failed"
  end.

Ltac mstep_apply_safe H :=
  match type of H with
  | ?a -[ ?b ]->> ?c / ?d =>
    apply mstep_refl with (c1 := a) (tm := b) (n1 := c) (c1' := d)
  | _ => idtac "mstep_apply_safe failed"
  end.

Lemma mstep_trans : forall tm x y z c c' c'',
  x + y = z ->
  c  -[ tm ]->> x / c' ->
  c' -[ tm ]->> y / c'' ->
  c  -[ tm ]->> z / c''.
Proof.
  intros. rewrite <- H. apply multistep_trans with (c' := c'); auto.
Qed.

Ltac mstep_split n1 n2 :=
  match goal with
  | |- ?C -[ ?TM ]->> ?N / ?C'' =>
    eapply mstep_trans with (tm := TM) (c := C) (c'' := C'') (x := n1) (y := n2) (z := N); try lia
  | _ => idtac "mstep_split failed"
  end.

Lemma halts_in_add:
  forall tm c x y z c',
  x + y = z ->
  c -[ tm ]->> x / c' ->
  halts_in_correct tm c' y ->
  halts_in_correct tm c z.
Proof.
  intro tm0. intro c. induction x.
  * intros. assert (c = c').
    + assert (c -[ tm0 ]->> 0 / c). auto.
      apply multistep_deterministic with (tm := tm0) (n := O) (c := c); auto.
    + assert (z = y). auto. rewrite H2. rewrite H3. auto.
  * intros. apply multistep_last in H0. inversion H0. specialize (IHx (S y) z x0). apply IHx.
    + lia.
    + apply H2.
    + unfold halts_in_correct in H1. cases y.
      - contradiction.
      - unfold halts_in_correct. unfold halts_in. unfold halts_in in H1. inversion H1.
        assert (x0 -[ tm0 ]->> S TEMP / x1 /\ halted tm0 x1).
        -- split.
          --- mstep_split (S O) TEMP. apply multistep_S with (c' := c').
              apply H2. finish_mstep. apply H3.
          --- apply H3.
        -- exists x1. auto.
Qed.