From BusyCoq Require Import Bounds.
From BusyCoq Require Import Individual992.
From BusyCoq Require Import FGH.
From Coq Require Import Lia.
From Coq Require Import NArith.

Definition tm : TM := fun '(q, s) =>
  match q, s with
  | Q00, 0 => Some (1, R, Q01)  | Q00, 1 => Some (1, L, Q02)
  | Q01, 0 => Some (1, R, Q02)  | Q01, 1 => Some (1, R, Q01)
  | Q02, 0 => Some (1, R, Q03)  | Q02, 1 => Some (0, L, Q04)
  | Q03, 0 => Some (1, L, Q00)  | Q03, 1 => Some (1, L, Q03)
  | Q04, 0 => None              | Q04, 1 => Some (0, L, Q00)
  | _, _ => None
  end.

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Notation "c -->> c' = n" := (c -[ tm ]->> n / c') (at level 40, c' at next level).
Notation "c -->> c' <= n" := (exists n', and (n' <= n) (c -[ tm ]->> n / c')) (at level 40, c' at next level).
Notation "c -->> c' >= n" := (exists n', and (n' >= n) (c -[ tm ]->> n / c')) (at level 40, c' at next level).

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
  | ?a -->> ?b = ?c =>
    apply mstep_refl with (c1 := a) (c1' := b) (n1 := c); auto
  | _ => idtac "mstep_apply failed"
  end.

Ltac mstep_apply_safe H :=
  match type of H with
  | ?a -->> ?b = ?c =>
    apply mstep_refl with (c1 := a) (c1' := b) (n1 := c)
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

Lemma rule_BR:
  forall n l r, l {{Q01}}> [1]^^n *> r -->> l <* [1]^^n {{Q01}}> r = n.
Proof.
  induction n; introv.
  - apply multistep_0.
  - apply multistep_S with (c' := l <* [1] {{Q01}}> [1]^^n *> r).
    * prove_step.
    * specialize (IHn (l <* [1]) r).
      rewrite lpow_S. rewrite <- lpow_shift. rewrite Str_app_assoc. apply IHn.
Qed.

Lemma rule_DL:
  forall n l r, l <* [1]^^n <{{Q03}} r -->> l <{{Q03}} [1]^^n *> r = n.
Proof.
  induction n; introv.
  - apply multistep_0.
  - apply multistep_S with (c' := l <* [1]^^n <{{Q03}} [1] *> r).
    * prove_step.
    * specialize (IHn l ([1] *> r)).
      rewrite lpow_S. rewrite <- lpow_shift. rewrite Str_app_assoc. apply IHn.
Qed.

Definition counter_right n := [0; 0; 1]^^n *> [1] *> const 0.
Definition counter m n := (const 0 <* [1]^^m <{{Q03}} (counter_right n)).

Lemma counter_dec:
  forall x y, counter x (S y) -->> counter (x + 5) y = (2 * x + 5).
Proof.
  intros. mstep_split x (x + 5).
  - apply rule_DL.
  - mstep_split 2 (x + 3).
    * mstep 2.
    * mstep_split (x + 1) 2.
      + specialize (rule_BR (x+1) (const 0 << 1) (counter_right (S y))). intros. mstep_apply H.
      assert (x+1 = S x). lia. rewrite H0. auto.
      + mstep 2.
      assert ([1]^^(x+5) *> const 0 = 1 >> 1 >> 1 >> 1 >> [1] ^^x *> 1 >> const 0).
        ++ induction x. auto. assert (S x + 5 = S (x + 5)). auto. rewrite H.
           rewrite lpow_S. rewrite lpow_S. rewrite Str_app_assoc. rewrite Str_app_assoc.
           assert ([1] ^^ (x + 5) *> const 0 = 1 >> 1 >> 1 >> 1 >> [1] ^^ x *> 1 >> const 0).
           apply IHx. rewrite H0. reflexivity.
        ++ unfold counter. rewrite H. auto.
Qed.

Lemma counter_total:
  forall y x, counter x y -->> counter (x + 5 * y) 0 = (y * (2*x + 5*y)).
Proof.
  induction y.
  - intros. finish_mstep.
  - intros. assert ((2 * x + 5 + y * (2 * (x+5) + 5 * y)) = (S y * (2 * x + 5 * S y))).
    * lia.
    * rewrite <- H. apply multistep_trans with (c' := counter (x + 5) y)
                            (n := (2 * x + 5)) (m := (y * (2 * (x+5) + 5 * y))).
      + apply counter_dec.
      + specialize (IHy (x+5)). assert (x+5*S y = x + 5 + 5 * y). lia. rewrite H0. apply IHy.
Qed.

Definition rightside n := const 0 <* [1]^^n {{Q03}}> const 0.

Lemma counter_reset:
  forall x, counter x 0 -->> rightside (x+5) = (2 * x + 6).
Proof.
  intros. mstep_split x (x + 6).
  - apply rule_DL.
  - mstep_split 2 (x + 4).
    * mstep 2.
    * mstep_split (x + 2) 2.
      + specialize (rule_BR (x+2) (const 0 << 1) (const 0)). intros. mstep_apply H.
        unfold counter_right. assert ((x + 2) = S (x + 1)). lia. rewrite H0. rewrite lpow_S.
        assert ([0; 0; 1]^^0 = [1]^^0). reflexivity. rewrite H1. rewrite <- Str_app_assoc.
        rewrite <- lpow_shift. rewrite <- lpow_add. rewrite Str_app_assoc. assert (x+1=S x). lia.
        rewrite H2. rewrite lpow_S. assert (x + 0 = x). lia. rewrite H3. reflexivity.
      + mstep 2. unfold rightside. assert (x+5 = S (S (S (S (S x))))). lia. rewrite H.
        do 5 (rewrite lpow_S). do 5 (rewrite Str_app_assoc). do 3 (rewrite <- lpow_shift').
        reflexivity.
Qed.

Lemma counter_initcycle:
  forall x y, const 0 <* [1]^^(x+3) <{{Q00}} (counter_right y)
         -->> const 0 <* [1]^^x <{{Q00}} (counter_right (S y)) = 3.
Proof.
  intros. assert (x + 3 = S (S (S x))). lia. rewrite H. unfold counter_right.
  do 4 (rewrite lpow_S). mstep 3.
Qed.

Lemma counter_init:
  forall x y z, const 0 <* [1]^^x <* [1]^^(3 * y) <{{Q00}} (counter_right z)
           -->> const 0 <* [1]^^x <{{Q00}} (counter_right (z + y)) = (3 * y).
Proof.
  induction y.
  * intro z. finish_mstep.
  * intro z. specialize (IHy (S z)). specialize (counter_initcycle (x + 3 * y) z). intros.
    mstep_split 3 (3 * y).
    + mstep_apply H. rewrite <- Str_app_assoc. rewrite <- lpow_add.
      assert (x + 3 * y + 3 = 3 * S y + x). lia. rewrite H0. auto.
    + mstep_apply IHy.
      - rewrite <- Str_app_assoc. rewrite <- lpow_add.
        assert (3 * y + x = x + 3 * y). lia. rewrite H0. auto.
      - assert (S z + y = z + S y). lia. rewrite H0. auto.
Qed.
     

Lemma counter_init0:
  forall x, rightside (3 * (S x)) -->> counter 4 x = (3 * x + 7).
Proof.
  intros. unfold rightside. assert (3 * S x = 3 + 3 * x). lia. rewrite H. auto.
  rewrite lpow_add. rewrite Str_app_assoc.
  mstep_split 4 (3 * x + 3).
  + mstep 4.
  + mstep_split (3 * x) 3.
    - specialize (counter_init 0 x 1). intros. mstep_apply H0.
      do 3 (rewrite <- Str_app_assoc). do 3 (rewrite <- lpow_add).
      assert (3 * x + 0 = x + x + x). lia. rewrite H1. auto.
    - mstep 3.
Qed.

Lemma counter_init1:
  forall x, rightside (3 * x + 1) -->> counter 2 x = (3 * x + 3).
Proof.
  intros. unfold rightside. mstep_split (S O) (3 * x + 2).
  + mstep (S O).
  + mstep_split (3 * x) 2.
    - specialize (counter_init 1 x 0). intros. mstep_apply H.
      rewrite <- Str_app_assoc. rewrite <- lpow_add.
      assert ([1]^^(S O) = [1]%list). auto. rewrite H0.
      do 3 (rewrite <- Str_app_assoc). rewrite <- lpow_S. do 2 (rewrite <- lpow_add).
      assert (S x + x + x = 3 * x + 1). lia. rewrite H1. unfold counter_right. auto.
    - mstep 2.
Qed.

Lemma counter_init2:
  forall x, halts_in_correct tm (rightside (3 * x + 2)) (3 * x + 4).
Proof.
  intros. apply halts_in_add with (c' := const 0 <* [1; 1] <{{Q00}} (counter_right x)) (x := 3 * x + 1) (y := 3).
  * lia.
  * mstep_split (S O) (3 * x).
    + mstep (S O).
    + specialize (counter_init 2 x 0). intros. mstep_apply H.
      do 5 (rewrite <- Str_app_assoc). do 5 (rewrite <- lpow_add).
      assert (x + x + x + 0 + 2 = 3 * x + 2). lia. rewrite H0. auto.
  * unfold halts_in_correct. unfold halts_in. exists (const 0 {{Q04}}> (counter_right (S x))). split.
    + mstep 2.
    + reflexivity.
Qed.

Lemma iterate0:
  forall x, rightside (3 * (S x)) -->> rightside (5 * (S x) + 4) = (N.to_nat 5 * x * x + N.to_nat 21 * x + N.to_nat 21).
Proof.
  intro x. mstep_split (3 * x + 7) (5 * x * x + 18 * x + 14).
  * apply counter_init0.
  * mstep_split (5 * x * x + 8 * x) (10 * x + 14).
    + specialize (counter_total x 4). intros.
      assert (5 * x * x + 8 * x = x * (2 * 4 + 5 * x)). lia. rewrite H0. apply H.
    + specialize (counter_reset (4 + 5 * x)). intros.
      assert (5 * (S x) + 4 = 4 + 5 * x + 5). lia.
      assert (10 * x + 14 = 2 * (4 + 5 * x) + 6). lia.
      rewrite H0. rewrite H1. apply H.
Qed.

Lemma iterate1:
  forall x, rightside (3 * x + 1) -->> rightside (5 * x + 7) = (N.to_nat 5 * x * x + N.to_nat 17 * x + N.to_nat 13).
Proof.
  intro x. mstep_split (3 * x + 3) (5 * x * x + 14 * x + 10).
  * apply counter_init1.
  * mstep_split (5 * x * x + 4 * x) (10 * x + 10).
    + specialize (counter_total x 2). intros.
      assert (5 * x * x + 4 * x = x * (2 * 2 + 5 * x)). lia. rewrite H0. apply H.
    + specialize (counter_reset (2 + 5 * x)). intros.
      assert (5 * x + 7 = 2 + 5 * x + 5). lia.
      assert (10 * x + 10 = 2 * (2 + 5 * x) + 6). lia.
      rewrite H0. rewrite H1. apply H.
Qed.

Theorem bb5_theorem:
  halts_in_correct tm c0 (N.to_nat 47176870).
Proof.
  apply halts_in_add with (c' := (rightside (N.to_nat 12287))) (x := (N.to_nat 47164581)) (y := N.to_nat 12289).
  * rewrite <- N2Nat.inj_add. auto.
  * mstep_split 24 (N.to_nat 47164557). mstep 24.
    mstep_split 83 (N.to_nat 47164474). apply iterate0 with (x := 2).
    mstep_split 295 (N.to_nat 47164179). apply iterate1 with (x := 6).
    mstep_split 937 (N.to_nat 47163242). apply iterate1 with (x := 12).
    mstep_split 2807 (N.to_nat 47160435). apply iterate1 with (x := 22).
    mstep_split (N.to_nat 8039) (N.to_nat 47152396). apply iterate0 with (x := 38).
    mstep_split (N.to_nat 22915) (N.to_nat 47129481). apply iterate1 with (x := 66).
    mstep_split (N.to_nat 64637) (N.to_nat 47064844). apply iterate1 with (x := 112).
    mstep_split (N.to_nat 180689) (N.to_nat 46884155). apply iterate0 with (x := 188).
    mstep_split (N.to_nat 504665) (N.to_nat 46379490). apply iterate1 with (x := 316).
    mstep_split (N.to_nat 1405029) (N.to_nat 44974461).
    specialize (iterate0 (N.to_nat 528)). intros. mstep_apply_safe H. auto. auto. auto.
    do 3 (rewrite <- N2Nat.inj_mul). do 2 (rewrite <- N2Nat.inj_add). auto.
    mstep_split (N.to_nat 3908163) (N.to_nat 41066298).
    specialize (iterate0 (N.to_nat 882)). intros. mstep_apply_safe H. auto. auto. auto.
    do 3 (rewrite <- N2Nat.inj_mul). do 2 (rewrite <- N2Nat.inj_add). auto.
    mstep_split (N.to_nat 10864853) (N.to_nat 30201445).
    specialize (iterate0 (N.to_nat 1472)). intros. mstep_apply_safe H. auto. auto. auto.
    do 3 (rewrite <- N2Nat.inj_mul). do 2 (rewrite <- N2Nat.inj_add). auto.
    specialize (iterate1 (N.to_nat 2456)). intros. mstep_apply_safe H. auto. auto. auto.
    do 3 (rewrite <- N2Nat.inj_mul). do 2 (rewrite <- N2Nat.inj_add). auto.
  * apply counter_init2 with (x := 4095).
Qed.
