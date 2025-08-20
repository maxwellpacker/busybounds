From Coq Require Import Lia.
From BusyCoq Require Import Individual992.
Set Default Goal Selector "!".

(** halts_in is off by one. **)

Definition halts_in_correct (tm : TM) (c : Q * tape) (n : nat) :=
  match n with
  | O => False
  | S n' => halts_in tm c n'
  end.

Definition halts_within (tm : TM) (c : Q * tape) (n : nat) :=
  exists n', and (n' <= n) (halts_in_correct tm c n').

Definition upper_bound (tm : TM) (n : nat) :=
  halts_within tm c0 n.

Definition lower_bound (tm : TM) (n : nat) :=
  match n with
  | O => True
  | S n' => not (halts_within tm c0 n')
  end.

Definition easy_halter : TM := fun '(q, s) =>
  None.

Definition bb4 : TM := fun '(q, s) =>
  match q, s with
  | Q00, 0 => Some (1, R, Q01)  | Q00, 1 => Some (1, L, Q01)
  | Q01, 0 => Some (1, L, Q00)  | Q01, 1 => Some (0, L, Q02)
  | Q02, 0 => None              | Q02, 1 => Some (1, L, Q03)
  | Q03, 0 => Some (1, R, Q03)  | Q03, 1 => Some (0, R, Q00)
  | _, _ => None
  end.

Lemma easy_halter_leq1:
  upper_bound easy_halter 1.
Proof.
  unfold upper_bound. unfold halts_within. exists (S O). split.
  - reflexivity.
  - unfold halts_in. exists c0. split.
    * auto.
    * reflexivity.
Qed.

Lemma easy_halter_geq1:
  lower_bound easy_halter 1.
Proof.
  unfold lower_bound. unfold halts_within. intro a. destruct a as [b c]. destruct c as [d e].
  assert (b = O).
  * lia.
  * rewrite H in e. auto.
Qed.