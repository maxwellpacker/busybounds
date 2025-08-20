From Coq Require Import Lists.Streams.
From Coq Require Import Lia.
Require Import Program.
Require Import Relations.Relation_Definitions.

(** Ordinals equipped with fundamental sequences **)

Inductive fso :=
| fso0 : fso
| fsoS : fso -> fso
| fsoL : (nat -> fso) -> fso.

Fixpoint nat_to_fso (n : nat) : fso :=
  match n with
  | 0 => fso0
  | S n' => fsoS (nat_to_fso n')
  end.

Fixpoint fso_plus (o1 : fso) (o2 : fso) :=
  match o2 with
  | fso0 => o1
  | fsoS o2' => fsoS (fso_plus o1 o2')
  | fsoL f => fsoL (fun n => (fso_plus o1 (f n)))
  end.

(** Two limit fundamental-sequence-ordinals are equal if and only if
    their fundamental sequences are equal. This is not true for regular
    ordinals: lim(1, 2, 3, ...) = lim(2, 4, 6, ...) **)

Fixpoint fso_eq (o1: fso) (o2 : fso) :=
  match o1, o2 with
  | fso0, fso0 => True
  | fsoS o1', fsoS o2' => fso_eq o1' o2'
  | fsoL f, fsoL g => forall n : nat, fso_eq (f n) (g n)
  | _, _ => False
  end.

Lemma fso_eq_reflexive:
  forall a : fso, fso_eq a a.
Proof.
  intro a. unfold fso_eq. induction a; auto.
Qed.

Lemma fso_eq_implies_S_eq:
  forall a : fso, forall b : fso, fso_eq a b -> fso_eq (fsoS a) (fsoS b).
Proof.
  auto.
Qed.

Lemma fso_eq_symmetric:
  forall a : fso, forall b : fso, fso_eq a b -> fso_eq b a.
Proof.
  induction a, b; auto.
  - intros. apply IHa in H. apply fso_eq_implies_S_eq. auto.
  - intros. unfold fso_eq. intro n. unfold fso_eq in H0.
    specialize (H0 n). specialize (H n (f0 n)). apply H in H0. apply H0.
Qed.

Lemma fso_eq_transitive:
  forall a : fso, forall b : fso, forall c : fso, fso_eq a b -> fso_eq b c -> fso_eq a c.
Proof.
  induction a, b, c; auto; unfold fso_eq; auto.
  - contradiction.
  - intros. specialize (IHa b c). apply IHa.
    * apply H.
    * apply H0.
  - contradiction.
  - contradiction.
  - contradiction.
  - intros. specialize (H0 n). specialize (H1 n). specialize (H n (f0 n) (f1 n)). apply H.
    * apply H0.
    * apply H1.
Qed.

(** This definition of <= is for the benefit of the fast-growing hierarchy:
    o1 <= o2 guarantees that f_o2 eventually dominates f_o1 **)

Fixpoint fso_leq (o1 : fso) : fso -> Prop :=
  fix fso_leq_aux (o2 : fso) : Prop :=
    match o1, o2 with
    | fso0, _ => True
    | _, fso0 => False
    | fsoS o1', fsoS o2' => fso_leq o1' o2'
    | fsoS _, fsoL g => exists n : nat, fso_leq_aux (g n)
    | fsoL f, fsoS _ => forall n : nat, fso_leq (f n) o2
    | fsoL f, fsoL g => exists n : nat, (forall n' : nat, (n' > n -> fso_leq (f n) (g n)))
    end.

Lemma fso_leq_reflexive:
  forall a : fso, fso_leq a a.
Proof.
  intros. unfold fso_leq. induction a; auto. exists 0. intros. apply H.
Qed.

(** A Plus B (times) Omega To (the) C **)

Definition botc_leq : relation (nat * fso) :=
  fun p1 => (fun p2 => match p1, p2 with
                       | (b1, c1), (b2, c2) => (or (fso_leq c1 c2) (and (fso_eq c1 c2) (b1 <= b2)))
                       end).
(**
Program Fixpoint apbotc (a : fso) (b : nat) (c : fso) {measure (b, c) botc_leq} : fso :=
  match b, c with
  | _, fso0 => fso_plus a (nat_to_fso b)
  | 0, fsoS c' => a
  | 1, fsoS c' => fsoL (fun n => apbotc a n c')
  | S (S b'), fsoS c' => apbotc (apbotc a (S b') c) 1 c'
  | _, fsoL f => fsoL (fun n => (apbotc a b (f n)))
  end.**)

Definition fso1 : fso :=
  nat_to_fso 1.

Fixpoint repeated_apply (f : nat -> nat) (exp : nat) (n : nat) : nat :=
  match exp with
  | 0 => n
  | S exp' => repeated_apply f exp' (f n)
  end.

Fixpoint FGH (o : fso) (n : nat) : nat :=
  match o with
  | fso0 => S n
  | fsoS o' => repeated_apply (FGH o') n n
  | fsoL f => FGH (f n) n
  end.
