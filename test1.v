(* Test some aspects of using Coq with the Mathematical Components library.
Prove the following lemma: if n>0, m <= n*m. *)

From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Compute 3.+1.

Lemma muln_eq0 m n : (m * n == 0) = (m == 0) || (n == 0).
Proof.
case: m => [|m].
- reflexivity.
- case: n => [|n]; last first.
  + reflexivity.
  + induction m as [|m IHm].
    - reflexivity.
    - rewrite IHm.
      reflexivity.
Qed.


Lemma four_exists : exists u, u == 4.
Proof.
exists 4. reflexivity.
Qed.


Lemma pos_is_suc : forall n, n > 0 -> exists u, n = S u.
Proof.
intros n H.
destruct n as [|p]; last first.
- (* n = S p *)
  exists p. reflexivity.
- (* n = 0 *)
  discriminate.
Qed.

Lemma leq_itself : forall m : nat, m <= m.
Proof.
intros m.
induction m as [|u IHu].
- (* m=0 *) reflexivity.
- (* m = Su *) apply IHu.
Qed.

Lemma suc_equals_plus_one : forall m : nat, S m = m + 1.
Proof.
intros m.
rewrite addnC.
reflexivity.
Qed.


Lemma multsuc : forall x y, x.+1 * y = x * y + y.
Proof.
intros x y.
rewrite addnC.
reflexivity.
Qed.

Lemma multer : forall m n, n > 0 -> m <= n * m.
Proof.
intros m n H.
induction n as [|n' IHn']. 
- (* n=0 *) discriminate.
- (* n = Sn' *)
  rewrite (multsuc n' m).
  apply leq_addl.
Qed.