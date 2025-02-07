(* The goal of this document is to prove the spectral theorem for finite-dimensional
symmetric matrices over the real numbers.
On the way we hope to learn how to use real numbers and matrices in Coq / mathcomp. *)

(* The second part of this document (a work in progress) aims to prove the Cauchy Interlacing
Theorem. Currently it contains a (partial) statement of the Min-Max Theorem without proof,
and a proof of the Cauchy Interlacing Theorem from that statement. *)


From mathcomp Require Import all_ssreflect all_algebra all_field ssralg ssrint ssrnum.
From mathcomp.analysis Require Import reals.
From mathcomp.algebra_tactics Require Import ring.
Import GRing.Theory Num.Theory.
Import Num.Def.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Practice.

(* Some practice with \sum, which could come in handy for dealing with vector inner products: *)
Lemma sumofones (m n : nat) : \sum_(m <= i < n + m) 1 = n.
Proof.
(* by rewrite sum_nat_const_nat muln1 addnK. *)
elim: n=>[|n IH] in m *.
- by apply: big_geq; rewrite add0n.
rewrite big_ltn; last by rewrite addSn ltnS; apply: leq_addl.
by rewrite (addSnnS n) IH add1n.
Qed.


Open Scope ring_scope.

Variable R: realType.


(* Build a function that adds 2.5 to a real number. *)
Definition add_two_and_a_half (x : R) : R := x + (2 + 1/2).

Check add_two_and_a_half.
Check add_two_and_a_half 6.
Compute add_two_and_a_half 6.

Lemma six_and_two_and_a_half_make_eight_and_a_half : add_two_and_a_half 6 = (8 + 1/2).
Proof.
rewrite /add_two_and_a_half.
by ring.
Qed.

(* Build a function that multiplies a real number by sqrt2. *)
Definition multiply_by_sqrt_2 (x : R) : R := x * Num.sqrt 2.

Check multiply_by_sqrt_2.
Check multiply_by_sqrt_2 1.

Lemma sqrt2_times_sqrt2_is_2 : multiply_by_sqrt_2 (Num.sqrt 2) = 2.
Proof.
rewrite /multiply_by_sqrt_2; apply: sqr_sqrtr.
by apply: ler0n.
Qed.

(* Build a specific matrix. *)

Definition M1 : 'M[R]_5 := const_mx 12.

Definition M2 : 'M[R]_5 := \matrix_(i < 5, j < 5) 0.

Definition M3 : 'M[R]_5 := \matrix_(i < 5, j < 5) if i==j then 1 else 2.

Definition M4 : 'M[R]_5 := M1 + M3.

Definition M5 : 'M[R]_5 := \matrix_(i < 5, j < 5) if i==0 then 1 else 0.

Definition M6 : 'M[R]_5 := \matrix_(i < 5, j < 5) if i==j then 13 else 14.

(*Compare some concrete matrices entrywise to show they are equal:*)
Lemma comp_matrices : M4 = M6.
Proof.
apply/matrixP=> i j; rewrite !mxE.
by case: eqP=>_; ring.
Qed.

Definition constmx1 : 'M[R]_1 := const_mx 1.

Lemma comp_m2 : constmx1 = 1%:M.
Proof.
apply/matrixP=> i j; rewrite !mxE.
by rewrite !ord1.
Qed.

(* Some useful, simple lemmata about matrix addition with 0: *)
Lemma addM0 {m n : nat} (M : 'M[R]_(m,n)) : M + 0 = M.
Proof.
by apply/matrixP=> i j; rewrite !mxE addr0.
Qed.

Lemma add0M {m n : nat} (M : 'M[R]_(m,n)) : 0 + M = M.
by apply/matrixP=> i j; rewrite !mxE add0r.
Qed.


End Practice.
(* State and prove: if A and B are matrices with a simultaneous eigenvector,
then A+B has the same eigenvector. *)

(* Note that the mathcomp library has a definition of eigenvalue/eigenvector,
but it uses a left row vector and doesn't have an eigenpair statement,
so I'd like to write my own. *)

Section mxn. (*Definitions and lemmas applying specifically to matrices/vectors of size n.*)
Variable R: realType.
Variable (n : nat).
Open Scope ring_scope.

Definition eigenpair (M : 'M[R]_n) (lambda : R) (v : 'cV[R]_n) : Prop :=
  v != 0 /\ M *m v = lambda *: v.

Definition eigenval (lambda : R) (M : 'M[R]_n) : Prop :=
  exists v : 'cV[R]_n, eigenpair M lambda v.

Definition eigenvec (v : 'cV[R]_n) (M : 'M[R]_n) : Prop :=
  exists lambda:R, eigenpair M lambda v.

Definition simul_eigenvec (v : 'cV[R]_n) (A B : 'M[R]_n) : Prop :=
  eigenvec v A /\ eigenvec v B.

Lemma simul_eigenval_sum (v : 'cV[R]_n) (A B : 'M[R]_n) : simul_eigenvec v A B -> eigenvec v (A+B).
Proof.
rewrite /simul_eigenvec /eigenvec /eigenpair; case=>[[lA [_ HA]][lB [Nv HB]]].
by exists (lA+lB); split=>//; rewrite mulmxDl scalerDl HA HB.
Qed.


(* Now onto the spectral theorem. We will admit the fact that all symmetric real matrices
have one eigenvalue -- proofs of this fact of which I am aware go either through
complexification and the fundamental theorem of algebra, or through an optimization argument
on the Rayleigh quotient. Both are beyond the scope of the current project. *)

(* Definition of a symmetric matrix. *)
Definition symmx (M : 'M[R]_n) : Prop := M = M^T.

Axiom symmx_has_eigenvalue :
  forall (M : 'M[R]_n), (0 < n)%N -> symmx M -> exists l:R, eigenval l M.

(* Definition of orthogonal matrix .*)
Definition orthmx (M : 'M[R]_n) : Prop := M *m (M^T) = 1%:M.

(*Product of orthogonal matrices is orthogonal.*)
Lemma orthmx_prod (M N : 'M[R]_n) : orthmx M -> orthmx N -> orthmx (M *m N).
Proof.
rewrite /orthmx => HM HN.
by rewrite trmx_mul -mulmxA (mulmxA N) HN mul1mx HM.
Qed.

(*Adding a one to the top left corner and 0s in the rest of its row/column*)
Definition one_dirp (M: 'M[R]_n) : 'M[R]_n.+1 :=
  block_mx (1%:M : 'M[R]_1) 0 0 M.

Lemma one_dirp_tr (M : 'M[R]_n) : (one_dirp M)^T = one_dirp M^T.
Proof.
by rewrite /one_dirp (tr_block_mx (1%:M : 'M[R]_1)) trmx1 !trmx0.
Qed.

(* Multiplying block diagonal matrices with two blocks :*)
Lemma block_diag_mulmx {p q : nat} (A B : 'M[R]_q) (M N : 'M[R]_p) :
  block_mx A 0 0 M *m block_mx B 0 0 N = block_mx (A *m B) 0 0 (M *m N).
Proof.
by rewrite mulmx_block !mulmx0 !mul0mx !addM0 add0M.
Qed.

(* The specific case of the latter lemma when the topleft blocks are single 1s: *)
Lemma one_dirp_mulmx (M N : 'M[R]_n) : one_dirp M *m one_dirp N = one_dirp (M *m N).
Proof.
by rewrite /one_dirp (block_diag_mulmx (1%:M : 'M[R]_1)) mulmx1.
Qed.

Lemma one_dirp_id : one_dirp 1%:M = 1%:M.
Proof.
by rewrite (scalar_mx_block 1).
Qed.


(* A matrix maps the orthogonal complement of an eigenvector to itself: *)
Lemma mx_maps_orthcomp_to_itself (M : 'M[R]_n) (v : 'cV[R]_n) (w : 'rV[R]_n) :
  eigenvec v M -> (w <= kermx v)%MS -> (w *m M <= kermx v)%MS.
Proof.
rewrite /eigenvec /eigenpair; case=>lam [_ EM].
rewrite !sub_kermx => subs.
by rewrite -mulmxA EM -scalemxAr scalemx_eq0 subs orbT.
Qed.

(* Define vector norms and normalization: *)
Definition normsqR (v : 'rV[R]_n) : R := (v *m v^T) 0 0.

Definition normsqC (v : 'cV[R]_n) : R := (v^T *m v) 0 0.

Definition normR (v : 'rV[R]_n) : 'rV[R]_n := (1/Num.sqrt (normsqR v)) *: v.

Definition normC (v : 'cV[R]_n) : 'cV[R]_n := (1/Num.sqrt (normsqC v)) *: v.

Definition is_normalR (v : 'rV[R]_n) : Prop := normsqR v = 1.

Definition is_normalC (v : 'cV[R]_n) : Prop := normsqC v = 1.

(* Two useful lemmata I couldn't find on mathcomp: *)
Lemma tr_mul {m : nat} (a : R) (A : 'M[R]_(m,n)) : (a *: A)^T = a *: A^T.
Proof.
by rewrite -!mul_scalar_mx trmx_mul tr_scalar_mx scalar_mxC.
Qed.

Lemma ssmx_mul {m p : nat} (a b : R) (A : 'M[R]_(m,p)) : a *: (b *: A) = (b * a) *: A.
Proof.
by rewrite -!mul_scalar_mx mulmxA mul_mx_scalar scale_scalar_mx.
Qed.

(* Recasting the size of the matrix to split off the first entry of a row/column vector: *)
Lemma suc_eq : n.+1 = (1 + n)%N.
Proof. by apply/esym/add1n. Qed.

Definition splitofR (v : 'rV[R]_n.+1) : 'rV[R]_(1 + n) := castmx (erefl 1%N, suc_eq) v.

Definition splitofC (v : 'cV[R]_n.+1) : 'cV[R]_(1 + n) := castmx (suc_eq, erefl 1%N) v.

(*
Lemma splitR' (v : 'rV[R]_n.+1) (o : 'I_1) (i : 'I_n.+1) : v o i = splitofR v o (cast_ord suc_eq i).
Proof. by rewrite castmxE /= cast_ordK cast_ord_id. Qed.
*)

Lemma splitR (v : 'rV[R]_n.+1) (o : 'I_1) (i : 'I_n.+1) : v o i = splitofR v o i.
Proof. by rewrite castmxE /= !cast_ord_id. Qed.

(*
Lemma splitC' (v : 'cV[R]_n.+1) (o : 'I_1) (i : 'I_n.+1) : v i o = (splitofC v) (cast_ord suc_eq i) o.
Proof. by rewrite castmxE /= cast_ordK cast_ord_id. Qed.
*)

Lemma splitC (v : 'cV[R]_n.+1) (o : 'I_1) (i : 'I_n.+1) : v i o = splitofC v i o.
Proof.
by rewrite castmxE /= !cast_ord_id.
Qed.

Lemma split_prod (rv : 'rV[R]_n.+1) (cv : 'cV[R]_n.+1) :
  rv *m cv = splitofR rv *m splitofC cv.
Proof.
apply/matrixP=> i j; rewrite !mxE /=; apply: eq_big_seq=>/= z _.
by rewrite splitR splitC.
Qed.

Lemma split_tr (v : 'rV[R]_n.+1) : (splitofR v)^T = splitofC v^T.
Proof.
by apply/ matrixP=> i j; rewrite -splitC !mxE -splitR.
Qed.

End mxn.

Section real.
Variable R: realType.
Open Scope ring_scope.


(*Showing vector norms are nonnegative and positive when nonzero:*)
(*First, we show that the square of a nonzero real is nonzero:*)
Lemma sqnz (x : R) : x != 0 -> 0 < x * x.
Proof. by move=>H; rewrite -expr2 exprn_even_gt0. Qed.

(*We show nonnegativity, then positivity when nonzero, for one-dimensional vectors:*)
Lemma normRpos1 (v : 'rV[R]_1) : 0 <= normsqR v.
Proof.
rewrite /normsqR mxE /= big_ord_recl big_ord0 mxE addr0 -expr2.
by exact: sqr_ge0.
Qed.

(* Now for general vectors: *)
Lemma normRpos {n : nat} (v : 'rV[R]_n) : 0 <= normsqR v.
Proof.
rewrite /normsqR; elim: n=>[|n IH] in v *.
- by rewrite mxE /= big_ord0.
rewrite split_prod -split_tr -(hsubmxK (splitofR v))
  tr_row_mx mul_row_col mxE /= -(addr0 0).
by apply: ler_add; [exact: normRpos1 | exact: IH].
Qed.

Lemma normCpos {n : nat} (v : 'cV[R]_n) : 0 <= normsqC v.
Proof.
rewrite /normsqC -(trmxK v) (trmxK v^T).
by apply: normRpos.
Qed.

Lemma normRnz1 (v : 'rV[R]_1) : v != 0 -> 0 < normsqR v.
Proof.
rewrite /normsqR mxE big_ord_recl big_ord0 mxE addr0.
case/cV0Pn=>i; rewrite !ord1.
by exact: sqnz.
Qed.

Lemma normRnzp {n : nat} (v : 'rV[R]_n) : v != 0 -> 0 < normsqR v.
Proof.
elim: n=>[|n IH] in v *; first by rewrite thinmx0 eqxx.
move=>H; rewrite /normsqR split_prod -split_tr -(hsubmxK (splitofR v))
  tr_row_mx mul_row_col mxE.
move: (eqVneq (lsubmx (splitofR v)) 0)=>[El|Hl]; last first.
- (* left submatrix nonzero *)
  by rewrite -(addr0 0); apply: ltr_le_add; [apply: normRnz1 | apply: normRpos].
move: (eqVneq (rsubmx (splitofR v)) 0)=>[Er|Hr]; last first.
(* right submatrix nonzero *)
- by rewrite -(addr0 0); apply: ler_lt_add; [apply: normRpos | apply: IH].
(* both submatrices 0 *)
by apply: contraR H =>_; rewrite -(castmxK (erefl 1%N) (suc_eq n) v) /= -/(splitofR v)
  -(hsubmxK (splitofR v)) Er El row_mx0 castmx_const.
Qed.

Lemma normRnz {n : nat} (v : 'rV[R]_n) : v != 0 -> normsqR v != 0.
Proof. by move=>H; apply/lt0r_neq0/normRnzp. Qed.

Lemma normCnz {n : nat} (v : 'cV[R]_n) : v != 0 -> normsqC v != 0.
Proof.
move=>H; rewrite /normsqC  -(trmxK v) (trmxK v^T).
by apply: normRnz; rewrite trmx_eq0.
Qed.

End real.

Section mxn. (*Definitions and lemmas applying specifically to matrices/vectors of size n.*)
Variable (n : nat).
Variable R: realType.
Open Scope ring_scope.

(*Normalizing a nonzero vector makes it normal:*)
Lemma normR_is_normal (v : 'rV[R]_n) : v != 0 -> is_normalR (normR v).
Proof.
move=>vnz; rewrite /is_normalR /normsqR /normR tr_mul -!mul_scalar_mx mulmxA.
suff ->: (1 / Num.sqrt (normsqR v))%:M *m v *m (1 / Num.sqrt (normsqR v))%:M *m v^T = const_mx 1
  by rewrite mxE.
rewrite -(mulmxA (1 / Num.sqrt (normsqR v))%:M) scalar_mxC mulmxA mul_mx_scalar scale_scalar_mx -mulmxA.
rewrite mulf_div mulr1 -!expr2 sqr_sqrtr; last by exact: normRpos.
rewrite mul_scalar_mx.
have -> : v *m v^T = const_mx (normsqR v).
- by rewrite /normsqR; apply/matrixP=> i j; rewrite !mxE !ord1.
rewrite scalemx_const; congr const_mx.
by rewrite mul1r; apply/mulVf/normRnz.
Qed.

(*A different, useful characerization of a normal vector:*)
Lemma normal_to_id (v : 'rV[R]_n) : is_normalR v -> v *m v^T = 1%:M.
Proof.
rewrite /is_normalR /normsqR => H.
by apply/matrixP=> i j; rewrite !ord1 H mxE.
Qed.

(* We need a procedure to develop a single unit vector into an orthogonal matrix. *)
(* For this, it will be helpful to first define the notion of a set of orthonormal (row)
vectors, then show that if there are fewer than n vectors in the set, we can
add a vector to the set. *)
Definition orthvecs {m : nat} (V : 'M[R]_(m,n)) := V *m V^T = 1%:M.

(* Show orthognality: *)
Lemma orthvecs_orth {m m' : nat} (V : 'M[R]_(m,n)) (W : 'M[R]_(m',n)) :
  orthvecs (col_mx V W) -> W *m V^T = 0.
Proof.
rewrite /orthvecs tr_col_mx mul_col_row scalar_mx_block.
by case/eq_block_mx.
Qed.

(* Adding a normal vector in the cokernel will preserve orthogonality: *)
Lemma add_orthvec' {m : nat} (V : 'M[R]_(m,n)) (v : 'rV[R]_n) :
  orthvecs V -> is_normalR v -> V *m v^T = 0 -> orthvecs (col_mx V v).
Proof.
rewrite /orthvecs=>orthV normalv kernelv; rewrite tr_col_mx mul_col_row.
rewrite orthV kernelv (normal_to_id normalv).
suff ->: v *m V^T = 0 by rewrite -scalar_mx_block.
rewrite -(trmxK v) -trmx0 - (trmxK ((v^T)^T *m V^T)).
by move: kernelv; rewrite -(trmxK (V *m v^T)) trmx_mul => ->.
Qed.

(* As long as there are fewer than n vectors, we can find such a normal vector to add: *)
Lemma add_orthvec {m : nat} (V: 'M[R]_(m,n)) :
  (m < n)%N -> orthvecs V ->
  exists (v : 'rV[R]_n), orthvecs (col_mx V v).
Proof.
move=> mltn orthV.
have {mltn}: ~~ row_free V^T.
- rewrite -row_leq_rank -ltnNge.
  by apply/leq_ltn_trans/mltn; exact: rank_leq_col.
rewrite -kermx_eq0=>nrf.
exists (normR (nz_row (kermx V^T))).
have {nrf}: is_normalR (normR (nz_row (kermx V^T))).
- by apply: normR_is_normal; rewrite nz_row_eq0.
suff {orthV}/[swap] : V *m (normR (nz_row (kermx V^T)))^T = 0 by apply: add_orthvec'.
rewrite /normR tr_mul -!mul_scalar_mx mulmxA scalar_mxC -mulmxA.
suff -> : V *m (nz_row (kermx V^T))^T = 0 by apply: mulmx0.
apply: trmx_inj; rewrite trmx_mul trmxK trmx0.
by apply/sub_kermxP/nz_row_sub.
Qed.

(* To add multiple vectors, we will need to typecast the matrix dimensions.
The following lemmas should help. *)
Definition nested_exp (m p : nat) : nat :=
  if p is q.+1 then m + q + 1 else m + 0.

Lemma nested_eq (m p : nat) : nested_exp m p = (m + p)%N.
Proof. by case: p=>//= q; rewrite -addnA addn1. Qed.

Lemma orthvecs_cast {m p : nat} (V : 'M[R]_(nested_exp m p,n)) :
  orthvecs V -> orthvecs (castmx (nested_eq m p, erefl n) V).
Proof.
rewrite /orthvecs => H.
apply/matrixP=> i j; rewrite !mxE.
transitivity (\sum_j0 V (cast_ord (esym (nested_eq m p)) i) j0 *
                      V^T j0 (cast_ord (esym (nested_eq m p)) j)).
- by apply: eq_bigr=>k _; rewrite !mxE !castmxE /= cast_ord_id.
transitivity ((V *m V^T) (cast_ord (esym (nested_eq m p)) i)
                         (cast_ord (esym (nested_eq m p)) j)).
- by rewrite mxE.
by rewrite H mxE.
Qed.

(* We are now ready for the general lemma that a set of orthogonal vectors can be expanded
up to n vectors and remain a set of orthogonal vectors. *)
Lemma add_orthvecs {m : nat} (p : nat) (V : 'M[R]_(m,n)) :
  (m + p <= n)%N -> orthvecs V ->
  exists (W : 'M[R]_(p,n)), orthvecs (col_mx V W).
Proof.
elim: p=>[_|p IH].
- rewrite /orthvecs => orthV; exists 0.
  rewrite tr_col_mx mul_col_row orthV trmx0 mulmx0 mul0mx scalar_mx_block.
  suff ->: (0 : 'M[R]_(0,n)) *m 0 = (1%:M : 'M[R]_0) by [].
  by rewrite mul0mx flatmx0.
rewrite {1}addnS => mplen ortv.
case: (IH (ltnW mplen) ortv)=>W' /(add_orthvec mplen) {IH}[v vec].
exists (dsubmx (castmx (nested_eq m p.+1, erefl n) (col_mx (col_mx V W') v))).
suff {1}->: V = usubmx (castmx (nested_eq m p.+1, erefl n) (col_mx (col_mx V W') v)).
- by rewrite vsubmxK; apply: orthvecs_cast.
apply/matrixP=> i j; rewrite mxE castmxE /=.
rewrite cast_ord_id.
have -> : cast_ord (esym (nested_eq m p.+1)) (lshift p.+1 i) = lshift 1 (lshift p i) by apply: ord_inj.
by rewrite !col_mxEu.
Qed.

End mxn.

Section spec. (*Definitions and lemmas applying specifically to matrices/vectors of size n.*)
Variable R: realType.
Open Scope ring_scope.

(* Special case of the latter lemma for expanding a single vector into an orthogonal matrix :*)
Lemma vec_to_orthmx {m : nat} (v : 'rV[R]_m.+1) :
  is_normalR v ->
  exists (W : 'M[R]_(m, m.+1)), orthmx (col_mx v W).
Proof.
move/normal_to_id; case: m v => [| m] v orthv.
- exists 0; rewrite /orthmx tr_col_mx mul_col_row orthv trmx0 mulmx0 mul0mx.
  suff ->: (0 : 'M[R]_(0,1)) *m 0 = (1%:M : 'M[R]_0) by rewrite -scalar_mx_block.
  by rewrite mul0mx flatmx0.
have mplen : (1 + m.+1 <= m.+2)%N by rewrite add1n.
by case: (add_orthvecs mplen orthv)=>W H; exists W.
Qed.

(* Adding a 1 above and to the left of an orthogonal matrix preserves its orthogonality. *)
Lemma one_dirp_pres_orth {n : nat} (M : 'M[R]_n) :
  orthmx M -> orthmx (one_dirp M).
Proof.
rewrite /orthmx=>H; rewrite one_dirp_tr one_dirp_mulmx H.
by exact: one_dirp_id.
Qed.

(* The first step of spectral decomposition: putting a single eigenvalue on the diagonal *)
Lemma spec1 {n : nat} (M : 'M[R]_n.+1) :
  symmx M ->
  exists (U : 'M[R]_n.+1) (M' : 'M[R]_n) (lambda : R),
    [/\ orthmx U, symmx M' & U *m M *m U^T = block_mx (lambda%:M : 'M[R]_1) 0 0 M'].
Proof.
move=>H; case: (symmx_has_eigenvalue (isT : (0 < n.+1)%N) H)=>lam [v][vnz Heig].
have vtnz : v^T != 0 by apply: contra_neq vnz; rewrite -trmx0; exact: trmx_inj.
case: (vec_to_orthmx (normR_is_normal vtnz))=>W oU.
exists (col_mx (normR v^T) W).
have Heigt : v^T *m M = lam *: v^T by rewrite H -trmx_mul Heig tr_mul.
have Heigtn : (normR v^T) *m M = lam *: (normR v^T)
  by rewrite /normR -scalemxAl Heigt !ssmx_mul mulrC.
have Heign : M *m (normR v^T)^T = lam *: (normR v^T)^T
  by rewrite H -trmx_mul Heigtn tr_mul.
have [M' eM] : exists M' : 'M[R]_n, (col_mx (normR v^T) W) *m M *m (col_mx (normR v^T) W)^T =
                                     block_mx (lam%:M : 'M[R]_1) 0 0 M'.
- rewrite mul_col_mx tr_col_mx mul_col_row; exists (W *m M *m W^T).
  have z3 : W *m (normR v^T)^T = 0 by apply: orthvecs_orth.
  have z2 : normR v^T *m W^T = 0
    by rewrite -(trmxK (normR v^T)) -trmx0 -z3 trmx_mul.
  have eM1 : normR v^T *m M *m (normR v^T)^T = lam%:M
    by rewrite Heigtn -scalemxAl (normal_to_id (normR_is_normal vtnz)) scalemx1.
  have eM2 : normR v^T *m M *m W^T = 0
    by rewrite Heigtn -scalemxAl z2 scalemx_const mulr0.
  have eM3 : W *m M *m (normR v^T)^T = 0
    by rewrite -mulmxA Heign -mul_scalar_mx mulmxA scalar_mxC -mulmxA z3 mulmx0.
  by rewrite eM1 eM2 eM3.
exists M', lam; split=>//.
(*Proving M' is symmetric*)
suff : symmx (block_mx (lam%:M : 'M[R]_1) 0 0 M')
  by rewrite /symmx tr_block_mx; case/eq_block_mx.
by rewrite -eM /symmx trmx_mul trmxK trmx_mul -H mulmxA.
Qed.

(* The spectral theorem for finite-dimensional real symmetric matrices: *)
Theorem spec {n : nat} (M : 'M[R]_n) :
  symmx M ->
  exists U D : 'M[R]_n, [/\ orthmx U, is_diag_mx D & M = U^T *m D *m U].
Proof.
elim: n M=>[|n IH] M H.
- (*0-dimensional case*) exists 0, 0; rewrite !flatmx0; split=>//.
  - (* orthogonality: *)
    by rewrite /orthmx mul0mx flatmx0.
  (* diagonal: *)
  by exact: mx0_is_diag.
(*inductive case:*)
case: (spec1 H)=>U [M'][lam][oU H' mult].
case: (IH M' H')=>U'[D'][oU' IH' mult'].
exists ((one_dirp U') *m U), (block_mx (lam%:M : 'M[R]_1) 0 0 D'); split.
- (* orthogonality: *)
  by apply: orthmx_prod=>//; apply: one_dirp_pres_orth.
- (* diagonal: *)
  rewrite (is_diag_block_mx (lam%:M : 'M[R]_1) 0 0 D') // !eqxx /= IH' andbT.
  by exact: scalar_mx_is_diag.
(* product: *)
rewrite mulmxA trmx_mul one_dirp_tr.
have -> :  U^T *m (one_dirp U'^T) *m (block_mx (lam%:M : 'M[R]_1) 0 0 D') =
          U^T *m ((one_dirp U'^T) *m (block_mx (lam%:M : 'M[R]_1) 0 0 D')) by rewrite mulmxA.
have -> : U^T *m ((one_dirp U'^T) *m (block_mx (lam%:M : 'M[R]_1) 0 0 D')) *m one_dirp U' =
          U^T *m (((one_dirp U'^T) *m (block_mx (lam%:M : 'M[R]_1) 0 0 D')) *m one_dirp U')
  by rewrite [in RHS]mulmxA.
rewrite /one_dirp (block_diag_mulmx (1%:M : 'M[R]_1) (lam%:M : 'M[R]_1) U'^T D') mul1mx.
rewrite (block_diag_mulmx (lam%:M : 'M[R]_1) (1%:M : 'M[R]_1) (U'^T *m D') U') mulmx1.
by rewrite -mult' -mult !mulmxA (mulmx1C oU) mul1mx -mulmxA (mulmx1C oU) mulmx1.
Qed.



(* The goal of the second part of this document is to state the Min-Max Theorem for
eigenvalues of real symmetric matrices and to use it to prove the Cauchy Interlacing Theorem. *)

(* One lemma first: Multiplying two orthvecs matrices gives an orthvecs matrix. *)
Lemma orthvecs_mul {m n p : nat} (M : 'M[R]_(m,n)) (N : 'M[R]_(n,p)) :
  orthvecs M -> orthvecs N -> orthvecs (M *m N).
Proof.
by move=>HM HN; rewrite /orthvecs trmx_mul -mulmxA (mulmxA N) HN mul1mx HM.
Qed.

(* Since the min-max theorem and the Cauchy interlacing theorem are about the full list of
sorted eigenvalues of a matrix, we define what it means to be such a list and use the spectral
theorem to show that every symmetric matrix has such a list. *)

(* A list of reals can be expressed in mathcomp as type seq R. *)
(* The following proposition states that a list is sorted in increasing order. *)
Fixpoint sortedreals (l : seq R) : Prop :=
  if l is h :: t then (h <= head h t) /\ sortedreals t else True.

Import Order.Theory.

Lemma sortedreals_sorted (l : seq R) : reflect (sortedreals l) (sorted (<=%R) l).
Proof.
apply: (iffP idP); elim: l=>//= h t.
- move=>IH H; split; last by apply: IH (path_sorted H).
  by case: {IH}t H=>//= h1 t1; case/andP.
move=>IH [H1 H2]; rewrite (path_sortedE le_trans); apply/andP; split; last by apply: IH.
case: t H1 H2 IH=>//= h1 t1 E H IH; rewrite E /=.
by apply/(order_path_min le_trans)/(path_le le_trans E)/IH.
Qed.

(*
(* Since head and last need to be called with default values, the following is useful to
interchange the default values in case the list is nonempty. *)
Lemma head_interchange (l : seq R) (h1 h2 : R) : l != nil -> head h1 l = head h2 l.
Proof. by case: l. Qed.

Lemma last_interchange (l : seq R) (t1 t2 : R) : l != nil -> last t1 l = last t2 l.
Proof. by case: l. Qed.

(* The following lemma states that concatenations of sorted lists are sorted if the last
element of the first list is <= the head of the second. *)
Lemma concat_sorted (l1 l2 : seq R) :
  last 0 l1 <= head 0 l2 -> sortedreals l1 -> sortedreals l2 ->
  sortedreals (l1 ++ l2).
Proof.
elim: l1=>//=h1 l1 IH H1 [H2 S1 S2].
case: l1=>/=[|h11 l11] in IH H1 H2 S1 *.
- move=>{H2 S1}; split=>//.
  by case: l2 S2 IH H1.
by split=>//; apply: IH.
Qed.

(* Note that 'prefix l1 l2' means l1 is a list that appears as the beginning of list l2.
The following lemma will show that if the larger list l2 is sorted, so is the smaller list l1. *)
Lemma prefix_sorted (l1 l2 : seq R) : prefix l1 l2 -> sortedreals l2 -> sortedreals l1.
Proof.
elim: l1 l2=>//= h1 l1 IH [|h2 l2] //= /andP [/eqP {h1}-> Hp][H S].
split; last by apply: (IH l2).
by case: l2 H Hp S=>/=; case: {IH}l1=>//= h22 l22 h11 l11 H /andP [/eqP ->].
Qed.

(*We can insert any value into a sorted list:*)
Lemma insert_into_sorted (r : R) (l : seq R) :
  sortedreals l ->
  exists (l1 l2 : seq R), l = l1 ++ l2 /\ sortedreals (l1 ++ r :: l2).
Proof.
elim: l=>/= [|h t IH] S; first by exists [::], [::].
intros S.
induction l as [| h t IH].
- exists nil. exists nil. by [].
- destruct (r <= h) eqn:L.
  + exists nil. exists (h::t). by [].
  + destruct S as [H S]. destruct (IH S) as [l1 IH']. destruct IH' as [l2 IH'].
    exists (h::l1). exists l2. destruct IH' as [IH1 IH2]. split.
    rewrite cat_cons IH1 //.
    rewrite cat_cons. split; last first. apply IH2.
    destruct l1 as [| h1 t1].
    - (*l1 empty*) rewrite real_leNgt in L.
      rewrite cat0s.
      assert (L' : h <= r). { apply le_l. apply (negbFE L). }
      apply L'. apply num_real. apply num_real.
    - (*l1 = h1::t1*) rewrite IH1 in H. apply H.
Qed.

(*It follows that every list can be sorted. We use 'perm_eq' from the MathComp library
as the predicate that two lists are equivalent up to permutation. *)
Lemma sortable (l : seq R) : exists (s : seq R), perm_eq l s /\ sortedreals s.
Proof.
induction l as [| h t IH].
- exists nil. by [].
- destruct IH as [s' IH]. destruct IH as [IHP IHS].
  destruct (insert_into_sorted h IHS) as [l1 El2]. destruct El2 as [l2 H].
  destruct H as [HC HS]. exists (l1 ++ h :: l2).
  split; last first. apply HS.
  assert (T : perm_eq (h::t) ((h::l2) ++ l1)). {
    rewrite cat_cons perm_cons. apply (perm_trans IHP). rewrite HC.
    apply permEl. apply (perm_catC l1 l2). }
  apply (perm_trans T). apply permEl. apply perm_catC.
Qed.
*)

(*We define what it means to be a full list of eigenvalues, and a sorted list of eigenvalues,
for a matrix. Note that this definition will hold only if M is diagonalizable. Since we are
interested in symmteric matrices, the spectral theorem will guarantee this is always the case.
Since diagonal matrices are constructed in the MathComp matrix library from row vectors, we
need a way to convert a list into a row vector.*)
Definition vectorize {n : nat} (l : seq R) : 'rV_n := \matrix_(i < 1, j < n) nth 0 l j.

Definition eiglist {n : nat} (l : seq R) (M : 'M[R]_n) : Prop :=
  exists (U : 'M[R]_n), orthmx U /\ M = U^T *m diag_mx (vectorize l) *m U.

Definition sortedeiglist {n : nat} (l : seq R) (M : 'M[R]_n) : Prop :=
  sorted (<=%R) l /\ exists (l' : seq R), perm_eq l l' /\ eiglist l' M.

(*Towards stating the min-max theorem:*)
(* We define what it means to have the max/min
Rayleigh quotient corresponding to a subspace.*)
(* Note that in the MathComp mxlagebra library,
subspaces are expressed as the rowspace of a
matrix M and (v <= M)%MS expresses that the
row vector v is in the subspace. *)
(* For dimensionality we can use rank, or
alternatively require that the vectors are
orthogonal. *)

(*We first define the
maximum/minimum Rayleigh quotient relative to
a subspace.*)
Definition maxRay {k n : nat} (M : 'M[R]_n) (r : R) (U : 'M[R]_(k,n)) : Prop :=
  (exists (v : 'rV_n), [/\ is_normalR v, (v <= U)%MS & (v *m M *m v^T) 0 0 = r]) /\
  forall (v : 'rV_n), is_normalR v -> (v <= U)%MS -> (v *m M *m v^T) 0 0 <= r.

Definition minRay {k n : nat} (M : 'M[R]_n) (r : R) (U : 'M[R]_(k,n)) : Prop :=
  (exists (v : 'rV_n), [/\ is_normalR v, (v <= U)%MS & (v *m M *m v^T) 0 0 = r]) /\
  forall (v : 'rV_n), is_normalR v -> (v <= U)%MS -> r <= (v *m M *m v^T) 0 0.

(*Now we define what it means to be kth min-max and max-min.*)
Definition minmax {n : nat} (k : nat) (M : 'M[R]_n) (r : R) : Prop :=
  (exists (U : 'M[R]_(k,n)), orthvecs U /\ maxRay M r U) /\
  forall (U : 'M[R]_(k,n)) (r' : R), orthvecs U -> maxRay M r' U -> r <= r'.
Definition maxmin {n : nat} (k : nat) (M : 'M[R]_n) (r : R) : Prop :=
  (exists (U : 'M[R]_(k,n)), orthvecs U /\ minRay M r U) /\
  forall (U : 'M[R]_(k,n)) (r' : R), orthvecs U -> minRay M r' U -> r >= r'.
Theorem MinMax {n : nat} (M : 'M[R]_n) :
  symmx M ->
  forall (k : nat),
  (0 < k <= n)%N -> forall (r : R), minmax k M r <-> maxmin (n.+1-k) M r.
Admitted.

(* We do not here make the connection to eigenvalues explicit,
but minmax k M r expresses that r is the kth eigenvalue of M. *)

(* One helper lemma about conjugations of symmetric matrices: *)
Lemma symmx_conj {m n : nat} (U : 'M[R]_(m,n)) (M : 'M[R]_n) : symmx M -> symmx (U *m M *m U^T).
Proof.
by move=>S; rewrite /symmx !trmx_mul trmxK mulmxA -S.
Qed.

(* We now state the Cauchy interlacing theorem. *)
Theorem CIT {m n : nat} (M : 'M[R]_m) (N : 'M[R]_n) : symmx N -> (m < n)%N ->
  (exists (P : 'M[R]_(m,n)), (orthvecs P /\ M = P *m N *m P^T)) ->
  forall (k : nat), (0 < k <= m)%N -> forall (r r' r'' : R),
  minmax k M r -> minmax k N r' -> minmax (k+n-m) N r'' -> r' <= r <= r''.
Proof.
move=>S Hmn [P][HO HP] k Hk0m r r' r'' ErM Er'N Er''N.
apply/andP; split.
- (* The left side does not require the MinMax Theorem and can be proven based on the
  definition of minmax. *)
  case: ErM => ErM1 ErM2; case: Er'N => Er'N1 Er'N2.
  case: ErM1 =>UM [HUMO][[v][Hv1 Hv2 Hv3] HUM2]; case: Er'N1 => UN [HUNO HUN].
  apply: (Er'N2 (UM *m P)); first by apply: orthvecs_mul.
  split.
  - (* The eigenvector of M also gives the maximal Rayleigh quotient for UM * P. *)
    exists (v *m P); split.
    - (*is normal:*)
      by rewrite /is_normalR /normsqR trmx_mul -mulmxA (mulmxA P) HO mul1mx.
    - (*is in subspace:*)
      by apply: submxMr.
    (*r is Rayleigh quotient:*)
    by rewrite trmx_mul -!mulmxA (mulmxA N) !(mulmxA P) -HP mulmxA.
  (* Confirming it is indeed maximal, i.e., any other vector gives a smaller Rayleigh quotient. *)
  move=>v' Hv'1; case/submxP=>w; rewrite mulmxA=>Ew.
  rewrite Ew trmx_mul -!mulmxA (mulmxA N) !(mulmxA P) -HP !mulmxA.
  apply: HUM2; (* The vector w *m UM is in the subspace UM. *)
    last by apply: submxMl.
  (* The vector w *m UM (v' in m dimensions) is normal *)
  rewrite /is_normalR /normsqR trmx_mul -(mulmx1 (w *m UM)) -HO -trmx_mul -!mulmxA.
  by rewrite -(trmx_mul (w*m UM)) 2!mulmxA -!Ew.
(* The right side proceeds similarly but requires the minmax theorem to transform
  both minmax statements into maxmin statments. *)
rewrite HP (MinMax (symmx_conj P S) Hk0m) in ErM.
have t : (0 < k + n - m <= n)%N.
- apply/andP; split.
  - by rewrite subn_gt0; apply: ltn_addl.
  by rewrite leq_subLR leq_add2r; case/andP: Hk0m.
rewrite (MinMax S t) in Er''N.
have Hmnk : (m <= n + k)%N by apply: (leq_trans (ltnW Hmn)); exact: leq_addr.
have t'' : (m.+1 - k = n.+1 - (k + n - m))%N.
- rewrite (addnC k) (subnBA n.+1)%N // subnDA.
  by rewrite -(addnBAC m) // subSnn add1n.
rewrite -t'' in Er''N; rewrite -HP in ErM. (*With this prepared we proceed as the left side.*)
case: ErM => ErM1 ErM2; case: Er''N => Er''N1 Er''N2.
case: ErM1 => UM [HUMO [[v][Hv1 Hv2 Hv3] HUM2]]; case: Er''N1 => UN [HUNO HUN].
apply: (Er''N2 (UM *m P) r); first by apply: orthvecs_mul.
split.
- (* The eigenvector of M also gives the minimal Rayleigh quotient for UM * P. *)
  exists (v *m P); split.
  - (*is normal:*)
    by rewrite /is_normalR /normsqR trmx_mul -mulmxA (mulmxA P) HO mul1mx.
  - (*is in subspace:*)
    by apply: submxMr.
  (*r is Rayleigh quotient:*)
  by rewrite trmx_mul -mulmxA -mulmxA (mulmxA N) (mulmxA P) (mulmxA P) -HP mulmxA.
(* Confirming it is indeed minimal, i.e., any other vector gives a smaller Rayleigh quotient. *)
move=>v' Hv'1; case/submxP=>w; rewrite mulmxA=>Ew.
rewrite Ew trmx_mul -!mulmxA (mulmxA N) !(mulmxA P) -HP !mulmxA.
apply: HUM2; (* The vector w *m UM is in the subspace UM. *)
  last by apply: submxMl.
(* The vector w *m UM (v' in m dimensions) is normal *)
rewrite /is_normalR /normsqR trmx_mul -(mulmx1 (w *m UM)) -HO -trmx_mul -!mulmxA.
by rewrite -(trmx_mul (w*m UM)) 2!mulmxA -!Ew.
Qed.
