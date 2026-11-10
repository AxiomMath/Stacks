module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.PrincipalIdealDomain
public import StacksFrontier.RingTheory.AdicCompletion.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# A quotient of an adically complete ring need not be complete

There is a commutative ring which is complete for a principal ideal and a second principal
ideal whose quotient is not complete for the induced adic topology.

The construction is the source's. Let `C n = ℚ[x]/(x^{n+1})`, let `B = ∏ₙ C n` and let
`M = ⊕ₙ C n` as a `B`-module. The ring is `A = B ⊕ M` with `M` a square-zero ideal, `u ∈ A`
is the element `x` of `B` and `I = (u)`. Writing `t ∈ B` for the element whose `n`-th
coordinate is `x^n`, the element `f = ∑ₙ t·eₙ` of the `I`-adic completion `R` of `A` is a limit
of the partial sums, each of which is divisible by `t`; but `f` itself is not, because a
quotient would have to have unit `n`-th coordinate in every degree `n`, and an element of the
direct sum has only finitely many nonzero coordinates. So `f` lies in every `J + Iⁿ` without
lying in `J = (t)`, which by Stacks 031A is exactly the failure of completeness of `R/J`.

The statement is produced in an arbitrary universe by transporting the whole situation along
`ULift`.

## Main results

* `Stacks.Examples.exists_complete_principal_ideal_not_complete_quotient`: there is a
  commutative ring `R` with principal ideals `I` and `J` such that `R` is `I`-adically complete
  but `R ⧸ J` is not complete for the image of `I`.

## Implementation notes

Completeness is `IsAdicComplete`. On the quotient the ideal of definition is the image of the
original principal ideal under the quotient map, which is the shape Stacks uses; Mathlib's
`IsAdicComplete.map_algebraMap_iff` converts between that and completeness for the ideal of the
base ring.

## References

* [Stacks Project, Tag 05JE](https://stacks.math.columbia.edu/tag/05JE)
* [Stacks Project, Tag 031A](https://stacks.math.columbia.edu/tag/031A)
-/

@[expose] public noncomputable section

universe u

namespace Stacks.Examples

namespace NoncompleteQuotient

open scoped DirectSum

/-- The `n`-th truncated polynomial ring `ℚ[x]/(x^{n+1})`. -/
private abbrev C (n : ℕ) :=
  Polynomial ℚ ⧸ Ideal.span ({Polynomial.X ^ (n + 1)} : Set (Polynomial ℚ))

/-- The product of the truncated polynomial rings. -/
private abbrev B := (n : ℕ) → C n

/-- The direct sum of the truncated polynomial rings, a `B`-module. -/
private abbrev M := ⨁ n : ℕ, C n

private def proj (n : ℕ) : B →+* C n := Pi.evalRingHom C n

private def unopHom (R : Type*) [CommRing R] : Rᵐᵒᵖ →+* R where
  toFun := MulOpposite.unop
  map_one' := rfl
  map_mul' a b := by simp [MulOpposite.unop_mul, mul_comm]
  map_zero' := rfl
  map_add' a b := by simp

private def projOp (n : ℕ) : Bᵐᵒᵖ →+* C n := (proj n).comp (unopHom B)

private instance (n : ℕ) : Module B (C n) := Module.compHom (C n) (proj n)
private instance (n : ℕ) : Module Bᵐᵒᵖ (C n) := Module.compHom (C n) (projOp n)
private instance (n : ℕ) : IsCentralScalar B (C n) := by
  refine ⟨fun r m => ?_⟩
  change (projOp n (MulOpposite.op r)) * m = (proj n r) * m
  simp [projOp, proj, unopHom]

/-- The ring of the counterexample: `B` extended by the square-zero ideal `M`. -/
private abbrev A := TrivSqZeroExt B M

private instance (priority := 10000) : AddCommMonoid A :=
  (inferInstance : AddCommGroup A).toAddCommMonoid
private instance (priority := 10000) : Semiring A :=
  (inferInstance : CommRing A).toCommSemiring.toSemiring
private instance (priority := 10000) : CommSemiring A :=
  (inferInstance : CommRing A).toCommSemiring
private instance (priority := 10000) : Module A A :=
  (inferInstance : CommSemiring A).toSemiring.toModule

/-- The element of `B` whose every coordinate is the class of `x`. -/
private abbrev xbase : B := fun _ => Ideal.Quotient.mk _ Polynomial.X
/-- The element of `B` whose `n`-th coordinate is the class of `x ^ n`. -/
private abbrev tbase : B := fun n => Ideal.Quotient.mk _ (Polynomial.X ^ n)
/-- The generator of the ideal of definition. -/
private abbrev u : A := TrivSqZeroExt.inl xbase
/-- The ideal of definition. -/
private abbrev I : Ideal A := Ideal.span {u}

private abbrev basis (n : ℕ) : M := DirectSum.lof B ℕ C n 1
private abbrev term (n : ℕ) : A := TrivSqZeroExt.inr (tbase • basis n)
private abbrev partialSum (n : ℕ) : A := ∑ i ∈ Finset.range n, term i

private lemma u_pow (n : ℕ) : u ^ n = TrivSqZeroExt.inl (xbase ^ n) := by
  induction n with
  | zero => simp [u]
  | succ n ih => rw [pow_succ, ih, TrivSqZeroExt.inl_mul_inl, pow_succ]

private lemma basis_coord (i n : ℕ) : basis i n = if i = n then 1 else 0 := by
  by_cases h : i = n
  · subst i
    simp [basis]
  · change DirectSum.component B ℕ C n (DirectSum.lof B ℕ C i 1) = _
    rw [DirectSum.component.of]
    simp [h]

private lemma tbase_smul_basis (n : ℕ) : tbase • basis n = xbase ^ n • basis n := by
  ext i
  rw [DirectSum.smul_apply, DirectSum.smul_apply, basis_coord]
  split_ifs with h
  · subst i
    change (proj n tbase) • (1 : C n) = (proj n (xbase ^ n)) • (1 : C n)
    simp [proj, tbase, xbase]
  · simp

private lemma term_eq (n : ℕ) : term n = u ^ n * TrivSqZeroExt.inr (basis n) :=
  calc
    term n = TrivSqZeroExt.inr (tbase • basis n) := rfl
    _ = TrivSqZeroExt.inr (xbase ^ n • basis n) := by rw [tbase_smul_basis]
    _ = TrivSqZeroExt.inl (xbase ^ n) * TrivSqZeroExt.inr (basis n) :=
      (TrivSqZeroExt.inl_mul_inr (xbase ^ n) (basis n)).symm
    _ = u ^ n * TrivSqZeroExt.inr (basis n) := by rw [u_pow]

private lemma term_mem (n : ℕ) : term n ∈ I ^ n • (⊤ : Submodule A A) := by
  rw [term_eq]
  exact Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton u)) n)
    Submodule.mem_top

private lemma partialSum_cauchy_step (n : ℕ) :
    partialSum n ≡ partialSum (n + 1) [SMOD (I ^ n • (⊤ : Submodule A A))] := by
  simpa [SModEq.sub_mem, partialSum, Finset.sum_range_succ, add_sub_cancel_left]
    using (I ^ n • (⊤ : Submodule A A)).neg_mem (term_mem n)

/-- Evaluation at `0`, as a homomorphism out of `C n`. -/
private def residue (n : ℕ) : C n →+* ℚ :=
  Ideal.Quotient.lift _ (Polynomial.evalRingHom (0 : ℚ)) (by
    intro p hp
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.mp hp
    simp)

private lemma residue_mk (n : ℕ) (p : Polynomial ℚ) :
    residue n (Ideal.Quotient.mk _ p) = Polynomial.eval 0 p := by
  simp [residue]

private lemma residue_one_of_xpow_mul_eq (n : ℕ) (r : C n)
    (h : (Ideal.Quotient.mk _ Polynomial.X : C n) ^ n * r =
      Ideal.Quotient.mk _ (Polynomial.X ^ n)) :
    residue n r = 1 := by
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective r
  have heq : Ideal.Quotient.mk (Ideal.span {Polynomial.X ^ (n + 1)})
      (Polynomial.X ^ n * p) = Ideal.Quotient.mk _ (Polynomial.X ^ n) := by
    simpa [hp, map_mul, map_pow] using h
  have hmem := (Ideal.Quotient.eq).mp heq
  rw [Ideal.mem_span_singleton] at hmem
  have hdiv : Polynomial.X ^ (n + 1) ∣ Polynomial.X ^ n * (p - 1) := by
    rwa [show Polynomial.X ^ n * p - Polynomial.X ^ n = Polynomial.X ^ n * (p - 1) by ring]
      at hmem
  rcases hdiv with ⟨q, hq⟩
  have hcancel : p - 1 = Polynomial.X * q := by
    apply mul_left_cancel₀ (pow_ne_zero n (Polynomial.X_ne_zero (R := ℚ)))
    calc
      Polynomial.X ^ n * (p - 1) = Polynomial.X ^ (n + 1) * q := hq
      _ = Polynomial.X ^ n * (Polynomial.X * q) := by rw [pow_succ]; ring
  have heval : Polynomial.eval 0 (p - 1) = 0 := by simp [hcancel]
  have hpval : Polynomial.eval 0 p = 1 := by simpa [sub_eq_zero] using heval
  rw [← hp]
  simpa [residue_mk] using hpval

/-- The `n`-th coordinate of the square-zero part of an element of `A`. -/
private def sndCoord (a : A) (n : ℕ) : C n :=
  DirectSum.component B ℕ C n (TrivSqZeroExt.snd a)

/-- Multiplying by `inl b` multiplies the `n`-th square-zero coordinate by `b n`. -/
private lemma sndCoord_inl_mul (b : B) (z : A) (n : ℕ) :
    sndCoord (TrivSqZeroExt.inl b * z) n = b n * sndCoord z n := by
  simp only [sndCoord, TrivSqZeroExt.snd_mul]
  simp only [TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, smul_zero, add_zero]
  change (b • TrivSqZeroExt.snd z) n = _
  rw [DirectSum.smul_apply]
  rfl

/-- The `n`-th square-zero coordinate is additive. -/
private lemma sndCoord_sub (a b : A) (n : ℕ) :
    sndCoord (a - b) n = sndCoord a n - sndCoord b n := rfl

/-- The square-zero coordinates of an element of `I ^ m` are multiples of `xbase n ^ m`. -/
private lemma sndCoord_eq_mul_of_mem_pow (m n : ℕ) (a : A) (ha : a ∈ I ^ m) :
    ∃ z : A, sndCoord a n = xbase n ^ m * sndCoord z n := by
  have hp : I ^ m = Ideal.span {u ^ m} := by rw [I, Ideal.span_singleton_pow]
  rw [hp, Ideal.mem_span_singleton] at ha
  obtain ⟨z, hz⟩ := ha
  exact ⟨z, by rw [hz, u_pow, sndCoord_inl_mul]; rfl⟩

private lemma xbase_pow_succ_eq_zero (n : ℕ) : xbase n ^ (n + 1) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span (by simp)

private lemma sndCoord_eq_zero_of_mem_succ_pow (n : ℕ) (a : A) (ha : a ∈ I ^ (n + 1)) :
    sndCoord a n = 0 := by
  obtain ⟨z, hz⟩ := sndCoord_eq_mul_of_mem_pow (n + 1) n a ha
  rw [hz, xbase_pow_succ_eq_zero]
  simp

private lemma residue_sndCoord_eq_zero_of_mem_I (n : ℕ) (a : A) (ha : a ∈ I) :
    residue n (sndCoord a n) = 0 := by
  obtain ⟨z, hz⟩ := sndCoord_eq_mul_of_mem_pow 1 n a (by simpa using ha)
  rw [hz]
  simp [residue, xbase]

/-- The `I`-adic completion of `A`. -/
private abbrev Rhat := AdicCompletion I A

private def t0 : A := TrivSqZeroExt.inl tbase
private def tR : Rhat := algebraMap A Rhat t0
private def partialPre (n : ℕ) : A := ∑ i ∈ Finset.range n, TrivSqZeroExt.inr (basis i)

private lemma partialSum_eq_t_mul (n : ℕ) : partialSum n = t0 * partialPre n := by
  simp [partialSum, term, partialPre, t0, TrivSqZeroExt.inl_mul_inr,
    Finset.mul_sum]

private def cseq : AdicCompletion.AdicCauchySequence I A :=
  AdicCompletion.AdicCauchySequence.mk I A partialSum partialSum_cauchy_step

/-- The element of the completion which is not divisible by `t`. -/
private def fhat : Rhat := AdicCompletion.mk I A cseq

private lemma eval_fhat (n : ℕ) :
    AdicCompletion.evalₐ I n fhat = Ideal.Quotient.mk (I ^ n) (partialSum n) := by
  simp [fhat, cseq, AdicCompletion.evalₐ_mk]

private lemma fhat_sub_partial_mem (n : ℕ) :
    fhat - algebraMap A Rhat (partialSum n) ∈ (I.map (algebraMap A Rhat)) ^ n := by
  have heval : AdicCompletion.evalₐ I n
      (fhat - algebraMap A Rhat (partialSum n)) = 0 := by
    rw [map_sub, eval_fhat, AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of]
    exact sub_self _
  have hle : I ^ n ≤ I ^ n • (⊤ : Submodule A A) := fun x hx => by
    simpa using Submodule.smul_mem_smul hx (Submodule.mem_top : (1 : A) ∈ ⊤)
  have heval' : AdicCompletion.eval I A n
      (fhat - algebraMap A Rhat (partialSum n)) = 0 := by
    rw [← AdicCompletion.factor_evalₐ_eq_eval I _ hle, heval]
    simp
  have hmem : fhat - algebraMap A Rhat (partialSum n) ∈
      (I ^ n • (⊤ : Submodule A Rhat)) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton u), LinearMap.mem_ker]
    exact heval'
  rw [Ideal.smul_top_eq_map] at hmem
  simpa only [Submodule.restrictScalars_mem, Ideal.map_pow] using hmem

private lemma termCoord (i n : ℕ) :
    (tbase • basis i) n = if i = n then xbase n ^ n else 0 := by
  rw [DirectSum.smul_apply]
  change tbase • basis i n = _
  rw [basis_coord]
  split_ifs with h
  · subst i
    change (proj n tbase) • (1 : C n) = _
    simp [proj, tbase, xbase]
  · simp

private def sndCoordHom (n : ℕ) : A →ₗ[B] C n :=
  (DirectSum.component B ℕ C n).comp (TrivSqZeroExt.sndHom B M)

private lemma sndCoord_partialSum (n : ℕ) :
    sndCoord (partialSum (n + 1)) n = xbase n ^ n := by
  change sndCoordHom n (partialSum (n + 1)) = _
  simp only [sndCoordHom, LinearMap.comp_apply, partialSum,
    TrivSqZeroExt.sndHom_apply, map_sum]
  change (∑ i ∈ Finset.range (n + 1), (tbase • basis i) n) = _
  simp [termCoord, Finset.sum_ite_eq']

private lemma sndCoord_t0_mul (z : A) (n : ℕ) :
    sndCoord (t0 * z) n = xbase n ^ n * sndCoord z n :=
  sndCoord_inl_mul tbase z n

/-- For a putative quotient `f = t · r`, the `n`-th coordinate of a representative of `r` has
residue `1` at every stage. -/
private lemma residue_sndCoord_eq_one
    (c : AdicCompletion.AdicCauchySequence I A) {r : Rhat}
    (hc : AdicCompletion.mk I A c = r) (hr : fhat = tR * r) (n : ℕ) :
    residue n (sndCoord (c.val (n + 1)) n) = 1 := by
  have heq : Ideal.Quotient.mk (I ^ (n + 1)) (partialSum (n + 1)) =
      Ideal.Quotient.mk (I ^ (n + 1)) (t0 * c.val (n + 1)) := by
    calc
      Ideal.Quotient.mk (I ^ (n + 1)) (partialSum (n + 1)) =
          AdicCompletion.evalₐ I (n + 1) fhat := (eval_fhat (n + 1)).symm
      _ = AdicCompletion.evalₐ I (n + 1) (tR * r) := by rw [hr]
      _ = Ideal.Quotient.mk (I ^ (n + 1)) (t0 * c.val (n + 1)) := by
        rw [map_mul, tR, AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of, ← hc,
          AdicCompletion.evalₐ_mk]
        rfl
  have hmem : partialSum (n + 1) - t0 * c.val (n + 1) ∈ I ^ (n + 1) :=
    (Ideal.Quotient.eq).mp heq
  have hz := sndCoord_eq_zero_of_mem_succ_pow n _ hmem
  have hcoord : sndCoord (partialSum (n + 1)) n = sndCoord (t0 * c.val (n + 1)) n := by
    rw [sndCoord_sub] at hz
    exact sub_eq_zero.mp hz
  rw [sndCoord_partialSum, sndCoord_t0_mul] at hcoord
  have hmul : xbase n ^ n * sndCoord (c.val (n + 1)) n =
      Ideal.Quotient.mk _ (Polynomial.X ^ n) := by
    simpa [xbase] using hcoord.symm
  exact residue_one_of_xpow_mul_eq n (sndCoord (c.val (n + 1)) n) hmul

/-- All stages of a Cauchy sequence have the same residues, because they differ by elements
of `I`. -/
private lemma residue_sndCoord_stable
    (c : AdicCompletion.AdicCauchySequence I A) (n : ℕ) :
    residue n (sndCoord (c.val 1) n) = residue n (sndCoord (c.val (n + 1)) n) := by
  have hC : c.val 1 ≡ c.val (n + 1) [SMOD (I ^ 1 • (⊤ : Submodule A A))] :=
    c.property (m := 1) (n := n + 1) (by omega)
  rw [SModEq.sub_mem] at hC
  have hCI : c.val 1 - c.val (n + 1) ∈ I := by
    simpa [pow_one, Ideal.smul_top_eq_map] using hC
  have hz := residue_sndCoord_eq_zero_of_mem_I n (c.val 1 - c.val (n + 1)) hCI
  rw [sndCoord_sub, map_sub] at hz
  exact sub_eq_zero.mp hz

private lemma fhat_not_mem_span_tR : fhat ∉ Ideal.span {tR} := by
  intro hf
  rw [Ideal.mem_span_singleton] at hf
  obtain ⟨r, hr⟩ := hf
  obtain ⟨c, hc⟩ := AdicCompletion.mk_surjective I A r
  have hall : ∀ n : ℕ, residue n (sndCoord (c.val 1) n) = 1 := fun n =>
    (residue_sndCoord_stable c n).trans (residue_sndCoord_eq_one c hc hr n)
  classical
  obtain ⟨n, hn⟩ := (TrivSqZeroExt.snd (c.val 1)).support.exists_notMem
  have hzero : sndCoord (c.val 1) n = 0 := DFinsupp.notMem_support_iff.mp hn
  simpa [hzero] using hall n

private abbrev Ibar : Ideal Rhat := I.map (algebraMap A Rhat)
private abbrev Jbar : Ideal Rhat := Ideal.span {tR}

private lemma Rhat_complete : IsAdicComplete Ibar Rhat :=
  (IsAdicComplete.map_algebraMap_iff (R := A) (S := Rhat) (M := Rhat) I).mpr
    (AdicCompletion.isAdicComplete (Submodule.fg_span_singleton u))

private lemma quotient_not_complete :
    ¬ IsAdicComplete (Ibar.map (Ideal.Quotient.mk Jbar)) (Rhat ⧸ Jbar) := by
  intro hcomp
  have hcomp' : IsAdicComplete Ibar (Rhat ⧸ Jbar) :=
    (IsAdicComplete.map_algebraMap_iff (R := Rhat) (S := Rhat ⧸ Jbar)
      (M := Rhat ⧸ Jbar) Ibar).mp hcomp
  have := Rhat_complete
  have hEq := (main_theorem_031a Ibar Rhat Jbar).mpr hcomp'
  have hmem (n : ℕ) : fhat ∈ Jbar ⊔ (Ibar ^ n • (⊤ : Submodule Rhat Rhat)) := by
    have hp : algebraMap A Rhat (partialSum n) ∈ Jbar := by
      rw [partialSum_eq_t_mul, map_mul, Ideal.mem_span_singleton]
      exact ⟨algebraMap A Rhat (partialPre n), by simp [tR]⟩
    have hd' : fhat - algebraMap A Rhat (partialSum n) ∈
        Ibar ^ n • (⊤ : Submodule Rhat Rhat) := by
      simpa using Submodule.smul_mem_smul (fhat_sub_partial_mem n)
        (Submodule.mem_top : (1 : Rhat) ∈ (⊤ : Submodule Rhat Rhat))
    simpa [add_sub_cancel_right] using Submodule.add_mem_sup hp hd'
  have hfJ : fhat ∈ Jbar := by
    rw [hEq]
    simpa only [Submodule.mem_iInf] using hmem
  exact fhat_not_mem_span_tR hfJ

/-- The same situation, transported into an arbitrary universe. -/
private abbrev Rbig := ULift.{u} Rhat

private def eSmallBig : Rhat ≃+* Rbig := ULift.ringEquiv.symm
private abbrev Ibig : Ideal Rbig := Ibar.map eSmallBig.toRingHom
private abbrev Jbig : Ideal Rbig := Jbar.map eSmallBig.toRingHom

private def Qe : (Rhat ⧸ Jbar) ≃+* (Rbig ⧸ Jbig) :=
  Ideal.quotientEquiv Jbar Jbig eSmallBig (by rfl)

private lemma map_adic_ideal_quotient :
    (Ibar.map (Ideal.Quotient.mk Jbar)).map Qe.toRingHom =
      Ibig.map (Ideal.Quotient.mk Jbig) := by
  change ((I.map (algebraMap A Rhat)).map (Ideal.Quotient.mk Jbar)).map Qe.toRingHom =
    ((I.map (algebraMap A Rhat)).map eSmallBig.toRingHom).map (Ideal.Quotient.mk Jbig)
  simp only [Ideal.map_map]
  have hq : Qe.toRingHom.comp ((Ideal.Quotient.mk Jbar).comp (algebraMap A Rhat)) =
      (Ideal.Quotient.mk Jbig).comp (eSmallBig.toRingHom.comp (algebraMap A Rhat)) := by
    ext x
    exact Ideal.quotientEquiv_mk Jbar Jbig eSmallBig rfl (algebraMap A Rhat x)
  rw [hq]

private lemma quotient_big_not_complete :
    ¬ IsAdicComplete (Ibig.map (Ideal.Quotient.mk Jbig)) (Rbig.{u} ⧸ Jbig) := by
  intro h
  rw [← map_adic_ideal_quotient] at h
  exact quotient_not_complete ((IsAdicComplete.congr_ringEquiv _ Qe).mp h)

private lemma Ibig_isPrincipal : (Ibig.{u}).IsPrincipal :=
  Submodule.IsPrincipal.map_ringHom eSmallBig.toRingHom
    (Submodule.IsPrincipal.map_ringHom (algebraMap A Rhat) ⟨u, rfl⟩)

private lemma Jbig_isPrincipal : (Jbig.{u}).IsPrincipal :=
  Submodule.IsPrincipal.map_ringHom eSmallBig.toRingHom ⟨tR, rfl⟩

private lemma Rbig_complete : IsAdicComplete (Ibig.{u}) Rbig.{u} :=
  (IsAdicComplete.congr_ringEquiv Ibar eSmallBig).2 Rhat_complete

end NoncompleteQuotient

/-- **Stacks 05JE.** A quotient by a principal ideal of a ring complete for another principal
ideal need not be complete for the induced ideal. -/
@[stacks 05JE]
theorem exists_complete_principal_ideal_not_complete_quotient :
    ∃ (R : Type u) (_ : CommRing R) (I J : Ideal R),
      I.IsPrincipal ∧ J.IsPrincipal ∧ IsAdicComplete I R ∧
        ¬ IsAdicComplete (I.map (Ideal.Quotient.mk J)) (R ⧸ J) :=
  ⟨NoncompleteQuotient.Rbig.{u}, inferInstance, NoncompleteQuotient.Ibig,
    NoncompleteQuotient.Jbig, NoncompleteQuotient.Ibig_isPrincipal,
    NoncompleteQuotient.Jbig_isPrincipal, NoncompleteQuotient.Rbig_complete,
    NoncompleteQuotient.quotient_big_not_complete⟩

end Stacks.Examples

end
