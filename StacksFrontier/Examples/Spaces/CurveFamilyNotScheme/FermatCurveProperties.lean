module

public import StacksFrontier.Examples.Spaces.CurveFamilyNotScheme.FermatCurve
public import StacksFrontier.AlgebraicGeometry.Curves.InseparableGenusChange
public import StacksFrontier.AlgebraicGeometry.Curves.InseparableGenusChangeCurveDimension
public import StacksFrontier.AlgebraicGeometry.Curves.PlaneCurveGenus
public import StacksFrontier.AlgebraicGeometry.Curves.PlaneCurveIrreducibleEquation
public import StacksFrontier.AlgebraicGeometry.ProjCoherentCohomologyFinite.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveChart.HypersurfaceFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
public import StacksFrontier.RingTheory.Smooth.PlaneHypersurface

/-!
# The Fermat cubic curve is a smooth proper curve of genus one

Let `k` be a field and `Y₀ = Proj (k[T₀, T₁, T₂] ⧸ (T₀ ^ 3 + T₁ ^ 3 + T₂ ^ 3))` the plane Fermat
cubic of `StacksFrontier/Examples/Spaces/CurveFamilyNotScheme/FermatCurve.lean`, the central fibre of
the cubic surface of [Stacks, Tag 0D5E]. This file proves that `Y₀ ⟶ Spec k` is proper, and,
when the characteristic of `k` is not three, that it is smooth, that `Y₀` is a curve over `k`,
and that its genus is one.

## Main results

* `Stacks.Examples.CurveFamilyNotScheme.idealOfClosedSubscheme_fermatEmbedding`: the homogeneous
  ideal of equations of `Y₀ ⊆ 𝐏²_k` is `(T₀ ^ 3 + T₁ ^ 3 + T₂ ^ 3)`.
* `Stacks.Examples.CurveFamilyNotScheme.irreducible_fermatCubic`: the Fermat cubic is irreducible
  in characteristic other than three.
* `Stacks.Examples.CurveFamilyNotScheme.isProper_fermatCurveToSpec`: `Y₀` is proper over `k`.
* `Stacks.Examples.CurveFamilyNotScheme.smooth_fermatCurveToSpec`: `Y₀` is smooth over `k`.
* `Stacks.Examples.CurveFamilyNotScheme.isCurve_fermatCurveToSpec`: `Y₀` is a curve over `k`.
* `Stacks.Examples.CurveFamilyNotScheme.genus_fermatCurveToSpec`: the genus of `Y₀` is one.

## Implementation notes

The three standard charts `Y₀ ∩ D₊(Tⱼ)` all have the same affine equation
`Y₀ ^ 3 + Y₁ ^ 3 + 1` (`dehomCoeff_fermatCubic`). Its partial derivatives are `3 Y₀ ^ 2` and
`3 Y₁ ^ 2`, which vanish together only where `Y₀ = Y₁ = 0`, off the curve, as soon as `3 ≠ 0`;
the Jacobian criterion `Stacks.Curves.isSmoothAt_iff_exists_pderiv_notMem` then makes each chart
smooth. Irreducibility is Eisenstein's criterion at `T₀ + T₁` for the cubic
`T₂ ^ 3 + (T₀ ^ 3 + T₁ ^ 3)` in `T₂`. The curve property is [Stacks, Tag 0BYC]
(`AlgebraicGeometry.ProjectiveSpectrum.Proj`
`.projectivePlane_isCurve_iff_irreducible_of_equidimensional`)
and the genus is the degree formula of [Stacks, Tag 0BYD]
(`AlgebraicGeometry.ProjectiveSpectrum.Proj.genus_planeCurve`) at degree three.

The hypothesis `IsAlgClosed k` of the main statements is not used.

## References

* [Stacks Project, Tag 0D5E](https://stacks.math.columbia.edu/tag/0D5E)
* [Stacks Project, Tag 0BYC](https://stacks.math.columbia.edu/tag/0BYC)
* [Stacks Project, Tag 0BYD](https://stacks.math.columbia.edu/tag/0BYD)
* [Stacks Project, Tag 00TE](https://stacks.math.columbia.edu/tag/00TE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial

open AlgebraicGeometry.ProjectiveSpectrum.Proj (idealOfClosedSubscheme PlaneCurveData
  genus_planeCurve)
open Stacks.ProjectiveChart (dehomCoeff dehomCoeff_eq_aeval subschemeChart chartQuotientEquiv
  isAffineOpen_subschemeChart iSup_subschemeChart_eq_top)
open Stacks.AlgebraicGeometry.ProjPolyChart (projToSpecCoeff)
open Stacks.RingTheory.HomogeneousQuotient (quotientGrading)
open AlgebraicGeometry.ProjectiveSpectrum.Proj
  (projectivePlane_isCohenMacaulay_iff_hasNoEmbeddedPoints
  projectivePlane_isCurve_iff_irreducible_of_equidimensional)
open Stacks.ProjQuotientChartIdeal (mem_idealOfClosedSubscheme_projQuotientHom
  exists_pow_mul_mem_of_mem_idealOfClosedSubscheme_projQuotientHom)

universe u

namespace Stacks.Examples.CurveFamilyNotScheme

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k]

/-! ### Characteristic not three -/

/-- In a field whose characteristic is not three, `3 ≠ 0`. -/
theorem three_ne_zero_of_ringChar_ne_three {k : Type u} [Field k] (h3 : ringChar k ≠ 3) :
    (3 : k) ≠ 0 := by
  intro h
  have hdvd : ringChar k ∣ 3 := ringChar.dvd (by exact_mod_cast h)
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h1
  · exact CharP.ringChar_ne_one h1
  · exact h3 h1

/-! ### Irreducibility of the Fermat cubic -/

/-- The linear form `Y₀ + Y₁` is prime in `k[Y₀, Y₁]`: splitting off `Y₀` it is the monic linear
polynomial `Y₀ + Y₁` over `k[Y₁]`. -/
theorem prime_X_zero_add_X_one :
    Prime (X 0 + X 1 : MvPolynomial (Fin 2) k) := by
  refine (MulEquiv.prime_iff (MvPolynomial.finSuccEquiv k 1).toMulEquiv).mp ?_
  change Prime (MvPolynomial.finSuccEquiv k 1 (X 0 + X 1))
  rw [map_add, MvPolynomial.finSuccEquiv_X_zero, show (1 : Fin 2) = Fin.succ 0 from rfl,
    MvPolynomial.finSuccEquiv_X_succ, ← sub_neg_eq_add, ← map_neg]
  exact Polynomial.prime_X_sub_C _

/-- Read as a cubic in `T₂` over `k[T₀, T₁]` (after the reindexing of
`Stacks.Curves.InseparableGenus.cubicChart`), the Fermat cubic is
`T₂ ^ 3 - (-(T₀ ^ 3 + T₁ ^ 3))`. -/
theorem cubicChart_fermatCubic :
    Stacks.Curves.InseparableGenus.cubicChart k (fermatCubic k) =
      Polynomial.X ^ 3 - Polynomial.C (-(X 0 ^ 3 + X 1 ^ 3)) := by
  rw [fermatCubic]
  simp only [map_add, map_pow, map_neg, Stacks.Curves.InseparableGenus.cubicChart_X_zero,
    Stacks.Curves.InseparableGenus.cubicChart_X_one,
    Stacks.Curves.InseparableGenus.cubicChart_X_two]
  ring

/-- `(Y₀ + Y₁) ^ 2` does not divide `Y₀ ^ 3 + Y₁ ^ 3` when `3 ≠ 0`: the cofactor
`Y₀ ^ 2 - Y₀ Y₁ + Y₁ ^ 2` takes the value `3` at `(-1, 1)`, where `Y₀ + Y₁` vanishes. -/
theorem not_sq_dvd_X_zero_pow_three_add_X_one_pow_three {k : Type u} [Field k] (h3 : (3 : k) ≠ 0) :
    ¬ (X 0 + X 1 : MvPolynomial (Fin 2) k) ^ 2 ∣ X 0 ^ 3 + X 1 ^ 3 := by
  intro h
  have hfac : (X 0 ^ 3 + X 1 ^ 3 : MvPolynomial (Fin 2) k) =
      (X 0 + X 1) * (X 0 ^ 2 - X 0 * X 1 + X 1 ^ 2) := by ring
  rw [hfac, sq] at h
  have hne : (X 0 + X 1 : MvPolynomial (Fin 2) k) ≠ 0 := (prime_X_zero_add_X_one k).ne_zero
  obtain ⟨r, hr⟩ := (mul_dvd_mul_iff_left hne).mp h
  have hev := congrArg (MvPolynomial.eval fun j : Fin 2 => if j = 0 then (-1 : k) else 1) hr
  simp only [map_add, map_sub, map_mul, map_pow, MvPolynomial.eval_X] at hev
  norm_num at hev
  exact h3 (by linear_combination hev)

/-- **The Fermat cubic is irreducible in characteristic other than three**, by Eisenstein's
criterion at `T₀ + T₁` for the cubic `T₂ ^ 3 + (T₀ ^ 3 + T₁ ^ 3)` in `T₂`. -/
theorem irreducible_fermatCubic {k : Type u} [Field k] (h3 : ringChar k ≠ 3) :
    Irreducible (fermatCubic k) := by
  refine (MulEquiv.irreducible_iff
    (Stacks.Curves.InseparableGenus.cubicChart k).toMulEquiv).mp ?_
  change Irreducible (Stacks.Curves.InseparableGenus.cubicChart k (fermatCubic k))
  rw [cubicChart_fermatCubic]
  refine Stacks.Curves.InseparableGenus.irreducible_X_pow_sub_C_of_prime_dvd_notDvd_sq
    (prime_X_zero_add_X_one k) (dvd_neg.mpr ⟨X 0 ^ 2 - X 0 * X 1 + X 1 ^ 2, by ring⟩) ?_
    (by decide)
  rw [dvd_neg]
  exact not_sq_dvd_X_zero_pow_three_add_X_one_pow_three (three_ne_zero_of_ringChar_ne_three h3)

/-! ### The ideal of equations -/

/-- The Fermat cubic is homogeneous of degree `3 • 1`, the form the chart presentations take. -/
theorem fermatCubic_mem_homogeneousSubmodule_smul :
    fermatCubic k ∈ MvPolynomial.homogeneousSubmodule (Fin 3) k (3 • 1) := by
  simpa using (MvPolynomial.mem_homogeneousSubmodule 3 _).2 (fermatCubic_isHomogeneous k)

/-- **The homogeneous ideal of equations of the Fermat cubic curve is
`(T₀ ^ 3 + T₁ ^ 3 + T₂ ^ 3)`.**
The inclusion `(F) ⊆ I(Y₀)` holds for every homogeneous ideal; conversely a homogeneous equation
`b` has `F ∣ T₀ ^ p · b` and `F ∣ T₁ ^ q · b` on two charts, and `T₀`, `T₁` are coprime. -/
theorem idealOfClosedSubscheme_fermatEmbedding :
    idealOfClosedSubscheme (MvPolynomial.homogeneousSubmodule (Fin 3) k) (fermatEmbedding k) =
      Ideal.span {fermatCubic k} := by
  have hgen := MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top (Fin 3) k
  refine le_antisymm (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ?_))
  · rintro - ⟨n, b, rfl, hzero⟩
    have hb : (b : MvPolynomial (Fin 3) k) ∈
        idealOfClosedSubscheme (MvPolynomial.homogeneousSubmodule (Fin 3) k)
          (fermatEmbedding k) :=
      AlgebraicGeometry.ProjectiveSpectrum.Proj.mem_idealOfClosedSubscheme _ _ n b hzero
    have hdvd := fun j : Fin 3 => (exists_pow_mul_mem_of_mem_idealOfClosedSubscheme_projQuotientHom
      _ (fermatIdeal k) hgen (MvPolynomial.isHomogeneous_X k j) b hb).imp
      fun _ => Ideal.mem_span_singleton.mp
    obtain ⟨p, hp⟩ := hdvd 0
    obtain ⟨q, hq⟩ := hdvd 1
    exact Ideal.mem_span_singleton.mpr
      (Stacks.Curves.InseparableGenus.dvd_of_dvd_X_zero_pow_mul_of_dvd_X_one_pow_mul k hp hq)
  · exact mem_idealOfClosedSubscheme_projQuotientHom _ (fermatIdeal k) hgen
      (⟨fermatCubic k, (MvPolynomial.mem_homogeneousSubmodule 3 _).2
        (fermatCubic_isHomogeneous k)⟩ : MvPolynomial.homogeneousSubmodule (Fin 3) k 3)
      (Ideal.mem_span_singleton_self _)

/-! ### Nonemptiness and irreducibility -/

/-- In characteristic other than three the homogeneous ideal `(F)` is prime. -/
theorem isPrime_fermatIdeal {k : Type u} [Field k] (h3 : ringChar k ≠ 3) :
    (fermatIdeal k).toIdeal.IsPrime := by
  have hne : fermatCubic k ≠ 0 := (irreducible_fermatCubic h3).ne_zero
  rw [toIdeal_fermatIdeal, Ideal.span_singleton_prime hne]
  exact UniqueFactorizationMonoid.irreducible_iff_prime.mp (irreducible_fermatCubic h3)

/-- **The Fermat cubic curve is nonempty** in characteristic other than three: the quotient by
`(F)` is a domain, and its zero ideal is relevant because `T₀ ∉ (F)`. -/
theorem nonempty_fermatCurve {k : Type u} [Field k] (h3 : ringChar k ≠ 3) :
    Nonempty (fermatCurve k) := by
  have := isPrime_fermatIdeal h3
  have : IsDomain (MvPolynomial (Fin 3) k ⧸ (fermatIdeal k).toIdeal) :=
    Ideal.Quotient.isDomain _
  refine ⟨⟨⊥, by
    rw [HomogeneousIdeal.toIdeal_bot]
    exact Ideal.isPrime_bot, fun hle => ?_⟩⟩
  have hmem : Ideal.Quotient.mk (fermatIdeal k).toIdeal (MvPolynomial.X 0) ∈
      (⊥ : HomogeneousIdeal
        (quotientGrading (MvPolynomial.homogeneousSubmodule (Fin 3) k) (fermatIdeal k))) :=
    hle (HomogeneousIdeal.mem_irrelevant_of_mem _ Nat.one_pos
      (Stacks.RingTheory.HomogeneousQuotient.quotientGrading_mk_mem _ _
        (MvPolynomial.isHomogeneous_X k 0)))
  have hdvd : fermatCubic k ∣ MvPolynomial.X 0 := Ideal.mem_span_singleton.mp
    (Ideal.Quotient.eq_zero_iff_mem.mp (Ideal.mem_bot.mp (HomogeneousIdeal.mem_iff.mpr hmem)))
  obtain ⟨q, hq⟩ := ((irreducible_fermatCubic h3).associated_of_dvd
    (MvPolynomial.X_prime (R := k) (i := 0)).irreducible hdvd).symm.dvd
  have hev := congrArg (MvPolynomial.eval (fun i : Fin 3 => if i = 2 then (1 : k) else 0)) hq
  simp [fermatCubic] at hev

/-- **The Fermat cubic curve is irreducible** in characteristic other than three: it is `Proj` of
a nonempty graded domain. -/
theorem irreducibleSpace_fermatCurve {k : Type u} [Field k] (h3 : ringChar k ≠ 3) :
    IrreducibleSpace (fermatCurve k) := by
  have := isPrime_fermatIdeal h3
  have : IsDomain (MvPolynomial (Fin 3) k ⧸ (fermatIdeal k).toIdeal) :=
    Ideal.Quotient.isDomain _
  have := nonempty_fermatCurve h3
  exact AlgebraicGeometry.irreducibleSpace_proj_of_isDomain _

/-! ### The affine equation on the charts -/

/-- On `D₊(T₀)` the Fermat cubic becomes `Y₀ ^ 3 + Y₁ ^ 3 + 1`. -/
theorem dehomCoeff_fermatCubic_zero :
    dehomCoeff k (0 : Fin 3) (fermatCubic k) = X 0 ^ 3 + X 1 ^ 3 + 1 := by
  have h1 : finSuccEquiv' (0 : Fin 3) 1 = some 0 := by decide
  have h2 : finSuccEquiv' (0 : Fin 3) 2 = some 1 := by decide
  rw [dehomCoeff_eq_aeval, fermatCubic]
  simp [h1, h2]
  ring

/-- On `D₊(T₁)` the Fermat cubic becomes `Y₀ ^ 3 + Y₁ ^ 3 + 1`. -/
theorem dehomCoeff_fermatCubic_one :
    dehomCoeff k (1 : Fin 3) (fermatCubic k) = X 0 ^ 3 + X 1 ^ 3 + 1 := by
  have h1 : finSuccEquiv' (1 : Fin 3) 0 = some 0 := by decide
  have h2 : finSuccEquiv' (1 : Fin 3) 2 = some 1 := by decide
  rw [dehomCoeff_eq_aeval, fermatCubic]
  simp [h1, h2]
  ring

/-- On `D₊(T₂)` the Fermat cubic becomes `Y₀ ^ 3 + Y₁ ^ 3 + 1`. -/
theorem dehomCoeff_fermatCubic_two :
    dehomCoeff k (2 : Fin 3) (fermatCubic k) = X 0 ^ 3 + X 1 ^ 3 + 1 := by
  have h1 : finSuccEquiv' (2 : Fin 3) 0 = some 0 := by decide
  have h2 : finSuccEquiv' (2 : Fin 3) 1 = some 1 := by decide
  rw [dehomCoeff_eq_aeval, fermatCubic]
  simp [h1, h2]

/-- **All three dehomogenizations of the Fermat cubic are `Y₀ ^ 3 + Y₁ ^ 3 + 1`.** -/
theorem dehomCoeff_fermatCubic (j : Fin 3) :
    dehomCoeff k j (fermatCubic k) = X 0 ^ 3 + X 1 ^ 3 + 1 := by
  obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by fin_cases j <;> simp
  · exact dehomCoeff_fermatCubic_zero k
  · exact dehomCoeff_fermatCubic_one k
  · exact dehomCoeff_fermatCubic_two k

/-- The affine Fermat cubic `Y₀ ^ 3 + Y₁ ^ 3 + 1` is nonzero and not a unit: it takes the value
`1` at the origin and vanishes at `(-1, 0)`. -/
theorem affineFermat_ne_zero_and_not_isUnit :
    (X 0 ^ 3 + X 1 ^ 3 + 1 : MvPolynomial (Fin 2) k) ≠ 0 ∧
      ¬ IsUnit (X 0 ^ 3 + X 1 ^ 3 + 1 : MvPolynomial (Fin 2) k) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hev := congrArg (MvPolynomial.eval (0 : Fin 2 → k)) h
    simp at hev
  · have hu := h.map (MvPolynomial.eval fun j : Fin 2 => if j = 0 then (-1 : k) else 0)
    norm_num at hu

/-! ### Smoothness -/

/-- **Jacobian criterion for an affine plane curve, globally.** `k[Y₀, Y₁] ⧸ (f)` is smooth over
`k` when no prime containing `f` contains both partial derivatives of `f`. -/
theorem smooth_quotient_span_of_forall_isPrime {k : Type u} [Field k]
    {f : MvPolynomial (Fin 2) k} (hne : f ≠ 0)
    (hnu : ¬ IsUnit f) (h : ∀ P : Ideal (MvPolynomial (Fin 2) k), P.IsPrime → f ∈ P →
      (∀ i, pderiv i f ∈ P) → False) :
    Algebra.Smooth k (MvPolynomial (Fin 2) k ⧸ Ideal.span {f}) := by
  have hfp : Algebra.FinitePresentation k (MvPolynomial (Fin 2) k ⧸ Ideal.span {f}) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton _)
  refine { formallySmooth := ?_, finitePresentation := hfp }
  rw [← Algebra.smoothLocus_eq_univ_iff]
  refine Set.eq_univ_of_forall fun Q => ?_
  change Algebra.IsSmoothAt k Q.asIdeal
  rw [Stacks.Curves.isSmoothAt_iff_exists_pderiv_notMem hne hnu]
  by_contra! hQ
  refine h _ (Ideal.comap_isPrime _ _) ?_ hQ
  change Ideal.Quotient.mk _ _ ∈ Q.asIdeal
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)]
  exact zero_mem _

/-- **The affine Fermat cubic is smooth over `k` when `3 ≠ 0`.** Its partial derivatives are
`3 Y₀ ^ 2` and `3 Y₁ ^ 2`; a prime containing both contains `Y₀` and `Y₁`, hence
`1 = (Y₀ ^ 3 + Y₁ ^ 3 + 1) - Y₀ ^ 3 - Y₁ ^ 3`, if it also contains the equation. -/
theorem smooth_affineFermat {k : Type u} [Field k] (h3 : (3 : k) ≠ 0) :
    Algebra.Smooth k (MvPolynomial (Fin 2) k ⧸
      Ideal.span {(X 0 ^ 3 + X 1 ^ 3 + 1 : MvPolynomial (Fin 2) k)}) := by
  obtain ⟨hne, hnu⟩ := affineFermat_ne_zero_and_not_isUnit k
  refine smooth_quotient_span_of_forall_isPrime hne hnu fun P hP hf h => ?_
  have hunit : IsUnit (3 : MvPolynomial (Fin 2) k) := by
    have h := (isUnit_iff_ne_zero.mpr h3).map (C : k →+* MvPolynomial (Fin 2) k)
    rwa [map_ofNat] at h
  have hX : ∀ i : Fin 2, X i ∈ P := by
    intro i
    have hd : pderiv i (X 0 ^ 3 + X 1 ^ 3 + 1 : MvPolynomial (Fin 2) k) = 3 * X i ^ 2 := by
      obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
      all_goals simp [pderiv_X]
    have hmem := hd ▸ h i
    have hsq : X i ^ 2 ∈ P :=
      (hP.mem_or_mem hmem).resolve_left fun h' => hP.ne_top (Ideal.eq_top_of_isUnit_mem _ h' hunit)
    exact hP.mem_of_pow_mem 2 hsq
  refine hP.ne_top ((Ideal.eq_top_iff_one _).mpr ?_)
  have : (X 0 ^ 3 + X 1 ^ 3 + 1 : MvPolynomial (Fin 2) k) - X 0 ^ 2 * X 0 - X 1 ^ 2 * X 1 = 1 := by
    ring
  rw [← this]
  exact sub_mem (sub_mem hf (Ideal.mul_mem_left _ _ (hX 0))) (Ideal.mul_mem_left _ _ (hX 1))

/-- **The Fermat cubic curve is smooth over `k` when `3 ≠ 0`.** Smoothness is checked on the three
standard charts, each of which is `k[Y₀, Y₁] ⧸ (Y₀ ^ 3 + Y₁ ^ 3 + 1)` as a `k`-algebra. -/
theorem smooth_fermatCurveToSpec_of_three_ne_zero {k : Type u} [Field k] (h3 : (3 : k) ≠ 0) :
    Smooth (fermatCurveToSpec k) := by
  have hiso := (HasRingHomProperty.isLocal_ringHomProperty @Smooth).respectsIso
  refine HasRingHomProperty.of_iSup_eq_top (P := @Smooth) (Q := RingHom.Smooth)
    (fun l : Fin 3 => ⟨subschemeChart (fermatEmbedding k) l,
      isAffineOpen_subschemeChart (fermatEmbedding k) l⟩)
    (iSup_subschemeChart_eq_top (fermatEmbedding k)) fun l => ?_
  set ψ := ((fermatCurveToSpec k).appLE ⊤ (subschemeChart (fermatEmbedding k) l) le_top).hom
  set e : k ≃+* Γ(Spec (CommRingCat.of k), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
  set ε := chartQuotientEquiv (fermatEmbedding k) l (fermatCubic k)
    (fermatCubic_mem_homogeneousSubmodule_smul k) (idealOfClosedSubscheme_fermatEmbedding k)
  have hcomp : ψ.comp e.toRingHom = ε.toRingHom.comp
      (algebraMap k (MvPolynomial (Fin 2) k ⧸ Ideal.span {dehomCoeff k l (fermatCubic k)})) := by
    ext r
    exact (Stacks.ProjectiveChart.chartPresentation_C (fermatEmbedding k) l r).symm
  have hQ : RingHom.Smooth
      (algebraMap k (MvPolynomial (Fin 2) k ⧸ Ideal.span {dehomCoeff k l (fermatCubic k)})) := by
    rw [RingHom.smooth_algebraMap, dehomCoeff_fermatCubic]
    exact smooth_affineFermat h3
  have h1 : RingHom.Smooth (ψ.comp e.toRingHom) := by
    rw [hcomp]
    exact hiso.1 _ _ hQ
  have h2 := hiso.2 (ψ.comp e.toRingHom) e.symm h1
  rwa [RingHom.comp_assoc, show e.toRingHom.comp e.symm.toRingHom = RingHom.id _ from
    RingHom.ext fun x => e.apply_symm_apply x, RingHom.comp_id] at h2

/-- **The Fermat cubic curve is smooth over `k`** in characteristic other than three. -/
theorem smooth_fermatCurveToSpec [IsAlgClosed k] (h3 : ringChar k ≠ 3) :
    Smooth (fermatCurveToSpec k) :=
  smooth_fermatCurveToSpec_of_three_ne_zero (three_ne_zero_of_ringChar_ne_three h3)

/-! ### Properness -/

/-- **The Fermat cubic curve is proper over `k`**: it is a closed subscheme of the projective
plane, which is proper over `k`. -/
instance isProper_fermatCurveToSpec : IsProper (fermatCurveToSpec k) := by
  have := Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff k 2
  infer_instance

/-! ### Dimension and embedded points -/

/-- **Each standard chart of the Fermat cubic curve has dimension one**: its ring of sections is
`k[Y₀, Y₁] ⧸ (Y₀ ^ 3 + Y₁ ^ 3 + 1)`, a hypersurface in the affine plane. -/
theorem topologicalKrullDim_subschemeChart_fermatEmbedding (j : Fin 3) :
    topologicalKrullDim
        ((subschemeChart (fermatEmbedding k) j : Set (fermatCurve k))) = 1 := by
  obtain ⟨hne, hnu⟩ := affineFermat_ne_zero_and_not_isUnit k
  rw [← dehomCoeff_fermatCubic k j] at hne hnu
  rw [AlgebraicGeometry.topologicalKrullDim_coe_eq_ringKrullDim_of_isAffineOpen _
      (isAffineOpen_subschemeChart (fermatEmbedding k) j),
    ← ringKrullDim_eq_of_ringEquiv
      (chartQuotientEquiv (fermatEmbedding k) j (fermatCubic k)
        (fermatCubic_mem_homogeneousSubmodule_smul k)
        (idealOfClosedSubscheme_fermatEmbedding k)),
    Stacks.MvPolynomial.ringKrullDim_quotient_span_singleton k (Fin 2) (n := 1)
      (by simp) _ hne hnu]
  rfl

/-- **The Fermat cubic curve has dimension one**: each point has a chart of dimension one for a
neighbourhood, and a chart is a subspace. -/
theorem topologicalKrullDim_fermatCurve : topologicalKrullDim (fermatCurve k) = 1 := by
  refine le_antisymm ?_ ?_
  · rw [TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim]
    refine iSup_le fun x => ?_
    have hx : x ∈ (⨆ j : Fin 3, subschemeChart (fermatEmbedding k) j) := by
      rw [iSup_subschemeChart_eq_top]
      trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    refine le_trans ?_ (topologicalKrullDim_subschemeChart_fermatEmbedding k j).le
    exact iInf_le_of_le ((subschemeChart (fermatEmbedding k) j : Set (fermatCurve k)))
      (iInf_le_of_le (subschemeChart (fermatEmbedding k) j).2 (iInf_le _ hj))
  · rw [← topologicalKrullDim_subschemeChart_fermatEmbedding k 0]
    exact topologicalKrullDim_subspace_le (fermatCurve k) _

/-- **The Fermat cubic curve is equidimensional of dimension one** in characteristic other than
three: it is irreducible, so its only irreducible component is the whole space. -/
theorem forall_mem_irreducibleComponents_topologicalKrullDim_fermatCurve {k : Type u} [Field k]
    (h3 : ringChar k ≠ 3) :
    ∀ W ∈ irreducibleComponents (fermatCurve k), topologicalKrullDim W = 1 := by
  have := irreducibleSpace_fermatCurve h3
  intro W hW
  rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hW
  subst hW
  rw [topologicalKrullDim_univ]
  exact topologicalKrullDim_fermatCurve k

/-- **The Fermat cubic curve has no embedded points** in characteristic other than three: it is
smooth over `k`, hence regular, hence Cohen–Macaulay, which for a one-dimensional closed
subscheme of `𝐏²_k` is the absence of embedded points ([Stacks, Tag 0BYB]). -/
theorem hasNoEmbeddedPoints_fermatCurve {k : Type u} [Field k] (h3 : ringChar k ≠ 3) :
    HasNoEmbeddedPoints (fermatCurve k) := by
  have := smooth_fermatCurveToSpec_of_three_ne_zero (three_ne_zero_of_ringChar_ne_three h3)
  exact (projectivePlane_isCohenMacaulay_iff_hasNoEmbeddedPoints k (fermatEmbedding k)
      (forall_mem_irreducibleComponents_topologicalKrullDim_fermatCurve h3)).mp
    (AlgebraicGeometry.isCohenMacaulay_of_isRegular
      (AlgebraicGeometry.isRegular_of_smooth_over_field (fermatCurveToSpec k)))

/-! ### The main statements -/

/-- **The Fermat cubic curve is a curve over `k`** in characteristic other than three
([Stacks, Tag 0BYC]: a one-dimensional plane curve is a curve exactly when its equation is
irreducible). -/
theorem isCurve_fermatCurveToSpec [IsAlgClosed k] (h3 : ringChar k ≠ 3) :
    IsCurve k (fermatCurveToSpec k) := by
  have := nonempty_fermatCurve h3
  exact (projectivePlane_isCurve_iff_irreducible_of_equidimensional k (fermatEmbedding k)
    (forall_mem_irreducibleComponents_topologicalKrullDim_fermatCurve h3)
    (idealOfClosedSubscheme_fermatEmbedding k)).mpr (irreducible_fermatCubic h3)

/-- The Fermat cubic curve as a plane curve of degree three, in the sense of
[Stacks, Tag 0BYB], in characteristic other than three. -/
def fermatPlaneCurveData {k : Type u} [Field k] (h3 : ringChar k ≠ 3) : PlaneCurveData k :=
  haveI := nonempty_fermatCurve h3
  { Z := fermatCurve k
    i := fermatEmbedding k
    hasNoEmbeddedPoints := hasNoEmbeddedPoints_fermatCurve h3
    equidimensional := forall_mem_irreducibleComponents_topologicalKrullDim_fermatCurve h3
    deg := 3
    F := fermatCubic k
    isHomogeneous := (MvPolynomial.mem_homogeneousSubmodule 3 _).2 (fermatCubic_isHomogeneous k)
    span_eq := idealOfClosedSubscheme_fermatEmbedding k }

/-- The degree recorded by `fermatPlaneCurveData` is three. -/
@[simp] theorem fermatPlaneCurveData_deg {k : Type u} [Field k] (h3 : ringChar k ≠ 3) :
    (fermatPlaneCurveData h3).deg = 3 := rfl

/-- **The genus of the Fermat cubic curve is one** in characteristic other than three: the degree
formula `(d - 1)(d - 2)/2` of [Stacks, Tag 0BYD] at `d = 3`. -/
theorem genus_fermatCurveToSpec [IsAlgClosed k] (h3 : ringChar k ≠ 3) :
    genus (fermatCurveToSpec k) = 1 :=
  (genus_planeCurve (fermatPlaneCurveData h3)).trans (by rw [fermatPlaneCurveData_deg])

end Stacks.Examples.CurveFamilyNotScheme

end
