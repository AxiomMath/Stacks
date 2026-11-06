module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportClopen
public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.BaseChangeDegree
public import StacksFrontier.AlgebraicGeometry.Curves.Models.ExceptionalComponentsMeet
public import StacksFrontier.AlgebraicGeometry.Curves.Models.RealConicModel
public import StacksFrontier.AlgebraicGeometry.Curves.PlaneCurveGenus
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.AutomaticProperties
public import StacksFrontier.AlgebraicGeometry.Examples.CoefficientProjFibreModels
public import StacksFrontier.AlgebraicGeometry.HProjective.Basic
public import StacksFrontier.AlgebraicGeometry.ProjModelStructureMap.ComparisonNatural
public import StacksFrontier.AlgebraicGeometry.ProjModelStructureMap.CoefficientBaseChangeCartesian
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.HypersurfaceCohomology
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.IdealSheafOfHypersurface
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.RingTheory.MvPolynomial.HypersurfaceDimension
public import StacksFrontier.RingTheory.Smooth.PlaneHypersurface

/-!
# The smooth conic `T₁² + T₂² = aT₀²` over a field

Let `K` be a field in which `2` is invertible and let `a ∈ K` be nonzero. The plane conic

`Z = V(T₁² + T₂² - aT₀²) ⊆ ℙ²_K`

is a smooth projective curve over `K` with `H⁰(Z, 𝒪_Z) = K`. This is the generic fibre of the
conic model of [Stacks, Tag 0CDL], where `a = π`.

## Main results

* `Stacks.Models.RealConicModel.smooth_toSpec`: `Z` is smooth over `K`.
* `Stacks.Models.RealConicModel.topologicalKrullDim_scheme`: `Z` has dimension one.
* `Stacks.Models.RealConicModel.isIso_globalSections`: `H⁰(Z, 𝒪_Z) = K`.
* `Stacks.Models.RealConicModel.isCurve_toSpec`: `Z` is a curve over `K`.
* `Stacks.Models.RealConicModel.isHProjective_toSpec`: `Z` is projective over `K`.

## Implementation notes

Everything is read off the three standard charts `K[Y₀, Y₁]/(Y₀² + Y₁² - a)` and
`K[Y₀, Y₁]/(1 + Y₁² - aY₀²)` of `Stacks.Models.PlaneCurveModel.chartEquiv`. Smoothness is the
Jacobian criterion for plane curves, `Stacks.Curves.isSmoothAt_iff_exists_pderiv_notMem`: no
prime contains both partial derivatives of a chart equation. The dimension is the Krull dimension
of the charts, `Stacks.MvPolynomial.ringKrullDim_quotient_span_singleton`. The global sections
come from the sequence `0 → 𝒪(-2) → 𝒪 → 𝒪_Z → 0` on `ℙ²_K`. A smooth scheme over a field with
only constant global functions is connected, hence integral.

## References

* [Stacks Project, Tag 0CDL](https://stacks.math.columbia.edu/tag/0CDL)
* [Stacks Project, Tag 0BYD](https://stacks.math.columbia.edu/tag/0BYD)
* [Stacks Project, Tag 00TE](https://stacks.math.columbia.edu/tag/00TE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
open AlgebraicGeometry.ProjectiveSpectrum.Proj
  (projectiveSpace_ker_eq_zeroScheme_of_idealOfClosedSubscheme_eq_span)
open Stacks.ProjectiveSpace.Cohomology

universe u

namespace Stacks.Models.RealConicModel

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type u} [Field K]

/-! ### The chart equations are nonzero non-units -/

/-- A polynomial over a field with a nonzero coefficient at a nonconstant monomial is neither zero
nor a unit. -/
theorem ne_zero_and_not_isUnit_of_coeff_ne_zero {f : MvPolynomial (Fin 2) K} {m : Fin 2 →₀ ℕ}
    (hm : m ≠ 0) (hf : f.coeff m ≠ 0) : f ≠ 0 ∧ ¬ IsUnit f := by
  refine ⟨fun h => hf (by rw [h, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]), fun h => ?_⟩
  obtain ⟨r, -, rfl⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp h
  exact hf (coeff_C_of_ne_zero hm r)

/-- The polynomial `Y₀² + Y₁² - a` in `K[Y₀, Y₁]` is neither zero nor a unit. -/
theorem chart_zero_ne_zero_and_not_isUnit (a : K) :
    (X 0 ^ 2 + X 1 ^ 2 - C a : MvPolynomial (Fin 2) K) ≠ 0 ∧
      ¬ IsUnit (X 0 ^ 2 + X 1 ^ 2 - C a : MvPolynomial (Fin 2) K) :=
  ne_zero_and_not_isUnit_of_coeff_ne_zero (m := Finsupp.single 0 2) (by simp)
    (by rw [coeff_chart_zero]; exact one_ne_zero)

/-- The polynomial `1 + Y₁² - aY₀²` in `K[Y₀, Y₁]` is neither zero nor a unit. -/
theorem chart_one_ne_zero_and_not_isUnit (a : K) :
    (1 + X 1 ^ 2 - C a * X 0 ^ 2 : MvPolynomial (Fin 2) K) ≠ 0 ∧
      ¬ IsUnit (1 + X 1 ^ 2 - C a * X 0 ^ 2 : MvPolynomial (Fin 2) K) :=
  ne_zero_and_not_isUnit_of_coeff_ne_zero (m := Finsupp.single 1 2) (by simp)
    (by rw [coeff_chart_one]; exact one_ne_zero)

/-- The dehomogenizations of `T₁² + T₂² - aT₀²` are nonzero non-units. -/
theorem dehomCoeff_ne_zero_and_not_isUnit (a : K) (k : Fin 3) :
    Stacks.ProjectiveChart.dehomCoeff K k (equation a) ≠ 0 ∧
      ¬ IsUnit (Stacks.ProjectiveChart.dehomCoeff K k (equation a)) := by
  obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
  · rw [dehomCoeff_equation_zero]
    exact chart_zero_ne_zero_and_not_isUnit a
  · rw [dehomCoeff_equation_one]
    exact chart_one_ne_zero_and_not_isUnit a
  · rw [dehomCoeff_equation_two]
    exact chart_one_ne_zero_and_not_isUnit a

/-! ### Smoothness of the charts -/

variable {a : K}

private theorem isUnit_C_two (h2 : (2 : K) ≠ 0) : IsUnit (2 : MvPolynomial (Fin 2) K) := by
  have h := (isUnit_iff_ne_zero.mpr h2).map (C : K →+* MvPolynomial (Fin 2) K)
  rwa [map_ofNat] at h

/-- If `c * X i` lies in a prime ideal `P` and `c` is a unit, then `X i ∈ P`. -/
private theorem X_mem_of_mul_X_mem {P : Ideal (MvPolynomial (Fin 2) K)} (hP : P.IsPrime)
    {c : MvPolynomial (Fin 2) K} (hc : IsUnit c) {i : Fin 2} (h : c * X i ∈ P) : X i ∈ P :=
  (hP.mem_or_mem h).resolve_left fun h' => hP.ne_top (Ideal.eq_top_of_isUnit_mem _ h' hc)

/-- Jacobian criterion: `K[Y₀, Y₁]/(f)` is smooth over `K` when no prime containing `f` contains
both partial derivatives of `f`. -/
private theorem smooth_quotient_span_of_forall_isPrime {f : MvPolynomial (Fin 2) K} (hne : f ≠ 0)
    (hnu : ¬ IsUnit f) (h : ∀ P : Ideal (MvPolynomial (Fin 2) K), P.IsPrime → f ∈ P →
      (∀ i, pderiv i f ∈ P) → False) :
    Algebra.Smooth K (MvPolynomial (Fin 2) K ⧸ Ideal.span {f}) := by
  have hfp : Algebra.FinitePresentation K (MvPolynomial (Fin 2) K ⧸ Ideal.span {f}) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton _)
  refine { formallySmooth := ?_, finitePresentation := hfp }
  rw [← Algebra.smoothLocus_eq_univ_iff]
  refine Set.eq_univ_of_forall fun Q => ?_
  show Algebra.IsSmoothAt K Q.asIdeal
  rw [Stacks.Curves.isSmoothAt_iff_exists_pderiv_notMem hne hnu]
  by_contra! hQ
  refine h _ (Ideal.comap_isPrime _ _) ?_ hQ
  show Ideal.Quotient.mk _ _ ∈ Q.asIdeal
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)]
  exact zero_mem _

/-- `K[Y₀, Y₁]/(Y₀² + Y₁² - a)` is smooth over `K`. -/
theorem smooth_chart_zero (ha : a ≠ 0) (h2 : (2 : K) ≠ 0) :
    Algebra.Smooth K (MvPolynomial (Fin 2) K ⧸
      Ideal.span {(X 0 ^ 2 + X 1 ^ 2 - C a : MvPolynomial (Fin 2) K)}) := by
  obtain ⟨hne, hnu⟩ := chart_zero_ne_zero_and_not_isUnit a
  refine smooth_quotient_span_of_forall_isPrime hne hnu fun P hP hf h => ?_
  have hX : ∀ i : Fin 2, X i ∈ P := by
    intro i
    have hd : pderiv i (X 0 ^ 2 + X 1 ^ 2 - C a : MvPolynomial (Fin 2) K) = 2 * X i := by
      obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
      all_goals simp [pderiv_X]
    exact X_mem_of_mul_X_mem hP (isUnit_C_two h2) (hd ▸ h i)
  have hC : (C a : MvPolynomial (Fin 2) K) ∈ P := by
    have : (X 0 * X 0 + X 1 * X 1 : MvPolynomial (Fin 2) K) - (X 0 ^ 2 + X 1 ^ 2 - C a) = C a := by
      ring
    rw [← this]
    exact sub_mem (add_mem (Ideal.mul_mem_right _ _ (hX 0)) (Ideal.mul_mem_right _ _ (hX 1))) hf
  exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ hC ((isUnit_iff_ne_zero.mpr ha).map C))

/-- `K[Y₀, Y₁]/(1 + Y₁² - aY₀²)` is smooth over `K`. -/
theorem smooth_chart_one (ha : a ≠ 0) (h2 : (2 : K) ≠ 0) :
    Algebra.Smooth K (MvPolynomial (Fin 2) K ⧸
      Ideal.span {(1 + X 1 ^ 2 - C a * X 0 ^ 2 : MvPolynomial (Fin 2) K)}) := by
  obtain ⟨hne, hnu⟩ := chart_one_ne_zero_and_not_isUnit a
  refine smooth_quotient_span_of_forall_isPrime hne hnu fun P hP hf h => ?_
  have hunit : IsUnit (-(2 * C a) : MvPolynomial (Fin 2) K) :=
    ((isUnit_C_two h2).mul ((isUnit_iff_ne_zero.mpr ha).map C)).neg
  have hX0 : (X 0 : MvPolynomial (Fin 2) K) ∈ P := by
    have hd : pderiv 0 (1 + X 1 ^ 2 - C a * X 0 ^ 2 : MvPolynomial (Fin 2) K) =
        -(2 * C a) * X 0 := by
      simp [pderiv_X]
      ring
    exact X_mem_of_mul_X_mem hP hunit (hd ▸ h 0)
  have hX1 : (X 1 : MvPolynomial (Fin 2) K) ∈ P := by
    have hd : pderiv 1 (1 + X 1 ^ 2 - C a * X 0 ^ 2 : MvPolynomial (Fin 2) K) = 2 * X 1 := by
      simp [pderiv_X]
    exact X_mem_of_mul_X_mem hP (isUnit_C_two h2) (hd ▸ h 1)
  refine hP.ne_top ((Ideal.eq_top_iff_one _).mpr ?_)
  have : (1 + X 1 ^ 2 - C a * X 0 ^ 2 : MvPolynomial (Fin 2) K) - X 1 * X 1 +
      (C a * X 0) * X 0 = 1 := by ring
  rw [← this]
  exact add_mem (sub_mem hf (Ideal.mul_mem_right _ _ hX1)) (Ideal.mul_mem_left _ _ hX0)

/-! ### The conic is smooth of dimension one -/

/-- The variable `T₀` does not divide `T₁² + T₂² - aT₀²` in `K[T₀, T₁, T₂]`. -/
theorem not_X_zero_dvd_equation_field (a : K) :
    ¬ (X 0 : MvPolynomial (Fin 3) K) ∣ equation a :=
  not_X_zero_dvd_equation a

/-- **The conic `V(T₁² + T₂² - aT₀²)` is smooth over `K`.** -/
theorem smooth_toSpec (ha : a ≠ 0) (h2 : (2 : K) ≠ 0) : Smooth (toSpec a) := by
  refine PlaneCurveModel.hasRingHomProperty_toSpec (P := @Smooth) (Q := RingHom.Smooth)
    (equation a) (isHomogeneous_equation a) 0 (not_X_zero_dvd_equation a) fun k => ?_
  rw [RingHom.smooth_algebraMap]
  obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
  · rw [dehomCoeff_equation_zero]
    exact smooth_chart_zero ha h2
  · rw [dehomCoeff_equation_one]
    exact smooth_chart_one ha h2
  · rw [dehomCoeff_equation_two]
    exact smooth_chart_one ha h2

/-- Each chart of the conic has dimension one. -/
theorem topologicalKrullDim_chart (a : K) (k : Fin 3) :
    topologicalKrullDim
      ((PlaneCurveModel.chart (equation a) (isHomogeneous_equation a) k : Set (scheme a))) = 1 := by
  obtain ⟨hne, hnu⟩ := dehomCoeff_ne_zero_and_not_isUnit a k
  rw [AlgebraicGeometry.topologicalKrullDim_coe_eq_ringKrullDim_of_isAffineOpen _
      (PlaneCurveModel.isAffineOpen_chart (equation a) (isHomogeneous_equation a) k),
    ← ringKrullDim_eq_of_ringEquiv (PlaneCurveModel.chartEquiv (equation a)
      (isHomogeneous_equation a) 0 (not_X_zero_dvd_equation a) k),
    Stacks.MvPolynomial.ringKrullDim_quotient_span_singleton K (Fin 2) (n := 1)
      (by simp) _ hne hnu]
  rfl

/-- **The conic `V(T₁² + T₂² - aT₀²)` has dimension one.** -/
theorem topologicalKrullDim_scheme (a : K) : topologicalKrullDim (scheme a) = 1 := by
  refine le_antisymm ?_ ?_
  · rw [TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim]
    refine iSup_le fun x => ?_
    have hx :
        x ∈ (⨆ k : Fin 3, PlaneCurveModel.chart (equation a) (isHomogeneous_equation a) k) := by
      rw [PlaneCurveModel.iSup_chart_eq_top]
      trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    refine le_trans ?_ (topologicalKrullDim_chart a k).le
    exact iInf_le_of_le ((PlaneCurveModel.chart (equation a) (isHomogeneous_equation a) k :
      Set (scheme a))) (iInf_le_of_le
        (PlaneCurveModel.chart (equation a) (isHomogeneous_equation a) k).2 (iInf_le _ hk))
  · rw [← topologicalKrullDim_chart a 0]
    exact topologicalKrullDim_subspace_le (scheme a) _

/-! ### The global sections -/

/-- The polynomial `T₁² + T₂² - aT₀²` lies in the degree-`2` homogeneous submodule. -/
theorem equation_mem_homogeneousSubmodule (a : K) :
    equation a ∈ homogeneousSubmodule (Fin 3) K 2 :=
  (mem_homogeneousSubmodule 2 _).2 (isHomogeneous_equation a)

/-- The polynomial `T₁² + T₂² - aT₀²` in `K[T₀, T₁, T₂]` is nonzero. -/
theorem equation_ne_zero (a : K) : equation a ≠ 0 := fun h =>
  not_X_zero_dvd_equation a (h ▸ dvd_zero _)

/-- The kernel of the embedding of the conic into `ℙ²_K` is the zero scheme of its equation. -/
private theorem ker_embedding_eq_zeroScheme (a : K) :
    (PlaneCurveModel.embedding (equation a) (isHomogeneous_equation a)).ker =
      AlgebraicGeometry.zeroScheme
        (Proj (homogeneousSubmodule (Fin 3) K))
        (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheafModule
          (homogeneousSubmodule (Fin 3) K) ((2 : ℕ) : ℤ))
        (AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection
          (homogeneousSubmodule (Fin 3) K) 2
          ⟨equation a, equation_mem_homogeneousSubmodule a⟩) := by
  exact projectiveSpace_ker_eq_zeroScheme_of_idealOfClosedSubscheme_eq_span K 3
    (PlaneCurveModel.embedding (equation a) (isHomogeneous_equation a))
    ⟨equation a, equation_mem_homogeneousSubmodule a⟩
    (PlaneCurveModel.idealOfClosedSubscheme_embedding (equation a)
      (isHomogeneous_equation a) 0 (not_X_zero_dvd_equation a))

/-- **`dim_K H⁰(Z, 𝒪_Z) = 1`** for the conic `Z = V(T₁² + T₂² - aT₀²)`, from the sequence
`0 → 𝒪(-2) → 𝒪 → 𝒪_Z → 0` on `ℙ²_K`. -/
theorem finrank_structureSheafCohomology_zero (a : K) :
    Module.finrank K (structureSheafCohomology (toSpec a) 0) = 1 := by
  have hker := ker_embedding_eq_zeroScheme a
  obtain ⟨e⟩ := nonempty_structureSheafCohomologyIsoTwistCohomologyZero K 2 0 2
    (PlaneCurveModel.embedding (equation a) (isHomogeneous_equation a))
    ⟨equation a, equation_mem_homogeneousSubmodule a⟩ (equation_ne_zero a) hker
    (isZero_twistCohomology_plane_zero K (by norm_num)) (isZero_twistCohomology_plane_one K _)
  exact (e.toLinearEquiv.trans (twistCohomologyZeroEquivBase K 2)).finrank_eq.trans
    (Module.finrank_self K)

/-- The conic is nonempty: its chart on `D₊(T₀)` has a nonzero ring. -/
theorem nonempty_scheme (a : K) : Nonempty (scheme a) := by
  let U := PlaneCurveModel.chart (equation a) (isHomogeneous_equation a) 0
  obtain ⟨-, hnu⟩ := dehomCoeff_ne_zero_and_not_isUnit a 0
  have : Nontrivial (MvPolynomial (Fin 2) K ⧸
      Ideal.span {Stacks.ProjectiveChart.dehomCoeff K 0 (equation a)}) :=
    Ideal.Quotient.nontrivial_iff.mpr (by rwa [ne_eq, Ideal.span_singleton_eq_top])
  have : Nontrivial Γ(scheme a, U) := (PlaneCurveModel.chartEquiv (equation a)
    (isHomogeneous_equation a) 0 (not_X_zero_dvd_equation a) 0).symm.toEquiv.nontrivial
  obtain ⟨x⟩ : Nonempty U.toScheme := Nonempty.map
    (PlaneCurveModel.isAffineOpen_chart (equation a) (isHomogeneous_equation a) 0).isoSpec.inv
    inferInstance
  exact ⟨x.1⟩

/-- **`H⁰(Z, 𝒪_Z) = K`** for the conic `Z = V(T₁² + T₂² - aT₀²)`. -/
theorem isIso_globalSections (a : K) :
    IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ (toSpec a).appTop) := by
  obtain ⟨z⟩ := nonempty_scheme a
  have hne : Nonempty ((⊤ : (scheme a).Opens) : Type u) := ⟨⟨z, trivial⟩⟩
  refine Stacks.Models.isIso_constants_of_finrank_globalSections_eq_one (toSpec a) ?_
  rw [← finrank_structureSheafCohomology_zero_eq_finrank_globalSections K (toSpec a),
    finrank_structureSheafCohomology_zero a]

/-- **The conic `V(T₁² + T₂² - aT₀²)` has genus zero**: `(2 - 1)(2 - 2)/2 = 0`. -/
theorem genus_toSpec (a : K) : genus (toSpec a) = 0 := by
  have hker := ker_embedding_eq_zeroScheme a
  rw [genus_eq_finrank_structureSheafCohomology]
  show Module.finrank K (structureSheafCohomology
    (PlaneCurveModel.embedding (equation a) (isHomogeneous_equation a) ≫
      Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff K 2) 1) = 0
  rw [finrank_structureSheafCohomology_eq_finrank_twistCohomology_neg K 2 1 2
      (PlaneCurveModel.embedding (equation a) (isHomogeneous_equation a))
      ⟨equation a, equation_mem_homogeneousSubmodule a⟩ (equation_ne_zero a) hker
      (isZero_twistCohomology_plane_one K 0) (isZero_twistCohomology K 2 0 2 (by norm_num)),
    finrank_twistCohomology_plane_top]

/-! ### The conic is a projective curve -/

/-- **The conic `V(T₁² + T₂² - aT₀²)` is integral**: smooth over `K` with only constant global
functions, so connected, hence integral. -/
theorem isIntegral_scheme (ha : a ≠ 0) (h2 : (2 : K) ≠ 0) : IsIntegral (scheme a) := by
  have := smooth_toSpec ha h2
  have := isIso_globalSections a
  have : ConnectedSpace (scheme a) := connectedSpace_of_isIso_globalSections K (toSpec a)
  exact Stacks.Chow.isIntegral_of_connectedSpace_of_smooth (toSpec a)

/-- **The conic `V(T₁² + T₂² - aT₀²)` is a curve over `K`.** -/
theorem isCurve_toSpec (ha : a ≠ 0) (h2 : (2 : K) ≠ 0) : IsCurve K (toSpec a) :=
  have := isIntegral_scheme ha h2
  { toIsVariety := { }
    topologicalKrullDim_eq_one := topologicalKrullDim_scheme a }

/-- **The conic `V(T₁² + T₂² - aT₀²)` is projective over `K`**: it is a closed subscheme of
`ℙ²_K`. -/
theorem isHProjective_toSpec (a : K) : Stacks.HProjective.IsHProjective (toSpec a) := by
  refine ⟨2, PlaneCurveModel.embedding (equation a) (isHomogeneous_equation a) ≫
    (Stacks.ProjectiveCohomology.projModelIso K 2).hom, inferInstance, ?_⟩
  rw [Category.assoc, Stacks.CoefficientProj.projModelIso_hom_structure,
    ← Stacks.ProjectiveCohomology.projToSpecCoeff_eq_projModelToSpec]
  rfl

end Stacks.Models.RealConicModel

end
