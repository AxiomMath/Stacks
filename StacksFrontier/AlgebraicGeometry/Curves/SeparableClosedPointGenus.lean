module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.SmoothCurveDifferentials
public import StacksFrontier.AlgebraicGeometry.Curves.InseparableLinearSeries
public import StacksFrontier.AlgebraicGeometry.Curves.PencilDegree
public import StacksFrontier.AlgebraicGeometry.Curves.SeparableClosedPoint
public import StacksFrontier.AlgebraicGeometry.Curves.SmoothVectorFields
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular

/-!
# A separable closed point of degree at most `2g - 2`

Let `X` be a smooth proper curve over a field `k` with `H⁰(X, 𝒪_X) = k` and genus `g ≥ 2`. Then
`X` has a closed point `x` with `κ(x)/k` separable of degree at most `2g - 2`
([Stacks, Tag 0CD4]). The residue field `κ(x)` is a `k`-algebra through the structure morphism
followed by evaluation at `x`.

## Main results

* `AlgebraicGeometry.nonempty_linearSeries_relativeDifferentials`: for `g ≥ 1`, the canonical
  sheaf `Ω_{X/k}` with all its global sections is a `𝔤^{g-1}_{2g-2}`.
* `AlgebraicGeometry.exists_hom_projectiveLine_degreeOver_le_two_mul_genus_sub_two`: for `k`
  perfect and `g ≥ 2` there is a nonconstant morphism `X ⟶ 𝐏¹_k` over `k` of degree at most
  `2g - 2`.
* `AlgebraicGeometry.exists_isClosed_isSeparable_finrank_residueField_le_two_mul_genus_sub_two`:
  for `g ≥ 2` there is a closed point `x` with `κ(x)/k` finite separable of degree at most
  `2g - 2`.

## References

* [Stacks Project, Tag 0CD4](https://stacks.math.columbia.edu/tag/0CD4)
* [Stacks Project, Tag 0C1A](https://stacks.math.columbia.edu/tag/0C1A)
* [Stacks Project, Tag 0CCQ](https://stacks.math.columbia.edu/tag/0CCQ)
* [Stacks Project, Tag 0CCR](https://stacks.math.columbia.edu/tag/0CCR)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

attribute [local instance] isCurve_projectiveSpaceOver_one

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f]
  [Smooth f] [IsProper f] [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]

/-- **The canonical linear series.** On a smooth proper curve `X` over `k` with
`H⁰(X, 𝒪_X) = k` and genus `g ≥ 1`, the sheaf `Ω_{X/k}` together with all of `H⁰(X, Ω_{X/k})` is
a `𝔤^{g-1}_{2g-2}` ([Stacks, Tag 0C1A]). -/
theorem nonempty_linearSeries_relativeDifferentials (hg : 1 ≤ genus f) :
    Nonempty (LinearSeries k f (Stacks.Curves.topologicalKrullDim_le_one_of_isCurve f)
      (2 * genus f - 2) (genus f - 1)) := by
  have hdim := Stacks.Curves.topologicalKrullDim_le_one_of_isCurve f
  have h0 := finrank_cohomologyOverField_zero_relativeDifferentials_eq_genus f
  have hdeg : invertibleCurveDegree k f hdim (Scheme.Hom.relativeDifferentials f) =
      2 * (genus f : ℤ) - 2 := by
    let := smoothOfRelativeDimension_one_of_isCurve k f
    let := Scheme.Hom.isFiniteLocallyFreeOfRank_one_relativeDifferentials f
    rw [invertibleCurveDegree_eq_curveDegree k f hdim]
    exact curveDegree_relativeDifferentials_eq_two_mul_genus_sub_two f
  have : FiniteDimensional k
      (cohomologyOverField k f (Scheme.Hom.relativeDifferentials f) 0) :=
    Module.finite_of_finrank_pos (by rw [h0]; omega)
  exact ⟨{ L := Scheme.Hom.relativeDifferentials f
           isInvertible := inferInstance
           degree_eq := by rw [hdeg]; push_cast [show 2 ≤ 2 * genus f by omega]; ring
           V := ⊤
           finrank_eq := by rw [finrank_top, h0]; omega }⟩

/-- On a smooth proper curve `X` over a perfect field `k` with `H⁰(X, 𝒪_X) = k` and genus
`g ≥ 2`, a pencil in the canonical linear series gives a nonconstant morphism `X ⟶ 𝐏¹_k` over `k`
of degree at most `2g - 2` ([Stacks, Tags 0CCQ, 0CCR]). -/
theorem exists_hom_projectiveLine_degreeOver_le_two_mul_genus_sub_two [PerfectField k]
    (hg : 2 ≤ genus f) :
    ∃ (φ : X ⟶ projectiveSpaceOver 1 (Spec (.of k)))
      (hφ : φ ≫ (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) = f)
      (hnc : ¬ ∃ y : projectiveSpaceOver 1 (Spec (.of k)), ∀ x : X, φ.base x = y),
      @degreeOver X (projectiveSpaceOver 1 (Spec (.of k))) φ inferInstance inferInstance
          (locallyOfFiniteType_of_isCurve_comp k f
            (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) φ hφ)
          (isDominant_of_not_constant k f
            (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) φ hnc) ≤ 2 * genus f - 2 := by
  have hdim := Stacks.Curves.topologicalKrullDim_le_one_of_isCurve f
  obtain ⟨E⟩ := nonempty_linearSeries_relativeDifferentials k f (by omega)
  obtain ⟨E1⟩ := linearSeries_nonempty_of_le f hdim _ _ 1 ⟨E⟩ (by omega)
  obtain ⟨⟨b, φ, hφ, α, hα⟩, hall⟩ :=
    Stacks.LinearSeriesMorphism.degreeOver_le_or_constant_of_isRegular k f
      (isRegular_of_smooth_over_field f) E1
  obtain h | ⟨-, hrank⟩ := hall b φ hφ α hα
  · obtain ⟨hnc, hle⟩ := h
    exact ⟨φ, hφ, hnc, hle⟩
  · have h1 := finrank_cohomologyOverField_unit_zero_eq_one f
    have : FiniteDimensional k
        (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 0) :=
      Module.finite_of_finrank_pos (by rw [h1]; omega)
    rw [← Module.finrank_eq_rank, h1] at hrank
    norm_num at hrank

/-- A smooth proper curve `X` over a field `k` with `H⁰(X, 𝒪_X) = k` and genus `g ≥ 2` has a
closed point `x` with `κ(x)/k` finite separable of degree at most `2g - 2`. -/
@[stacks 0CD4]
theorem exists_isClosed_isSeparable_finrank_residueField_le_two_mul_genus_sub_two
    (hg : 2 ≤ genus f) :
    ∃ x : X, IsClosed ({x} : Set X) ∧
      (letI := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra;
      Module.Finite k (X.residueField x) ∧ Algebra.IsSeparable k (X.residueField x) ∧
        Module.finrank k (X.residueField x) ≤ 2 * genus f - 2) := by
  by_cases hperf : PerfectField k
  · obtain ⟨φ, hφ, hnc, hle⟩ := exists_hom_projectiveLine_degreeOver_le_two_mul_genus_sub_two k f hg
    obtain ⟨x, hx, hfin, hsep, hdeg⟩ :=
      exists_isClosed_isSeparable_finrank_le_degreeOver_of_perfectField f φ hφ hnc
    exact ⟨x, hx, hfin, hsep, hdeg.trans hle⟩
  have hchar : ringChar k ≠ 0 := fun h => hperf (by
    have : CharZero k := (CharP.ringChar_zero_iff_CharZero k).mp h
    infer_instance)
  have hinf : Infinite k := by
    by_contra h
    have : Finite k := not_infinite_iff_finite.mp h
    have : Fintype k := Fintype.ofFinite k
    exact hperf inferInstance
  set p := ringChar k
  have : CharP k p := ringChar.charP k
  have : Fact p.Prime := ⟨(CharP.char_is_prime_or_zero k p).resolve_right hchar⟩
  have hdim := Stacks.Curves.topologicalKrullDim_le_one_of_isCurve f
  obtain ⟨E⟩ := nonempty_linearSeries_relativeDifferentials k f (by omega)
  have hS : Stacks.Frobenius.IsInCharacteristic (Spec (.of k)) p :=
    Stacks.Frobenius.isInCharacteristic_spec k p
  rcases exists_genericallyEtale_pencil_or_linearSeries_frobeniusTwist p hS f hdim (by omega) E
    with ⟨E₁, b₁, q, hq, α, hα, U, hU, het⟩ | h
  · have hnc := not_constant_of_etale f q hq U hU het
    have hle : @degreeOver X _ q _ _ (locallyOfFiniteType_of_isCurve_comp k f
        (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) q hq)
        (isDominant_of_not_constant k f
          (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) q hnc) ≤ 2 * genus f - 2 := by
      rcases Stacks.LinearSeriesMorphism.degreeOver_le_or_constant k f E₁ b₁ q hq α hα with
        ⟨_, h⟩ | ⟨⟨y, -, hy⟩, -⟩
      · exact h
      · exact absurd ⟨y, hy⟩ hnc
    obtain ⟨x, hx, hfin, hsep, hdeg⟩ :=
      exists_isClosed_isSeparable_finrank_le_degreeOver_of_etale f q hq hnc U hU het
    exact ⟨x, hx, hfin, hsep, hdeg.trans hle⟩
  · exfalso
    let := isCurve_frobeniusTwist_curve p hS f
    let := isProper_frobeniusTwist_curve p hS f
    have := isIso_globalSections_frobeniusTwist_curve f p hS
    obtain ⟨d', hd', -, ⟨E'⟩⟩ := h
    obtain ⟨hrd, heq⟩ := linearSeries_dimension_le_degree_and_genus_eq_zero _ E'
    rw [genus_frobeniusTwist_curve f p hS] at heq
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    have : d' ≤ genus f - 1 := by
      have : 2 * d' ≤ p * d' := Nat.mul_le_mul_right d' hp2
      omega
    have := heq (by omega) (by omega)
    omega

end AlgebraicGeometry

end
