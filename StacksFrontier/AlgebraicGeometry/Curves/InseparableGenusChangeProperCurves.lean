module

public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import StacksFrontier.AlgebraicGeometry.Curves.InseparableGenusChangeProjectionEmbedding
public import StacksFrontier.AlgebraicGeometry.ProjCoherentCohomologyFinite.Basic
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Smooth
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Dimension.Basic

/-!
# [Stacks, Tag 0CD1]: an inseparable morphism of proper nonsingular curves changing the genus

Let `k` be a field of characteristic three and `a ∈ k` an element which is not a cube. The plane
cubic `Z = Proj (k[T₀, T₁, T₂] ⧸ (F))`, `F = T₁²T₀ - T₂³ + aT₀³`, of
`StacksFrontier/AlgebraicGeometry/Curves/InseparableGenusChangeCurve.lean` and the coordinate
projection `f : Z ⟶ 𝐏¹_k` of
`StacksFrontier/AlgebraicGeometry/Curves/InseparableGenusChangeDominant.lean` form a morphism of
proper nonsingular curves over `k` inducing a purely inseparable extension of function fields of
degree three, while the genus of `Z` is `1` and that of `𝐏¹_k` is `0`. This file states the
example in that form.

## Main results

* `Stacks.AlgebraicGeometry.ProjPolyChart.isRegular_proj`: projective space over a regular ring
  is a regular scheme.
* `Stacks.AlgebraicGeometry.ProjPolyChart.isCurve_projToSpecCoeff_one`: the projective line
  `Proj k[S₀, S₁]` over a field is a curve.
* `Stacks.Curves.InseparableGenus.planeCubicProjection_inseparable_genus_change`:
  **[Stacks, Tag 0CD1].**

## Implementation notes

The function-field extension is stated for the algebra structure
`AlgebraicGeometry.dominantFunctionFieldMap f` itself, between the function fields of `𝐏¹_k` and
of `Z`. It is obtained from
`Stacks.Curves.InseparableGenus.isPurelyInseparable_and_finrank_projectionFunctionField`, which
states the same extension over `RatFunc k`, by moving the base along the identification
`Stacks.Curves.InseparableGenus.projectiveLineFunctionFieldEquiv` of the function field of
`𝐏¹_k` with `RatFunc k`.

## References

* [Stacks Project, Tag 0CD1](https://stacks.math.columbia.edu/tag/0CD1)
* [Stacks Project, Tag 02IS](https://stacks.math.columbia.edu/tag/02IS)
* [Stacks Project, Tag 0A23](https://stacks.math.columbia.edu/tag/0A23)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.AlgebraicGeometry.ProjPolyChart

/-- **Projective space over a regular ring is regular.** Each standard chart `D₊(Tᵢ)` is an
affine open whose ring of sections is a polynomial ring over the base
(`Stacks.ProjectiveChart.sectionsChartEquiv`), which is regular, and the standard charts cover. -/
theorem isRegular_proj (R : Type u) [CommRing R] [IsRegularRing R] (n : ℕ) :
    IsRegular (AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) := by
  intro x
  obtain ⟨i, hi⟩ := Stacks.ProjectiveSpace.exists_mem_basicOpen_X (R := R) x
  exact ⟨⟨_, AlgebraicGeometry.Proj.isAffineOpen_basicOpen _ _
      (Stacks.ProjectiveChart.X_mem_degree_one R i) Nat.one_pos⟩, hi,
    IsRegularRing.of_ringEquiv (Stacks.ProjectiveChart.sectionsChartEquiv R i)⟩

/-- **The projective line over a field is a curve.** It is integral, its structure morphism is
separated, quasi-compact and (being smooth) of finite type, and its dimension is one. -/
theorem isCurve_projToSpecCoeff_one (k : Type u) [Field k] :
    IsCurve k (projToSpecCoeff k 1) := by
  obtain ⟨_, _⟩ : IsSeparated (projToSpecCoeff k 1) ∧ QuasiCompact (projToSpecCoeff k 1) := by
    rw [projToSpecCoeff]; exact ⟨inferInstance, inferInstance⟩
  have := smooth_projToSpecCoeff k 1
  have : LocallyOfFiniteType (projToSpecCoeff k 1) := inferInstance
  refine (isCurve_iff k _).mpr ⟨by constructor, ?_⟩
  rw [Stacks.ProjectiveSpace.topologicalKrullDim_proj_fin k (r := 2) (by norm_num)]
  rfl

end Stacks.AlgebraicGeometry.ProjPolyChart

namespace Stacks.Curves.InseparableGenus

open Stacks.AlgebraicGeometry.ProjPolyChart (projToSpecCoeff isRegular_proj
  isCurve_projToSpecCoeff_one)

/-- **The extension of function fields that `f : Z ⟶ 𝐏¹_k` induces is purely inseparable of
degree three**, stated between the function fields of `𝐏¹_k` and of `Z` for the algebra
structure `AlgebraicGeometry.dominantFunctionFieldMap f`. -/
theorem isPurelyInseparable_and_finrank_dominantFunctionFieldMap (k : Type u) [Field k]
    [ExpChar k 3] (a : k) (ha : ∀ b : k, b ^ 3 ≠ a) :
    letI := isIntegral_planeCubicCurve k a ha
    letI := isDominant_planeCubicProjection k a
    letI : Algebra (AlgebraicGeometry.Proj
        (MvPolynomial.homogeneousSubmodule (Fin 2) k)).functionField
        (planeCubicCurve k a).functionField :=
      (dominantFunctionFieldMap (planeCubicProjection k a)).toAlgebra
    IsPurelyInseparable (AlgebraicGeometry.Proj
        (MvPolynomial.homogeneousSubmodule (Fin 2) k)).functionField
        (planeCubicCurve k a).functionField ∧
      Module.finrank (AlgebraicGeometry.Proj
        (MvPolynomial.homogeneousSubmodule (Fin 2) k)).functionField
        (planeCubicCurve k a).functionField = 3 := by
  let := isIntegral_planeCubicCurve k a ha
  let := isDominant_planeCubicProjection k a
  let : Algebra (AlgebraicGeometry.Proj
      (MvPolynomial.homogeneousSubmodule (Fin 2) k)).functionField
      (planeCubicCurve k a).functionField :=
    (dominantFunctionFieldMap (planeCubicProjection k a)).toAlgebra
  let : Algebra (RatFunc k) (planeCubicCurve k a).functionField :=
    projectionRatFuncAlgebra k a ha
  let : Algebra (RatFunc k) (AlgebraicGeometry.Proj
      (MvPolynomial.homogeneousSubmodule (Fin 2) k)).functionField :=
    (projectiveLineFunctionFieldEquiv k).symm.toRingHom.toAlgebra
  have : IsScalarTower (RatFunc k) (AlgebraicGeometry.Proj
      (MvPolynomial.homogeneousSubmodule (Fin 2) k)).functionField
      (planeCubicCurve k a).functionField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨hins, hrank⟩ := isPurelyInseparable_and_finrank_projectionFunctionField k a ha
  refine ⟨IsPurelyInseparable.tower_top (RatFunc k) _ _, ?_⟩
  rw [← hrank]
  exact (Algebra.finrank_eq_of_equiv_equiv (projectiveLineFunctionFieldEquiv k).symm
    (RingEquiv.refl (planeCubicCurve k a).functionField) rfl).symm

/-- **[Stacks, Tag 0CD1].** Let `k` be a field of characteristic three and `a ∈ k` an element
which is not a cube (for instance `k = 𝐅₃(a)`, `exists_charThree_notCube`). Let
`Z = Proj (k[T₀, T₁, T₂] ⧸ (F))` be the plane cubic with homogeneous equation
`F = T₁²T₀ - T₂³ + aT₀³`, embedded in `𝐏²_k` by `planeCubicEmbedding`, and let
`f : Z ⟶ 𝐏¹_k` be the coordinate projection `planeCubicProjection`, which on `D₊(T₀)` sends
`(x, y)` to `x`. Then:

* `Z` is a closed subscheme of `𝐏²_k`, proper over `k`, a curve over `k`, and nonsingular;
* `𝐏¹_k` is proper over `k`, a curve over `k`, and nonsingular;
* `f` is a morphism over `Spec k`, it is the projection `(T₀ : T₁ : T₂) ↦ (T₀ : T₁)` in the
  sense that `f ⁻¹ᵁ D₊(G) = Z ∩ D₊(G(T₀, T₁))` for every homogeneous `G` of positive degree, and
  it is dominant;
* the extension `k(Z)/k(𝐏¹_k)` of function fields induced by `f` is purely inseparable of
  degree three;
* the genus of `Z` is `1` and the genus of `𝐏¹_k` is `0`.

So the genus is not preserved by a purely inseparable morphism of proper nonsingular curves.
Characteristic three is `ExpChar k 3`, which for the prime `3` is the same as `CharP k 3`. -/
@[stacks 0CD1]
theorem planeCubicProjection_inseparable_genus_change (k : Type u) [Field k] [ExpChar k 3]
    (a : k) (ha : ∀ b : k, b ^ 3 ≠ a) :
    letI := isIntegral_planeCubicCurve k a ha
    letI := isDominant_planeCubicProjection k a
    letI : Algebra (AlgebraicGeometry.Proj
        (MvPolynomial.homogeneousSubmodule (Fin 2) k)).functionField
        (planeCubicCurve k a).functionField :=
      (dominantFunctionFieldMap (planeCubicProjection k a)).toAlgebra
    IsClosedImmersion (planeCubicEmbedding k a) ∧
      IsProper (planeCubicEmbedding k a ≫ projToSpecCoeff k 2) ∧
      IsCurve k (planeCubicEmbedding k a ≫ projToSpecCoeff k 2) ∧
      IsRegular (planeCubicCurve k a) ∧
      IsProper (projToSpecCoeff k 1) ∧
      IsCurve k (projToSpecCoeff k 1) ∧
      IsRegular (AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)) ∧
      planeCubicProjection k a ≫ projToSpecCoeff k 1 =
        planeCubicEmbedding k a ≫ projToSpecCoeff k 2 ∧
      (∀ (G : MvPolynomial (Fin 2) k) (d : ℕ),
        G ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k d → 0 < d →
        planeCubicProjection k a ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
            (MvPolynomial.homogeneousSubmodule (Fin 2) k) G =
          planeCubicEmbedding k a ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
            (MvPolynomial.homogeneousSubmodule (Fin 3) k) (coordProjHom k G)) ∧
      IsDominant (planeCubicProjection k a) ∧
      IsPurelyInseparable (AlgebraicGeometry.Proj
          (MvPolynomial.homogeneousSubmodule (Fin 2) k)).functionField
          (planeCubicCurve k a).functionField ∧
      Module.finrank (AlgebraicGeometry.Proj
          (MvPolynomial.homogeneousSubmodule (Fin 2) k)).functionField
          (planeCubicCurve k a).functionField = 3 ∧
      genus (planeCubicEmbedding k a ≫ projToSpecCoeff k 2) = 1 ∧
      genus (projToSpecCoeff k 1) = 0 := by
  let := isIntegral_planeCubicCurve k a ha
  let := isDominant_planeCubicProjection k a
  let : Algebra (AlgebraicGeometry.Proj
      (MvPolynomial.homogeneousSubmodule (Fin 2) k)).functionField
      (planeCubicCurve k a).functionField :=
    (dominantFunctionFieldMap (planeCubicProjection k a)).toAlgebra
  obtain ⟨hins, hrank⟩ := isPurelyInseparable_and_finrank_dominantFunctionFieldMap k a ha
  obtain ⟨hcurve, hreg, -, -, -, hone, hline, -⟩ := planeCubicCurve_isRegular_and_genus_ne k a ha
  have := Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff k 2
  exact ⟨inferInstance, inferInstance, hcurve, hreg,
    Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff k 1,
    isCurve_projToSpecCoeff_one k, isRegular_proj k 1,
    planeCubicProjection_comp_projToSpecCoeff k a,
    planeCubicProjection_preimage_basicOpen k a, isDominant_planeCubicProjection k a,
    hins, hrank, hone, hline⟩

end Stacks.Curves.InseparableGenus

end
