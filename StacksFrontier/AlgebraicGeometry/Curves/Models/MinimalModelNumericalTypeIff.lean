module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.MinimalModelNumericalType
public import StacksFrontier.AlgebraicGeometry.Curves.Models.ReducedFibreFirstCohomology
public import StacksFrontier.AlgebraicGeometry.Curves.Models.ReducedFibreGenusEquality
public import StacksFrontier.AlgebraicGeometry.Curves.ProjectiveLineCriterion.ProjectiveLine
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingTwistSectionCount
import StacksCore.Tactic.StacksAttribute

/-!
# A regular proper model is minimal exactly when its numerical type is

In the situation of [Stacks, Tag 0C61], [Stacks, Tag 0CA6] asserts that the regular proper model
`X` is a minimal model if and only if the numerical type associated to `X` ([Stacks, Tag 0CA5])
is minimal ([Stacks, Tag 0C7A]).

The implication from the numerical type to the model is
`Stacks.Models.RegularProperModelSituation.isMinimalModel_of_isMinimal_associatedNumericalType`.
This file proves the other one. Suppose the numerical type has a minus-one index `i`, that is
`gᵢ = 0` and `(Cᵢ · Cᵢ) = -[κᵢ : k]`. The invertible module `𝒪_X(-Cᵢ)|_{Cᵢ}` has degree
`-(Cᵢ · Cᵢ) = [κᵢ : k]` over `k`, hence degree `1` over `κᵢ`; so the proper integral curve `Cᵢ`
over `κᵢ`, of genus zero with `H⁰(Cᵢ, 𝒪) = κᵢ`, is the projective line over `κᵢ`
([Stacks, Tag 0C6U]). A component which is a projective line with `(Cᵢ · Cᵢ) = -[κᵢ : k]` is an
exceptional curve of the first kind
(`RegularProperModelSituation.isExceptionalCurveOfFirstKind_specialFiberComponentIdeal_of_iso`),
so `X` is not minimal.

## Main results

All in the namespace `Stacks.Models.RegularProperModelSituation`:

* `exists_iso_projectiveLineProj_specialFiberComponentIdeal`:
  a component of genus zero with `(Cᵢ · Cᵢ) = -[κᵢ : k]` is the projective line over `κᵢ`.
* `isMinimal_associatedNumericalType_of_isMinimalModel`:
  the numerical type associated to a minimal model is minimal.
* `isMinimalModel_iff_isMinimal_associatedNumericalType`:
  **[Stacks, Tag 0CA6]**.
* `surjective_and_not_injective_of_isMinimalModel`:
  **[Stacks, Tag 0CE9]**, the map `H¹(X_k, 𝒪) ⟶ H¹((X_k)_red, 𝒪)` of a minimal model.
* `genus_reduction_le_and_lt_of_not_hasExceptionalCurveOfFirstKind`:
  the dimension form of [Stacks, Tag 0CE9].

## References

* [Stacks Project, Tag 0CA6](https://stacks.math.columbia.edu/tag/0CA6)
* [Stacks Project, Tag 0C6U](https://stacks.math.columbia.edu/tag/0C6U)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.SheafOfModules.Invertible (tensorPowerModule)

universe u

namespace Stacks.Models

namespace RegularProperModelSituation

variable (S : RegularProperModelSituation.{u}) [DecidableEq (irreducibleComponents S.specialFiber)]

/-- **A component of genus zero with `(C_Z · C_Z) = -[κ_Z : k]` is the projective line over its
field of constants.** Over `κ_Z = Γ(C_Z, 𝒪)` the curve `C_Z` is proper, integral and
one-dimensional with `H⁰(C_Z, 𝒪) = κ_Z` and genus `g_Z = 0`. The module `𝒪_X(C_Z)|_{C_Z}` has
degree `(C_Z · C_Z) = -[κ_Z : k]` over `k`, hence degree `-1` over `κ_Z` by the tower law, so its
inverse has degree `1`, and a genus-zero curve with an invertible module of degree one is the
projective line ([Stacks, Tag 0C6U]). -/
theorem exists_iso_projectiveLineProj_specialFiberComponentIdeal
    (Z : irreducibleComponents S.specialFiber) (hg : S.specialFiberComponentGenus Z = 0)
    (hN : S.specialFiberIntersectionMatrix Z Z = -(S.specialFiberComponentWeight Z : ℤ)) :
    ∃ (κ : Type u) (_ : Field κ),
      Nonempty (projectiveLineProj κ ≅ (S.specialFiberComponentIdeal Z).subscheme) := by
  obtain ⟨hκC, -⟩ := S.isField_and_finite_globalSections_specialFiberComponent Z
  let : Field Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) := hκC.toField
  have : IsProper (S.specialFiberComponentIdeal Z).subscheme.toSpecΓ :=
    Stacks.AlgebraicGeometry.ProperGeomConnected.isProper_toSpecΓ
      (S.specialFiberComponentToSpec Z)
  have : IsIntegral (S.specialFiberComponentIdeal Z).subscheme :=
    S.toRegularModelSituation.isIntegral_specialFiberComponentIdeal Z
  have : IsIso ((Scheme.ΓSpecIso (.of Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤))).inv ≫
      (S.specialFiberComponentIdeal Z).subscheme.toSpecΓ.appTop) := by
    have hid : (Scheme.ΓSpecIso (.of Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤))).inv ≫
        (S.specialFiberComponentIdeal Z).subscheme.toSpecΓ.appTop =
          𝟙 Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) := by
      rw [Scheme.toSpecΓ_appTop]
      exact (Scheme.ΓSpecIso Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤)).inv_hom_id
    rw [hid]
    infer_instance
  have hdim := S.topologicalKrullDim_specialFiberComponent_eq_one Z
  have hdimC := S.toRegularModelSituation.topologicalKrullDim_specialFiberComponent Z
  have hD : Stacks.Divisors.IsEffectiveCartierDivisor (S.specialFiberComponentIdeal Z) :=
    S.isEffectiveCartierDivisor_specialFiberComponent Z
  set M := (Scheme.Modules.pullback (S.specialFiberComponentIdeal Z).subschemeι).obj
    (Stacks.Divisors.invertibleSheaf' (S.specialFiberComponentIdeal Z)) with hMdef
  have hMs : Stacks.SheafOfModules.IsInvertible
      (S.specialFiberComponentIdeal Z).subscheme.presheaf
      (structureSheafRing (S.specialFiberComponentIdeal Z).subscheme.toRingedSpace).property M :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).2
      (isInvertible_restrict (S.specialFiberComponentIdeal Z) _
        (Stacks.Divisors.isTensorInvertible_invertibleSheaf (S.specialFiberComponentIdeal Z)))
  have hM : AlgebraicGeometry.SheafOfModules.IsInvertible
      (S.specialFiberComponentIdeal Z).subscheme.presheaf
      (S.specialFiberComponentIdeal Z).subscheme.ringCatSheaf.2 M :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).1 hMs
  -- the degree of `𝒪_X(C_Z)|_{C_Z}` over `κ_Z` is `-1`
  have h1 : S.specialFiberIntersectionMatrix Z Z =
      invertibleCurveDegree S.k (S.specialFiberComponentToSpec Z) hdimC M := by
    rw [S.specialFiberIntersectionMatrix_eq_componentDegree Z Z]
    rfl
  have h2 : invertibleCurveDegree S.k (S.specialFiberComponentToSpec Z) hdimC M =
      (S.specialFiberComponentWeight Z : ℤ) *
        invertibleCurveDegree Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤)
          (S.specialFiberComponentIdeal Z).subscheme.toSpecΓ hdimC M :=
    invertibleCurveDegree_eq_finrank_globalSections_mul_toSpecΓ S.k
      (S.specialFiberComponentToSpec Z) hdimC hκC M
  have hw := S.specialFiberComponentWeight_pos Z
  have hdegM : invertibleCurveDegree Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤)
      (S.specialFiberComponentIdeal Z).subscheme.toSpecΓ hdimC M = -1 := by
    rw [h1, h2] at hN
    exact mul_left_cancel₀ (a := (S.specialFiberComponentWeight Z : ℤ)) (by omega) (by linarith)
  -- its inverse has degree `1`
  have hMa : Stacks.Ample.IsInvertibleModule (S.specialFiberComponentIdeal Z).subscheme M :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ _).mp hMs
  have hL : Stacks.Ample.IsInvertibleModule (S.specialFiberComponentIdeal Z).subscheme
      (tensorPowerModule M (-1)) :=
    Stacks.SheafOfModules.Invertible.tensorPower_isInvertible
      (S.specialFiberComponentIdeal Z).subscheme.toRingedSpace.presheaf
      (structureSheafRing (S.specialFiberComponentIdeal Z).subscheme.toRingedSpace).property M (-1)
  have hdegL : invertibleCurveDegree Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤)
      (S.specialFiberComponentIdeal Z).subscheme.toSpecΓ hdim.le
        (tensorPowerModule M (-1)) = 1 := by
    rw [invertibleCurveDegree_tensorPowerModule_neg_one_of_topologicalKrullDim_le_one]
    rw [show hdim.le = hdimC from rfl, hdegM]
    norm_num
  -- [Stacks, Tag 0C6U], (6) ⇒ (1)
  obtain ⟨e⟩ := ProjectiveLineCriterion.exists_iso_projectiveLine_of_invertibleCurveDegree_eq_one
    (S.specialFiberComponentIdeal Z).subscheme.toSpecΓ hdim.le hg (tensorPowerModule M (-1))
    hdegL
  exact ⟨Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤), inferInstance,
    ⟨((Over.forget _).mapIso e ≪≫
      (Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison _ 1).iso).symm⟩⟩

/-- **[Stacks, Tag 0CA6], (1) ⇒ (2).** In the situation of [Stacks, Tag 0C61], the numerical type
associated to a minimal model is minimal: a minus-one index `i` would make the component `Cᵢ`,
which is then a projective line over `κᵢ`, an exceptional curve of the first kind. -/
theorem isMinimal_associatedNumericalType_of_isMinimalModel
    (n : ℕ) (e : Fin n ≃ irreducibleComponents S.specialFiber)
    (h : IsMinimalModel S.C_to_K S.X_to_R S.genericFiberIso) :
    (S.associatedNumericalType n e).IsMinimal := by
  rintro ⟨i, hg, hN⟩
  change (S.specialFiberComponentGenus (e i) : ℤ) = 0 at hg
  change S.specialFiberIntersectionMatrix (e i) (e i) =
    -(S.specialFiberComponentWeight (e i) : ℤ) at hN
  obtain ⟨κ, hκ, ⟨ε⟩⟩ :=
    S.exists_iso_projectiveLineProj_specialFiberComponentIdeal (e i) (by exact_mod_cast hg) hN
  exact h.not_hasExceptionalCurveOfFirstKind ⟨κ, hκ, _, ε,
    S.isExceptionalCurveOfFirstKind_specialFiberComponentIdeal_of_iso (e i) hN κ ε⟩

/-- **Stacks Project, Tag 0CA6.** In the situation of [Stacks, Tag 0C61], let `C₁, …, Cₙ` be the
irreducible components of the special fibre, enumerated by `e`. Then `X` is a minimal model if and
only if the numerical type associated to `X` ([Stacks, Tag 0CA5]) is minimal
([Stacks, Tag 0C7A]). -/
@[stacks 0CA6]
theorem isMinimalModel_iff_isMinimal_associatedNumericalType
    (n : ℕ) (e : Fin n ≃ irreducibleComponents S.specialFiber) :
    IsMinimalModel S.C_to_K S.X_to_R S.genericFiberIso ↔
      (S.associatedNumericalType n e).IsMinimal :=
  ⟨S.isMinimal_associatedNumericalType_of_isMinimalModel n e,
    S.isMinimalModel_of_isMinimal_associatedNumericalType n e⟩

/-- The numerical type associated to a regular proper model without exceptional curves of the
first kind is minimal ([Stacks, Tag 0CA6], (1) ⇒ (2)). -/
theorem isMinimal_associatedNumericalType_of_not_hasExceptionalCurveOfFirstKind
    (hS : ¬ S.X.HasExceptionalCurveOfFirstKind)
    (n : ℕ) (e : Fin n ≃ irreducibleComponents S.specialFiber) :
    (S.associatedNumericalType n e).IsMinimal :=
  S.isMinimal_associatedNumericalType_of_isMinimalModel n e (S.isMinimalModel hS)

omit [DecidableEq (irreducibleComponents S.specialFiber)] in
/-- **Stacks Project, Tag 0CE9.** In the situation of [Stacks, Tag 0C61] assume `X` is a minimal
model, `gcd(m₁, …, mₙ) = 1` and `H⁰((X_k)_red, 𝒪) = k`. Then the map
`H¹(X_k, 𝒪_{X_k}) ⟶ H¹((X_k)_red, 𝒪_{(X_k)_red})` induced by the reduction `(X_k)_red ⟶ X_k`
(`AlgebraicGeometry.cohomologyOverFieldStructureSheafMap`) is surjective, and it has a nontrivial
kernel, that is it is not injective, as soon as `(X_k)_red ≠ X_k`, that is as soon as `X_k` is not
reduced. -/
@[stacks 0CE9]
theorem surjective_and_not_injective_of_isMinimalModel
    (hmin : IsMinimalModel S.C_to_K S.X_to_R S.genericFiberIso)
    (hgcd : Finset.univ.gcd S.specialFiberMultiplicity = 1)
    (hred : IsIso ((Scheme.ΓSpecIso (.of S.k)).inv ≫
      (S.specialFiber.reductionι ≫ S.specialFiberToSpec).appTop)) :
    Function.Surjective (cohomologyOverFieldStructureSheafMap S.k S.specialFiberToSpec
        S.specialFiber.reductionι 1) ∧
      (¬ IsReduced S.specialFiber →
        ¬ Function.Injective (cohomologyOverFieldStructureSheafMap S.k S.specialFiberToSpec
          S.specialFiber.reductionι 1)) := by
  classical
  exact S.surjective_and_not_injective_of_isMinimal_associatedNumericalType _
    (Fintype.equivFin _).symm
    (S.isMinimal_associatedNumericalType_of_isMinimalModel _ _ hmin) hgcd hred

omit [DecidableEq (irreducibleComponents S.specialFiber)] in
/-- **[Stacks, Tag 0CE9], in dimensions.** For a regular proper model without exceptional curves
of the first kind, with `gcd(m₁, …, mₙ) = 1` and `H⁰((X_k)_red, 𝒪) = k`,
`dim H¹((X_k)_red, 𝒪) ≤ dim H¹(X_k, 𝒪)`, strictly when `X_k` is not reduced. -/
theorem genus_reduction_le_and_lt_of_not_hasExceptionalCurveOfFirstKind
    (hS : ¬ S.X.HasExceptionalCurveOfFirstKind)
    (hgcd : Finset.univ.gcd S.specialFiberMultiplicity = 1)
    (hred : IsIso ((Scheme.ΓSpecIso (.of S.k)).inv ≫
      (S.specialFiber.reductionι ≫ S.specialFiberToSpec).appTop)) :
    genus (S.specialFiber.reductionι ≫ S.specialFiberToSpec) ≤ genus S.specialFiberToSpec ∧
      (¬ IsReduced S.specialFiber →
        genus (S.specialFiber.reductionι ≫ S.specialFiberToSpec) <
          genus S.specialFiberToSpec) := by
  have hdimk : topologicalKrullDim S.specialFiber ≤ 1 :=
    (S.toRegularModelSituation.topologicalKrullDim_specialFiber S.nonempty_specialFiber).le
  have hle := genus_comp_le_of_isClosedImmersion S.k S.specialFiberToSpec hdimk
    S.specialFiber.reductionι
  refine ⟨hle, fun hnr => lt_of_le_of_ne hle fun heq => ?_⟩
  obtain ⟨hsurj, hninj⟩ := S.surjective_and_not_injective_of_isMinimalModel
    (S.isMinimalModel hS) hgcd hred
  apply hninj hnr
  have key {Y : Scheme.{u}} (f : Y ⟶ Spec (.of S.k)) [IsProper f] :
      FiniteDimensional S.k (cohomologyOverField S.k f (structureSheafModule Y) 1) ∧
        genus f = Module.finrank S.k (cohomologyOverField S.k f (structureSheafModule Y) 1) := by
    have := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit S.k f
    have := finiteDimensional_cohomologyOverField_of_isProper S.k f (structureSheafModule Y) 1
    exact ⟨this, by rw [genus_eq_finrank_structureSheafCohomology,
      (structureSheafCohomologyIsoCohomologyOverField S.k f 1).toLinearEquiv.finrank_eq]⟩
  obtain ⟨_, h₁⟩ := key S.specialFiberToSpec
  obtain ⟨_, h₂⟩ := key (S.specialFiber.reductionι ≫ S.specialFiberToSpec)
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (h₁.symm.trans (heq.symm.trans h₂))).2 hsurj

end RegularProperModelSituation

end Stacks.Models

end
