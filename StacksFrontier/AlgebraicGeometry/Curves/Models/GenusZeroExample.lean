module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.SplitConicExceptional
import StacksCore.Tactic.StacksAttribute

/-!
# In genus zero minimal models are not unique

Let `R` be a discrete valuation ring with fraction field `K`, residue field `k` and uniformizer
`π`, and let

`X = Proj R[T₀, T₁, T₂]/(T₁T₂ - πT₀²) ⊆ ℙ²_R`.

The generic fibre of `X` is the conic `T₁T₂ = πT₀²` over `K`, which the parametrization
`[u : v] ↦ [uv : v² : πu²]` identifies with `ℙ¹_K`; so `X` is a regular proper model of `ℙ¹_K`.
Its special fibre is the sum of the two lines `C₁ = V(π, T₁)` and `C₂ = V(π, T₂)`, both
isomorphic to `ℙ¹_k` and exceptional curves of the first kind. The projection `[T₂ : T₀]` from
`(0 : 1 : 0)` contracts `C₂` and maps `C₁` isomorphically onto the special fibre of `ℙ¹_R`; the
projection `[T₀ : T₁]` from `(0 : 0 : 1)` contracts `C₁` and maps `C₂` isomorphically onto the
special fibre of `ℙ¹_R`. Both are morphisms of models, for two different identifications `e₁` and
`e₂` of the generic fibre of `ℙ¹_R` with `ℙ¹_K`, and `(ℙ¹_R, e₁)`, `(ℙ¹_R, e₂)` are two minimal
models of `ℙ¹_K` which are not isomorphic as models.

## Main results

* `Stacks.Models.GenusZero.minimalModel_not_unique`: [Stacks, Tag 0CA0].

## References

* [Stacks Project, Tag 0CA0](https://stacks.math.columbia.edu/tag/0CA0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial

universe u

namespace Stacks.Models.GenusZero

open Stacks.AlgebraicGeometry.ProjBaseChange Stacks.AlgebraicGeometry.ProjPolyChart

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K] {π : R}

local notation "κ" => IsLocalRing.ResidueField R

attribute [local instance] AlgebraicGeometry.isCurve_projectiveSpaceOver_one

/-- **Stacks Project, Tag 0CA0: in genus zero, minimal models are not unique.** Let `R` be a
discrete valuation ring with fraction field `K`, residue field `k` and uniformizer `π`, and let
`X = Proj R[T₀, T₁, T₂]/(T₁T₂ - πT₀²)`.

1. `X` is a closed subscheme of `ℙ²_R`, regular and proper over `R`, and a model of `ℙ¹_K`, its
   generic fibre being identified with `ℙ¹_K` by `[u : v] ↦ [uv : v² : πu²]`.
2. The special fibre of `X` is the union, and as a divisor the sum, of the lines
   `C₁ = V(π, T₁)` and `C₂ = V(π, T₂)`; each is a copy of `ℙ¹_k` and an exceptional curve of the
   first kind on `X`. In particular `X` is not a minimal model.
3. The projection `[T₂ : T₀]` from `(0 : 1 : 0)` is a morphism of models from `X` to `ℙ¹_R` with
   the identification `e₂` of its generic fibre twisted by `[u : v] ↦ [πu : v]`; it contracts
   `C₂` to a `k`-point and maps `C₁` isomorphically onto the special fibre of `ℙ¹_R`. The
   projection `[T₀ : T₁]` from `(0 : 0 : 1)` is a morphism of models from `X` to `ℙ¹_R` with the
   canonical identification `e₁`; it contracts `C₁` and maps `C₂` isomorphically onto the special
   fibre of `ℙ¹_R`.
4. `(ℙ¹_R, e₁)` and `(ℙ¹_R, e₂)` are minimal models of `ℙ¹_K`, and no isomorphism of models
   relates them. -/
@[stacks 0CA0]
theorem minimalModel_not_unique (hπ : Irreducible π) :
    -- (1) `X ⊆ ℙ²_R` is a regular proper model of `ℙ¹_K`
    IsClosedImmersion (PlaneCurveModel.embedding (conicEquation π)
      (isHomogeneous_conicEquation π)) ∧
    IsRegular (conicScheme π) ∧ IsProper (conicToSpec π) ∧
    IsModel (projectiveSpaceOverRing 1 (.of K) ↘ Spec (.of K)) (conicToSpec π)
      (conicGenericFibreIso (K := K) hπ) ∧
    -- (2) the special fibre is `C₁ + C₂`, two exceptional curves of the first kind
    Set.range (pullback.fst (conicToSpec π) (residueSpecMap R)) =
      Set.range (firstLine (mem_maximalIdeal_of_irreducible hπ)) ∪
        Set.range (secondLine (mem_maximalIdeal_of_irreducible hπ)) ∧
    (pullback.fst (conicToSpec π) (residueSpecMap R)).ker =
      (firstLine (mem_maximalIdeal_of_irreducible hπ)).ker *
        (secondLine (mem_maximalIdeal_of_irreducible hπ)).ker ∧
    (firstLine (mem_maximalIdeal_of_irreducible hπ)).ker.IsExceptionalCurveOfFirstKind κ
      (firstLineIso hπ) ∧
    (secondLine (mem_maximalIdeal_of_irreducible hπ)).ker.IsExceptionalCurveOfFirstKind κ
      (secondLineIso hπ) ∧
    (conicScheme π).HasExceptionalCurveOfFirstKind ∧
    -- (3) the projection from `(0 : 1 : 0)` contracts `C₂` and maps `C₁` onto the special fibre
    IsModelHom (conicToSpec π) (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R))
      (conicGenericFibreIso (K := K) hπ) (twistedGenericFibreIso (K := K) hπ) (secondProjection π) ∧
    (∃ q : Spec (.of κ) ⟶ projectiveSpaceOverRing 1 (.of R),
      secondLine (mem_maximalIdeal_of_irreducible hπ) ≫ secondProjection π =
        projToSpecCoeff κ 1 ≫ q) ∧
    (∃ e : AlgebraicGeometry.Proj (lineGrading κ) ≅
        pullback (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R)) (residueSpecMap R),
      firstLine (mem_maximalIdeal_of_irreducible hπ) ≫ secondProjection π =
        e.hom ≫ pullback.fst _ _) ∧
    -- the projection from `(0 : 0 : 1)` contracts `C₁` and maps `C₂` onto the special fibre
    IsModelHom (conicToSpec π) (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R))
      (conicGenericFibreIso (K := K) hπ) (projectiveLineGenericFibreIso (K := K))
      (firstProjection π) ∧
    (∃ q : Spec (.of κ) ⟶ projectiveSpaceOverRing 1 (.of R),
      firstLine (mem_maximalIdeal_of_irreducible hπ) ≫ firstProjection π =
        projToSpecCoeff κ 1 ≫ q) ∧
    (∃ e : AlgebraicGeometry.Proj (lineGrading κ) ≅
        pullback (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R)) (residueSpecMap R),
      secondLine (mem_maximalIdeal_of_irreducible hπ) ≫ firstProjection π =
        e.hom ≫ pullback.fst _ _) ∧
    -- (4) two minimal models of `ℙ¹_K`, not isomorphic as models
    IsMinimalModel (projectiveSpaceOverRing 1 (.of K) ↘ Spec (.of K))
      (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R)) (projectiveLineGenericFibreIso (K := K)) ∧
    IsMinimalModel (projectiveSpaceOverRing 1 (.of K) ↘ Spec (.of K))
      (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R)) (twistedGenericFibreIso (K := K) hπ) ∧
    ¬ ∃ g : projectiveSpaceOverRing 1 (.of R) ⟶ projectiveSpaceOverRing 1 (.of R), IsIso g ∧
      IsModelHom (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R))
        (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R))
        (projectiveLineGenericFibreIso (K := K)) (twistedGenericFibreIso hπ) g := by
  have hπ' := mem_maximalIdeal_of_irreducible hπ
  have hiso : ∀ f : AlgebraicGeometry.Proj (lineGrading κ) ⟶
      projectiveSpaceOverRing 1 (.of R),
      f = (polynomialComparison κ 1).iso.inv ≫ specialFibreMap →
      ∃ e : AlgebraicGeometry.Proj (lineGrading κ) ≅
        pullback (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R)) (residueSpecMap R),
        f = e.hom ≫ pullback.fst _ _ := by
    rintro f rfl
    exact ⟨(polynomialComparison κ 1).iso.symm ≪≫
      (projectiveSpaceOverBaseChangeIso 1 (residueSpecMap R)).symm, by simp⟩
  refine ⟨inferInstance, isRegular_conicScheme hπ, inferInstance, isModel_conic hπ,
    range_specialFibre_eq_union hπ, specialFiberIdeal_eq_mul K hπ,
    isExceptionalCurveOfFirstKind_firstLine hπ, isExceptionalCurveOfFirstKind_secondLine hπ,
    ⟨κ, inferInstance, _, firstLineIso hπ, isExceptionalCurveOfFirstKind_firstLine hπ⟩,
    isModelHom_secondProjection hπ, ⟨_, secondLine_comp_secondProjection hπ'⟩,
    hiso _ (firstLine_comp_secondProjection hπ'),
    isModelHom_firstProjection hπ, ⟨_, firstLine_comp_firstProjection hπ'⟩,
    hiso _ (secondLine_comp_firstProjection hπ'),
    isMinimalModel_projectiveLine _ projectiveLineGenericFibreIso_hom_snd,
    isMinimalModel_projectiveLine _ (twistedGenericFibreIso_hom_snd hπ),
    not_exists_isIso_isModelHom_twisted hπ⟩

end Stacks.Models.GenusZero

end
