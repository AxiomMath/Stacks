module

public import StacksFrontier.AlgebraicGeometry.AmpleProjectiveImmersion.Basic
public import StacksFrontier.AlgebraicGeometry.SegreProdIso.Main
public import StacksFrontier.AlgebraicGeometry.HProjective.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.ExternalTensorProduct

/-!
# Immersions through the Segre embedding

Let `S` be a scheme. A morphism `X ⟶ ℙⁿ_S ×_S ℙᵐ_S` over `S` is an immersion as soon as one of its
components is, and the Segre embedding `ℙⁿ_S ×_S ℙᵐ_S ⟶ ℙ^{nm+n+m}_S` is a closed immersion over
`S`; so an immersion `j : X ⟶ ℙⁿ_S` over `S` and any morphism `j' : X ⟶ ℙᵐ_S` over `S` give an
immersion `X ⟶ ℙ^{nm+n+m}_S` over `S`.

This file also states, as the proposition `Stacks.ChartImmersionAssembly.SegreTwist`, that the
Segre embedding may be chosen to pull `𝒪(1)` back to the external tensor product
(`AlgebraicGeometry.externalTensorProduct`) of the two hyperplane sheaves.

## Main definitions

* `Stacks.ChartImmersionAssembly.SegreTwist`: there is a closed immersion
  `ℙⁿ_S ×_S ℙᵐ_S ⟶ ℙ^{nm+n+m}_S` over `S` pulling `𝒪(1)` back to the external tensor product of
  the hyperplane sheaves of the factors.

## Main results

* `Stacks.ChartImmersionAssembly.exists_segreEmbedding_of_segreTwist`: `SegreTwist` implies the
  existence of a closed immersion `ℙⁿ_S ×_S ℙᵐ_S ⟶ ℙ^{nm+n+m}_S` over `S`.
* `Stacks.ChartImmersionAssembly.exists_isImmersion_over_of_isImmersion_pair`: an immersion
  `X ⟶ ℙⁿ_S` over `S` and any morphism `X ⟶ ℙᵐ_S` over `S` give an immersion
  `X ⟶ ℙ^{nm+n+m}_S` over `S`.

## References

* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
* [Stacks Project, Tag 01WD](https://stacks.math.columbia.edu/tag/01WD)
* [Stacks Project, Tag 0G46](https://stacks.math.columbia.edu/tag/0G46)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AmpleProjectiveImmersion

namespace Stacks.ChartImmersionAssembly

universe u

/-! ### The pullback of `𝒪(1)` along the Segre embedding -/

/-- There is a closed immersion `σ : ℙⁿ_S ×_S ℙᵐ_S ⟶ ℙ^{nm+n+m}_S` over `S` such that the
pullback of `𝒪(1)` along `σ` is isomorphic to the external tensor product of the hyperplane
sheaves of the two factors. -/
def SegreTwist (n m : ℕ) (S : Scheme.{u}) : Prop :=
  ∃ σ : pullback ((projectiveSpaceOver n S) ↘ S) ((projectiveSpaceOver m S) ↘ S) ⟶
      projectiveSpaceOver (n * m + n + m) S,
    IsClosedImmersion σ ∧
      σ ≫ ((projectiveSpaceOver (n * m + n + m) S) ↘ S) =
        pullback.fst ((projectiveSpaceOver n S) ↘ S) ((projectiveSpaceOver m S) ↘ S) ≫
          ((projectiveSpaceOver n S) ↘ S) ∧
      Nonempty ((Scheme.Modules.pullback σ).obj
          (projectiveSpaceTwistingSheaf (n * m + n + m) S) ≅
        externalTensorProduct ((projectiveSpaceOver n S) ↘ S) ((projectiveSpaceOver m S) ↘ S)
          (projectiveSpaceTwistingSheaf n S) (projectiveSpaceTwistingSheaf m S))

/-- If `SegreTwist n m S` holds, then there is a closed immersion
`ℙⁿ_S ×_S ℙᵐ_S ⟶ ℙ^{nm+n+m}_S` over `S`. -/
theorem exists_segreEmbedding_of_segreTwist {n m : ℕ} {S : Scheme.{u}} (h : SegreTwist n m S) :
    ∃ σ : pullback ((projectiveSpaceOver n S) ↘ S) ((projectiveSpaceOver m S) ↘ S) ⟶
        projectiveSpaceOver (n * m + n + m) S,
      IsClosedImmersion σ ∧
        σ ≫ ((projectiveSpaceOver (n * m + n + m) S) ↘ S) =
          pullback.fst ((projectiveSpaceOver n S) ↘ S) ((projectiveSpaceOver m S) ↘ S) ≫
            ((projectiveSpaceOver n S) ↘ S) :=
  h.imp fun _ h => ⟨h.1, h.2.1⟩

/-! ### Immersions through the Segre embedding -/

/-- Given an immersion `j : X ⟶ ℙⁿ_S` over `S` and any morphism `j' : X ⟶ ℙᵐ_S` over `S`, there
is an immersion `X ⟶ ℙ^{nm+n+m}_S` over `S`. -/
theorem exists_isImmersion_over_of_isImmersion_pair {X S : Scheme.{u}} {f : X ⟶ S} {n m : ℕ}
    (j : X ⟶ projectiveSpaceOver n S) (hj : j ≫ ((projectiveSpaceOver n S) ↘ S) = f)
    [IsImmersion j] (j' : X ⟶ projectiveSpaceOver m S)
    (hj' : j' ≫ ((projectiveSpaceOver m S) ↘ S) = f) :
    ∃ k : X ⟶ projectiveSpaceOver (n * m + n + m) S,
      IsImmersion k ∧ k ≫ ((projectiveSpaceOver (n * m + n + m) S) ↘ S) = f := by
  obtain ⟨σ, hcl, hover⟩ := Stacks.AlgebraicGeometry.SegreProdIso.exists_segreEmbedding n m S
  have := isImmersion_lift j j' (hj.trans hj'.symm)
  refine ⟨pullback.lift j j' (hj.trans hj'.symm) ≫ σ, inferInstance, ?_⟩
  rw [Category.assoc, hover, ← Category.assoc, pullback.lift_fst, hj]

end Stacks.ChartImmersionAssembly

end
