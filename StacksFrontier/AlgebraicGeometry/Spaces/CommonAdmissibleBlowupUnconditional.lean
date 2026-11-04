module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowBlowupDiagramExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.CommonAdmissibleBlowup
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteMorphismLimitSystem
import all StacksFrontier.AlgebraicGeometry.Spaces.ChowBlowupDiagramExistence

/-!
# Two admissible blowups which glue to a separated space of finite type

Let `Y` be a quasi-compact and quasi-separated algebraic space over a scheme `S` and let
`U ⟶ X₁`, `U ⟶ X₂` be open immersions of algebraic spaces over `Y`, with `U`, `X₁` and `X₂`
separated and of finite type over `Y`. Stacks 088Q says that there are `U`-admissible blowups
`X₁' ⟶ X₁` and `X₂' ⟶ X₂` and open immersions `X₁' ⟶ X`, `X₂' ⟶ X` into an algebraic space `X`
separated and of finite type over `Y`, compatibly with `U`.

This is `AlgebraicGeometry.Space.exists_isAdmissibleBlowup_isOpenImmersion_of_isOpenImmersion`,
whose two inputs are the statements of Stacks 07VR and 0873. Both are discharged here, as in the
proof of Stacks 088R: Stacks 07VR is
`AlgebraicGeometry.Space.exists_integralFiniteSystem_of_isFinite`, and Stacks 0873 is the
factorization of a separated morphism of finite type proved in
`StacksFrontier.AlgebraicGeometry.Spaces.ChowBlowupDiagramExistence`.

## Main results

* `Space.exists_isAdmissibleBlowup_isOpenImmersion_of_isOpenImmersion_unconditional`:
  **Stacks 088Q**.

## References

* [Stacks Project, Tag 088Q](https://stacks.math.columbia.edu/tag/088Q)
* [Stacks Project, Tag 07VR](https://stacks.math.columbia.edu/tag/07VR)
* [Stacks Project, Tag 0873](https://stacks.math.columbia.edu/tag/0873)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 088Q.** Let `Y` be a quasi-compact and quasi-separated algebraic space over `S` and
let `j₁ : U ⟶ X₁`, `j₂ : U ⟶ X₂` be open immersions of algebraic spaces over `Y`, with `U`,
`X₁` and `X₂` separated and of finite type over `Y`. There is a commutative diagram
`X₁ ⟵ X₁' ⟶ X ⟵ X₂' ⟶ X₂` under `U` and over `Y`, in which `b_k : X_k' ⟶ X_k` is a
`U`-admissible blowup (`U` being the open subspace `j_k(U)` of `X_k`), `i_k : X_k' ⟶ X` is an
open immersion, and `X` is separated and of finite type over `Y`. Moreover the morphisms
`u_k : U ⟶ X_k'` of the diagram are open immersions. -/
@[stacks 088Q]
theorem exists_isAdmissibleBlowup_isOpenImmersion_of_isOpenImmersion_unconditional
    {Y U X₁ X₂ : AlgebraicSpaces B S hS}
    (f₁ : X₁ ⟶ Y) (f₂ : X₂ ⟶ Y) (j₁ : U ⟶ X₁) (j₂ : U ⟶ X₂)
    (hYqc : IsQuasiCompactSpace B S hS Y.1)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y.1)
    (hj₁ : IsOpenImmersion B S hS j₁.hom) (hj₂ : IsOpenImmersion B S hS j₂.hom)
    (hj : j₁ ≫ f₁ = j₂ ≫ f₂)
    (hUft : IsFiniteType B S hS (j₁ ≫ f₁).hom) (hUsep : IsSeparated B S hS (j₁ ≫ f₁).hom)
    (hX₁ft : IsFiniteType B S hS f₁.hom) (hX₁sep : IsSeparated B S hS f₁.hom)
    (hX₂ft : IsFiniteType B S hS f₂.hom) (hX₂sep : IsSeparated B S hS f₂.hom) :
    ∃ (X₁' X₂' X : AlgebraicSpaces B S hS) (b₁ : X₁' ⟶ X₁) (b₂ : X₂' ⟶ X₂)
      (i₁ : X₁' ⟶ X) (i₂ : X₂' ⟶ X) (g : X ⟶ Y) (u₁ : U ⟶ X₁') (u₂ : U ⟶ X₂'),
      IsAdmissibleBlowup B S hS ⟨Subfunctor.range j₁.hom, @isOpenSubspace_range_of_open B S hS
        _ _ j₁.hom (mono_of_isOpenImmersion B S hS _ hj₁) U.2 hj₁⟩ b₁ ∧
      IsAdmissibleBlowup B S hS ⟨Subfunctor.range j₂.hom, @isOpenSubspace_range_of_open B S hS
        _ _ j₂.hom (mono_of_isOpenImmersion B S hS _ hj₂) U.2 hj₂⟩ b₂ ∧
      IsOpenImmersion B S hS i₁.hom ∧ IsOpenImmersion B S hS i₂.hom ∧
      IsSeparated B S hS g.hom ∧ IsFiniteType B S hS g.hom ∧
      i₁ ≫ g = b₁ ≫ f₁ ∧ i₂ ≫ g = b₂ ≫ f₂ ∧
      u₁ ≫ b₁ = j₁ ∧ u₂ ≫ b₂ = j₂ ∧ u₁ ≫ i₁ = u₂ ≫ i₂ ∧
      IsOpenImmersion B S hS u₁.hom ∧ IsOpenImmersion B S hS u₂.hom :=
  exists_isAdmissibleBlowup_isOpenImmersion_of_isOpenImmersion B.contains_terminal
    f₁ f₂ j₁ j₂ hYqc hYqs hj₁ hj₂ hj hUft hUsep hX₁ft hX₁sep hX₂ft hX₂sep
    (exists_integralFiniteSystem_of_isFinite B S hS)
    (exists_closedImmersion_separated_finitePresentation_of_finiteType B S hS)

end AlgebraicGeometry.Space

end
