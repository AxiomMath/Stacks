module

public import StacksFrontier.AlgebraicGeometry.WeilDeRham.DiagonalClaimsFromCup
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.StarIdentityProof
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.FactorizationThroughSection
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.TopInjectiveProof
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.TopDegreeCupInjective
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.TopFormsGenerator

/-!
# The two claims of the diagonal argument of [Stacks, Tag 0G8J]

Let `A` be a Noetherian ring and `f : X ⟶ Spec A` proper and smooth of relative dimension
`n = e + 1` with `A ⟶ Γ(X, 𝒪_X)` bijective and a section `σ`. This file proves the two claims of
`StacksFrontier.AlgebraicGeometry.WeilDeRham.DiagonalClaims`.

* **The diagonal claim** (`Stacks.WeilDeRham.diagonalClaim`): through [Stacks, Tag 0G8C] it is the
  identity `(★)` `p₁^*θ ∪ η = p₁^*θ ∪ p₂^*ξ + p₂^*θ ∪ p₁^*ξ`
  (`Stacks.WeilDeRham.diagonalClaim_of_starIdentity`); by the Künneth decomposition of the forms of
  `X ×_A X` ([Stacks, Tag 0FMA]) this reduces to the factorization of the cup product with
  `p^*θ` through the section of the other projection
  (`Stacks.WeilDeRham.starIdentity_of_cupFactorsThroughSection`), which is the Künneth formula
  ([Stacks, Tag 0FU4]) together with the splitting `RΓ(X, 𝒪_X) = A ⊕ P` of [Stacks, Tag 0G8H] and
  the vanishing of [Stacks, Tag 0BCG] (`Stacks.WeilDeRham.cupFactorsThroughSection_fst`,
  `Stacks.WeilDeRham.cupFactorsThroughSection_snd`).

* **Top-degree injectivity** (`Stacks.WeilDeRham.topInjective`): through [Stacks, Tag 0G8C] it is
  the injectivity of `x ↦ p₂^*x ∪ p₁^*ξ` (`Stacks.WeilDeRham.topInjective_of_cupTopInjective`,
  `Stacks.WeilDeRham.cupTopInjective_of_pullbackCup`), which is the top-degree Künneth formula
  together with the fact that `ξ` generates `Hⁿ(X, Ωⁿ_{X/A})`
  (`Stacks.WeilDeRham.pullbackCupTopInjective`,
  `Stacks.WeilDeRham.sectionClassNormalized_generates`).

## Main results

* `Stacks.WeilDeRham.diagonalClaim`.
* `Stacks.WeilDeRham.topInjective`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.WeilDeRham

/-- **The diagonal claim of [Stacks, Tag 0G8J]**: for `θ ∈ Hⁿ(X, Ω^{n-1}_{X/A})`, the Gysin map of
the diagonal is the sum of those of `(id, σ ∘ f)` and `(σ ∘ f, id)`. -/
theorem diagonalClaim {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [IsProper f] (e : ℕ) [SmoothOfRelativeDimension (e + 1) f]
    [IsIso f.appTop] (σ : Spec (.of A) ⟶ X) (hσ : σ ≫ f = 𝟙 _) [IsClosedImmersion σ]
    [LocallyOfFinitePresentation σ] [Smooth (σ ≫ f)] [FormallyUnramified (σ ≫ f)] :
    DiagonalClaim f e σ hσ :=
  diagonalClaim_of_starIdentity f e σ hσ
    (starIdentity_of_cupFactorsThroughSection f e σ hσ
      (cupOnProduct_fstPullback_diagonalClass f e)
      (cupFactorsThroughSection_fst f e σ hσ e (e + 1))
      (cupFactorsThroughSection_snd f e σ hσ e (e + 1)))

/-- **Top-degree injectivity in the diagonal argument of [Stacks, Tag 0G8J]**: the Gysin map of
`(σ ∘ f, id)` is injective on `Hⁿ(X, Ωⁿ_{X/A})`. -/
theorem topInjective {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [IsProper f] (e : ℕ) [SmoothOfRelativeDimension (e + 1) f]
    [IsIso f.appTop] (σ : Spec (.of A) ⟶ X) (hσ : σ ≫ f = 𝟙 _) [IsClosedImmersion σ]
    [LocallyOfFinitePresentation σ] [Smooth (σ ≫ f)] [FormallyUnramified (σ ≫ f)] :
    TopInjective f e σ hσ :=
  topInjective_of_cupTopInjective f e σ hσ
    (cupTopInjective_of_pullbackCup f e σ (sectionClassNormalized f e σ) rfl
      (pullbackCupTopInjective f (e + 1) σ hσ (sectionClassNormalized f e σ)
        (fun x => sectionClassNormalized_generates f e σ hσ x)))

end Stacks.WeilDeRham

end
