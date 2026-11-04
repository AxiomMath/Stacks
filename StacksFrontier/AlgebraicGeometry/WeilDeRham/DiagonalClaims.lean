module

public import StacksFrontier.AlgebraicGeometry.WeilDeRham.DiagonalGysinMaps

/-!
# The two claims of the diagonal argument of [Stacks, Tag 0G8J]

Let `f : X ⟶ Spec A` be proper and smooth of relative dimension `n = e + 1` with a section `σ`,
`W = X ×_A X`, `Δ` the diagonal, `j = (σ ∘ f, id)` and `j' = (id, σ ∘ f)`. The proof of
[Stacks, Tag 0G8J] in the case of a section rests on two facts about the Gysin maps of
[Stacks, Tag 0G8A] of these closed immersions (`Stacks.WeilDeRham.diagonalGysin`,
`Stacks.WeilDeRham.sectionFstGysin`, `Stacks.WeilDeRham.sectionSndGysin`):

* **the diagonal claim**: for `θ ∈ Hⁿ(X, Ω^{n-1}_{X/A})`,
  `γ_Δ(θ) = γ_{j'}(θ) + γ_j(θ)` in `H^{2n}(W, Ω^{2n-1}_{W/A})`. Through [Stacks, Tag 0G8C] and the
  Künneth formula this is the claim `θ₁ = θ₂ = θ` of the source, i.e.
  `γ^{n-1,n}(θ) = θ ⊗ ξ + ξ ⊗ θ`, where `ξ` is the Gysin class of the section;
* **top-degree injectivity**: `γ_j` is injective on `Hⁿ(X, Ωⁿ_{X/A})`. Through
  [Stacks, Tag 0G8C] and the Künneth formula in top degree this is the injectivity of
  `x ↦ ξ ⊗ x`.

This file states them as propositions, so that the argument assembling them into the vanishing
of the top de Rham differential and their proofs can be written separately.

## Main definitions

* `Stacks.WeilDeRham.DiagonalClaim`.
* `Stacks.WeilDeRham.TopInjective`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.DeRham.CohomologicalGysin

universe u

namespace Stacks.WeilDeRham

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
  (e : ℕ) [SmoothOfRelativeDimension (e + 1) f] (σ : Spec (.of A) ⟶ X) (hσ : σ ≫ f = 𝟙 _)
  [IsClosedImmersion σ] [LocallyOfFinitePresentation σ]

/-- **The diagonal claim** of [Stacks, Tag 0G8J]: for every class
`θ ∈ Hⁿ(X, Ω^{n-1}_{X/A})`, `n = e + 1`, the Gysin map of the diagonal is the sum of those of
`j' = (id, σ ∘ f)` and `j = (σ ∘ f, id)`. -/
def DiagonalClaim : Prop :=
  ∀ θ : Hgroup (structureSheafRing X.toRingedSpace) ⊤ (e + 1)
      (Scheme.Hom.relativeDifferentialForms f (e : ℤ)),
    (diagonalGysin f (e + 1) e (e + 1)).hom θ =
      (sectionSndGysin f (e + 1) σ hσ e (e + 1)).hom θ +
        (sectionFstGysin f (e + 1) σ hσ e (e + 1)).hom θ

/-- **Top-degree injectivity**: the Gysin map of `j = (σ ∘ f, id)` is injective on
`Hⁿ(X, Ωⁿ_{X/A})`, `n = e + 1`. -/
def TopInjective : Prop :=
  ∀ x : Hgroup (structureSheafRing X.toRingedSpace) ⊤ (e + 1)
      (Scheme.Hom.relativeDifferentialForms f ((e + 1 : ℕ) : ℤ)),
    (sectionFstGysin f (e + 1) σ hσ (e + 1) (e + 1)).hom x = 0 → x = 0

end Stacks.WeilDeRham

end
