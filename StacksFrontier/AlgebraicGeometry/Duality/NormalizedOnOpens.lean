module

public import StacksFrontier.AlgebraicGeometry.Duality.NormalizedDualizingTransitivity

/-!
# Dualizing complexes normalized on every open separated over the base

Fix an upper shriek formalism `A` (`Stacks.Duality.UpperShriek`), a morphism `p : X ⟶ S` of
finite type with Noetherian target and a complex `ω_S^•` on `S`. The definition of a complex
normalized relative to `ω_S^•` in [Stacks, Tag 0AU5] is made relative to a finite covering of
`X` by opens separated over `S`. The discussion before [Stacks, Tag 0AUA] uses the covering-free
form: isomorphisms `K|_W ≅ ω_W^•` for every open `W` separated over `S`, compatible with
restriction. This file defines that form and passes from it to the form relative to a covering.

## Main definitions

* `Stacks.Duality.NormalizedOnOpens` — a complex normalized relative to `ω_S^•` on every open
  separated over `S`.
* `Stacks.Duality.NormalizedOnOpens.toNormalized` — such a complex is normalized relative to
  `ω_S^•` and every finite covering by opens separated over `S`.

## References

* [Stacks Project, Tag 0AU5](https://stacks.math.columbia.edu/tag/0AU5)
* [Stacks Project, Tag 0AUA](https://stacks.math.columbia.edu/tag/0AUA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u v v' w w'

namespace Stacks.Duality

/-- **A dualizing complex normalized relative to `ω_S^•`**, the covering-free notion of the
discussion before [Stacks, Tag 0AUA]: a complex `K` on `X` with isomorphisms
`α_W : K|_W ≅ ω_W^• = (W → S)^! ω_S^•` for every open `W` separated over `S`, compatible with
restriction. -/
structure NormalizedOnOpens {𝒟 : Scheme.{u} → Type v} [∀ X : Scheme.{u}, Category.{v'} (𝒟 X)]
    (A : UpperShriek 𝒟) {X S : Scheme.{u}} {p : X ⟶ S} (hp : IsFiniteTypeOverNoetherian p)
    (ωS : 𝒟 S) where
  /-- The complex `ω_X^•` itself. -/
  complex : 𝒟 X
  /-- The isomorphism `α_W : K|_W ≅ ω_W^•` on an open separated over `S`. -/
  localIso (W : X.Opens) (hW : IsShriekable (W.ι ≫ p)) :
    A.restrictTo hp W complex ≅ A.localModel hW ωS
  /-- The restriction of `α_W` to `W' ≤ W` is `α_{W'}`. -/
  compat {W' W : X.Opens} (h : W' ≤ W) (hW : IsShriekable (W.ι ≫ p))
    (hW' : IsShriekable (W'.ι ≫ p)) :
    A.restrictLocalIso hp ωS complex h hW (localIso W hW) = localIso W' hW'

namespace NormalizedOnOpens

variable {𝒟 : Scheme.{u} → Type v} [∀ X : Scheme.{u}, Category.{v'} (𝒟 X)] {A : UpperShriek 𝒟}
  {X S : Scheme.{u}} {p : X ⟶ S} {hp : IsFiniteTypeOverNoetherian p} {ωS : 𝒟 S}

/-- A dualizing complex normalized relative to `ω_S^•` is normalized relative to `ω_S^•` and every
finite covering of `X` by opens separated over `S`. -/
def toNormalized (𝒦 : NormalizedOnOpens A hp ωS) {ι : Type w} (𝒰 : SeparatedCovering p ι) :
    Normalized A hp ωS 𝒰 where
  complex := 𝒦.complex
  localIso i := 𝒦.localIso (𝒰.U i) (𝒰.shriekable i)
  compat _ _ := (𝒦.compat inf_le_left _ _).trans (𝒦.compat inf_le_right _ _).symm

end NormalizedOnOpens

end Stacks.Duality

end
