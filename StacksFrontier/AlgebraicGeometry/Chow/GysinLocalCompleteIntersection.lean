module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksCore.Tactic.StacksAttribute

/-!
# Gysin maps for local complete intersection morphisms

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `f : X ⟶ Y` be a
local complete intersection morphism of schemes locally of finite type over `S`. Stacks 0FF3 says
that *the Gysin map for `f` exists* if `f` can be written as `f = g ∘ i` with `g` smooth and `i` an
immersion, and in that case defines the *Gysin map*

  `f^! = i^! ∘ g^* ∈ A^*(X ⟶ Y)`,

where `i^! = c(X ⟶ P, 𝒩_{X/P})` is the bivariant class attached in section 42.54 of the Stacks
Project to the normal sheaf of `i` — an immersion through which an lci morphism of locally
Noetherian schemes factors smoothly is automatically regular, so that normal sheaf is finite
locally free — and `g^*` is the flat pullback class of Stacks 0B78. The composite depends only on
`f`, by Stacks 0FF2.

## Main definitions

* `Stacks.Chow.GysinMapExists` — the existence condition of Stacks 0FF3: a factorization of the
  morphism as an immersion followed by a smooth morphism.

## Main results

* `Stacks.Chow.GysinMapExists.of_comp` — the condition holds for a composite of an immersion with
  a smooth morphism, which is the construction the definition refers to.
* `Stacks.Chow.GysinMapExists.of_isImmersion` and `Stacks.Chow.GysinMapExists.of_smooth` — it
  holds for an immersion and for a smooth morphism, the two cases in which the Gysin map of
  Stacks 0FF3 reduces to the class of section 42.54 and to flat pullback respectively.

## Implementation notes

The condition is recorded for an arbitrary morphism of schemes. Local complete intersectionness
of `f` — `AlgebraicGeometry.IsLocalCompleteIntersectionMorphism`, Stacks 069F — and finite type
over the base are standing hypotheses of the section rather than part of the condition, and the
condition does not use them; for an lci morphism of schemes locally of finite type over `S` it is
Stacks 0FF3 verbatim.

### The Gysin map itself

The class `f^! = i^! ∘ g^*` is `Stacks.Chow.SmoothFactorization.gysinMap` and
`Stacks.Chow.lciGysinMap`, in
`StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.GysinMap`; it needs the
factorization datum and the regularity of its immersion, which are in
`StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.FactorizationIndependence`,
downstream of this file.

## References

* [Stacks Project, Tag 0FF3](https://stacks.math.columbia.edu/tag/0FF3)
* [Stacks Project, Tag 0FF2](https://stacks.math.columbia.edu/tag/0FF2)
* [Stacks Project, Tag 069F](https://stacks.math.columbia.edu/tag/069F)
* [Stacks Project, Tag 0B78](https://stacks.math.columbia.edu/tag/0B78)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-- **Stacks 0FF3.** The Gysin map of a local complete intersection morphism `f : X ⟶ Y` of
schemes locally of finite type over the base *exists* when `f` factors as an immersion
`i : X ⟶ P` followed by a smooth morphism `g : P ⟶ Y`. -/
@[stacks 0FF3 "the existence of the Gysin map"]
def GysinMapExists {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∃ (P : Scheme.{u}) (i : X ⟶ P) (g : P ⟶ Y), IsImmersion i ∧ Smooth g ∧ i ≫ g = f

/-- The Gysin map exists for the composite of an immersion with a smooth morphism. -/
theorem GysinMapExists.of_comp {X P Y : Scheme.{u}} (i : X ⟶ P) [IsImmersion i] (g : P ⟶ Y)
    [Smooth g] : GysinMapExists (i ≫ g) :=
  ⟨P, i, g, inferInstance, inferInstance, rfl⟩

/-- The Gysin map exists for an immersion, factored through the identity of its target. -/
theorem GysinMapExists.of_isImmersion {X Y : Scheme.{u}} (f : X ⟶ Y) [IsImmersion f] :
    GysinMapExists f :=
  Category.comp_id f ▸ GysinMapExists.of_comp f (𝟙 Y)

/-- The Gysin map exists for a smooth morphism, factored through the identity of its source. -/
theorem GysinMapExists.of_smooth {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] : GysinMapExists f :=
  Category.id_comp f ▸ GysinMapExists.of_comp (𝟙 X) f

end Stacks.Chow

end
