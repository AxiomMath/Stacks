module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CohenMacaulay.Source
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingNoetherian

/-!
# Faithful flatness of a flat local homomorphism and of the étale local rings of a flat morphism

A flat local homomorphism of local rings is faithfully flat. Applied to the canonical
homomorphism of étale local rings induced by a morphism of algebraic spaces at a geometric
point of its source, this says that a flat morphism `f : F ⟶ G` of algebraic spaces over a
scheme `S` induces at every geometric point `x` of `F` a faithfully flat homomorphism

`𝒪_{G, f ∘ x} ⟶ 𝒪_{F, x}`

of étale local rings.

## Main results

* `RingHom.Flat.faithfullyFlat_of_isLocalHom`: a flat local homomorphism of local rings is
  faithfully flat.
* `AlgebraicGeometry.Space.faithfullyFlat_etaleLocalRingMap`: the canonical homomorphism of étale
  local rings of a flat morphism of algebraic spaces at a geometric point of its source is
  faithfully flat.

## Implementation notes

The first result is Stacks Algebra, Lemma 10.39.17 (Tag 00HR), in the form of a ring
homomorphism. The second is a corollary of Stacks 04NG (the étale local ring map of a flat
morphism is flat) and 00HR; the Stacks proofs that use it cite it as
"Morphisms of Spaces, Section 03MK". That section tag itself is registered on the definition of
flatness and its agreement with the representable notion, which is what the section's
introduction states.

## References

* [Stacks Project, Tag 00HR](https://stacks.math.columbia.edu/tag/00HR)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
* [Stacks Project, Tag 03MK](https://stacks.math.columbia.edu/tag/03MK)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace RingHom.Flat

/-- **Stacks 00HR**, in the form of a ring homomorphism: a flat local homomorphism of local rings
is faithfully flat. -/
@[stacks 00HR "for a ring homomorphism",
  ega "0 6.6.1" "(e) ⇒ (a), special case",
  ega "0 6.6.2" "partial, special case",
  sga "1 IV 2.2" "special case",
  sga "1 IV 2.6" "(i), special case"]
theorem faithfullyFlat_of_isLocalHom {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] {f : R →+* S} (hf : f.Flat) [IsLocalHom f] : f.FaithfullyFlat := by
  let : Algebra R S := f.toAlgebra
  have : Module.Flat R S := hf
  have : IsLocalHom (algebraMap R S) := ‹IsLocalHom f›
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

end RingHom.Flat

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The canonical homomorphism of étale local rings `𝒪_{G, f ∘ x} ⟶ 𝒪_{F, x}` induced by a flat
morphism `f : F ⟶ G` of algebraic spaces at a geometric point `x` of its source is faithfully
flat.

This is a corollary of Stacks 04NG (`flat_etaleLocalRingMap`: the map is flat) and Stacks 00HR
(`RingHom.Flat.faithfullyFlat_of_isLocalHom`); the Stacks proofs that use it cite it as
"Morphisms of Spaces, Section 03MK". -/
theorem faithfullyFlat_etaleLocalRingMap {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G)
    (hf : IsFlat B S hS f) (x : GeometricPoint B S hS F) :
    (etaleLocalRingMap hF f x).FaithfullyFlat := by
  have : IsLocalRing (etaleLocalRing B S hS G (geometricPointMap f x)) :=
    isLocalRing_etaleLocalRing B S hS G hG (geometricPointMap f x)
  have : IsLocalRing (etaleLocalRing B S hS F x) := isLocalRing_etaleLocalRing B S hS F hF x
  have : IsLocalHom (etaleLocalRingMap hF f x) := isLocalHom_etaleLocalRingMap B S hS hF hG f x
  exact (flat_etaleLocalRingMap B S hS hF hG f hf x).faithfullyFlat_of_isLocalHom

end AlgebraicGeometry.Space

end
