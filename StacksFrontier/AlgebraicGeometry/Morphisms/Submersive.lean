module

public import Mathlib.AlgebraicGeometry.Morphisms.Constructors
public import Mathlib.CategoryTheory.MorphismProperty.Limits
import StacksCore.Tactic.StacksAttribute

/-!
# Submersive and universally submersive morphisms of schemes

A morphism of schemes is *submersive* when the continuous map of underlying topological spaces
is submersive in the sense of Stacks 0406, part (2), that is a quotient map: it is surjective
and the topology of the target is the quotient topology. It is *universally submersive* when its
base change along every morphism of schemes to its target is submersive. A submersive morphism
is in particular surjective.

This notion is unrelated to that of a submersion of differentiable manifolds.

## Main definitions

* `AlgebraicGeometry.Submersive`: **Stacks 040H**, part (1).
* `AlgebraicGeometry.UniversallySubmersive`: **Stacks 040H**, part (2).

## Main results

* `AlgebraicGeometry.Submersive.comp` and `AlgebraicGeometry.UniversallySubmersive.comp` are the
  two assertions of **Stacks 0CET**: both notions are stable under composition.
* `AlgebraicGeometry.submersive_of_universallySubmersive`: a universally submersive morphism is
  submersive, being the base change of itself along the identity.

## Implementation notes

Both notions are built from Mathlib's combinators on morphism properties, in the shape
`AlgebraicGeometry.UniversallyClosed` and `AlgebraicGeometry.UniversallyOpen` have: submersiveness
is `CategoryTheory.MorphismProperty.topologically` applied to `Topology.IsQuotientMap`, and
universal submersiveness is `CategoryTheory.MorphismProperty.universally` applied to that. The
quantification over all pullback squares rather than over the chosen pullback is the encoding
Mathlib uses throughout for the universal properties, and is equivalent to the Stacks Project's
because submersiveness respects isomorphisms.

Composition is then inherited twice: `Topology.IsQuotientMap.comp` gives it for the topological
property, and `CategoryTheory.MorphismProperty.IsStableUnderComposition.universally` transports
it through the universal quantifier.

## References

* [Stacks Project, Tag 0406](https://stacks.math.columbia.edu/tag/0406)
* [Stacks Project, Tag 040H](https://stacks.math.columbia.edu/tag/040H)
* [Stacks Project, Tag 0CET](https://stacks.math.columbia.edu/tag/0CET)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MorphismProperty

universe u

namespace AlgebraicGeometry

/-- **Stacks 040H, part (1).** A morphism of schemes is *submersive* when the continuous map of
underlying topological spaces is a quotient map, that is submersive in the sense of Stacks 0406,
part (2). This is unrelated to the notion of a submersion of differentiable manifolds. -/
@[stacks 040H "part (1): submersive", sga "1 IX 2.1" "submersive", ega "IV 15.7.8"]
def Submersive : MorphismProperty Scheme.{u} := topologically @Topology.IsQuotientMap

/-- **Stacks 040H, part (2).** A morphism of schemes `f : X ⟶ Y` is *universally submersive*
when the base change `Y' ×_Y X ⟶ Y'` of `f` along every morphism of schemes `Y' ⟶ Y` is
submersive. -/
@[stacks 040H "part (2): universally submersive",
  sga "1 IX 2.1" "univ. submersive",
  ega "IV 15.7.8"]
def UniversallySubmersive : MorphismProperty Scheme.{u} := Submersive.universally

/-- Universal submersiveness is submersiveness after an arbitrary base change. -/
theorem universallySubmersive_eq : UniversallySubmersive.{u} = Submersive.{u}.universally := rfl

/-- A morphism of schemes is submersive exactly when the map it induces on underlying
topological spaces is a quotient map. -/
theorem submersive_iff {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Submersive f ↔ Topology.IsQuotientMap f.base := Iff.rfl

/-- A morphism of schemes is universally submersive exactly when every morphism fitting into a
pullback square over it is submersive. -/
theorem universallySubmersive_iff {X Y : Scheme.{u}} (f : X ⟶ Y) :
    UniversallySubmersive f ↔ ∀ ⦃X' Y' : Scheme.{u}⦄ (i₁ : X' ⟶ X) (i₂ : Y' ⟶ Y) (f' : X' ⟶ Y'),
      IsPullback f' i₁ i₂ f → Submersive f' := Iff.rfl

/-- Submersiveness of morphisms of schemes is stable under composition, because a composition of
quotient maps of topological spaces is a quotient map. -/
instance submersive_isStableUnderComposition : Submersive.{u}.IsStableUnderComposition :=
  topologically_isStableUnderComposition _ fun _ _ hf hg ↦ hg.comp hf

/-- **Stacks 0CET, submersive morphisms.** The composition of a pair of submersive morphisms of
schemes is submersive. -/
@[stacks 0CET "submersive"]
theorem Submersive.comp {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : Submersive f) (hg : Submersive g) : Submersive (f ≫ g) :=
  MorphismProperty.comp_mem _ f g hf hg

/-- Universal submersiveness of morphisms of schemes is stable under composition, inherited from
submersiveness through the universal quantifier. -/
instance universallySubmersive_isStableUnderComposition :
    UniversallySubmersive.{u}.IsStableUnderComposition :=
  universallySubmersive_eq ▸ IsStableUnderComposition.universally Submersive.{u}

/-- **Stacks 0CET, universally submersive morphisms.** The composition of a pair of universally
submersive morphisms of schemes is universally submersive. -/
@[stacks 0CET "universally submersive"]
theorem UniversallySubmersive.comp {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : UniversallySubmersive f) (hg : UniversallySubmersive g) :
    UniversallySubmersive (f ≫ g) :=
  MorphismProperty.comp_mem _ f g hf hg

/-- A universally submersive morphism of schemes is submersive: it is its own base change along
the identity of its target. -/
theorem submersive_of_universallySubmersive {X Y : Scheme.{u}} {f : X ⟶ Y}
    (hf : UniversallySubmersive f) : Submersive f :=
  Submersive.universally_le f hf

end AlgebraicGeometry
