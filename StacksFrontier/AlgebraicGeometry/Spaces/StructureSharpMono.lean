module

public import StacksFrontier.AlgebraicGeometry.Spaces.RingedToposHomConsequences
public import StacksFrontier.CategoryTheory.Sites.WhiskeringMono

/-!
# Injectivity of the structure map is the same at both levels

A morphism `f : X ⟶ Y` of algebraic spaces has two structure maps: the map
`AlgebraicGeometry.Space.structureSharp` of sheaves of *rings*, which the chart formula
`AlgebraicGeometry.Space.chartProjection_structureMapApp` computes, and the field `fSharp`
of the morphism of small étale ringed topoi
`AlgebraicGeometry.Space.smallEtaleRingedToposHom` of Stacks 03G8, which is a map of sheaves
of *commutative* rings. The second is the first with commutativity remembered
(`AlgebraicGeometry.Space.forgetCommRingSheaf_map_fSharp`).

This file supplies the direction
`AlgebraicGeometry.Space.mono_fSharp_of_mono_structureSharp` left open, so that injectivity
of the structure map may be read off either level.

## Main results

* `AlgebraicGeometry.Space.mono_structureSharp_of_mono_fSharp`: if the structure map of the
  morphism of ringed topoi is a monomorphism, so is the structure map of sheaves of rings.
* `AlgebraicGeometry.Space.mono_fSharp_iff_mono_structureSharp`: the two monomorphism
  conditions are equivalent.

## Implementation notes

Forgetting commutativity on sheaves is fully faithful
(`Stacks.Sheaves.ToposPullback.fullyFaithfulForgetCommRingSheaf`), and that gives the
direction already proved: a fully faithful functor *reflects* monomorphisms. The direction
here needs the same functor to *preserve* them, which full faithfulness indeed does not
give. It does not, however, need a description of the monomorphisms of sheaves of rings by
injectivity on sections. `CategoryTheory.sheafCompose_preservesMonomorphisms` gets it from
limit preservation instead: `CategoryTheory.sheafToPresheaf` creates fibre squares, so it
preserves and reflects monomorphisms, and on presheaves the functor is whiskering by
`forget₂ CommRingCat RingCat`, which preserves monomorphisms objectwise.

The equivalence is what lets the hypothesis of Stacks 0B8B — stated there as injectivity of
`𝒪_T ⟶ f_{T,*}𝒪_{X ×_Y T}` for every `T ⟶ Y`, hence at the level of sheaves of rings — be
both supplied to and consumed from the `fSharp` form carried by the morphism of ringed
topoi.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 0B8B](https://stacks.math.columbia.edu/tag/0B8B)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X Y : AlgebraicSpaces B S hS}

/-- If the structure map of the morphism of small étale ringed topoi of Stacks 03G8 is a
monomorphism, then so is the structure map `f♯ : 𝒪_Y ⟶ f_*𝒪_X` of sheaves of rings. The
latter is the former with commutativity forgotten, and forgetting commutativity on sheaves
preserves monomorphisms by `CategoryTheory.sheafCompose_preservesMonomorphisms`. -/
theorem mono_structureSharp_of_mono_fSharp (f : X ⟶ Y)
    (h : Mono (smallEtaleRingedToposHom B S hS f).fSharp) :
    Mono (structureSharp B S hS f) := by
  rw [← forgetCommRingSheaf_map_fSharp B S hS f]
  exact (sheafCompose (SmallEtale.topology B S hS Y.1)
    (forget₂ CommRingCat.{u} RingCat.{u})).map_mono _

/-- Injectivity of the structure map of a morphism of algebraic spaces may be read off
either the morphism of small étale ringed topoi of Stacks 03G8 or the structure map of
sheaves of rings: the two monomorphism conditions agree. -/
theorem mono_fSharp_iff_mono_structureSharp (f : X ⟶ Y) :
    Mono (smallEtaleRingedToposHom B S hS f).fSharp ↔ Mono (structureSharp B S hS f) :=
  ⟨mono_structureSharp_of_mono_fSharp B S hS f, mono_fSharp_of_mono_structureSharp B S hS f⟩

end AlgebraicGeometry.Space

end
