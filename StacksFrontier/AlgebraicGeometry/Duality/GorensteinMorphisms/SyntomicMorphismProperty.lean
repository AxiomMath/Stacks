module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinMorphisms.Locality
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Syntomic

/-!
# Syntomic morphisms satisfy the Gorenstein morphism property

A syntomic morphism of schemes is a Gorenstein morphism, and equivalently so is a flat local
complete intersection morphism. Here both formulations are recorded as inclusions of morphism
properties into `AlgebraicGeometry.gorensteinWithLocallyNoetherianFibers`.

## Main results

* `AlgebraicGeometry.syntomic_le_gorensteinWithLocallyNoetherianFibers`: the syntomic morphisms
  are Gorenstein morphisms with locally Noetherian fibres.
* `AlgebraicGeometry.flat_inf_lci_le_gorensteinWithLocallyNoetherianFibers`: the flat local
  complete intersection morphisms are Gorenstein morphisms with locally Noetherian fibres.

## Implementation notes

`AlgebraicGeometry.Scheme.Hom.IsGorenstein` takes a proof that every fibre is locally Noetherian
as an explicit argument, so Gorensteinness of a morphism is not by itself a predicate on
morphisms. `AlgebraicGeometry.gorensteinWithLocallyNoetherianFibers` packages that proof
existentially and is the resulting `CategoryTheory.MorphismProperty`; the statements below are the
two formulations of the lemma in that packaging, which is the form the morphism-property API — the
monotonicity lemmas of `CategoryTheory.MorphismProperty.IsLocalAtSource` and
`CategoryTheory.MorphismProperty.IsLocalAtTarget`, and stability under a precoverage — consumes.

The existential witness is not an added hypothesis: it is supplied from
`AlgebraicGeometry.isLocallyNoetherian_fiber_of_syntomic`, a syntomic morphism being locally of
finite presentation so that each of its fibres is locally of finite type over a field. The
witness-explicit forms `AlgebraicGeometry.isGorenstein_of_syntomic` and
`AlgebraicGeometry.isGorenstein_of_flat_of_isLocalCompleteIntersectionMorphism` remain the primary
statements of the lemma and are used here.

The second inclusion is the first one precomposed with the equivalence of "syntomic" and "flat and
local complete intersection morphism", Stacks 069K; `⊓` is the meet of morphism properties, so its
source is exactly the class of flat local complete intersection morphisms. Its name abbreviates
`AlgebraicGeometry.IsLocalCompleteIntersectionMorphism` to `lci`, as elsewhere in this library.

## References

* [Stacks Project, Tag 0C15](https://stacks.math.columbia.edu/tag/0C15)
* [Stacks Project, Tag 0C0A](https://stacks.math.columbia.edu/tag/0C0A)
* [Stacks Project, Tag 069K](https://stacks.math.columbia.edu/tag/069K)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Stacks 0C15.** A syntomic morphism of schemes is a Gorenstein morphism: the syntomic
morphisms are contained in the morphism property of having locally Noetherian fibres and being
Gorenstein. -/
@[stacks 0C15 "a syntomic morphism is Gorenstein, as an inclusion of morphism properties"]
public theorem syntomic_le_gorensteinWithLocallyNoetherianFibers :
    (@Syntomic : MorphismProperty Scheme.{u}) ≤ gorensteinWithLocallyNoetherianFibers :=
  fun _ _ f hf => ⟨isLocallyNoetherian_fiber_of_syntomic hf, isGorenstein_of_syntomic f hf⟩

/-- **Stacks 0C15.** A flat local complete intersection morphism of schemes is a Gorenstein
morphism: the meet of flatness and being a local complete intersection morphism is contained in
the morphism property of having locally Noetherian fibres and being Gorenstein. This is the second
formulation of the lemma, equivalent to the first by Stacks 069K. -/
@[stacks 0C15 "a flat lci morphism is Gorenstein, as an inclusion of morphism properties"]
public theorem flat_inf_lci_le_gorensteinWithLocallyNoetherianFibers :
    (@Flat ⊓ @IsLocalCompleteIntersectionMorphism : MorphismProperty Scheme.{u}) ≤
      gorensteinWithLocallyNoetherianFibers :=
  fun _ _ f hf =>
    syntomic_le_gorensteinWithLocallyNoetherianFibers _ _ f
      (syntomic_of_flat_of_isLocalCompleteIntersectionMorphism hf.1 hf.2)

end AlgebraicGeometry

end
