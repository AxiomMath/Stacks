module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.Topology.Sober
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.SchemeProperty.UniversallyInjective

/-!
# Universally injective étale morphisms are open immersions

A universally injective étale morphism of schemes is an open immersion. Combined with the
criterion for universal injectivity of a flat separated morphism in terms of its generic
points, this gives a criterion for an étale separated morphism to be an open immersion: it
suffices that the morphism be injective on the generic points of its source and induce
isomorphisms on the residue fields there.

## Main results

* `AlgebraicGeometry.isOpenImmersion_of_etale_universallyInjective`: a universally injective
  étale morphism is an open immersion.
* `AlgebraicGeometry.isOpenImmersion_of_etale_of_separated_of_genericPoints_injOn`: the
  open-immersion criterion at the generic points.

## Implementation notes

The first result is an instance, so that the open-immersion property is available to typeclass
search from the étale and universally injective hypotheses. The equality of residue fields is
stated as the canonical residue-field map being an isomorphism, and the condition on distinct
generic points is injectivity on `genericPoints`.

## References

* [Stacks Project, Tag 02LC](https://stacks.math.columbia.edu/tag/02LC)
* [Stacks Project, Tag 09NQ](https://stacks.math.columbia.edu/tag/09NQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A universally injective étale morphism of schemes is an open immersion. -/
@[stacks 02LC,
  ega "IV 17.9.1" "c) => a)",
  sga "1 IX 1.4" "étale+radicial ⇒ open",
  sga "1 I 5.1" "sufficiency"]
public instance isOpenImmersion_of_etale_universallyInjective
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] [UniversallyInjective f] :
    IsOpenImmersion f :=
  @IsOpenImmersion.of_flat_of_mono.{u} X Y f inferInstance inferInstance
    ((pullback.isIso_diagonal_iff f).mp ((isIso_iff_isOpenImmersion_and_surjective _).2
      ⟨inferInstance, (UniversallyInjective.iff_diagonal f).mp inferInstance⟩))

/-- An étale separated morphism with isomorphic residue fields at, and distinct images of, the
generic points of its source is an open immersion. -/
@[stacks 09NQ]
public theorem isOpenImmersion_of_etale_of_separated_of_genericPoints_injOn
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] [IsSeparated f]
    (hres : ∀ ξ ∈ genericPoints X, IsIso (f.residueFieldMap ξ))
    (hinj : Set.InjOn f (genericPoints X)) :
    IsOpenImmersion f :=
  @isOpenImmersion_of_etale_universallyInjective X Y f inferInstance
    (universallyInjective_of_flat_of_separated_of_genericPoints_injOn f hres hinj)

end AlgebraicGeometry

end
