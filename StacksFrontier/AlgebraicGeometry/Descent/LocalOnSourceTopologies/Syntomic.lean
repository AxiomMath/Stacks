module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.SyntomicLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Morphisms.SyntomicScheme

/-!
# Syntomicity is local on the source for the syntomic topology

A morphism of schemes is syntomic if and only if its composites with the members of a syntomic
covering of its source are syntomic.

## Main results

* `AlgebraicGeometry.Syntomic.isLocalAtSource_syntomicPrecoverage`: syntomicity is local on the
  source for the syntomic topology.

## Implementation notes

Syntomic coverings of the source are the families of `AlgebraicGeometry.Scheme.precoverage` of
`AlgebraicGeometry.Syntomic`, which are exactly the syntomic coverings of Tag 0225.

## References

* [Stacks Project, Tag 0225](https://stacks.math.columbia.edu/tag/0225)
* [Stacks Project, Tag 02KM](https://stacks.math.columbia.edu/tag/02KM)
* [Stacks Project, Tag 036H](https://stacks.math.columbia.edu/tag/036H)
* [Stacks Project, Tag 036S](https://stacks.math.columbia.edu/tag/036S)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Being syntomic is local on the source for the syntomic topology: a morphism of schemes is
syntomic exactly when its composites with the members of a syntomic covering of its source are. -/
@[stacks 036S]
instance Syntomic.isLocalAtSource_syntomicPrecoverage :
    MorphismProperty.IsLocalAtSource (@Syntomic.{u} : MorphismProperty Scheme.{u})
      (Scheme.precoverage (@Syntomic.{u})) :=
  letI : MorphismProperty.RespectsLeft (@Syntomic.{u} : MorphismProperty Scheme.{u})
      (@Syntomic.{u} : MorphismProperty Scheme.{u}) :=
    { precomp := fun i hi f hf => MorphismProperty.comp_mem _ i f hi hf }
  isLocalAtSource_syntomic_of_affine_descent (@Syntomic.{u})
    syntomic_of_comp_surjective_syntomic_of_isAffine

end AlgebraicGeometry

end
