module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSourceTopologies.AffineCriteria
public import StacksFrontier.AlgebraicGeometry.Descent.SmoothDescent

/-!
# Smoothness is local on the source for the smooth topology

A morphism of schemes is smooth if and only if its composites with the members of a smooth
covering of its source are smooth.

This is the smooth case of Tag 036H applied to smoothness itself. Three of its four hypotheses
are formal: smoothness is Zariski local on the source and on the target through Mathlib's
`AlgebraicGeometry.HasRingHomProperty` machinery for `RingHom.Smooth`, and it is preserved by
precomposition with a smooth morphism because smooth morphisms compose. The remaining
hypothesis, descent along a surjective smooth morphism of affine schemes, is the smooth case of
Tag 02KM.

## Main results

* `AlgebraicGeometry.smooth_isLocalAtSource`: **Stacks 036U**.

## Implementation notes

Mathlib's Zariski locality instances for `AlgebraicGeometry.Smooth` are supplied by name rather
than by synthesis, because the ring-homomorphism property they are indexed by is not an output
parameter and so cannot be inferred from `AlgebraicGeometry.Smooth` alone.

Smooth coverings of the source are the families of the precoverage
`AlgebraicGeometry.Scheme.precoverage` of `AlgebraicGeometry.Smooth`, which are exactly the
jointly surjective families of smooth morphisms.

## References

* [Stacks Project, Tag 02KM](https://stacks.math.columbia.edu/tag/02KM)
* [Stacks Project, Tag 036H](https://stacks.math.columbia.edu/tag/036H)
* [Stacks Project, Tag 036U](https://stacks.math.columbia.edu/tag/036U)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 036U.** Being a smooth morphism of schemes is local on the source for
the smooth topology. -/
@[stacks 036U]
instance smooth_isLocalAtSource :
    MorphismProperty.IsLocalAtSource (@Smooth.{u}) (Scheme.precoverage (@Smooth.{u})) := by
  have : IsZariskiLocalAtSource (@Smooth.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Smooth)
  have : IsZariskiLocalAtTarget (@Smooth.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Smooth.{u}) (Q := RingHom.Smooth)
  have : MorphismProperty.RespectsLeft (@Smooth.{u}) (@Smooth.{u}) :=
    ⟨fun g hg f hf ↦ by
      have : Smooth g := hg
      have : Smooth f := hf
      exact inferInstance⟩
  refine isLocalAtSource_smooth_of_affine_descent _ fun g f hg hgs hcomp ↦ ?_
  have : Surjective g := hg
  have : Smooth g := hgs
  have : Smooth (g ≫ f) := hcomp
  exact Stacks.Smooth.smooth_of_comp_surjective_smooth g f

end AlgebraicGeometry

end
