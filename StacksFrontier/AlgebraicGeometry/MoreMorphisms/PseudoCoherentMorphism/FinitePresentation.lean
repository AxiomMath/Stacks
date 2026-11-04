module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Morphisms.PseudoCoherent
public import StacksFrontier.RingTheory.PseudoCoherentMap.Flat

/-!
# Pseudo-coherence and local finite presentation

A flat morphism of schemes locally of finite presentation is pseudo-coherent. Conversely, a
pseudo-coherent morphism is locally of finite presentation, with no flatness assumed: that is
Stacks 0682, the instance `AlgebraicGeometry.locallyOfFinitePresentation_of_pseudoCoherent` of
`StacksFrontier/AlgebraicGeometry/Morphisms/PseudoCoherent.lean`.

## Main results

* `AlgebraicGeometry.pseudoCoherent_of_flat_of_locallyOfFinitePresentation`: **Stacks 0695**, a
  flat morphism of schemes locally of finite presentation is pseudo-coherent.

## Implementation notes

The statement is the affine-local shadow of a statement about ring maps, so it is proved by
`AlgebraicGeometry.HasRingHomProperty.iff_appLE` from the corresponding property of
`RingHom.PseudoCoherent`; the instance `AlgebraicGeometry.hasRingHomProperty_pseudoCoherent`
identifies `AlgebraicGeometry.PseudoCoherent` with that property of ring maps.

For Stacks 0695 the ring-level input is Stacks 067J, already available as
`RingHom.isPerfectRingMap_of_flat_of_finitePresentation`: a flat ring map of finite presentation
is perfect. The instance uses its pseudo-coherence half,
`RingHom.PseudoCoherent.of_flat_of_finitePresentation` (`RingTheory/PseudoCoherentMap/Flat.lean`).

The conclusion is registered as an instance, so that typeclass inference can chain it with the
other morphism properties.

## References

* [The Stacks Project, Lemma 37.60.5 (0682)](https://stacks.math.columbia.edu/tag/0682)
* [The Stacks Project, Lemma 37.60.6 (0695)](https://stacks.math.columbia.edu/tag/0695)
* [The Stacks Project, Lemma 15.83.5 (067J)](https://stacks.math.columbia.edu/tag/067J)
-/

@[expose] public noncomputable section

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- **Stacks 0695.** A flat morphism of schemes which is locally of finite presentation is
pseudo-coherent.

On every compatible pair of affine opens the map on sections is flat and of finite presentation,
hence pseudo-coherent by `RingHom.PseudoCoherent.of_flat_of_finitePresentation`, the
pseudo-coherence half of Stacks 067J. -/
@[stacks 0695]
instance pseudoCoherent_of_flat_of_locallyOfFinitePresentation {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f] : PseudoCoherent f := by
  rw [HasRingHomProperty.iff_appLE (P := @PseudoCoherent)]
  exact fun V U e ↦ RingHom.PseudoCoherent.of_flat_of_finitePresentation
    (HasRingHomProperty.appLE @Flat f ‹_› V U e)
    (HasRingHomProperty.appLE @LocallyOfFinitePresentation f ‹_› V U e)

end AlgebraicGeometry

end
