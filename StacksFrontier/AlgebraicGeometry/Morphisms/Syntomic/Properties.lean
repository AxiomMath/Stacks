module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.RingHomProperty
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Syntomic morphisms are flat, locally of finite presentation, and universally open

A syntomic morphism of schemes is locally of finite presentation and flat, and therefore
universally open.

## Main results

* `AlgebraicGeometry.locallyOfFinitePresentation`: every syntomic morphism is locally of finite
  presentation.
* `AlgebraicGeometry.flat`: every syntomic morphism is flat.
* `AlgebraicGeometry.universallyOpen_of_syntomic`: every syntomic morphism is universally open.

## Implementation notes

Local finite presentation and flatness are Mathlib's morphism properties
`AlgebraicGeometry.LocallyOfFinitePresentation` and `AlgebraicGeometry.Flat`. Both are checked
on the affine neighbourhoods witnessing syntomicity at a point, using that a syntomic algebra is
of finite presentation and flat. Universal openness then follows from Mathlib's
`UniversallyOpen.of_flat`.

## References

* [Stacks Project, Tag 01UK](https://stacks.math.columbia.edu/tag/01UK)
* [Stacks Project, Tag 01UL](https://stacks.math.columbia.edu/tag/01UL)
* [Stacks Project, Tag 056F](https://stacks.math.columbia.edu/tag/056F)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A syntomic morphism of schemes is locally of finite presentation. -/
@[stacks 01UK]
lemma locallyOfFinitePresentation {X S : Scheme.{u}} {f : X ⟶ S}
    (hf : Syntomic f) : LocallyOfFinitePresentation f := by
  apply (HasRingHomProperty.iff_exists_appLE (P := @LocallyOfFinitePresentation)
    (Q := RingHom.FinitePresentation)
    (RingHom.finitePresentation_stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.finitePresentation_holdsForLocalizationAway).left).2
  intro x
  obtain ⟨U, hx, V, hUV, hsyn⟩ := (syntomicAt_iff f x).mp (hf x)
  refine ⟨V, U, hx, hUV, ?_⟩
  let := (f.appLE V.1 U.1 hUV).hom.toAlgebra
  exact Algebra.Syntomic.finitePresentation

/-- A syntomic morphism of schemes is flat. -/
@[stacks 01UL]
lemma flat {X S : Scheme.{u}} {f : X ⟶ S} (hf : Syntomic f) : Flat f := by
  apply (HasRingHomProperty.iff_exists_appLE (P := @Flat) (Q := RingHom.Flat)
    (RingHom.Flat.stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.Flat.holdsForLocalizationAway).left).2
  intro x
  obtain ⟨U, hx, V, hUV, hsyn⟩ := (syntomicAt_iff f x).mp (hf x)
  refine ⟨V, U, hx, hUV, ?_⟩
  let := (f.appLE V.1 U.1 hUV).hom.toAlgebra
  exact hsyn.flat

/-- A syntomic morphism of schemes is universally open. -/
@[stacks 056F]
theorem universallyOpen_of_syntomic {X S : Scheme.{u}} {f : X ⟶ S}
    (hf : Syntomic f) : UniversallyOpen f :=
  @UniversallyOpen.of_flat _ _ f (flat hf) (locallyOfFinitePresentation hf)

end AlgebraicGeometry
