module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective

/-!
# Universally injective and radicial morphisms

This file records the two notions of [Stacks Project, Tag 01S3] for a morphism of schemes
`f : X ⟶ S`:

1. `f` is *universally injective* if for every morphism `S' ⟶ S` the base change
   `X ×_S S' ⟶ S'` is injective on underlying topological spaces;
2. `f` is *radicial* if it is injective on underlying topological spaces and every residue field
   extension `κ(x)/κ(f x)` is purely inseparable.

Mathlib defines (1) as `AlgebraicGeometry.UniversallyInjective`, through
`CategoryTheory.MorphismProperty.universally`, which quantifies over all pullback squares rather
than over the chosen pullbacks. Mathlib does not name (2): its condition appears only as one of
the equivalent conditions of `AlgebraicGeometry.tfae_universallyInjective` (Tag 01S4).

## Main definitions and results

* `AlgebraicGeometry.universallyInjective_iff_forall_injective_pullback_fst`: Mathlib's
  `UniversallyInjective` is the source's condition (1), stated with the chosen pullbacks.
* `AlgebraicGeometry.IsRadicial`: the source's condition (2).
* `AlgebraicGeometry.isRadicial_iff_universallyInjective`: the two notions agree; this is part
  of Tag 01S4, read off from `AlgebraicGeometry.tfae_universallyInjective`.

## References

* [Stacks Project, Tag 01S3](https://stacks.math.columbia.edu/tag/01S3)
* [Stacks Project, Tag 01S4](https://stacks.math.columbia.edu/tag/01S4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Mathlib's `AlgebraicGeometry.UniversallyInjective` is the definition of the source: `f` is
universally injective if and only if for every morphism `g : S' ⟶ S` the base change
`S' ×_S X ⟶ S'` (the first projection of the chosen pullback) is injective on points. -/
@[stacks 01S3 "(1) universally injective: every base change `S' ×_S X ⟶ S'` is injective on
points; the definition is Mathlib's `AlgebraicGeometry.UniversallyInjective`, and this states it
in the source's form"]
theorem universallyInjective_iff_forall_injective_pullback_fst :
    UniversallyInjective f ↔
      ∀ (S' : Scheme.{u}) (g : S' ⟶ S), Function.Injective (pullback.fst g f) := by
  rw [universallyInjective_iff]
  refine ⟨fun h S' g ↦ h _ _ _ (IsPullback.of_hasPullback g f), fun h ↦ ?_⟩
  exact MorphismProperty.universally_mk' _ f fun g _ ↦ h _ g

/-- A morphism of schemes `f : X ⟶ S` is *radicial* if it is injective on underlying
topological spaces and, for every point `x` of `X`, the residue field extension
`κ(x)/κ(f x)` given by `f.residueFieldMap x` is purely inseparable. -/
@[stacks 01S3 "(2) radicial: injective on points, with every residue field extension
`κ(x)/κ(f x)` purely inseparable"]
class IsRadicial : Prop where
  /-- A radicial morphism is injective on underlying topological spaces. -/
  injective : Function.Injective f
  /-- The residue field extensions of a radicial morphism are purely inseparable. -/
  isPurelyInseparable_residueFieldMap : ∀ x, (f.residueFieldMap x).hom.IsPurelyInseparable

/-- A morphism of schemes is radicial if and only if it is universally injective (part of
[Stacks Project, Tag 01S4], read off from `AlgebraicGeometry.tfae_universallyInjective`). -/
theorem isRadicial_iff_universallyInjective : IsRadicial f ↔ UniversallyInjective f := by
  have h := (tfae_universallyInjective f).out 1 3
  exact ⟨fun hf ↦ h.mpr ⟨hf.1, hf.2⟩, fun hf ↦ ⟨(h.mp hf).1, (h.mp hf).2⟩⟩

end AlgebraicGeometry
