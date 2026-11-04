module

public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinMorphisms.Locality
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.OverAField

/-!
# Gorenstein schemes over a field

Over a base whose residue field inclusions are isomorphisms — the spectrum of a field being the
case of interest — the scheme-theoretic fibres of a morphism are the source of the morphism
itself. Consequently such a scheme is Gorenstein exactly when every fibre of its structure
morphism is, and a flat morphism to the spectrum of a field with locally Noetherian fibres is a
Gorenstein morphism exactly when its source is a Gorenstein scheme.

## Main results

* `AlgebraicGeometry.isGorenstein_iff_forall_fiber_of_isIso_fromSpecResidueField` and
  `AlgebraicGeometry.isGorenstein_iff_forall_fiber_of_field`: a scheme over such a base, in
  particular over a field, is Gorenstein exactly when all fibres of its structure morphism are.
* `AlgebraicGeometry.Scheme.Hom.isGorenstein_iff_isGorenstein_of_field`: a flat morphism to the
  spectrum of a field is Gorenstein exactly when its source is a Gorenstein scheme.

## Implementation notes

The fibre inclusion is an isomorphism by
`AlgebraicGeometry.isIso_fiberι_of_isIso_fromSpecResidueField`, Gorensteinness of schemes is
invariant under isomorphism (`AlgebraicGeometry.isGorenstein_iff_of_iso`), and a flat morphism
is Gorenstein exactly when its fibres are Gorenstein schemes by Tag 0C05
(`AlgebraicGeometry.Scheme.Hom.isGorenstein_iff_flat_and_isGorenstein_fiber`).

## References

* [Stacks Project, Tag 0C05](https://stacks.math.columbia.edu/tag/0C05)
* [Stacks Project, Tag 0C04](https://stacks.math.columbia.edu/tag/0C04)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A scheme carrying a morphism to a nonempty base all of whose residue field inclusions are
isomorphisms is Gorenstein exactly when every scheme-theoretic fibre of that morphism is
Gorenstein: every fibre is isomorphic to the scheme itself. -/
theorem isGorenstein_iff_forall_fiber_of_isIso_fromSpecResidueField {X Y : Scheme.{u}}
    (f : X ⟶ Y) (hne : Nonempty Y)
    (hres : ∀ y : Y, IsIso (Y.fromSpecResidueField y)) :
    (∀ y : Y, IsGorenstein (f.fiber y)) ↔ IsGorenstein X := by
  have key (y : Y) : IsGorenstein (f.fiber y) ↔ IsGorenstein X := by
    have := isIso_fiberι_of_isIso_fromSpecResidueField f y (hres y)
    exact isGorenstein_iff_of_iso (asIso (f.fiberι y))
  exact (forall_congr' key).trans (forall_const Y)

/-- A scheme over a field is Gorenstein exactly when every scheme-theoretic fibre of its
structure morphism is Gorenstein; the base being a one-point scheme, that fibre is the scheme
itself. -/
theorem isGorenstein_iff_forall_fiber_of_field (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) :
    (∀ y : Spec (.of k), IsGorenstein (f.fiber y)) ↔ IsGorenstein X :=
  isGorenstein_iff_forall_fiber_of_isIso_fromSpecResidueField f inferInstance
    (isIso_fromSpecResidueField_of_field k)

/-- **A morphism to the spectrum of a field is Gorenstein exactly when its source is.** A flat
morphism with locally Noetherian fibres to the spectrum of a field is a Gorenstein morphism in
the sense of Tag 0C04 exactly when its source is a Gorenstein scheme: by Tag 0C05 it is
Gorenstein exactly when its fibres are, and its only fibre is the source. -/
theorem Scheme.Hom.isGorenstein_iff_isGorenstein_of_field (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Flat f]
    (hf : ∀ y : Spec (.of k), IsLocallyNoetherian (f.fiber y)) :
    f.IsGorenstein hf ↔ _root_.AlgebraicGeometry.IsGorenstein X := by
  rw [Scheme.Hom.isGorenstein_iff_flat_and_isGorenstein_fiber f hf,
    ← isGorenstein_iff_forall_fiber_of_field k f]
  exact and_iff_right inferInstance

end AlgebraicGeometry

end
