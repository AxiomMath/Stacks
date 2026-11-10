module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkEquivalence.FieldFiber
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FppfLocalTarget

/-!
# Cohen–Macaulay schemes over a field

Over a base whose residue field inclusions are isomorphisms — the spectrum of a field being the
case of interest — the scheme-theoretic fibres of a morphism are the source of the morphism
itself. Consequently such a scheme is Cohen–Macaulay exactly when every fibre of its structure
morphism is.

## Main results

* `AlgebraicGeometry.isIso_fiberι_of_isIso_fromSpecResidueField`: the inclusion of a fibre is
  an isomorphism when the residue field inclusion at the point is.
* `AlgebraicGeometry.isCohenMacaulay_iff_forall_fiber_of_isIso_fromSpecResidueField` and
  `AlgebraicGeometry.isCohenMacaulay_iff_forall_fiber_of_field`: a scheme over such a base,
  in particular over a field, is Cohen–Macaulay exactly when all fibres of its structure
  morphism are.

## References

* [Stacks Project, Tag 02IO](https://stacks.math.columbia.edu/tag/02IO)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The inclusion of the scheme-theoretic fibre of a morphism at a point of its target is an
isomorphism when the inclusion of the residue field at that point is. -/
theorem isIso_fiberι_of_isIso_fromSpecResidueField {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y)
    (hy : IsIso (Y.fromSpecResidueField y)) : IsIso (f.fiberι y) := by
  have := hy
  change IsIso (pullback.fst f (Y.fromSpecResidueField y))
  infer_instance

/-- A scheme carrying a morphism to a nonempty base all of whose residue field inclusions are
isomorphisms is Cohen–Macaulay exactly when every scheme-theoretic fibre of that morphism is
Cohen–Macaulay. -/
theorem isCohenMacaulay_iff_forall_fiber_of_isIso_fromSpecResidueField {X Y : Scheme.{u}}
    (f : X ⟶ Y) (hne : Nonempty Y)
    (hres : ∀ y : Y, IsIso (Y.fromSpecResidueField y)) :
    (∀ y : Y, IsCohenMacaulay (f.fiber y)) ↔ IsCohenMacaulay X := by
  have (y : Y) := isIso_fiberι_of_isIso_fromSpecResidueField f y (hres y)
  exact ⟨fun h ↦ hne.elim fun y ↦ (isCohenMacaulay_iff_of_iso (asIso (f.fiberι y))).mp (h y),
    fun hX y ↦ (isCohenMacaulay_iff_of_iso (asIso (f.fiberι y))).mpr hX⟩

/-- A scheme over a field is Cohen–Macaulay exactly when every scheme-theoretic fibre of its
structure morphism is Cohen–Macaulay. -/
theorem isCohenMacaulay_iff_forall_fiber_of_field (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) :
    (∀ y : Spec (.of k), IsCohenMacaulay (f.fiber y)) ↔ IsCohenMacaulay X :=
  isCohenMacaulay_iff_forall_fiber_of_isIso_fromSpecResidueField f inferInstance
    (isIso_fromSpecResidueField_of_field k)

end AlgebraicGeometry

end
