module

public import StacksFrontier.AlgebraicGeometry.DenominatorIdealResidue.Basic

/-!
# The canonical map `L ⟶ K_X(L)` is `x ↦ 1 ⊗ x` followed by sheafification

`Stacks.DenominatorIdeal.toK` is the unit of
`Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction`, and that adjunction is
assembled from `Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsAdjunction`, the **data** form
  of Tag 03CU.  Its unit is
therefore the explicit morphism `Stacks.DenominatorIdealResidue.toKExplicit` — the map
`x ↦ 1 ⊗ x` followed by sheafification, whose value on sections is
  `Stacks.PresheafOfModules.ChangeOfRings.unitApp_apply` —
and the two are equal by `rfl`.

That equation is the whole content of this file, and it is what makes the denominator rule of
Stacks Tag 02P0 usable: a clause of the form `∃ t, f = toK t` is now a clause about a map whose
value on sections is known.

## Main results

* `Stacks.DenominatorIdealUnit.toK_eq_toKExplicit`: the canonical map is the explicit one,
  by `rfl`.
* `Stacks.DenominatorIdealUnit.toK_val_app_apply`: hence so is its value on sections.
* `Stacks.DenominatorIdealUnit.exists_toK_app_eq_iff`: the image of the canonical map on the
  sections over an open set, expressed through `toKExplicit`.
* `Stacks.DenominatorIdealUnit.denominatorIdeal_sections_explicit`: the denominator rule of
  Stacks Tag 02P0 with the canonical map replaced by the explicit one.

## Implementation notes

An adjunction between a fixed pair of functors is not unique as data, so
`Nonempty (changeOfRings θ ⊣ restrictScalars θ)` records nothing about *which* adjunction was
produced and a consumer obtaining one by `Classical.choice` cannot compute with its unit.  While
`extendRestrictScalarsAdjunction` was assembled from that `Nonempty` form, `toK` was opaque: no
unfolding, rewriting or simplification produced a formula for it on sections.  The repair was to
pass `Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsAdjunction θ` instead, which is an
  adjunction between the *same two
functors*; the `rfl` below is the measurement that nothing else stood in the way.

Before that repair this file carried a comparison device — a second assembly of the same
adjunction from the data form, together with the automorphism of `K_X(L)` that
`CategoryTheory.Adjunction.leftAdjointUniq` produces between the two left adjoints, and a
transport of every statement along it.  With the two assemblies now literally the same term, the
comparison automorphism is the identity and the transport layer is gone.

## References

* [Stacks Project, Tag 02P0](https://stacks.math.columbia.edu/tag/02P0)
* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.DenominatorIdeal Stacks.DenominatorIdealResidue

universe u

namespace Stacks.DenominatorIdealUnit

variable (X : Scheme.{u}) (L : SheafOfModules.{u} (O X))

/-- **The canonical morphism `L ⟶ K_X(L)` is `x ↦ 1 ⊗ x` followed by sheafification.**

Both sides are the unit of the change-of-rings adjunction along `𝒪_X ⟶ K_X`: the left-hand side
reads it off `Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction`, the right-hand
side writes it out as `Stacks.PresheafOfModules.ChangeOfRings.unitHom`.  Since that adjunction is
  assembled from the data form
of Tag 03CU, the two are the same term. -/
theorem toK_eq_toKExplicit : toK X L = toKExplicit X L := rfl

/-- The value of the canonical morphism `L ⟶ K_X(L)` on the sections over an open set is the
value of the explicit morphism. -/
theorem toK_val_app_apply (U : (Opens X)ᵒᵖ) (t : L.val.obj U) :
    (toK X L).val.app U t = (toKExplicit X L).val.app U t := rfl

/-- **The image of the canonical map on sections, through the explicit map.**  A section of
`K_X(L)` over `U` comes from a section of `L` under the canonical map exactly when it comes from
one under `x ↦ 1 ⊗ x` followed by sheafification. -/
theorem exists_toK_app_eq_iff (U : (Opens X)ᵒᵖ) (y : (kAsOModule X L).val.obj U) :
    (∃ t : L.val.obj U, (toK X L).val.app U t = y) ↔
      (∃ t : L.val.obj U, (toKExplicit X L).val.app U t = y) :=
  Iff.rfl

variable (s : MeromorphicSection.{u, u} X.sheaf L)

/-- **The denominator rule of Stacks Tag 02P0 through the explicit map.**  A section `f` of
`𝒪_X` over `U` is a denominator of the meromorphic section `s` exactly when `f · s` is
`1 ⊗ t`, sheafified, for a section `t` of `L` over `U`. -/
theorem denominatorIdeal_sections_explicit (U : Opens X)
    (f : (SheafOfModules.unit (O X)).val.obj (op U)) :
    (∃ d : (denominatorIdeal X L s).val.obj (op U),
      (denominatorIdealι X L s).val.app (op U) d = f) ↔
    (∃ t : L.val.obj (op U), (sectionMap X L s).val.app (op U) f =
      (toKExplicit X L).val.app (op U) t) :=
  denominatorIdeal_sections X L s U f

end Stacks.DenominatorIdealUnit

end
