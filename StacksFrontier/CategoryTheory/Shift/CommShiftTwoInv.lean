module

public import Mathlib.CategoryTheory.Shift.CommShiftTwo
import StacksCore.Tactic.StacksAttribute

/-!
# The inverse of a two-variable shift-compatible isomorphism of bifunctors

Let `e : G ≅ G'` be an isomorphism of bifunctors `C₁ ⥤ C₂ ⥤ D`, both commuting with the shifts in
both variables, and suppose `e.hom` is compatible with those shifts.  This file records that
`e.inv` is too.  It is the two-variable analogue of Mathlib's
`CategoryTheory.NatTrans.CommShift.of_iso_inv`.

## Main results

* `CategoryTheory.NatTrans.CommShift₂.of_iso_inv`: **the inverse of a shift-compatible
  isomorphism of bifunctors is shift-compatible**, and `of_iso_invInt` at the standard `ℤ` setup.

## Implementation notes

`CategoryTheory.NatTrans.CommShift₂` has two fields, each a one-variable
`CategoryTheory.NatTrans.CommShift` — at the components of the transformation in the second
variable and at the components of its flip in the first — so there is nothing to do beyond
observing that the component of `e.inv` at `X₁` is the inverse of the component of `e` at `X₁`
and appealing to Mathlib's one-variable lemma twice.

It is worth a declaration nonetheless.  Every `CategoryTheory.Functor.CommShift₂` datum in this
development that is obtained by *transport* — the example is
`Stacks.SheafOfModules.DerivedMonoidal.canonicalTensor_commShift₂Int`, a second description of the
shift datum of the derived tensor product of [Stacks, Tag 06YU] — makes its transport
isomorphism shift-compatible by construction, and a consumer that needs to move a statement in
the other direction along that isomorphism needs exactly this.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public section

namespace CategoryTheory

open Category _root_.CategoryTheory.Functor

namespace NatTrans.CommShift₂

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]
  {M : Type*} [AddCommMonoid M] [HasShift C₁ M] [HasShift C₂ M] [HasShift D M]
  {G G' : C₁ ⥤ C₂ ⥤ D} (e : G ≅ G') (h : CommShift₂Setup D M)
  [G.CommShift₂ h] [G'.CommShift₂ h]

/-- **The inverse of a shift-compatible isomorphism of bifunctors is shift-compatible.** -/
instance of_iso_inv [NatTrans.CommShift₂ e.hom h] : NatTrans.CommShift₂ e.inv h where
  commShift_app X₁ := by
    have : NatTrans.CommShift (e.app X₁).hom M :=
      NatTrans.CommShift₂.commShift_app (τ := e.hom) (h := h) X₁
    exact NatTrans.CommShift.of_iso_inv (e.app X₁) M
  commShift_flipApp X₂ := by
    -- the flipped isomorphism, ascribed at the `G.flip` spelling the instances are stored at:
    -- `(flipFunctor C₁ C₂ D).obj G` is definitionally `G.flip` but instance search does not
    -- unfold it, and `commShiftFlipObj` is registered for the latter
    let ef : G.flip ≅ G'.flip := (flipFunctor C₁ C₂ D).mapIso e
    have : NatTrans.CommShift (ef.app X₂).hom M :=
      NatTrans.CommShift₂.commShift_flipApp (τ := e.hom) (h := h) X₂
    exact NatTrans.CommShift.of_iso_inv (ef.app X₂) M

/-- `CategoryTheory.NatTrans.CommShift₂.of_iso_inv` at the standard `ℤ` setup
`CategoryTheory.CommShift₂Setup.int`, with Mathlib's sign `(-1) ^ (p * q)`. -/
theorem of_iso_invInt {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]
    [Preadditive D] [HasShift C₁ ℤ] [HasShift C₂ ℤ] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] {G G' : C₁ ⥤ C₂ ⥤ D}
    [G.CommShift₂Int] [G'.CommShift₂Int] (e : G ≅ G') [NatTrans.CommShift₂Int e.hom] :
    NatTrans.CommShift₂Int e.inv :=
  of_iso_inv e CommShift₂Setup.int

end NatTrans.CommShift₂

end CategoryTheory

end
