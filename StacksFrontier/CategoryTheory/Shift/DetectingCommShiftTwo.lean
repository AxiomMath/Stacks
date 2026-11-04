module

public import StacksFrontier.CategoryTheory.Shift.DetectingCommShift
public import Mathlib.CategoryTheory.Shift.CommShiftTwo

/-!
# Detecting the commutation of a transformation of bifunctors with the shifts

`CategoryTheory.NatTrans.CommShift₂ τ h` is two conditions, one per variable, each a
one-variable `CategoryTheory.NatTrans.CommShift` of a component of `τ`: `commShift_app X₁` for
the transformation in the second variable at a fixed `X₁`, and `commShift_flipApp X₂` for the
transformation in the first variable at a fixed `X₂`.  This file reduces both to the
corresponding conditions after restriction along essentially surjective functors which commute
with the shifts — the two-variable form of
`CategoryTheory.NatTrans.commShift_of_whiskerLeft`.

The *fixed* variable is reduced along with the varying one:
`CategoryTheory.NatTrans.CommShift₂.of_essSurj` asks for the condition only at objects of the
form `q₁.obj K₁` and `q₂.obj K₂`.  That is what makes it usable for a transformation on a
category of models whose components are only recognisable as a composite of whiskerings once
*both* arguments have been replaced by chosen representatives.

## Main results

* `CategoryTheory.NatTrans.commShift_app_of_iso` and `commShift_flipApp_of_iso`: the condition
  in one variable depends on the fixed object of the other only up to isomorphism.  The two
  isomorphisms needed by `CategoryTheory.NatTrans.commShift_of_eq_conj` are the images of the
  comparison isomorphism under the two bifunctors, and those are shift-compatible by the
  `commShift_map` and `commShift_flip_map` fields of
  `CategoryTheory.Functor.CommShift₂`.
* `CategoryTheory.NatTrans.CommShift₂.of_whiskerLeft`: both conditions may be tested after
  restriction along essentially surjective shift-compatible functors.
* `CategoryTheory.NatTrans.CommShift₂.of_essSurj`: **the same with the fixed variable also
  restricted to the image**, which is the usable form.

## Implementation notes

`CategoryTheory.NatTrans.flipApp` is an `abbrev` ascribed at the `G.flip` spelling while the
naturality of `τ` in the second variable is stated for `(flipFunctor _ _ _).map τ`.  The two
are definitionally equal but `rw` does not cross between them, so the `show … from rfl` casts
in `commShift_flipApp_of_iso` are not removable; this is the same mismatch recorded in
`StacksFrontier/CategoryTheory/Shift/CommShiftTwoInv.lean`.
-/

@[expose] public section

namespace CategoryTheory.NatTrans

open Category CategoryTheory.Functor

universe v₁ v₂ v w₁ w₂ u₁ u₂ u t₁ t₂

variable {C₁ : Type u₁} {C₂ : Type u₂} {D : Type u}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v} D]
  {M : Type*} [AddCommMonoid M] [HasShift C₁ M] [HasShift C₂ M] [HasShift D M]
  {G₁ G₂ : C₁ ⥤ C₂ ⥤ D} (τ : G₁ ⟶ G₂) (h : CommShift₂Setup D M)
  [G₁.CommShift₂ h] [G₂.CommShift₂ h]

/-- **The condition in the second variable only depends on the fixed object of the first
variable up to isomorphism.**  By naturality `τ.app X₁` is the conjugate of `τ.app Y₁` by the
images of `e` under the two bifunctors, and those are shift-compatible because a
`CategoryTheory.Functor.CommShift₂` structure makes every `G.map f` shift-compatible. -/
theorem commShift_app_of_iso {X₁ Y₁ : C₁} (e : X₁ ≅ Y₁)
    (hτ : NatTrans.CommShift (τ.app Y₁) M) : NatTrans.CommShift (τ.app X₁) M := by
  have := hτ
  have : NatTrans.CommShift (G₁.mapIso e).hom M :=
    Functor.CommShift₂.commShift_map (G := G₁) (h := h) e.hom
  have : NatTrans.CommShift (G₂.mapIso e).hom M :=
    Functor.CommShift₂.commShift_map (G := G₂) (h := h) e.hom
  refine commShift_of_eq_conj (G₁.mapIso e) (G₂.mapIso e) (τ.app Y₁) ?_
  exact (NatTrans.naturality_2 τ e).symm

/-- **The condition in the first variable only depends on the fixed object of the second
variable up to isomorphism**, the mirror of `commShift_app_of_iso` through
`CategoryTheory.Functor.flip`. -/
theorem commShift_flipApp_of_iso {X₂ Y₂ : C₂} (e : X₂ ≅ Y₂)
    (hτ : NatTrans.CommShift (τ.flipApp Y₂) M) : NatTrans.CommShift (τ.flipApp X₂) M := by
  have := hτ
  have : NatTrans.CommShift (G₁.flip.mapIso e).hom M :=
    Functor.CommShift₂.commShift_flip_map (G := G₁) (h := h) e.hom
  have : NatTrans.CommShift (G₂.flip.mapIso e).hom M :=
    Functor.CommShift₂.commShift_flip_map (G := G₂) (h := h) e.hom
  refine commShift_of_eq_conj (G₁.flip.mapIso e) (G₂.flip.mapIso e) (τ.flipApp Y₂) ?_
  exact (NatTrans.naturality_2 ((flipFunctor C₁ C₂ D).map τ) e).symm

namespace CommShift₂

variable {V₁ : Type t₁} {V₂ : Type t₂} [Category.{w₁} V₁] [Category.{w₂} V₂]
  [HasShift V₁ M] [HasShift V₂ M]

/-- **Both halves of `CategoryTheory.NatTrans.CommShift₂` may be tested after restriction
along essentially surjective functors which commute with the shifts.**  Each half is one
application of `CategoryTheory.NatTrans.commShift_of_whiskerLeft`, in the variable that
varies. -/
theorem of_whiskerLeft (q₁ : V₁ ⥤ C₁) [q₁.EssSurj] [q₁.CommShift M]
    (q₂ : V₂ ⥤ C₂) [q₂.EssSurj] [q₂.CommShift M]
    (h₁ : ∀ X₁ : C₁, NatTrans.CommShift (Functor.whiskerLeft q₂ (τ.app X₁)) M)
    (h₂ : ∀ X₂ : C₂, NatTrans.CommShift (Functor.whiskerLeft q₁ (τ.flipApp X₂)) M) :
    NatTrans.CommShift₂ τ h where
  commShift_app X₁ := commShift_of_whiskerLeft q₂ _ (h₁ X₁)
  commShift_flipApp X₂ := commShift_of_whiskerLeft q₁ _ (h₂ X₂)

/-- **`CategoryTheory.NatTrans.CommShift₂` from the two conditions at objects in the image of
two essentially surjective shift-compatible functors.**  Both variables are restricted at
once: the varying one by `CategoryTheory.NatTrans.commShift_of_whiskerLeft` and the fixed one
by `commShift_app_of_iso`, whose comparison isomorphism is
`CategoryTheory.Functor.objObjPreimageIso`. -/
theorem of_essSurj (q₁ : V₁ ⥤ C₁) [q₁.EssSurj] [q₁.CommShift M]
    (q₂ : V₂ ⥤ C₂) [q₂.EssSurj] [q₂.CommShift M]
    (h₁ : ∀ K₁ : V₁, NatTrans.CommShift (Functor.whiskerLeft q₂ (τ.app (q₁.obj K₁))) M)
    (h₂ : ∀ K₂ : V₂, NatTrans.CommShift (Functor.whiskerLeft q₁ (τ.flipApp (q₂.obj K₂))) M) :
    NatTrans.CommShift₂ τ h where
  commShift_app X₁ :=
    commShift_app_of_iso τ h (q₁.objObjPreimageIso X₁).symm
      (commShift_of_whiskerLeft q₂ _ (h₁ (q₁.objPreimage X₁)))
  commShift_flipApp X₂ :=
    commShift_flipApp_of_iso τ h (q₂.objObjPreimageIso X₂).symm
      (commShift_of_whiskerLeft q₁ _ (h₂ (q₂.objPreimage X₂)))

end CommShift₂

end CategoryTheory.NatTrans

end
