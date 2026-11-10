module

public import StacksFrontier.CategoryTheory.Shift.CommShiftTwoPostcomp

/-!
# Whiskering a transformation of bifunctors preserves compatibility with the shifts

`CategoryTheory.NatTrans.CommShift₂ τ h` is the compatibility with the shifts in both variables of
a transformation `τ : G₁ ⟶ G₂` of bifunctors.  Mathlib has the two closure properties under
*composition* (`CategoryTheory.NatTrans.CommShift₂.id` and the instance for `τ ≫ τ'`) and nothing
else; in particular none of the four whiskerings is covered, although the one-variable
counterparts — `CategoryTheory.NatTrans.CommShift.whiskerLeft` and `whiskerRight` — are.

This file supplies six.  Two precompose a bifunctor with a *transformation* of one-variable
functors, one in each variable; two precompose with a one-variable *functor*, again one in each
variable; two postcompose, one with a transformation of the target functors and one with a fixed
target functor.  Each is immediate from the one-variable statement in the variable that varies
together with a field of `CategoryTheory.Functor.CommShift₂` — `commShift_map` or
`commShift_flip_map` — in the one that is fixed, which is exactly why `Functor.CommShift₂` carries
those two fields.

## Main results

* `CategoryTheory.NatTrans.CommShift₂.whiskerRight_bifunctor`: precomposition in the first
  variable by `α : F ⟶ F'`, i.e. `CategoryTheory.Functor.whiskerRight α G`.
* `CategoryTheory.NatTrans.CommShift₂.whiskerLeft_bifunctor`: precomposition in the second
  variable by `β : F ⟶ F'`, i.e.
  `Functor.whiskerLeft G ((CategoryTheory.Functor.whiskeringLeft _ _ _).map β)`.
* `CategoryTheory.NatTrans.CommShift₂.whiskerLeft_precomp₁` and `whiskerRight_precomp₂`:
  restriction of a transformation of bifunctors along a shift-compatible functor, in the first and
  in the second variable.  Their composite is what `CategoryTheory.Functor.whiskeringLeft₂`
  applied to a transformation unfolds to, and its two fields are verbatim the two hypotheses of
  `CategoryTheory.NatTrans.CommShift₂.of_essSurj` — so this is how a shift compatibility proved on
  a category of models is read off as the pair of conditions that reduction consumes.
* `CategoryTheory.NatTrans.CommShift₂.whiskerRight_functorInt`: postcomposition of a
  transformation of bifunctors with a fixed additive shift-compatible `H : D ⥤ D'`, i.e.
  `Functor.whiskerRight τ ((Functor.whiskeringRight _ _ _).obj H)`.
* `CategoryTheory.NatTrans.CommShift₂.whiskerLeft_functorInt`: postcomposition of a bifunctor with
  a transformation `η : H ⟶ H'` of target functors, i.e.
  `Functor.whiskerLeft B ((Functor.whiskeringRight _ _ _).map η)`.

## Implementation notes

**Why the two postcomposition statements are stated only for the `ℤ` setups.**  The
`CategoryTheory.Functor.CommShift₂` structure on a postcomposite is
`CategoryTheory.Functor.CommShift₂.postcomp`, which takes the compatibility of the two setups'
signs as a *hypothesis*; a statement quantified over that hypothesis could not have the structure
found by instance search, and `CategoryTheory.NatTrans.CommShift₂` takes the two bifunctors'
structures as instance arguments.  At the standard `ℤ` setups the hypothesis is discharged by
additivity of `H`, and `CategoryTheory.Functor.CommShift₂.postcompInt` is an instance, so there
the structures *are* found.  That is the only form this development consumes.

**Why each field is an `inferInstanceAs` rather than a rewrite.**  In every case the component of
the whiskered transformation in the varying variable is, on the nose, a whiskering of a
transformation whose compatibility is already an instance: `Functor.whiskerRight α G` evaluated at
`K₁` *is* `G.map (α.app K₁)`, and its flip at `X₂` *is* `Functor.whiskerRight α (G.flip.obj X₂)`.
The `CategoryTheory.Functor.CommShift` data of the source and target match on the nose as well,
because `CategoryTheory.Functor.CommShift₂.precomp₁` and `precomp₂` fill their four fields with
exactly the `CategoryTheory.Functor.CommShift.comp` and `inferInstanceAs` this file's proofs
appeal to.  So no reassociation is needed and no equation of transformations has to be proved.
-/

@[expose] public section

namespace CategoryTheory.NatTrans.CommShift₂

open Category _root_.CategoryTheory.Functor

universe v₁ v₂ v₁' v₂' v v' u₁ u₂ u₁' u₂' u u'

section Precomp

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₁' : Type u₁'} {C₂' : Type u₂'} {D : Type u}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₁'} C₁'] [Category.{v₂'} C₂']
  [Category.{v} D] {M : Type*} [AddCommMonoid M]
  [HasShift C₁ M] [HasShift C₂ M] [HasShift C₁' M] [HasShift C₂' M] [HasShift D M]

/-- **Precomposing a bifunctor in the first variable with a shift-compatible transformation gives
a shift-compatible transformation of bifunctors.**  In the first variable the component is
`G.map (α.app K₁)`, which is the `commShift_map` field of `G`'s structure; in the second it is
`Functor.whiskerRight α (G.flip.obj X₂)`, which is Mathlib's one-variable whiskering. -/
instance whiskerRight_bifunctor (G : C₁ ⥤ C₂ ⥤ D) (h : CommShift₂Setup D M) [G.CommShift₂ h]
    {F F' : C₁' ⥤ C₁} [F.CommShift M] [F'.CommShift M] (α : F ⟶ F')
    [NatTrans.CommShift α M] :
    NatTrans.CommShift₂ (Functor.whiskerRight α G) h where
  commShift_app K₁ := inferInstanceAs (NatTrans.CommShift (G.map (α.app K₁)) M)
  commShift_flipApp X₂ :=
    inferInstanceAs (NatTrans.CommShift (Functor.whiskerRight α (G.flip.obj X₂)) M)

/-- **Precomposing a bifunctor in the second variable with a shift-compatible transformation gives
a shift-compatible transformation of bifunctors.**  In the second variable the component is
`G.flip.map (β.app K₂)`, which is the `commShift_flip_map` field of `G`'s structure; in the first
it is `Functor.whiskerRight β (G.obj X₁)`. -/
instance whiskerLeft_bifunctor (G : C₁ ⥤ C₂ ⥤ D) (h : CommShift₂Setup D M) [G.CommShift₂ h]
    {F F' : C₂' ⥤ C₂} [F.CommShift M] [F'.CommShift M] (β : F ⟶ F')
    [NatTrans.CommShift β M] :
    NatTrans.CommShift₂ (Functor.whiskerLeft G ((Functor.whiskeringLeft C₂' C₂ D).map β)) h where
  commShift_app X₁ :=
    inferInstanceAs (NatTrans.CommShift (Functor.whiskerRight β (G.obj X₁)) M)
  commShift_flipApp K₂ :=
    inferInstanceAs (NatTrans.CommShift (G.flip.map (β.app K₂)) M)

/-- **Restricting a shift-compatible transformation of bifunctors along a shift-compatible functor
in the first variable.**  In the first variable the component is a component of `τ`; in the second
it is `CategoryTheory.Functor.whiskerLeft q₁` of one, which is Mathlib's one-variable whiskering.

Composed with `whiskerRight_precomp₂` this gives the restriction in *both* variables,
`Functor.whiskerLeft q₁ (Functor.whiskerRight τ ((Functor.whiskeringLeft _ _ _).obj q₂))`, which
is what `CategoryTheory.Functor.whiskeringLeft₂` applied to `τ` unfolds to — and whose two fields
are verbatim the two conditions `CategoryTheory.NatTrans.CommShift₂.of_essSurj` consumes. -/
instance whiskerLeft_precomp₁ (q₁ : C₁' ⥤ C₁) [q₁.CommShift M] {G₁ G₂ : C₁ ⥤ C₂ ⥤ D}
    (h : CommShift₂Setup D M) [G₁.CommShift₂ h] [G₂.CommShift₂ h] (τ : G₁ ⟶ G₂)
    [NatTrans.CommShift₂ τ h] :
    NatTrans.CommShift₂ (Functor.whiskerLeft q₁ τ) h where
  commShift_app K₁ := inferInstanceAs (NatTrans.CommShift (τ.app (q₁.obj K₁)) M)
  commShift_flipApp X₂ :=
    inferInstanceAs (NatTrans.CommShift (Functor.whiskerLeft q₁ (τ.flipApp X₂)) M)

/-- **Restricting a shift-compatible transformation of bifunctors along a shift-compatible functor
in the second variable**, the mirror of `whiskerLeft_precomp₁`. -/
instance whiskerRight_precomp₂ (q₂ : C₂' ⥤ C₂) [q₂.CommShift M] {G₁ G₂ : C₁ ⥤ C₂ ⥤ D}
    (h : CommShift₂Setup D M) [G₁.CommShift₂ h] [G₂.CommShift₂ h] (τ : G₁ ⟶ G₂)
    [NatTrans.CommShift₂ τ h] :
    NatTrans.CommShift₂
      (Functor.whiskerRight τ ((Functor.whiskeringLeft C₂' C₂ D).obj q₂)) h where
  commShift_app X₁ :=
    inferInstanceAs (NatTrans.CommShift (Functor.whiskerLeft q₂ (τ.app X₁)) M)
  commShift_flipApp K₂ :=
    inferInstanceAs (NatTrans.CommShift (τ.flipApp (q₂.obj K₂)) M)

end Precomp

section Postcomp

variable {C₁ : Type u₁} {C₂ : Type u₂} {D : Type u} {D' : Type u'}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v} D] [Category.{v'} D']
  [HasShift C₁ ℤ] [HasShift C₂ ℤ] [HasShift D ℤ] [HasShift D' ℤ]
  [Preadditive D] [Preadditive D'] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor D' n).Additive]

/-- **Postcomposing a shift-compatible transformation of bifunctors with an additive
shift-compatible functor gives a shift-compatible transformation.**  Both components are
one-variable whiskerings of components of `τ`, and the target structures are
`CategoryTheory.Functor.CommShift₂.postcompInt`. -/
instance whiskerRight_functorInt {G₁ G₂ : C₁ ⥤ C₂ ⥤ D} [G₁.CommShift₂Int] [G₂.CommShift₂Int]
    (τ : G₁ ⟶ G₂) [NatTrans.CommShift₂Int τ] (H : D ⥤ D') [H.CommShift ℤ] [H.Additive] :
    NatTrans.CommShift₂Int
      (Functor.whiskerRight τ ((Functor.whiskeringRight C₂ D D').obj H)) where
  commShift_app X₁ :=
    inferInstanceAs (NatTrans.CommShift (Functor.whiskerRight (τ.app X₁) H) ℤ)
  commShift_flipApp X₂ :=
    inferInstanceAs (NatTrans.CommShift (Functor.whiskerRight (τ.flipApp X₂) H) ℤ)

/-- **Postcomposing a bifunctor with a shift-compatible transformation of additive
shift-compatible target functors gives a shift-compatible transformation of bifunctors.**  Both
components are `Functor.whiskerLeft` of `η` along a one-variable component of `B`, and the source
and target structures are `CategoryTheory.Functor.CommShift₂.postcompInt`. -/
instance whiskerLeft_functorInt (B : C₁ ⥤ C₂ ⥤ D) [B.CommShift₂Int] {H H' : D ⥤ D'}
    [H.CommShift ℤ] [H'.CommShift ℤ] [H.Additive] [H'.Additive] (η : H ⟶ H')
    [NatTrans.CommShift η ℤ] :
    NatTrans.CommShift₂Int
      (Functor.whiskerLeft B ((Functor.whiskeringRight C₂ D D').map η)) where
  commShift_app X₁ :=
    inferInstanceAs (NatTrans.CommShift (Functor.whiskerLeft (B.obj X₁) η) ℤ)
  commShift_flipApp X₂ :=
    inferInstanceAs (NatTrans.CommShift (Functor.whiskerLeft (B.flip.obj X₂) η) ℤ)

end Postcomp

end CategoryTheory.NatTrans.CommShift₂

end
