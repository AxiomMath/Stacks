module

public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.CategoryTheory.Shift.CommShift

/-!
# Lifting a natural transformation through a localization respects the shift

Let `L : A ⥤ B` be a localization functor for a morphism property `W`, and let `F, G : A ⥤ E`
factor through `L` as `F', G' : B ⥤ E`. A natural transformation `τ : F ⟶ G` descends to
`CategoryTheory.Localization.liftNatTrans L W F G F' G' τ : F' ⟶ G'`. If all the functors and
the factoring isomorphisms commute with a shift by an additive monoid `M`, and `τ` itself does,
then so does the descended transformation: both sides of the required square are determined by
their restrictions along `L`, where the statement is exactly the one assumed for `τ`.

This is what supplies a `CategoryTheory.NatTrans.CommShift` for a comparison isomorphism
produced by `CategoryTheory.Localization.liftNatIso`, which carries none by construction, so
that such a comparison can be evaluated at a shifted object.

## Main results

* `CategoryTheory.Localization.liftNatTrans_commShift`: the natural transformation obtained
  from `τ` by lifting through a localization commutes with the shift as soon as `τ` does.
* `CategoryTheory.Localization.liftNatIso_hom_commShift`: the same for a lifted natural
  isomorphism, whose inverse then inherits the compatibility from
  `CategoryTheory.NatTrans.CommShift.of_iso_inv`.

## Implementation notes

The hypotheses include `NatTrans.CommShift` for the two `CategoryTheory.Localization.Lifting.iso`
isomorphisms, which is what relates the shift on `B` to the shift on `A` through `L`; without
it the two squares cannot be compared. Mathlib supplies exactly that instance for the shift
transported along a localization, as
`CategoryTheory.NatTrans.commShift_iso_hom_of_localization`.

The proof reduces to objects of the form `L.obj X` by `CategoryTheory.Localization.natTrans_ext`
and then rewrites both shifted comparison isomorphisms in terms of their counterparts on `A`.
-/

@[expose] public section

namespace CategoryTheory.Localization

variable {A B E : Type*} [Category* A] [Category* B] [Category* E]
  {M : Type*} [AddMonoid M] [HasShift A M] [HasShift B M] [HasShift E M]
  (L : A ⥤ B) (W : MorphismProperty A) [L.IsLocalization W]
  (F G : A ⥤ E) (F' G' : B ⥤ E)
  [Localization.Lifting L W F F'] [Localization.Lifting L W G G']
  (τ : F ⟶ G) [L.CommShift M] [F.CommShift M] [G.CommShift M]
  [F'.CommShift M] [G'.CommShift M] [NatTrans.CommShift τ M]
  [NatTrans.CommShift (Localization.Lifting.iso L W F F').hom M]
  [NatTrans.CommShift (Localization.Lifting.iso L W G G').hom M]

omit [L.IsLocalization W] in
/-- The commutation isomorphism of a lift `F'` of `F` through `L`, evaluated at `L.obj X`,
expressed through that of `F`. -/
lemma commShiftIso_hom_app_obj_of_lifting (n : M) (X : A) :
    (F'.commShiftIso n).hom.app (L.obj X) =
      F'.map ((L.commShiftIso n).inv.app X) ≫
        (Localization.Lifting.iso L W F F').hom.app (X⟦n⟧) ≫
        (F.commShiftIso n).hom.app X ≫
        (shiftFunctor E n).map ((Localization.Lifting.iso L W F F').inv.app X) := by
  have hF := NatTrans.shift_app_comm (Localization.Lifting.iso L W F F').hom n X
  simp only [Functor.commShiftIso_comp_hom_app] at hF
  apply (cancel_mono ((shiftFunctor E n).map
    ((Localization.Lifting.iso L W F F').hom.app X))).1
  calc
    (F'.commShiftIso n).hom.app (L.obj X) ≫
        (shiftFunctor E n).map ((Localization.Lifting.iso L W F F').hom.app X) =
      F'.map ((L.commShiftIso n).inv.app X) ≫
        (F'.map ((L.commShiftIso n).hom.app X) ≫
          (F'.commShiftIso n).hom.app (L.obj X) ≫
          (shiftFunctor E n).map ((Localization.Lifting.iso L W F F').hom.app X)) := by
        simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.map_id,
          Category.id_comp]
    _ = F'.map ((L.commShiftIso n).inv.app X) ≫
        ((Localization.Lifting.iso L W F F').hom.app (X⟦n⟧) ≫
          (F.commShiftIso n).hom.app X) := by
      simpa [Category.assoc] using congrArg
        (fun f => F'.map ((L.commShiftIso n).inv.app X) ≫ f) hF
    _ = (F'.map ((L.commShiftIso n).inv.app X) ≫
        (Localization.Lifting.iso L W F F').hom.app (X⟦n⟧) ≫
        (F.commShiftIso n).hom.app X ≫
        (shiftFunctor E n).map ((Localization.Lifting.iso L W F F').inv.app X)) ≫
        (shiftFunctor E n).map ((Localization.Lifting.iso L W F F').hom.app X) := by
          simp only [Functor.comp_obj, Category.assoc, ← Functor.map_comp,
            Iso.inv_hom_id_app, Functor.map_id, Category.comp_id]

/-- **A natural transformation lifted through a localization functor commutes with the shift**
whenever the transformation it is lifted from does. -/
lemma liftNatTrans_commShift :
    NatTrans.CommShift (Localization.liftNatTrans L W F G F' G' τ) M := by
  apply NatTrans.CommShift.of_core
  intro n
  constructor
  apply Localization.natTrans_ext L W
  intro X
  let β := Localization.liftNatTrans L W F G F' G' τ
  change (F'.commShiftIso n).hom.app (L.obj X) ≫
      ((β.app (L.obj X))⟦n⟧') =
    β.app ((L.obj X)⟦n⟧) ≫ (G'.commShiftIso n).hom.app (L.obj X)
  rw [commShiftIso_hom_app_obj_of_lifting L W F F' n X,
    commShiftIso_hom_app_obj_of_lifting L W G G' n X]
  have hβ' : β.app ((L.obj X)⟦n⟧) ≫
      G'.map ((L.commShiftIso n).inv.app X) =
    F'.map ((L.commShiftIso n).inv.app X) ≫ β.app (L.obj (X⟦n⟧)) := by
    simpa only [Functor.comp_obj] using
      (β.naturality ((L.commShiftIso n).inv.app X)).symm
  simp only [← Category.assoc, hβ']
  simp [β, Localization.liftNatTrans_app, Functor.map_comp, Category.assoc]
  simp only [← Category.assoc]
  simp only [Category.assoc, ← Functor.map_comp]
  simpa [Category.assoc, Functor.commShiftIso_comp_hom_app] using congrArg
    (fun q => F'.map ((L.commShiftIso n).inv.app X) ≫
      (Localization.Lifting.iso L W F F').hom.app (X⟦n⟧) ≫ q ≫
      (shiftFunctor E n).map ((Localization.Lifting.iso L W G G').inv.app X))
    (NatTrans.shift_app_comm τ n X)

/-- **A natural isomorphism lifted through a localization functor commutes with the shift**
whenever the isomorphism it is lifted from does. This is the form a comparison isomorphism built
by `CategoryTheory.Localization.liftNatIso` is consumed in: the lifted isomorphism carries no
compatibility with the shift by construction, and this supplies it. -/
instance liftNatIso_hom_commShift (e : F ≅ G) [NatTrans.CommShift e.hom M] :
    NatTrans.CommShift (Localization.liftNatIso L W F G F' G' e).hom M :=
  liftNatTrans_commShift L W F G F' G' e.hom

end CategoryTheory.Localization

end
