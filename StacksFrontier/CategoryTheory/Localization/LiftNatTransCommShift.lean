module

public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.CategoryTheory.Quotient
public import Mathlib.CategoryTheory.Shift.CommShift

/-! # Lifting a transformation along a localization, compatibly with the shift

Let `L : C ⥤ D` be a localization functor for a class `W` of morphisms of `C`, and let
`F, G : D ⥤ E` be two functors. Whiskering with `L` is fully faithful on transformations between
functors out of `D` (`CategoryTheory.Localization.liftNatTrans`), so a transformation
`L ⋙ F ⟶ L ⋙ G` descends uniquely to `F ⟶ G`. This file proves that the descent commutes with a
shift as soon as the given transformation does.

This is what constructs a transformation between two functors on a localization *without*
appealing to a Kan extension property: the universal property of a derived functor produces
transformations in one direction only, while this descent produces them in both.

## Main results

* `CategoryTheory.whiskerLeft_natTransLift`: a transformation lifted to a quotient category
  restricts to the original one along the quotient functor.
* `CategoryTheory.Localization.liftNatTrans_compLeft_commShift`: the descent of a transformation
  along a localization commutes with the shift.
* `CategoryTheory.Iso.inv_eq_hom_of_hom_eq_inv`: two isomorphisms whose forward and backward maps
  agree are inverse to one another.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u₁ u₂ u₃ v₁ v₂ v₃

/-- If the forward map of an isomorphism is the inverse of another, the two are inverse. -/
theorem CategoryTheory.Iso.inv_eq_hom_of_hom_eq_inv {C : Type*} [Category C] {X Y : C}
    {e : X ≅ Y} {z : Y ≅ X} (h : e.hom = z.inv) : e.inv = z.hom :=
  congrArg Iso.inv (Iso.ext h : e = z.symm)

/-- The restriction along the quotient functor of a lifted transformation is the original one. -/
theorem CategoryTheory.whiskerLeft_natTransLift {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {r : HomRel C} {F G : CategoryTheory.Quotient r ⥤ D}
    (τ : CategoryTheory.Quotient.functor r ⋙ F ⟶ CategoryTheory.Quotient.functor r ⋙ G) :
    Functor.whiskerLeft (CategoryTheory.Quotient.functor r)
      (CategoryTheory.Quotient.natTransLift r τ) = τ := by
  ext X
  rfl

/-- **A transformation lifted along a localization commutes with the shift as soon as the
transformation does.** Here the two functors on the localization are lifted tautologically, their
liftings being `F ↦ L ⋙ F`, so no compatibility of the liftings with the shift has to be
assumed. -/
theorem CategoryTheory.Localization.liftNatTrans_compLeft_commShift
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {E : Type u₃}
    [Category.{v₃} E] (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] (F G : D ⥤ E)
    (M : Type*) [AddMonoid M] [HasShift C M] [HasShift D M] [HasShift E M]
    [L.CommShift M] [F.CommShift M] [G.CommShift M] (τ : L ⋙ F ⟶ L ⋙ G)
    [NatTrans.CommShift τ M] :
    NatTrans.CommShift (Localization.liftNatTrans L W (L ⋙ F) (L ⋙ G) F G τ) M := by
  refine ⟨fun a => Localization.natTrans_ext L W fun X => ?_⟩
  have hσ : ∀ Y, (Localization.liftNatTrans L W (L ⋙ F) (L ⋙ G) F G τ).app (L.obj Y) =
      τ.app Y := fun Y => by simp
  have hnat := (Localization.liftNatTrans L W (L ⋙ F) (L ⋙ G) F G τ).naturality
    ((L.commShiftIso a).hom.app X)
  dsimp only [Functor.comp_obj] at hnat
  have hL : F.map ((L.commShiftIso a).hom.app X) ≫
        (F.commShiftIso a).hom.app (L.obj X) ≫
          (CategoryTheory.shiftFunctor E a).map (τ.app X) =
      τ.app ((CategoryTheory.shiftFunctor C a).obj X) ≫
        G.map ((L.commShiftIso a).hom.app X) ≫
          (G.commShiftIso a).hom.app (L.obj X) := by
    rw [← Category.assoc, ← Functor.commShiftIso_comp_hom_app, NatTrans.shift_app_comm,
      Functor.commShiftIso_comp_hom_app]
  have hR : F.map ((L.commShiftIso a).hom.app X) ≫
        (Localization.liftNatTrans L W (L ⋙ F) (L ⋙ G) F G τ).app
            ((CategoryTheory.shiftFunctor D a).obj (L.obj X)) ≫
          (G.commShiftIso a).hom.app (L.obj X) =
      τ.app ((CategoryTheory.shiftFunctor C a).obj X) ≫
        G.map ((L.commShiftIso a).hom.app X) ≫
          (G.commShiftIso a).hom.app (L.obj X) := by
    rw [← Category.assoc, hnat, hσ ((CategoryTheory.shiftFunctor C a).obj X), Category.assoc]
  dsimp
  rw [hσ, ← cancel_epi (F.map ((L.commShiftIso a).hom.app X))]
  exact hL.trans hR.symm

end
