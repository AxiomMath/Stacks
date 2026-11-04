module

public import StacksFrontier.Homology.KFlat.BifunctorOneSidedComparison

/-!
# Components of the one-sided K-flat comparison at a left K-flat complex

For an additive bifunctor `F : A ⥤ B ⥤ D` with a derived descent, the two-sided comparison
`CochainComplex.KFlatBifunctor.comparison` and the one-sided comparison
`CochainComplex.KFlatBifunctor.comparisonRight` have the same source and target when both
complexes are K-flat, and are the same isomorphism:
`CochainComplex.KFlatBifunctor.comparisonRight_eq_comparison` of
`StacksFrontier/Homology/KFlat/BifunctorOneSidedComparison.lean`.  This file reads the ingredients
of that identity off componentwise — the one-sided identification of functors at a left K-flat
object, and the head of the comparison, which is everything before the total-complex bridge —
and names the objects of the two K-flat subcategories attached to a pair of complexes, which is
the spelling the component statements are written at.

## Main results

* `CochainComplex.KFlatBifunctor.derivedBifunctorRightIso_hom_app_kFlatQLeft`: the one-sided
  identification of functors, read at a left K-flat object of the homotopy category, is the
  isomorphism it is the `preimageIso` of; `derivedBifunctorRightIso_hom_app_Qh` and
  `derivedBifunctorRightIso_hom_app_Qh'` are its component forms.
* `CochainComplex.KFlatBifunctor.kFlatObjLeftOf` and
  `CochainComplex.KFlatBifunctor.kFlatObjOf`: the objects of the two K-flat subcategories
  attached to a left K-flat and to a K-flat cochain complex.
* `CochainComplex.KFlatBifunctor.comparisonRight_head_eq`: **the head of the one-sided
  comparison is the head of the two-sided one.**
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace CochainComplex.KFlatBifunctor

variable {A B D : Type*} [Category A] [Category B] [Category D]
  [Abelian A] [Abelian B] [Abelian D]
  (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
      (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
      K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]

variable [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory D]

variable [(kFlatQLeft F).IsLocalization (kFlatQuasiIsoLeft F)]
  [(kFlatQ F).IsLocalization (kFlatQuasiIso F)]

/-- The identification of `derivedBifunctor` with the one-sided descent, read at the image in
`D(A)` of a left K-flat object of `K(A)`: there it is the isomorphism whose `preimageIso` it
is, by `CategoryTheory.Functor.FullyFaithful.map_preimage`. -/
theorem derivedBifunctorRightIso_hom_app_kFlatQLeft
    (Xl : (kFlatObjectsLeft F).FullSubcategory) :
    (derivedBifunctorRightIso F).hom.app ((kFlatQLeft F).obj Xl) =
      (derivedBifunctorComparisonIso F ≪≫
        (Functor.isoWhiskerLeft (kFlatObjectsLeft F).ι (homotopyToDerivedRightIso F)).symm ≪≫
        (Functor.associator _ _ _).symm).hom.app Xl :=
  NatTrans.congr_app
    ((CategoryTheory.Localization.fullyFaithfulWhiskeringLeft (kFlatQLeft F)
        (kFlatQuasiIsoLeft F)
        ((kFlatObjects F).FullSubcategory ⥤ DerivedCategory D)).map_preimage
      (derivedBifunctorComparisonIso F ≪≫
        (Functor.isoWhiskerLeft (kFlatObjectsLeft F).ι (homotopyToDerivedRightIso F)).symm ≪≫
        (Functor.associator _ _ _).symm).hom) Xl

section Comparison

variable (K : CochainComplex A ℤ) (L : CochainComplex B ℤ)

/-- The one-sided identification at the image of a left K-flat object, with the
homotopy-level identification already inverted: the shape the two-sided comparison needs. -/
theorem derivedBifunctorRightIso_hom_app_Qh (X : (kFlatObjectsLeft F).FullSubcategory)
    (Y : (kFlatObjects F).FullSubcategory) :
    ((derivedBifunctorRightIso F).hom.app ((kFlatQLeft F).obj X)).app Y =
      ((derivedBifunctorComparisonIso F).hom.app X).app Y ≫
        ((homotopyToDerivedRightIso F).inv.app X.1).app Y := by
  rw [derivedBifunctorRightIso_hom_app_kFlatQLeft F X]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Category.comp_id, Functor.isoWhiskerLeft_inv]
  rfl

omit [HasDerivedCategory B] [(kFlatQLeft F).IsLocalization (kFlatQuasiIsoLeft F)]
  [(kFlatQ F).IsLocalization (kFlatQuasiIso F)] in
/-- The homotopy-level identification at the homotopy class of a complex, as a composite of
the `Q` versus `Qh ∘ quotient` bridge and the descent's agreement on complexes. -/
theorem homotopyToDerivedRightIso_hom_app_quotient_app
    (Y : (kFlatObjects F).FullSubcategory) :
    ((homotopyToDerivedRightIso F).hom.app
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)).app Y =
      ((derivedToDerivedRight F).map
          ((DerivedCategory.quotientCompQhIso A).hom.app K)).app Y ≫
        (((derivedToDerivedRightFac F).hom.app K)).app Y := by
  rw [homotopyToDerivedRightIso_hom_app_quotient F K, NatTrans.comp_app]

/-- `derivedBifunctorRightIso_hom_app_Qh`, with the image of the left K-flat object written
through `DerivedCategory.Qh`, which is the spelling the two-sided comparison uses. -/
theorem derivedBifunctorRightIso_hom_app_Qh' (X : (kFlatObjectsLeft F).FullSubcategory)
    (Y : (kFlatObjects F).FullSubcategory) :
    ((derivedBifunctorRightIso F).hom.app
          ((DerivedCategory.Qh (C := A)).obj X.1)).app Y =
      ((derivedBifunctorComparisonIso F).hom.app X).app Y ≫
        ((homotopyToDerivedRightIso F).inv.app X.1).app Y :=
  derivedBifunctorRightIso_hom_app_Qh F X Y

/-- The left K-flat object of `K(A)` attached to a left K-flat cochain complex. -/
abbrev kFlatObjLeftOf (hK : KFlatLeft F K) : (kFlatObjectsLeft F).FullSubcategory :=
  ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K, hK⟩

/-- The K-flat object of `K(B)` attached to a K-flat cochain complex. -/
abbrev kFlatObjOf (hL : KFlat F L) : (kFlatObjects F).FullSubcategory :=
  ⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L, hL⟩

/-- The head of the one-sided comparison — everything before the total-complex bridge — is the
head of the two-sided one. -/
theorem comparisonRight_head_eq (hK : KFlatLeft F K) (hL : KFlat F L) :
    ((derivedBifunctor F).obj (DerivedCategory.Q.obj K)).map
          ((DerivedCategory.quotientCompQhIso B).app L).inv ≫
        ((derivedBifunctorRightIso F).hom.app (DerivedCategory.Q.obj K)).app
          (kFlatObjOf F L hL) ≫
        ((derivedToDerivedRightFac F).hom.app K).app (kFlatObjOf F L hL) =
      ((derivedBifunctor F).map ((DerivedCategory.quotientCompQhIso A).app K).inv).app
          (DerivedCategory.Q.obj L) ≫
        ((derivedBifunctor F).obj ((DerivedCategory.Qh (C := A)).obj
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K))).map
          ((DerivedCategory.quotientCompQhIso B).app L).inv ≫
        ((derivedBifunctorComparisonIso F).hom.app (kFlatObjLeftOf F K hK)).app
          (kFlatObjOf F L hL) := by
  have hnat := (derivedBifunctorRightIso F).hom.naturality
    ((DerivedCategory.quotientCompQhIso A).hom.app K)
  simp only [Functor.comp_obj] at hnat
  have hmid : (derivedBifunctorRightIso F).hom.app (DerivedCategory.Q.obj K) =
      (derivedBifunctorRight F).map ((DerivedCategory.quotientCompQhIso A).inv.app K) ≫
        (derivedBifunctorRightIso F).hom.app ((DerivedCategory.Qh (C := A)).obj
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) ≫
        (derivedToDerivedRight F).map ((DerivedCategory.quotientCompQhIso A).hom.app K) := by
    rw [← hnat, ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
  have htail : ((homotopyToDerivedRightIso F).inv.app
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)).app (kFlatObjOf F L hL) ≫
        ((derivedToDerivedRight F).map
          ((DerivedCategory.quotientCompQhIso A).hom.app K)).app (kFlatObjOf F L hL) ≫
        ((derivedToDerivedRightFac F).hom.app K).app (kFlatObjOf F L hL) =
      𝟙 (((kFlatToDerived F).obj (kFlatObjLeftOf F K hK)).obj (kFlatObjOf F L hL)) := by
    rw [← homotopyToDerivedRightIso_hom_app_quotient_app F K (kFlatObjOf F L hL)]
    exact NatTrans.congr_app (NatTrans.congr_app
      (((homotopyToDerivedRightIso F).inv_hom_id))
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) (kFlatObjOf F L hL)
  rw [hmid]
  simp only [NatTrans.comp_app, Category.assoc,
    derivedBifunctorRightIso_hom_app_Qh' F (kFlatObjLeftOf F K hK) (kFlatObjOf F L hL)]
  rw [htail, Category.comp_id]
  have hconv : ((derivedBifunctorRight F).map
        ((DerivedCategory.quotientCompQhIso A).inv.app K)).app (kFlatObjOf F L hL) =
      ((derivedBifunctor F).map ((DerivedCategory.quotientCompQhIso A).inv.app K)).app
        ((DerivedCategory.Qh (C := B)).obj
          ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L)) := rfl
  rw [hconv, Iso.app_inv, Iso.app_inv,
    reassoc_of% (((derivedBifunctor F).map
      ((DerivedCategory.quotientCompQhIso A).inv.app K)).naturality
        ((DerivedCategory.quotientCompQhIso B).inv.app L))]

end Comparison

end CochainComplex.KFlatBifunctor

end

end
