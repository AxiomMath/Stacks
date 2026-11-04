module

public import StacksFrontier.Homology.KFlat.BifunctorOneSidedComparison
public import StacksFrontier.Homology.KFlat.BifunctorOneSidedLeft

/-!
# The left one-sided K-flat comparison agrees with the two-sided one

For an additive bifunctor `F : A ⥤ B ⥤ D` with derived descent
`CochainComplex.KFlatBifunctor.derivedBifunctor`, the left one-sided comparison
`CochainComplex.KFlatBifunctor.comparisonLeft` (only `K` left K-flat) and the two-sided
`CochainComplex.KFlatBifunctor.comparison` (`K` left K-flat and `L` K-flat) are the same
isomorphism wherever both are defined. This is the mirror, across the two variables of `F`,
of `CochainComplex.KFlatBifunctor.comparisonRight_eq_comparison`, and its proof is the same
bookkeeping: strip the two `preimageIso`s behind `comparisonLeft` and transport along
`DerivedCategory.quotientCompQhIso`.

## Main results

* `CochainComplex.KFlatBifunctor.comparisonLeftFac_hom_app`: on a K-flat right factor the
  one-sided factorisation `comparisonLeftFac` is the flipped two-sided `Lifting₂`
  isomorphism, transported to `Q L`.
* `CochainComplex.KFlatBifunctor.comparisonLeft_eq_comparison`: **the left one-sided and the
  two-sided K-flat comparisons agree.**
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

section

variable [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory D]

omit [HasDerivedCategory A] in
/-- `homotopyToDerivedLeftIso` is the preimage, along precomposition with the homotopy
quotient, of the `Q` versus `Qh ∘ quotient` bridge whiskered into `derivedToDerivedLeft`. -/
theorem whiskerLeft_homotopyToDerivedLeftIso_hom :
    Functor.whiskerLeft (HomotopyCategory.quotient B (ComplexShape.up ℤ))
        (homotopyToDerivedLeftIso F).hom =
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso B)
          (derivedToDerivedLeft F) ≪≫
        derivedToDerivedLeftFac F).hom :=
  (CategoryTheory.Localization.fullyFaithfulWhiskeringLeft
    (HomotopyCategory.quotient B (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences B (ComplexShape.up ℤ))
    ((kFlatObjectsLeft F).FullSubcategory ⥤ DerivedCategory D)).map_preimage _

omit [HasDerivedCategory A] in
/-- The component of `homotopyToDerivedLeftIso` at the homotopy class of a cochain complex. -/
theorem homotopyToDerivedLeftIso_hom_app_quotient (L : CochainComplex B ℤ) :
    (homotopyToDerivedLeftIso F).hom.app
        ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L) =
      (derivedToDerivedLeft F).map ((DerivedCategory.quotientCompQhIso B).hom.app L) ≫
        (derivedToDerivedLeftFac F).hom.app L := by
  simpa using NatTrans.congr_app (whiskerLeft_homotopyToDerivedLeftIso_hom F) L

omit [HasDerivedCategory A] in
/-- `derivedToDerivedLeftFac` transported from `Q L` to the homotopy class of `L`. -/
theorem derivedToDerivedLeftFac_hom_app (L : CochainComplex B ℤ) :
    (derivedToDerivedLeftFac F).hom.app L =
      (derivedToDerivedLeft F).map ((DerivedCategory.quotientCompQhIso B).inv.app L) ≫
        (homotopyToDerivedLeftIso F).hom.app
          ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L) := by
  rw [homotopyToDerivedLeftIso_hom_app_quotient, ← Category.assoc, ← Functor.map_comp,
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]

section Comparison

variable [(kFlatQLeft F).IsLocalization (kFlatQuasiIsoLeft F)]
  [(kFlatQ F).IsLocalization (kFlatQuasiIso F)]

/-- `derivedBifunctorLeftIso` is the preimage, along precomposition with `kFlatQ`, of the
flipped two-sided comparison corrected by `homotopyToDerivedLeftIso`. -/
theorem whiskerLeft_derivedBifunctorLeftIso_hom :
    Functor.whiskerLeft (kFlatQ F) (derivedBifunctorLeftIso F).hom =
      (derivedBifunctorComparisonIsoFlip F ≪≫
        (Functor.isoWhiskerLeft (kFlatObjects F).ι
          (homotopyToDerivedLeftIso F)).symm ≪≫
        (Functor.associator _ _ _).symm).hom :=
  (CategoryTheory.Localization.fullyFaithfulWhiskeringLeft (kFlatQ F)
    (kFlatQuasiIso F)
    ((kFlatObjectsLeft F).FullSubcategory ⥤ DerivedCategory D)).map_preimage _

/-- `derivedBifunctorLeftIso` at a K-flat object of `K(B)`, followed by
`homotopyToDerivedLeftIso`, is the flipped two-sided comparison. -/
theorem derivedBifunctorLeftIso_hom_app_comp
    (W : HomotopyCategory B (ComplexShape.up ℤ)) (hW : kFlatObjects F W) :
    (derivedBifunctorLeftIso F).hom.app ((DerivedCategory.Qh (C := B)).obj W) ≫
        (homotopyToDerivedLeftIso F).hom.app W =
      (derivedBifunctorComparisonIsoFlip F).hom.app ⟨W, hW⟩ := by
  have h : (derivedBifunctorLeftIso F).hom.app ((DerivedCategory.Qh (C := B)).obj W) =
      (derivedBifunctorComparisonIsoFlip F).hom.app ⟨W, hW⟩ ≫
        (homotopyToDerivedLeftIso F).inv.app W := by
    simpa using
      NatTrans.congr_app (whiskerLeft_derivedBifunctorLeftIso_hom F)
        (⟨W, hW⟩ : (kFlatObjects F).FullSubcategory)
  have hcancel : (homotopyToDerivedLeftIso F).inv.app W ≫
      (homotopyToDerivedLeftIso F).hom.app W =
    𝟙 ((homotopyToDerivedLeft F).obj W) := (homotopyToDerivedLeftIso F).inv_hom_id_app W
  rw [h, Category.assoc, hcancel]
  exact Category.comp_id _

/-- **`comparisonLeftFac` is the flipped two-sided comparison, transported to `Q L`**, on a
K-flat right factor. -/
theorem comparisonLeftFac_hom_app (L : CochainComplex B ℤ) (hL : KFlat F L) :
    (comparisonLeftFac F).hom.app L =
      (derivedBifunctorLeft F).map ((DerivedCategory.quotientCompQhIso B).inv.app L) ≫
        (derivedBifunctorComparisonIsoFlip F).hom.app
          ⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L, hL⟩ := by
  have hfac : (comparisonLeftFac F).hom.app L =
      (derivedBifunctorLeftIso F).hom.app (DerivedCategory.Q.obj L) ≫
        (derivedToDerivedLeftFac F).hom.app L := by
    simp only [comparisonLeftFac, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
  have hnat : (derivedBifunctorLeft F).map
          ((DerivedCategory.quotientCompQhIso B).inv.app L) ≫
        (derivedBifunctorLeftIso F).hom.app
          ((DerivedCategory.Qh (C := B)).obj
            ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L)) =
      (derivedBifunctorLeftIso F).hom.app (DerivedCategory.Q.obj L) ≫
        (derivedToDerivedLeft F).map ((DerivedCategory.quotientCompQhIso B).inv.app L) :=
    (derivedBifunctorLeftIso F).hom.naturality _
  rw [hfac, derivedToDerivedLeftFac_hom_app, ← Category.assoc, ← hnat, Category.assoc,
    derivedBifunctorLeftIso_hom_app_comp F
      ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L) hL]

/-- **The left one-sided comparison agrees with the two-sided one**, at the level of the
underlying morphism. -/
theorem comparisonLeft_hom_eq_comparison_hom (K : CochainComplex A ℤ)
    (L : CochainComplex B ℤ) (hK : KFlatLeft F K) (hL : KFlat F L) :
    (comparisonLeft F K L hK).hom = (comparison F K L hK hL).hom := by
  have hmid : ((comparisonLeftFac F).hom.app L).app
        ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K, hK⟩ =
      ((derivedBifunctor F).obj ((DerivedCategory.Qh (C := A)).obj
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K))).map
          ((DerivedCategory.quotientCompQhIso B).inv.app L) ≫
        ((derivedBifunctorComparisonIso F).hom.app
            ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K, hK⟩).app
          ⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L, hL⟩ :=
    NatTrans.congr_app (comparisonLeftFac_hom_app F L hL) _
  rw [comparisonLeft_hom, comparison_hom, hmid, Category.assoc]

/-- **The left one-sided K-flat comparison is the two-sided one** wherever both apply. -/
theorem comparisonLeft_eq_comparison (K : CochainComplex A ℤ) (L : CochainComplex B ℤ)
    (hK : KFlatLeft F K) (hL : KFlat F L) :
    comparisonLeft F K L hK = comparison F K L hK hL :=
  Iso.ext (comparisonLeft_hom_eq_comparison_hom F K L hK hL)

end Comparison

end

end CochainComplex.KFlatBifunctor

end

end
