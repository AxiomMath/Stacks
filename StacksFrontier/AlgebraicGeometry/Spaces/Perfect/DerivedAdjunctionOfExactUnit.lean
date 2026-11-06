module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.CoheratorQuasiInverse
public import StacksFrontier.AlgebraicGeometry.DerivedTildeEquivalence.DerivedAdjunction
public import StacksFrontier.Homology.Injectives.DerivedCategory.ArbitraryModelCounit

/-!
# The derived adjunction of an exact left adjoint, on a cochain complex

Let `adj : G ⊣ F` be an adjunction of additive functors between abelian categories with `G`
exact, and let `(R, α)` be a total right derived functor of `F` relative to chosen localizations
of the cochain complexes.  `Stacks.DerivedModel.adjunctionOfExact` is the derived adjunction of
[Stacks, Tag 09T5], and it is pinned down by two compatibilities stated on the homotopy
category: the counit one is `Stacks.DerivedModel.adjunctionOfExact_counit_fac`, and the unit one
is proved here.

At the standard model both compatibilities can be read on a cochain complex, for the adjunction
transported to `CategoryTheory.Functor.mapDerivedCategory` of the exact left adjoint.  What makes
that transport computable is the comparison between the arbitrary-model induced functor of an
exact functor and Mathlib's: it is a lift along `CategoryTheory.DerivedCategory.Qh`, so its value
at the image of a cochain complex is not immediate from its construction, and the identification
of the two models' factorisations through the homotopy category is what supplies it.

## Main results

* `Stacks.DerivedModel.adjunctionOfExact_unit_fac`: the unit of the derived adjunction at the
  image of an object of the homotopy category.
* `Stacks.DerivedQCoh.homotopyLocalizationQIso_hom_app_quotient` and
  `Stacks.DerivedModel.mapHomotopyCategoryCompLocalizationIso_hom_app`: the two comparisons of
  factorisations through the homotopy category, at the class of a cochain complex.
* `Stacks.DerivedQCoh.derivedFunctorOfExactIsoMapDerivedCategory_hom_app_Qh` and
  `…_hom_app_Q`: the comparison between the two induced functors of an exact functor, at the
  image of an object of the homotopy category and at the image of a cochain complex.
* `Stacks.DerivedModel.adjunctionOfExactMapDerivedCategory_unit_fac` and
  `…_counit_fac`: the unit and the counit of the derived adjunction
  `G.mapDerivedCategory ⊣ R`, on a cochain complex.

## References

* [Stacks Project, Tag 09T5](https://stacks.math.columbia.edu/tag/09T5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.DerivedModel

variable {A : Type*} {B : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
  [Category* B] [Abelian B] [HasDerivedCategory B]
  [CategoryWithHomology A] [CategoryWithHomology B]
  (G : B ⥤ A) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (QSource : CochainComplex A ℤ ⥤ DerivedCategory A)
  [QSource.IsLocalization (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))]
  (QTarget : CochainComplex B ℤ ⥤ DerivedCategory B)
  [QTarget.IsLocalization (HomologicalComplex.quasiIso B (ComplexShape.up ℤ))]
  [IsGrothendieckAbelian A] {F : A ⥤ B} [F.Additive]
  (adj : G ⊣ F)
  (R : DerivedCategory A ⥤ DerivedCategory B)
  (α : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ QTarget ⟶ QSource ⋙ R)
  [R.IsRightDerivedFunctor α (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))]

/-- The unit of `Stacks.DerivedModel.adjunctionOfExact`, at the image of an object of the
homotopy category, is the unit of the degreewise adjunction followed by the derivation unit of
`R`, read through the factorisation of the derived functor of the exact left adjoint. -/
theorem adjunctionOfExact_unit_fac (M : HomotopyCategory B (ComplexShape.up ℤ)) :
    (adjunctionOfExact G QSource QTarget adj R α).unit.app
          ((homotopyLocalization QTarget).obj M) ≫
        R.map ((derivedFunctorOfExactFac G QSource QTarget).hom.app M) =
      (homotopyLocalization QTarget).map
          ((Adjunction.mapHomotopyCategoryAdjunction adj (ComplexShape.up ℤ)).unit.app M) ≫
        (homotopyUnit F QTarget QSource R α).app
          ((G.mapHomotopyCategory (ComplexShape.up ℤ)).obj M) := by
  unfold adjunctionOfExact
  dsimp only
  generalize_proofs
  rename_i h
  exact (Classical.choose_spec h).1 M

/-- The comparison of the factorisation of `F.mapHomotopyCategory` is the identity on the class of
a cochain complex, so it disappears after `Qh`. -/
private theorem Qh_map_mapHomotopyCategoryFactors_hom_app_comp
    {C D : Type*} [Category* C] [Abelian C] [Category* D] [Abelian D] [HasDerivedCategory D]
    [CategoryWithHomology D] (H : C ⥤ D) [H.Additive] (M : CochainComplex C ℤ) :
    DerivedCategory.Qh.map ((H.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app M) ≫
      (DerivedCategory.quotientCompQhIso D).hom.app
        ((H.mapHomologicalComplex (ComplexShape.up ℤ)).obj M) =
      (DerivedCategory.quotientCompQhIso D).hom.app
        ((H.mapHomologicalComplex (ComplexShape.up ℤ)).obj M) :=
  have hmhc : (H.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app M =
      CategoryStruct.id ((H.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj M)) := rfl
  (congrArg (fun y => y ≫ (DerivedCategory.quotientCompQhIso D).hom.app
        ((H.mapHomologicalComplex (ComplexShape.up ℤ)).obj M))
      ((congrArg (fun x => DerivedCategory.Qh.map x) hmhc).trans
        (CategoryTheory.Functor.map_id DerivedCategory.Qh _))).trans (Category.id_comp _)

/-- The comparison of the factorisations through the homotopy category, at a cochain complex, is
the factorisation of the chosen localization through the lift to `Qh`. -/
private theorem homotopyLocalizationQuotientIso_hom_app_eq (N : CochainComplex B ℤ) :
    (homotopyLocalizationQuotientIso QTarget).hom.app N =
      (Localization.uniq (DerivedCategory.Q (C := B)) QTarget
            (HomologicalComplex.quasiIso B (ComplexShape.up ℤ))).functor.map
          ((DerivedCategory.quotientCompQhIso B).hom.app N) ≫
        (Localization.compUniqFunctor (DerivedCategory.Q (C := B)) QTarget
            (HomologicalComplex.quasiIso B (ComplexShape.up ℤ))).hom.app N :=
  Eq.trans (b := CategoryStruct.id _ ≫ _) rfl (Category.id_comp _)

omit [PreservesFiniteLimits G] [PreservesFiniteColimits G] [IsGrothendieckAbelian A]
  [R.IsRightDerivedFunctor α (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))]
  [HasDerivedCategory A] [CategoryWithHomology A] in
/-- The comparison identifying the degreewise functor followed by a chosen localization with its
factorisation through the homotopy category is the factorisation of that localization, read at
the image of the degreewise functor. -/
theorem mapHomotopyCategoryCompLocalizationIso_hom_app (M : CochainComplex A ℤ) :
    (mapHomotopyCategoryCompLocalizationIso F QTarget).hom.app M =
      (homotopyLocalizationQuotientIso QTarget).hom.app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj M) := by
  have h₁ : (mapHomotopyCategoryCompQhIso F).hom.app M =
      (DerivedCategory.quotientCompQhIso B).hom.app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj M) := by
    refine Eq.trans (b := CategoryStruct.id _ ≫ DerivedCategory.Qh.map
        ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app M) ≫ CategoryStruct.id _ ≫
          (DerivedCategory.quotientCompQhIso B).hom.app
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) rfl ?_
    rw [Category.id_comp, Category.id_comp, Qh_map_mapHomotopyCategoryFactors_hom_app_comp F M]
  have hdef₁ : (mapHomotopyCategoryCompLocalizationIso F QTarget).hom.app M =
      CategoryStruct.id _ ≫ (Localization.uniq (DerivedCategory.Q (C := B)) QTarget
            (HomologicalComplex.quasiIso B (ComplexShape.up ℤ))).functor.map
          ((mapHomotopyCategoryCompQhIso F).hom.app M) ≫
        CategoryStruct.id _ ≫ (Localization.compUniqFunctor (DerivedCategory.Q (C := B)) QTarget
            (HomologicalComplex.quasiIso B (ComplexShape.up ℤ))).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj M) := rfl
  rw [hdef₁, homotopyLocalizationQuotientIso_hom_app_eq, h₁, Category.id_comp, Category.id_comp]

end Stacks.DerivedModel

namespace Stacks.DerivedQCoh

universe w v u

section Model

variable (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  [CategoryWithHomology A]

/-- At the class of a cochain complex, the comparison of the two factorisations through the
homotopy category is the factorisation of the chosen localization. -/
theorem homotopyLocalizationQIso_hom_app_quotient (N : CochainComplex A ℤ) :
    (homotopyLocalizationQIso A).hom.app
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj N) =
      (Stacks.DerivedModel.homotopyLocalizationQuotientIso
          (DerivedCategory.Q (C := A))).hom.app N ≫
        (DerivedCategory.quotientCompQhIso A).inv.app N := by
  let : Localization.Lifting (DerivedCategory.Q (C := A))
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) (DerivedCategory.Q (C := A))
      (Localization.uniq (DerivedCategory.Q (C := A)) (DerivedCategory.Q (C := A))
        (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))).functor :=
    ⟨Localization.compUniqFunctor _ _ _⟩
  let : Localization.Lifting (DerivedCategory.Q (C := A))
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) (DerivedCategory.Q (C := A))
      (𝟭 (DerivedCategory A)) := ⟨Functor.rightUnitor _⟩
  set τ := Localization.liftNatTrans (DerivedCategory.Q (C := A))
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) (DerivedCategory.Q (C := A))
    (DerivedCategory.Q (C := A))
    (Localization.uniq (DerivedCategory.Q (C := A)) (DerivedCategory.Q (C := A))
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))).functor
    (𝟭 (DerivedCategory A)) (𝟙 (DerivedCategory.Q (C := A))) with hτ
  have hnat := τ.naturality ((DerivedCategory.quotientCompQhIso A).hom.app N)
  have happ : τ.app (DerivedCategory.Q.obj N) =
      (Localization.compUniqFunctor (DerivedCategory.Q (C := A)) (DerivedCategory.Q (C := A))
        (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))).hom.app N := by
    rw [hτ, Localization.liftNatTrans_app]
    dsimp only [NatTrans.id_app]
    rw [Category.id_comp]
    exact Category.comp_id _
  have hleft : (homotopyLocalizationQIso A).hom =
      Functor.whiskerLeft DerivedCategory.Qh τ ≫
        (Functor.rightUnitor (DerivedCategory.Qh (C := A))).hom := rfl
  have hright : (Stacks.DerivedModel.homotopyLocalizationQuotientIso
        (DerivedCategory.Q (C := A))).hom =
      (Functor.associator (HomotopyCategory.quotient A (ComplexShape.up ℤ))
          DerivedCategory.Qh _).inv ≫
        Functor.whiskerRight (DerivedCategory.quotientCompQhIso A).hom _ ≫
        (Localization.compUniqFunctor (DerivedCategory.Q (C := A)) (DerivedCategory.Q (C := A))
          (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))).hom := rfl
  have e₁ : (homotopyLocalizationQIso A).hom.app
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj N) =
      τ.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj N)) :=
    (NatTrans.congr_app hleft _).trans (Category.comp_id _)
  have e₂ := Stacks.DerivedModel.homotopyLocalizationQuotientIso_hom_app_eq
    (DerivedCategory.Q (C := A)) N
  have key : τ.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj N)) =
      (Localization.uniq (DerivedCategory.Q (C := A)) (DerivedCategory.Q (C := A))
            (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))).functor.map
          ((DerivedCategory.quotientCompQhIso A).hom.app N) ≫
        (Localization.compUniqFunctor (DerivedCategory.Q (C := A)) (DerivedCategory.Q (C := A))
            (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))).hom.app N ≫
          (DerivedCategory.quotientCompQhIso A).inv.app N := by
    rw [← cancel_mono ((DerivedCategory.quotientCompQhIso A).hom.app N), Category.assoc,
      Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    dsimp only [Functor.id_obj, Functor.id_map, Functor.comp_obj] at hnat
    rw [← hnat, happ]
  exact e₁.trans (key.trans ((Category.assoc _ _ _).symm.trans
    (congrArg (fun x => x ≫ (DerivedCategory.quotientCompQhIso A).inv.app N) e₂).symm))

/-- The class of a cochain complex in the comparison of the two factorisations through the homotopy
category, followed by the comparison with `Q`, is the factorisation of the chosen localization. -/
private theorem homotopyLocalizationQIso_hom_app_quotient_comp (N : CochainComplex A ℤ) :
    (homotopyLocalizationQIso A).hom.app
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj N) ≫
      (DerivedCategory.quotientCompQhIso A).hom.app N =
    (Stacks.DerivedModel.homotopyLocalizationQuotientIso
      (DerivedCategory.Q (C := A))).hom.app N := by
  rw [homotopyLocalizationQIso_hom_app_quotient, Category.assoc, Iso.inv_hom_id_app,
    Category.comp_id]

end Model

section Bridge

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  [CategoryWithHomology A] {B : Type u} [Category.{v} B] [Abelian B] [HasDerivedCategory.{w} B]
  [CategoryWithHomology B] (G : B ⥤ A) [G.Additive] [PreservesFiniteLimits G]
  [PreservesFiniteColimits G]

/-- The comparison between the arbitrary-model induced functor of an exact functor and Mathlib's,
at the image of an object of the homotopy category: it is the comparison of the two
factorisations through the homotopy category. -/
theorem derivedFunctorOfExactIsoMapDerivedCategory_hom_app_Qh
    (X : HomotopyCategory B (ComplexShape.up ℤ)) :
    (derivedFunctorOfExactIsoMapDerivedCategory G).hom.app (DerivedCategory.Qh.obj X) =
      ((Stacks.DerivedModel.derivedFunctorOfExact G (DerivedCategory.Q (C := A))
              (DerivedCategory.Q (C := B))).map ((homotopyLocalizationQIso B).inv.app X) ≫
          (Stacks.DerivedModel.derivedFunctorOfExactFac G (DerivedCategory.Q (C := A))
              (DerivedCategory.Q (C := B))).hom.app X ≫
            (homotopyLocalizationQIso A).hom.app
              ((G.mapHomotopyCategory (ComplexShape.up ℤ)).obj X)) ≫
        G.mapDerivedCategoryFactorsh.inv.app X := by
  let : Localization.Lifting (DerivedCategory.Qh (C := B))
      (HomotopyCategory.quasiIso B (ComplexShape.up ℤ))
      (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh (C := A))
      (Stacks.DerivedModel.derivedFunctorOfExact G (DerivedCategory.Q (C := A))
        (DerivedCategory.Q (C := B))) :=
    ⟨Functor.isoWhiskerRight (homotopyLocalizationQIso B).symm _ ≪≫
      Stacks.DerivedModel.derivedFunctorOfExactFac G _ _ ≪≫
      Functor.isoWhiskerLeft _ (homotopyLocalizationQIso A)⟩
  let : Localization.Lifting (DerivedCategory.Qh (C := B))
      (HomotopyCategory.quasiIso B (ComplexShape.up ℤ))
      (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh (C := A))
      G.mapDerivedCategory := ⟨G.mapDerivedCategoryFactorsh⟩
  dsimp only [derivedFunctorOfExactIsoMapDerivedCategory]
  rw [Localization.liftNatIso_hom, Localization.liftNatTrans_app]
  dsimp only [Iso.refl_hom, NatTrans.id_app]
  rw [Category.id_comp]
  rfl

/-- **The two models agree at the class of a cochain complex.**  The comparison between the
arbitrary-model induced functor of an exact functor and Mathlib's, read at the image of a cochain
complex, is the comparison of the two factorisations of the chosen localization. -/
theorem derivedFunctorOfExactIsoMapDerivedCategory_hom_app_Q (N : CochainComplex B ℤ) :
    (Stacks.DerivedModel.derivedFunctorOfExact G (DerivedCategory.Q (C := A))
            (DerivedCategory.Q (C := B))).map
          ((Stacks.DerivedModel.homotopyLocalizationQuotientIso
            (DerivedCategory.Q (C := B))).hom.app N) ≫
        (derivedFunctorOfExactIsoMapDerivedCategory G).hom.app (DerivedCategory.Q.obj N) ≫
          G.mapDerivedCategoryFactors.hom.app N =
      (Stacks.DerivedModel.derivedFunctorOfExactFac G (DerivedCategory.Q (C := A))
            (DerivedCategory.Q (C := B))).hom.app
          ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj N) ≫
        (Stacks.DerivedModel.homotopyLocalizationQuotientIso
            (DerivedCategory.Q (C := A))).hom.app
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) := by
  have hA : (homotopyLocalizationQIso A).hom.app
        ((G.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj N)) ≫
      (DerivedCategory.quotientCompQhIso A).hom.app
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) =
      (Stacks.DerivedModel.homotopyLocalizationQuotientIso
          (DerivedCategory.Q (C := A))).hom.app
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) :=
    homotopyLocalizationQIso_hom_app_quotient_comp A _
  have hQ : (Stacks.SmallDerivedCategory.leftDerivedFactorsQ
        (derivedFunctorOfExactIsoMapDerivedCategory G)).hom.app N =
      (derivedFunctorOfExactIsoMapDerivedCategory G).hom.app (DerivedCategory.Q.obj N) ≫
        G.mapDerivedCategoryFactors.hom.app N := rfl
  have hQh : (Stacks.SmallDerivedCategory.leftDerivedFactorsQh
        (derivedFunctorOfExactIsoMapDerivedCategory G)).hom.app
          ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj N) =
      (derivedFunctorOfExactIsoMapDerivedCategory G).hom.app
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj N)) ≫
        G.mapDerivedCategoryFactorsh.hom.app
          ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj N) := rfl
  have hldf := Stacks.SmallDerivedCategory.leftDerivedFactorsQ_hom_app
    (derivedFunctorOfExactIsoMapDerivedCategory G) N
  rw [hQ, hQh, derivedFunctorOfExactIsoMapDerivedCategory_hom_app_Qh] at hldf
  simp only [Category.assoc] at hldf
  rw [Iso.inv_hom_id_app_assoc,
    Stacks.DerivedModel.Qh_map_mapHomotopyCategoryFactors_hom_app_comp G, hA] at hldf
  have hcancel : (Stacks.DerivedModel.derivedFunctorOfExact G (DerivedCategory.Q (C := A))
          (DerivedCategory.Q (C := B))).map
        ((homotopyLocalizationQIso B).hom.app
          ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj N)) ≫
      (Stacks.DerivedModel.derivedFunctorOfExact G (DerivedCategory.Q (C := A))
          (DerivedCategory.Q (C := B))).map
        ((homotopyLocalizationQIso B).inv.app
          ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj N)) =
      CategoryStruct.id _ := by
    rw [← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id]
  calc (Stacks.DerivedModel.derivedFunctorOfExact G (DerivedCategory.Q (C := A))
          (DerivedCategory.Q (C := B))).map
            ((Stacks.DerivedModel.homotopyLocalizationQuotientIso
              (DerivedCategory.Q (C := B))).hom.app N) ≫
          ((derivedFunctorOfExactIsoMapDerivedCategory G).hom.app (DerivedCategory.Q.obj N) ≫
            G.mapDerivedCategoryFactors.hom.app N)
      = ((Stacks.DerivedModel.derivedFunctorOfExact G (DerivedCategory.Q (C := A))
              (DerivedCategory.Q (C := B))).map
            ((homotopyLocalizationQIso B).hom.app
              ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj N)) ≫
          (Stacks.DerivedModel.derivedFunctorOfExact G (DerivedCategory.Q (C := A))
              (DerivedCategory.Q (C := B))).map
            ((DerivedCategory.quotientCompQhIso B).hom.app N)) ≫
        ((derivedFunctorOfExactIsoMapDerivedCategory G).hom.app (DerivedCategory.Q.obj N) ≫
          G.mapDerivedCategoryFactors.hom.app N) := by
        rw [← homotopyLocalizationQIso_hom_app_quotient_comp B N, CategoryTheory.Functor.map_comp]
    _ = (Stacks.DerivedModel.derivedFunctorOfExact G (DerivedCategory.Q (C := A))
            (DerivedCategory.Q (C := B))).map
          ((homotopyLocalizationQIso B).hom.app
            ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj N)) ≫
        ((Stacks.DerivedModel.derivedFunctorOfExact G (DerivedCategory.Q (C := A))
              (DerivedCategory.Q (C := B))).map
            ((DerivedCategory.quotientCompQhIso B).hom.app N) ≫
          ((derivedFunctorOfExactIsoMapDerivedCategory G).hom.app (DerivedCategory.Q.obj N) ≫
            G.mapDerivedCategoryFactors.hom.app N)) := Category.assoc _ _ _
    _ = (Stacks.DerivedModel.derivedFunctorOfExact G (DerivedCategory.Q (C := A))
            (DerivedCategory.Q (C := B))).map
          ((homotopyLocalizationQIso B).hom.app
            ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj N)) ≫
        ((Stacks.DerivedModel.derivedFunctorOfExact G (DerivedCategory.Q (C := A))
              (DerivedCategory.Q (C := B))).map
            ((homotopyLocalizationQIso B).inv.app
              ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj N)) ≫
          ((Stacks.DerivedModel.derivedFunctorOfExactFac G (DerivedCategory.Q (C := A))
                (DerivedCategory.Q (C := B))).hom.app
              ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj N) ≫
            (Stacks.DerivedModel.homotopyLocalizationQuotientIso
                (DerivedCategory.Q (C := A))).hom.app
              ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N))) := by rw [hldf]
    _ = _ := by rw [← Category.assoc, hcancel, Category.id_comp]

end Bridge

end Stacks.DerivedQCoh

namespace Stacks.DerivedModel

universe w v u

section StandardModel

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  [CategoryWithHomology A] [IsGrothendieckAbelian A] {B : Type u} [Category.{v} B] [Abelian B]
  [HasDerivedCategory.{w} B] [CategoryWithHomology B] (G : B ⥤ A) [G.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G] {F : A ⥤ B} [F.Additive] (adj : G ⊣ F)
  (R : DerivedCategory A ⥤ DerivedCategory B)
  (α : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
    DerivedCategory.Q ⋙ R)
  [R.IsRightDerivedFunctor α (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))]

/-- **The unit of the derived adjunction of an exact left adjoint, on a cochain complex.**  For
`adj : G ⊣ F` with `G` exact and `(R, α)` a total right derived functor of `F`, the unit of the
adjunction `G.mapDerivedCategory ⊣ R` of Stacks 09T5 is, at the class of a cochain complex `N`,
the class of the degreewise unit followed by `α`. -/
theorem adjunctionOfExactMapDerivedCategory_unit_fac (N : CochainComplex B ℤ) :
    ((adjunctionOfExact G (DerivedCategory.Q (C := A)) (DerivedCategory.Q (C := B))
              adj R α).ofNatIsoLeft
            (Stacks.DerivedQCoh.derivedFunctorOfExactIsoMapDerivedCategory G)).unit.app
          (DerivedCategory.Q.obj N) ≫
        R.map (G.mapDerivedCategoryFactors.hom.app N) =
      DerivedCategory.Q.map
          ((Adjunction.mapHomologicalComplexAdjunction adj (ComplexShape.up ℤ)).unit.app N) ≫
        α.app ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) := by
  have hofn : ((adjunctionOfExact G (DerivedCategory.Q (C := A)) (DerivedCategory.Q (C := B))
            adj R α).ofNatIsoLeft
          (Stacks.DerivedQCoh.derivedFunctorOfExactIsoMapDerivedCategory G)).unit.app
        (DerivedCategory.Q.obj N) =
      (adjunctionOfExact G (DerivedCategory.Q (C := A)) (DerivedCategory.Q (C := B))
            adj R α).unit.app (DerivedCategory.Q.obj N) ≫
        R.map ((Stacks.DerivedQCoh.derivedFunctorOfExactIsoMapDerivedCategory G).hom.app
          (DerivedCategory.Q.obj N)) := rfl
  have hcomp : R.map ((Stacks.DerivedQCoh.derivedFunctorOfExactIsoMapDerivedCategory G).hom.app
          (DerivedCategory.Q.obj N)) ≫ R.map (G.mapDerivedCategoryFactors.hom.app N) =
      R.map ((Stacks.DerivedQCoh.derivedFunctorOfExactIsoMapDerivedCategory G).hom.app
          (DerivedCategory.Q.obj N) ≫ G.mapDerivedCategoryFactors.hom.app N) :=
    (CategoryTheory.Functor.map_comp R _ _).symm
  have hnu := (adjunctionOfExact G (DerivedCategory.Q (C := A)) (DerivedCategory.Q (C := B))
    adj R α).unit.naturality
      ((homotopyLocalizationQuotientIso (DerivedCategory.Q (C := B))).hom.app N)
  dsimp only [Functor.id_obj, Functor.id_map, Functor.comp_map] at hnu
  have hmapd : R.map ((derivedFunctorOfExact G (DerivedCategory.Q (C := A))
            (DerivedCategory.Q (C := B))).map
          ((homotopyLocalizationQuotientIso (DerivedCategory.Q (C := B))).hom.app N)) ≫
        R.map ((Stacks.DerivedQCoh.derivedFunctorOfExactIsoMapDerivedCategory G).hom.app
            (DerivedCategory.Q.obj N) ≫ G.mapDerivedCategoryFactors.hom.app N) =
      R.map ((derivedFunctorOfExactFac G (DerivedCategory.Q (C := A))
              (DerivedCategory.Q (C := B))).hom.app
            ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj N)) ≫
        R.map ((homotopyLocalizationQuotientIso (DerivedCategory.Q (C := A))).hom.app
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)) := by
    rw [← CategoryTheory.Functor.map_comp,
      Stacks.DerivedQCoh.derivedFunctorOfExactIsoMapDerivedCategory_hom_app_Q]
    exact CategoryTheory.Functor.map_comp R _ _
  have hu := adjunctionOfExact_unit_fac G (DerivedCategory.Q (C := A))
    (DerivedCategory.Q (C := B)) adj R α ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj N)
  have hhu : (homotopyUnit F (DerivedCategory.Q (C := B)) (DerivedCategory.Q (C := A)) R α).app
        ((G.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj N)) =
      (mapHomotopyCategoryCompLocalizationIso F (DerivedCategory.Q (C := B))).hom.app
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) ≫
        α.app ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) ≫
          (homotopyLocalizationCompIso (DerivedCategory.Q (C := A)) R).inv.app
            ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) :=
    homotopyUnit_app_quotient F (DerivedCategory.Q (C := B)) (DerivedCategory.Q (C := A)) R α _
  have hci : (homotopyLocalizationCompIso (DerivedCategory.Q (C := A)) R).inv.app
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) ≫
        R.map ((homotopyLocalizationQuotientIso (DerivedCategory.Q (C := A))).hom.app
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)) =
      CategoryStruct.id _ := by
    have hdef : (homotopyLocalizationCompIso (DerivedCategory.Q (C := A)) R).inv.app
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) =
        R.map ((homotopyLocalizationQuotientIso (DerivedCategory.Q (C := A))).inv.app
            ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)) ≫ CategoryStruct.id _ := rfl
    rw [hdef, Category.comp_id, ← CategoryTheory.Functor.map_comp]
    exact (congrArg (fun x => R.map x) (Iso.inv_hom_id_app _ _)).trans
      (CategoryTheory.Functor.map_id R _)
  have hHU : (homotopyUnit F (DerivedCategory.Q (C := B)) (DerivedCategory.Q (C := A)) R α).app
          ((G.mapHomotopyCategory (ComplexShape.up ℤ)).obj
            ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj N)) ≫
        R.map ((homotopyLocalizationQuotientIso (DerivedCategory.Q (C := A))).hom.app
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)) =
      (homotopyLocalizationQuotientIso (DerivedCategory.Q (C := B))).hom.app
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
              ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)) ≫
          α.app ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) := by
    have hci2 : α.app ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) ≫
          (homotopyLocalizationCompIso (DerivedCategory.Q (C := A)) R).inv.app
              ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) ≫
            R.map ((homotopyLocalizationQuotientIso (DerivedCategory.Q (C := A))).hom.app
              ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)) =
        α.app ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) := by
      rw [hci, Category.comp_id]
    rw [hhu, mapHomotopyCategoryCompLocalizationIso_hom_app]
    exact (Category.assoc
          ((homotopyLocalizationQuotientIso (DerivedCategory.Q (C := B))).hom.app
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
              ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)))
          (α.app ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) ≫
            (homotopyLocalizationCompIso (DerivedCategory.Q (C := A)) R).inv.app
              ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N))
          (R.map ((homotopyLocalizationQuotientIso (DerivedCategory.Q (C := A))).hom.app
            ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)))).trans
      (congrArg (fun y => (homotopyLocalizationQuotientIso (DerivedCategory.Q (C := B))).hom.app
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
              ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)) ≫ y)
        ((Category.assoc (α.app ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N))
            ((homotopyLocalizationCompIso (DerivedCategory.Q (C := A)) R).inv.app
              ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N))
            (R.map ((homotopyLocalizationQuotientIso (DerivedCategory.Q (C := A))).hom.app
              ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)))).trans hci2))
  have hnq := (homotopyLocalizationQuotientIso (DerivedCategory.Q (C := B))).hom.naturality
    ((Adjunction.mapHomologicalComplexAdjunction adj (ComplexShape.up ℤ)).unit.app N)
  dsimp only [Functor.comp_map] at hnq
  rw [← cancel_epi ((homotopyLocalizationQuotientIso (DerivedCategory.Q (C := B))).hom.app N),
    hofn]
  simp only [Category.assoc]
  rw [hcomp, reassoc_of% hnu, hmapd, reassoc_of% hu,
    Adjunction.mapHomotopyCategoryAdjunction_unit_app_quotient, hHU]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (fun y => y ≫
      α.app ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)) hnq).trans
    (Category.assoc _ _ _))

/-- **The counit of the derived adjunction of an exact left adjoint, on a cochain complex.**  In
the situation of `Stacks.DerivedModel.adjunctionOfExactMapDerivedCategory_unit_fac`, the
derivation unit followed by the counit of the adjunction `G.mapDerivedCategory ⊣ R` is the class
of the degreewise counit. -/
theorem adjunctionOfExactMapDerivedCategory_counit_fac (K : CochainComplex A ℤ) :
    G.mapDerivedCategory.map (α.app K) ≫
        ((adjunctionOfExact G (DerivedCategory.Q (C := A)) (DerivedCategory.Q (C := B))
              adj R α).ofNatIsoLeft
            (Stacks.DerivedQCoh.derivedFunctorOfExactIsoMapDerivedCategory G)).counit.app
          (DerivedCategory.Q.obj K) =
      G.mapDerivedCategoryFactors.hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((Adjunction.mapHomologicalComplexAdjunction adj (ComplexShape.up ℤ)).counit.app K) := by
  have hU := adjunctionOfExactMapDerivedCategory_unit_fac G adj R α
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
  have hnat := α.naturality
    ((Adjunction.mapHomologicalComplexAdjunction adj (ComplexShape.up ℤ)).counit.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hnat
  have htri := (Adjunction.mapHomologicalComplexAdjunction adj
    (ComplexShape.up ℤ)).right_triangle_components K
  have h₀ : G.mapDerivedCategory.map (α.app K) ≫
        ((adjunctionOfExact G (DerivedCategory.Q (C := A)) (DerivedCategory.Q (C := B))
              adj R α).ofNatIsoLeft
            (Stacks.DerivedQCoh.derivedFunctorOfExactIsoMapDerivedCategory G)).counit.app
          (DerivedCategory.Q.obj K) =
      (((adjunctionOfExact G (DerivedCategory.Q (C := A)) (DerivedCategory.Q (C := B))
              adj R α).ofNatIsoLeft
            (Stacks.DerivedQCoh.derivedFunctorOfExactIsoMapDerivedCategory G)).homEquiv
          (DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
          (DerivedCategory.Q.obj K)).symm (α.app K) := rfl
  rw [h₀, Equiv.symm_apply_eq, Adjunction.homEquiv_unit,
    CategoryTheory.Functor.map_comp, reassoc_of% hU, ← hnat,
    ← CategoryTheory.Functor.map_comp_assoc, htri, CategoryTheory.Functor.map_id,
    Category.id_comp]
  rfl

end StandardModel

end Stacks.DerivedModel

end
