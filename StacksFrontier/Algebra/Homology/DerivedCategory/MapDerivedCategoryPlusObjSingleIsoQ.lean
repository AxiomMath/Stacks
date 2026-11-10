module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSquareTransComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RightDerivedRestrictionUnit
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedFunctors.CompositeSingleModelCrossing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportExt

/-!
# The comparison `F(X[0]) ≅ (F X)[0]` of an exact functor on bounded below derived categories

For an exact functor `F`, the comparison `F⁺(X[0]) ≅ (F X)[0]` of
`Functor.mapDerivedCategoryPlusObjSingleIso` is, after the inclusion of the bounded below derived
category, Mathlib's comparison `Functor.mapDerivedCategorySingleFunctor`
(`Functor.ι_map_mapDerivedCategoryPlusObjSingleIso_hom`). Read against the commutation
`Q ⋙ F⁺ ≅ F ⋙ Q` of the localization with `F` (`Functor.mapDerivedCategoryPlusQIso`), it is the
localization of the termwise identification `F(X[0]) ≅ (F X)[0]` of complexes
(`Functor.mapDerivedCategoryPlusObjSingleIso_inv_comp_mapDerivedCategoryPlusQIso_hom`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
  {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
  [EnoughInjectives A] (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F]

omit [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
private lemma single_chase {D E : Type*} [Category* D] [Category* E] (W : E ⥤ D) {P Q0 T : D}
    {Ue Ve : E} (a : P ⟶ Q0) (b : Q0 ⟶ W.obj Ue) (m : P ⟶ T) (s : T ⟶ W.obj Ve)
    (s' : W.obj Ve ⟶ T) (i : Ve ⟶ Ue) (h : Ue ⟶ Ve) (hab : a ≫ b = m ≫ s ≫ W.map i)
    (hih : i ≫ h = 𝟙 Ve) (hss : s ≫ s' = 𝟙 T) : a ≫ b ≫ W.map h ≫ s' = m := by
  rw [reassoc_of% hab, ← W.map_comp_assoc, hih, W.map_id, Category.id_comp, hss, Category.comp_id]

/-- **`F⁺(X[0]) ≅ (F X)[0]` is Mathlib's `mapDerivedCategorySingleFunctor`**, after the inclusion
of the bounded below derived category. -/
theorem ι_map_mapDerivedCategoryPlusObjSingleIso_hom (X : A) :
    DerivedCategory.Plus.ι.map (F.mapDerivedCategoryPlusObjSingleIso X).hom =
      (F.mapDerivedCategorySingleFunctor 0).hom.app X := by
  have hd : ∀ Z : A,
      DerivedCategory.Plus.ι.map ((singleFunctorPlusIsoCompQh (A := A) 0).hom.app Z) =
        (DerivedCategory.singleFunctorIsoCompQh A 0).hom.app Z :=
    Stacks.DerivedIndexing.ι_map_singleFunctorPlusIsoCompQh_hom_app 0
  have hd' :
      DerivedCategory.Plus.ι.map ((singleFunctorPlusIsoCompQh (A := B) 0).inv.app (F.obj X)) =
        (DerivedCategory.singleFunctorIsoCompQh B 0).inv.app (F.obj X) :=
    DerivedCategory.Plus.ι.map_preimage _
  rw [mapDerivedCategoryPlusObjSingleIso_hom]
  simp only [CategoryTheory.Functor.map_comp]
  rw [hd']
  change F.mapDerivedCategory.map (DerivedCategory.Plus.ι.map
    ((singleFunctorPlusIsoCompQh (A := A) 0).hom.app X)) ≫ _ = _
  rw [hd X]
  have e1 : DerivedCategory.Plus.ι.map (F.mapDerivedCategoryPlusFactorsh.hom.app
      ((HomotopyCategory.Plus.singleFunctor A 0).obj X)) =
      F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.singleFunctor A 0).obj X) := rfl
  have e2 : DerivedCategory.Plus.ι.map
      (DerivedCategory.Plus.Qh.map (F.mapHomotopyCategoryPlusObjSingleIso 0 X).hom) =
      (HomotopyCategory.quotient B (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map
        ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app X) :=
    congrArg DerivedCategory.Qh.map ((HomotopyCategory.Plus.ι B).map_preimage _)
  refine (congrArg (fun t => _ ≫ t) (congrArg₂ (· ≫ ·) e1
    (congrArg (fun t => t ≫ _) e2))).trans ?_
  open Stacks.Cohomology.DerivedCompTransport in
  exact single_chase (HomotopyCategory.quotient B (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    _ _ _ _ _ _ _ (mapDerivedCategory_map_singleFunctorIsoCompQh_hom_app_comp_factorsh F X)
    (Iso.inv_hom_id_app _ _) (Iso.hom_inv_id_app _ _)

/-- **The localization of the termwise comparison `F(X[0]) ≅ (F X)[0]`**: the inverse of
`F⁺(X[0]) ≅ (F X)[0]` followed by `Q ⋙ F⁺ ≅ F ⋙ Q` at the single complex is the localization of the
termwise identification. -/
theorem mapDerivedCategoryPlusObjSingleIso_inv_comp_mapDerivedCategoryPlusQIso_hom (X : A) :
    (F.mapDerivedCategoryPlusObjSingleIso X).inv ≫
        (mapDerivedCategoryPlusQIso F).hom.app
          ((Stacks.DerivedIndexing.singlePlusFunctor A 0).obj X) =
      DerivedCategory.Plus.Q.map
        (Stacks.EtaleCohomology.mapCochainComplexPlusSinglePlusIso F X).inv := by
  apply DerivedCategory.Plus.ι.map_injective
  refine (DerivedCategory.Plus.ι.map_comp _ _).trans ?_
  have h1 : DerivedCategory.Plus.ι.map (F.mapDerivedCategoryPlusObjSingleIso X).inv =
      (F.mapDerivedCategorySingleFunctor 0).inv.app X :=
    congrArg Iso.inv (Iso.ext (ι_map_mapDerivedCategoryPlusObjSingleIso_hom F X) :
      DerivedCategory.Plus.ι.mapIso (F.mapDerivedCategoryPlusObjSingleIso X) =
        (F.mapDerivedCategorySingleFunctor 0).app X)
  have h2 := ι_map_mapDerivedCategoryPlusQIso_hom_app F
    ((Stacks.DerivedIndexing.singlePlusFunctor A 0).obj X)
  refine (congrArg₂ (· ≫ ·) h1 h2).trans ?_
  exact F.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app X

/-- **The transported resolution iso is the localization of the restricted augmentation**: if
`ξ : X[0] ≅ Q(N)` is the localization of a morphism of complexes `a : X[0] ⟶ N`, then
`F(X)[0] ≅ F⁺(X[0]) ≅ F⁺(Q N) ≅ Q(F N)` is the localization of `F(X)[0] ≅ F(X[0]) ⟶ F(N)`. -/
theorem mapDerivedCategoryPlusObjSingleIso_symm_trans_mapIso_trans_hom (X : A)
    {N : CochainComplex.Plus A}
    (ξ : (DerivedCategory.Plus.singleFunctor A 0).obj X ≅ DerivedCategory.Plus.Q.obj N)
    (a : (Stacks.DerivedIndexing.singlePlusFunctor A 0).obj X ⟶ N)
    (ha : ξ.hom = DerivedCategory.Plus.Q.map a) :
    ((F.mapDerivedCategoryPlusObjSingleIso X).symm ≪≫ F.mapDerivedCategoryPlus.mapIso ξ ≪≫
        (mapDerivedCategoryPlusQIso F).app N).hom =
      DerivedCategory.Plus.Q.map
        ((Stacks.EtaleCohomology.mapCochainComplexPlusSinglePlusIso F X).inv ≫
          F.mapCochainComplexPlus.map a) := by
  have hn := (mapDerivedCategoryPlusQIso F).hom.naturality a
  simp only [Functor.comp_map] at hn
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom, ha]
  exact (congrArg (fun t => _ ≫ t) hn).trans (((Category.assoc _ _ _).symm.trans
    (congrArg (fun t => t ≫ _)
      (mapDerivedCategoryPlusObjSingleIso_inv_comp_mapDerivedCategoryPlusQIso_hom F X))).trans
    (DerivedCategory.Plus.Q.map_comp _ _).symm)

end CategoryTheory.Functor

end
