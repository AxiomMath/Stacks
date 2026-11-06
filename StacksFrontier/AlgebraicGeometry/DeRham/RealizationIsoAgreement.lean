module

public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.RealizationShift
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSquareTransComposition
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomologyCompare
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso

/-!
# The two realization comparisons of Stacks 01F1 agree

Let `X` be a ringed space and `N` a bounded below complex of `𝒪_X`-modules. Stacks 01F1
identifies the hypercohomology of the underlying complex of abelian sheaves of `N` with its
hypercohomology computed in `𝒪_X`-modules, the module structure forgotten. The library carries
two constructions of that identification:

* `Stacks.Cech.Hypercohomology.realizationIso`, built in
  `StacksFrontier.AlgebraicGeometry.DeRham.RealizationComparison` from the comparison of the
  derived functors of the exact functor `toSheaf` and of `forget₂` with the functors they induce,
  and landing in the bounded below model of derived global sections; the de Rham first Chern
  class and the cup products of the de Rham cohomology files are transported along it;
* `Stacks.Cohomology.RealizationShift.realizationIsoAt`, built in
  `StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.RealizationShift` as a single natural
  transformation commuting with the shift, and landing in the unbounded model.

This file proves that they agree, once the bounded below model is read in the unbounded one
through `Stacks.Cohomology.DerivedSectionsModels.derivedSectionsFunctorIso`. The two differ in two
places: the comparison of the derived functor of an exact functor with the functor it induces is
spelled through `rightDerivedFunctorPlusIsoMapDerivedCategoryPlus` on one side and through the
units (`mapCochainComplexPlusDerivedUnit`, `RealizationShift.forgetComparisonIso`) on the other,
and the commutation of an exact functor with cohomology is built twice. Each pair is a pair of
descents of the same transformation through a localization, so they agree.

## Main results

* `Stacks.Cohomology.RealizationAgreement.realizationIso_hom_comp_derivedSectionsFunctorIso`:
  **the two realization comparisons agree.**
* `Stacks.Cohomology.RealizationAgreement.forgetComparisonIso_hom_app`,
  `Stacks.Cohomology.RealizationAgreement.toSheafQIso_hom_comp` and
  `Stacks.Cohomology.RealizationAgreement.mapDerivedCategoryHomologyIso_eq`: the agreement of
  their constituents.

## References

* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.Cohomology.Leray (AbelianSheaf sectionsFunctor)
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Cohomology.RealizationAgreement

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- Identities on both sides of a morphism, with every object a variable so that it applies across
two presentations of the same object. -/
private theorem comp_id_aux {C : Type*} [Category* C] {X Y : C} (a : X ⟶ Y) (i : Y ⟶ Y)
    (j : X ⟶ X) (k : X ⟶ X) (hi : i = 𝟙 _) (hj : j = 𝟙 _) (hk : k = 𝟙 _) :
    a ≫ i = k ≫ j ≫ a := by
  subst hi hj hk
  simp

/-- Two identities in front of a morphism, with every object a variable. -/
private theorem comp_id_aux' {C : Type*} [Category* C] {X Y : C} (a : X ⟶ Y) (j k : X ⟶ X)
    (hj : j = 𝟙 _) (hk : k = 𝟙 _) : j ≫ k ≫ a = a := by
  subst hj hk
  simp

/-- A naturality square pasted with a unit equation. -/
private theorem nat_aux {C : Type*} [Category* C] {P Q Q' R S S' : C} (a : P ⟶ Q) (u : Q ⟶ R)
    (rq : R ⟶ S) (θ : S ⟶ S') (θ' : R ⟶ Q') (mq : Q' ⟶ S') (φ : Q ⟶ Q')
    (hnat : rq ≫ θ = θ' ≫ mq) (hu : u ≫ θ' = φ) :
    (a ≫ u ≫ rq) ≫ θ = a ≫ φ ≫ mq := by
  rw [← hu, Category.assoc, Category.assoc, Category.assoc, hnat]

/-- The bookkeeping of `ι_map_mapCochainComplexPlusDerivedUnit_comp`, with every object and
morphism a variable so that it applies across two presentations of the same objects. -/
private theorem final_aux {C : Type*} [Category* C] {Oa Ob Oc Od : C} (x : Oa ⟶ Ob)
    (y : Ob ⟶ Oa) (y' : Oa ⟶ Ob) (fi : Ob ⟶ Oc) (fh : Oc ⟶ Ob) (tw tw' : Oc ⟶ Od) (z : Oa ⟶ Od)
    (zh : Od ⟶ Oa) (m : Ob ⟶ Ob) (yι : Ob ⟶ Oa) (hfi : fi ≫ fh = 𝟙 _) (hzz : zh ≫ z = 𝟙 _)
    (hy'y : y' ≫ y = 𝟙 _) (hxy : x ≫ yι = 𝟙 _) (hyι : yι = y)
    (h3 : fh = tw' ≫ zh ≫ y' ≫ m) (hm : m = 𝟙 _) (htw : tw = tw') : x ≫ fi ≫ tw = z := by
  subst hm htw hyι
  have e : fi ≫ tw = yι ≫ z := by
    calc fi ≫ tw = fi ≫ tw ≫ zh ≫ z := by rw [hzz, Category.comp_id]
      _ = (fi ≫ tw ≫ zh ≫ y' ≫ 𝟙 _) ≫ yι ≫ z := by
        simp only [Category.assoc, Category.id_comp, reassoc_of% hy'y]
      _ = yι ≫ z := by rw [← h3, hfi, Category.id_comp]
  rw [e, reassoc_of% hxy]


section Homology

variable {C₁ C₂ : Type*} [Category* C₁] [Category* C₂] [Abelian C₁] [Abelian C₂]
  (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- **The two copies of "an exact functor commutes with `Hⁿ`" agree**:
`StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso`, through which the
realization comparison of `StacksFrontier.AlgebraicGeometry.DeRham.RealizationComparison` is built,
and `CategoryTheory.Functor.mapDerivedCategoryHomologyIso`, through which
`Stacks.Cohomology.RealizationShift.realizationIsoAt` is built. Both are descents along `Q` of
`CategoryTheory.ShortComplex.mapHomologyIso`. -/
theorem mapDerivedCategoryHomologyIso_eq (n : ℤ) :
    StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso F n =
      F.mapDerivedCategoryHomologyIso n := by
  refine Iso.ext (Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ)) fun K => ?_)
  simp only [Functor.comp_obj, StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso,
    StacksDraft.DerivedCategoryHomology.mapHomologicalComplexHomologyIso,
    Localization.liftNatIso_hom, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Localization.liftNatTrans_app, Localization.Lifting.compLeft_iso,
    Iso.refl_hom, NatTrans.id_app, NatTrans.comp_app, Functor.associator_inv_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.whiskerLeft_app,
    Category.comp_id, Category.id_comp, Iso.refl_inv, Functor.mapDerivedCategoryHomologyIso,
    Functor.mapDerivedCategoryHomologyIsoAux, Functor.mapHomologicalComplexHomologyIso,
    Localization.Lifting.compRight_iso]
  rw [Functor.lifting_iso_mapDerivedCategory]
  simp only [ShortComplex.homologyFunctorIso]
  refine whisker_eq _ (whisker_eq _ ?_)
  exact (whisker_eq _ (Category.comp_id _)).symm

end Homology

/-- Identities interspersed in a composite, with every object and morphism a variable. -/
private theorem ids_aux {C : Type*} [Category* C] {O₀ O₁ O₂ O₃ O₄ O₅ : C} (a : O₀ ⟶ O₁)
    (b : O₁ ⟶ O₂) (c : O₂ ⟶ O₃) (d : O₃ ⟶ O₄) (e : O₄ ⟶ O₅) (i : O₃ ⟶ O₃) (j : O₅ ⟶ O₅)
    (f : O₅ ⟶ O₅) (hi : i = 𝟙 _) (hj : j = 𝟙 _) (hf : f = 𝟙 _) :
    a ≫ b ≫ c ≫ i ≫ d ≫ e ≫ j ≫ f = a ≫ b ≫ c ≫ d ≫ e := by
  subst hi hj hf
  simp

/-- The pasting of `realizationIso_hom_comp_derivedSectionsFunctorIso`, with every object and
morphism a variable. -/
private theorem paste_aux {C D : Type*} [Category* C] [Category* D] (H : C ⥤ D)
    {A₀ A₁ A₂ A₃ A₄ A₅ : C} {B₄ B₅ : D} (a₁ : A₀ ⟶ A₁) (a₂ : A₁ ⟶ A₂) (a₃ : A₂ ⟶ A₃)
    (a₄ : A₃ ⟶ A₄) (a₅ : A₄ ⟶ A₅) (h₁ : H.obj A₀ ⟶ H.obj A₁) (h₂ : H.obj A₁ ⟶ H.obj A₂)
    (h₃ : H.obj A₂ ⟶ H.obj A₃) (l : H.obj A₃ ⟶ B₄) (m : H.obj A₄ ⟶ B₄) (g : B₄ ⟶ B₅)
    (m' : H.obj A₅ ⟶ B₅) (h₄ : H.obj A₃ ⟶ H.obj A₄) (e₁ : h₁ = H.map a₁) (e₂ : h₂ = H.map a₂)
    (e₃ : h₃ = H.map a₃) (e₄ : h₄ = H.map a₄) (el : l = h₄ ≫ m)
    (hnat : m ≫ g = H.map a₅ ≫ m') :
    (h₁ ≫ h₂ ≫ h₃ ≫ l) ≫ g = H.map (a₁ ≫ a₂ ≫ a₃ ≫ a₄ ≫ a₅) ≫ m' := by
  subst e₁ e₂ e₃ e₄ el
  simp only [Category.assoc, hnat, Functor.map_comp]

section Forget

variable (R : Type u) [Ring R]

/-- **The comparison of the derived functor of `forget₂ : Mod(R) ⥤ Ab` with the functor it induces
on derived categories**: `RealizationShift.forgetComparisonIso` is
`rightDerivedFunctorPlusIsoMapDerivedCategoryPlus`, read in the unbounded derived category. Both
are transformations out of a right derived functor and agree after its unit. -/
theorem forgetComparisonIso_hom_app (Y : DerivedCategory.Plus (ModuleCat.{u} R)) :
    (Stacks.Cohomology.RealizationShift.forgetComparisonIso R).hom.app Y =
      DerivedCategory.Plus.ι.map
        ((forget₂ (ModuleCat.{u} R)
          AddCommGrpCat.{u}).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom.app Y) := by
  let γ : (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.ι ⟶
      DerivedCategory.Plus.ι ⋙ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapDerivedCategory :=
    Functor.whiskerRight
      (forget₂ (ModuleCat.{u} R)
        AddCommGrpCat.{u}).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom
      DerivedCategory.Plus.ι
  have h : (Stacks.Cohomology.RealizationShift.forgetComparisonIso R).hom = γ := by
    refine Functor.rightDerived_ext _ (Stacks.Cohomology.RealizationShift.forgetPlusUnit R)
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{u} R)) _ _ _ ?_
    rw [Stacks.Cohomology.RealizationShift.forgetComparisonIso_fac]
    ext K
    have hu := Functor.unit_comp_rightDerivedFunctorPlusIsoMapDerivedCategoryPlus_hom_app
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) K
    simp only [Stacks.Cohomology.RealizationShift.forgetUnbUnit,
      Stacks.Cohomology.RealizationShift.forgetPlusUnit, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, γ, Category.assoc,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp]
    show _ = _ ≫ DerivedCategory.Plus.ι.map _ ≫ DerivedCategory.Plus.ι.map
      ((forget₂ (ModuleCat.{u} R)
        AddCommGrpCat.{u}).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom.app
          (DerivedCategory.Plus.Qh.obj K))
    rw [← Functor.map_comp, hu]
    simp only [Functor.comp_obj, ObjectProperty.ι_obj, RealizationShift.plusQhCompιIso,
      ObjectProperty.liftCompιIso, Iso.refl_inv, NatTrans.id_app, ObjectProperty.lift_obj_obj,
      Category.comp_id, RealizationShift.presentationIso, RealizationShift.mapPlusCompιIso,
      Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      NatTrans.comp_app, Functor.associator_inv_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.whiskerLeft_app, Category.id_comp, ObjectProperty.ι_map,
      Category.assoc]
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.comp_id,
      Category.id_comp]
    rfl
  exact NatTrans.congr_app h Y

end Forget

section Exact

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B] [EnoughInjectives A]
  (T : A ⥤ B) [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]

omit [EnoughInjectives A] in
/-- The identification `Q⁺ ≅ quotient⁺ ⋙ Qh⁺` of the localizations of bounded below complexes,
read in the unbounded derived category, is the identification `Q ≅ quotient ⋙ Qh`. -/
theorem ι_map_plusQuotientCompQhIso_hom_app (K : CochainComplex.Plus A) :
    DerivedCategory.Plus.ι.map ((DerivedCategory.Plus.quotientCompQhIso A).hom.app K) =
      (DerivedCategory.quotientCompQhIso A).hom.app K.obj := by
  simp [DerivedCategory.Plus.quotientCompQhIso]

/-- **The unit of the derived functor of an exact functor, followed by the comparison with the
functor it induces**, read in the unbounded derived category, is the factorization of the induced
functor through the localization. -/
theorem ι_map_mapCochainComplexPlusDerivedUnit_comp (K : CochainComplex.Plus A) :
    DerivedCategory.Plus.ι.map ((Functor.mapCochainComplexPlusDerivedUnit T).app K ≫
        T.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom.app
          (DerivedCategory.Plus.Q.obj K)) =
      T.mapDerivedCategoryFactors.inv.app K.obj := by
  have hnat := T.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom.naturality
    ((DerivedCategory.Plus.quotientCompQhIso A).hom.app K)
  have hu := Functor.unit_comp_rightDerivedFunctorPlusIsoMapDerivedCategoryPlus_hom_app T
    ((HomotopyCategory.Plus.quotient A).obj K)
  have h1 : (Functor.mapCochainComplexPlusDerivedUnit T).app K ≫
      T.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom.app (DerivedCategory.Plus.Q.obj K) =
      (DerivedCategory.Plus.quotientCompQhIso B).inv.app (T.mapCochainComplexPlus.obj K) ≫
        T.mapDerivedCategoryPlusFactorsh.inv.app ((HomotopyCategory.Plus.quotient A).obj K) ≫
        T.mapDerivedCategoryPlus.map ((DerivedCategory.Plus.quotientCompQhIso A).hom.app K) :=
    nat_aux _ _ _ _ _ _ _ hnat hu
  have h3 := T.mapDerivedCategoryFactorsh_hom_app K.obj
  have h4 := ι_map_plusQuotientCompQhIso_hom_app K
  have h5 := ι_map_plusQuotientCompQhIso_hom_app (T.mapCochainComplexPlus.obj K)
  have hxy : DerivedCategory.Plus.ι.map
      ((DerivedCategory.Plus.quotientCompQhIso B).inv.app (T.mapCochainComplexPlus.obj K)) ≫
      DerivedCategory.Plus.ι.map
        ((DerivedCategory.Plus.quotientCompQhIso B).hom.app (T.mapCochainComplexPlus.obj K)) =
        𝟙 _ :=
    (Functor.map_comp _ _ _).symm.trans ((congrArg DerivedCategory.Plus.ι.map
      (Iso.inv_hom_id_app _ _)).trans (CategoryTheory.Functor.map_id _ _))
  have hm : DerivedCategory.Qh.map
      ((T.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K.obj) = 𝟙 _ :=
    CategoryTheory.Functor.map_id _ _
  refine (congrArg DerivedCategory.Plus.ι.map h1).trans ?_
  refine (Functor.map_comp _ _ _).trans ((whisker_eq _ (Functor.map_comp _ _ _)).trans ?_)
  exact final_aux _ _ _ _ _ _ _ _ _ _ _ (Iso.inv_hom_id_app _ _) (Iso.hom_inv_id_app _ _)
    (Iso.inv_hom_id_app _ _) hxy h5 h3 hm
    (congrArg (fun g => T.mapDerivedCategory.map g) h4)

end Exact

section Agreement

variable (X : RingedSpace.{u, u})

/-- The comparison `Stacks.Cech.Hypercohomology.toSheafQIso` is the unit of the derived functor of
`toSheaf` followed by the comparison of that derived functor with the induced functor. -/
theorem toSheafQIso_hom_eq :
    (Stacks.Cech.Hypercohomology.toSheafQIso X).hom =
      Functor.mapCochainComplexPlusDerivedUnit (SheafOfModules.toSheaf (structureSheafRing X)) ≫
        Functor.whiskerLeft DerivedCategory.Plus.Q
          (SheafOfModules.toSheaf
            (structureSheafRing X)).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom := by
  refine NatTrans.ext (funext fun N => DerivedCategory.Plus.ι.map_injective ?_)
  refine (Stacks.Cohomology.HigherDirectImagePresheaf.map_fullyFaithfulCancelRight_hom_app
    DerivedCategory.Plus.ι _ N).trans ?_
  exact (ι_map_mapCochainComplexPlusDerivedUnit_comp _ N).symm

/-- The abelian half of the two realization comparisons agree. -/
theorem toSheafQIso_hom_comp :
    (Stacks.Cech.Hypercohomology.toSheafQIso X).hom ≫
        Functor.whiskerLeft DerivedCategory.Plus.Q
          (SheafOfModules.toSheaf
            (structureSheafRing X)).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.inv =
      Functor.mapCochainComplexPlusDerivedUnit (SheafOfModules.toSheaf (structureSheafRing X)) := by
  rw [toSheafQIso_hom_eq, Category.assoc, ← Functor.whiskerLeft_comp, Iso.hom_inv_id,
    Functor.whiskerLeft_id', Category.comp_id]

/-- **The components of `RealizationShift.realizationTotal`**, in the factors of
`Stacks.Cech.Hypercohomology.realizationNatIso`. -/
theorem realizationTotal_app (N : CochainComplex.Plus (SheafOfModules.{u} (structureSheafRing X))) :
    (Stacks.Cohomology.RealizationShift.realizationTotal X).app N =
      DerivedCategory.Plus.ι.map ((sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus.map
          ((Stacks.Cech.Hypercohomology.toSheafQIso X).hom.app N)) ≫
        DerivedCategory.Plus.ι.map ((sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus.map
          ((SheafOfModules.toSheaf
            (structureSheafRing X)).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.inv.app
              (DerivedCategory.Plus.Q.obj N))) ≫
        DerivedCategory.Plus.ι.map
          ((Stacks.Cohomology.ModuleComparison.rightDerivedFunctorPlus_sections_forget_iso
            X ⊤).inv.app (DerivedCategory.Plus.Q.obj N)) ≫
        DerivedCategory.Plus.ι.map
          ((forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤)))
            AddCommGrpCat.{u}).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom.app
              ((SheafOfModules.evaluation (structureSheafRing X) (op ⊤)).rightDerivedFunctorPlus.obj
                (DerivedCategory.Plus.Q.obj N))) ≫
        (forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤)))
          AddCommGrpCat.{u}).mapDerivedCategory.map
          ((Stacks.Cohomology.DerivedSectionsModels.boundedDerivedSectionsIso X ⊤).hom.app
            (DerivedCategory.Plus.Q.obj N)) := by
  have hT := NatTrans.congr_app (toSheafQIso_hom_comp X) N
  have hF := forgetComparisonIso_hom_app ((structureSheafRing X).obj.obj (op ⊤))
    ((SheafOfModules.evaluation (structureSheafRing X) (op ⊤)).rightDerivedFunctorPlus.obj
      (DerivedCategory.Plus.Q.obj N))
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hT
  simp only [Stacks.Cohomology.RealizationShift.realizationTotal,
    Stacks.Cohomology.RealizationShift.realizationAbelianPart,
    Stacks.Cohomology.RealizationShift.realizationModulePart,
    Stacks.Cohomology.RealizationShift.realizationLocalizationPart,
    Stacks.Cohomology.RealizationShift.realizationTrans, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Functor.map_comp,
    CategoryTheory.Functor.map_id, Category.assoc, ← hT, ← hF]
  have hpq : (forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤)))
      AddCommGrpCat.{u}).mapDerivedCategory.map
        ((Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen X ⊤).map
          ((Stacks.Cohomology.RealizationShift.plusQCompιIso
            (SheafOfModules.{u} (structureSheafRing X))).hom.app N)) = 𝟙 _ :=
    (congrArg _ (CategoryTheory.Functor.map_id _ _)).trans (CategoryTheory.Functor.map_id _ _)
  exact ids_aux _ _ _ _ _ _ _ _ rfl rfl hpq

/-- **The two realization comparisons of Stacks 01F1 agree**: the comparison
`Stacks.Cech.Hypercohomology.realizationIso` of
`StacksFrontier.AlgebraicGeometry.DeRham.RealizationComparison`, read in the unbounded model of
derived global sections through
`Stacks.Cohomology.DerivedSectionsModels.derivedSectionsFunctorIso`, is the comparison
`Stacks.Cohomology.RealizationShift.realizationIsoAt`, which commutes with the shift. -/
theorem realizationIso_hom_comp_derivedSectionsFunctorIso
    (N : CochainComplex.Plus (SheafOfModules.{u} (structureSheafRing X))) (n : ℤ) :
    (Stacks.Cech.Hypercohomology.realizationIso X N n).hom ≫
        (forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) AddCommGrpCat.{u}).map
          ((DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) n).map
            ((Stacks.Cohomology.DerivedSectionsModels.derivedSectionsFunctorIso X ⊤).hom.app N)) =
      (Stacks.Cohomology.RealizationShift.realizationIsoAt X N n).hom := by
  have hnat := (Functor.mapDerivedCategoryHomologyIso
    (forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤)))
      AddCommGrpCat.{u}) n).hom.naturality
      ((Stacks.Cohomology.DerivedSectionsModels.boundedDerivedSectionsIso X ⊤).hom.app
        (DerivedCategory.Plus.Q.obj N))
  have he := mapDerivedCategoryHomologyIso_eq
    (forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) AddCommGrpCat.{u}) n
  show _ = (DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map
      ((Stacks.Cohomology.RealizationShift.realizationTotal X).app N) ≫ _
  rw [realizationTotal_app]
  simp only [Stacks.Cech.Hypercohomology.realizationIso,
    Stacks.Cech.Hypercohomology.realizationNatIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Iso.symm_hom, Iso.app_hom,
    Stacks.Cech.Hypercohomology.forgetPlusHomologyIso, he]
  exact paste_aux (DerivedCategory.homologyFunctor AddCommGrpCat.{u} n) _ _ _ _ _ _ _ _ _ _ _ _ _
    rfl rfl rfl rfl rfl hnat.symm

end Agreement

end Stacks.Cohomology.RealizationAgreement

end
