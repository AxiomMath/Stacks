module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalarsDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionComparisonAssoc

/-!
# The derived unit of direct image and restriction of scalars

The comparison `Rf_* ∘ res_ρ ≅ res_ρ ∘ Rf_*` of
`Stacks.EtaleCohomology.etaleModuleDerivedDirectImageRestrictScalars` is compatible with the
canonical maps `Q(f_* N) ⟶ Rf_*(Q N)` from the termwise direct image of a bounded below complex
to its derived direct image.  This is what makes the comparison of compactly supported
cohomology with coefficients `Λ'` and `Λ` compatible with the geometric Frobenius.

## References

* [Stacks Project, Tag 03V2](https://stacks.math.columbia.edu/tag/03V2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable {Λ Λ' : Type} [Ring Λ] [Ring Λ'] (ρ : Λ →+* Λ')

/-- The restriction comparison of derived direct images after the unit, on the bounded below
homotopy category: `res_ρ` of the unit of `Rf_*` at `K`, followed by the comparison, is the unit
of `Rf_*` at `res_ρ K`, up to the factorizations of the derived actions of `res_ρ`. -/
theorem restrictScalars_directImage_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : HomotopyCategory.Plus (EtaleModules.{u, 0} Λ' X)) :
    (etaleModuleRestrictScalars ρ Y).mapDerivedCategoryPlus.map
        ((etaleModuleDirectImage.{u, 0} Λ' f).rightDerivedFunctorPlusUnith.app K) ≫
      (etaleModuleDerivedDirectImageRestrictScalars ρ f).hom.app (DerivedCategory.Plus.Qh.obj K) =
    (etaleModuleRestrictScalars ρ Y).mapDerivedCategoryPlusFactorsh.hom.app
        ((etaleModuleDirectImage.{u, 0} Λ' f).mapHomotopyCategoryPlus.obj K) ≫
      (etaleModuleDirectImage.{u, 0} Λ f).rightDerivedFunctorPlusUnith.app
        ((etaleModuleRestrictScalars ρ X).mapHomotopyCategoryPlus.obj K) ≫
      (etaleModuleDerivedDirectImage.{u, 0} Λ f).map
        ((etaleModuleRestrictScalars ρ X).mapDerivedCategoryPlusFactorsh.inv.app K) := by
  have hid : (Functor.mapHomotopyCategoryPlusCompIso
        (Iso.refl (etaleModuleDirectImage.{u, 0} Λ' f ⋙
          etaleModuleRestrictScalars ρ Y))).hom.app K ≫
      (Functor.mapHomotopyCategoryPlusNatIso
        (etaleModuleDirectImageRestrictScalars ρ f)).hom.app K ≫
      (Functor.mapHomotopyCategoryPlusCompIso
        (Iso.refl (etaleModuleRestrictScalars ρ X ⋙ etaleModuleDirectImage.{u, 0} Λ f))).inv.app K =
      𝟙 _ := by
    rw [Functor.mapHomotopyCategoryPlusCompIso_refl_hom_app,
      show (Functor.mapHomotopyCategoryPlusNatIso
          (etaleModuleDirectImageRestrictScalars ρ f)).hom.app K = 𝟙 _ from
        Functor.mapHomotopyCategoryPlusNatIso_refl_hom_app _ K,
      Functor.mapHomotopyCategoryPlusCompIso_refl_inv_app]
    exact (Category.id_comp _).trans (Category.id_comp _)
  exact (Functor.map_unit_comp_rightDerivedRestrictionIso_hom_app _ _ _ _
    (etaleModuleDirectImageRestrictScalars ρ f)
    (fun I _ => rightAcyclic_directImage_of_isAcyclicEverywhere f _
      (isAcyclicEverywhere_restrictScalars' ρ I)) K).trans (whisker_eq _
    (Eq.trans (eq_whisker ((congrArg DerivedCategory.Plus.Qh.map hid).trans
      (DerivedCategory.Plus.Qh.map_id _)) _) (Category.id_comp _)))

/-- The inverse of the comparison `Q ⋙ F⁺ ≅ F ⋙ Q` at `N`, in terms of the factorizations through
the bounded below homotopy category. -/
private theorem mapDerivedCategoryPlusQIso_inv_app_eq {A B : Type*} [Category* A] [Category* B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B] (F : A ⥤ B)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (N : CochainComplex.Plus A) :
    (Functor.mapDerivedCategoryPlusQIso F).inv.app N =
      ((DerivedCategory.Plus.quotientCompQhIso B).app (F.mapCochainComplexPlus.obj N)).inv ≫
        F.mapDerivedCategoryPlusFactorsh.inv.app ((HomotopyCategory.Plus.quotient A).obj N) ≫
        F.mapDerivedCategoryPlus.map ((DerivedCategory.Plus.quotientCompQhIso A).app N).hom := by
  simp only [Functor.mapDerivedCategoryPlusQIso, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Iso.symm_inv, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.assoc,
    Functor.mapHomotopyCategoryPlusFactors_inv_app]
  exact whisker_eq _ ((eq_whisker (DerivedCategory.Plus.Qh.map_id _) _).trans
    (Category.id_comp _))

/-- **The derived unit of direct image commutes with `res_ρ`**: `res_ρ` of the comparison
`Q(f_* N) ⟶ Rf_*(Q N)` is the comparison for `res_ρ N`, under `Rf_* ∘ res_ρ ≅ res_ρ ∘ Rf_*`
and the commutation of `Q` with `res_ρ`. -/
theorem restrictScalars_directImage_derivedUnit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : CochainComplex.Plus (EtaleModules.{u, 0} Λ' X)) :
    (Functor.mapDerivedCategoryPlusQIso (etaleModuleRestrictScalars ρ Y)).inv.app
        ((etaleModuleDirectImage.{u, 0} Λ' f).mapCochainComplexPlus.obj N) ≫
      (etaleModuleRestrictScalars ρ Y).mapDerivedCategoryPlus.map
        ((etaleModuleDirectImage.{u, 0} Λ' f).mapCochainComplexPlusDerivedUnit.app N) ≫
      (etaleModuleDerivedDirectImageRestrictScalars ρ f).hom.app (DerivedCategory.Plus.Q.obj N) =
    (etaleModuleDirectImage.{u, 0} Λ f).mapCochainComplexPlusDerivedUnit.app
        ((etaleModuleRestrictScalars ρ X).mapCochainComplexPlus.obj N) ≫
      (etaleModuleDerivedDirectImage.{u, 0} Λ f).map
        ((Functor.mapDerivedCategoryPlusQIso (etaleModuleRestrictScalars ρ X)).inv.app N) := by
  let rX := etaleModuleRestrictScalars ρ X
  let rY := etaleModuleRestrictScalars ρ Y
  let f' := etaleModuleDirectImage.{u, 0} Λ' f
  let fΛ := etaleModuleDirectImage.{u, 0} Λ f
  let qX' := (DerivedCategory.Plus.quotientCompQhIso (EtaleModules.{u, 0} Λ' X)).app N
  let qY' := (DerivedCategory.Plus.quotientCompQhIso (EtaleModules.{u, 0} Λ' Y)).app
    (f'.mapCochainComplexPlus.obj N)
  let qX := (DerivedCategory.Plus.quotientCompQhIso (EtaleModules.{u, 0} Λ X)).app
    (rX.mapCochainComplexPlus.obj N)
  let qY := (DerivedCategory.Plus.quotientCompQhIso (EtaleModules.{u, 0} Λ Y)).app
    (rY.mapCochainComplexPlus.obj (f'.mapCochainComplexPlus.obj N))
  let K := (HomotopyCategory.Plus.quotient _).obj N
  have hQY := mapDerivedCategoryPlusQIso_inv_app_eq rY (f'.mapCochainComplexPlus.obj N)
  have hQX := mapDerivedCategoryPlusQIso_inv_app_eq rX N
  have hdu' : f'.mapCochainComplexPlusDerivedUnit.app N =
      qY'.inv ≫ f'.rightDerivedFunctorPlusUnith.app K ≫ f'.rightDerivedFunctorPlus.map qX'.hom :=
    rfl
  have hdu : fΛ.mapCochainComplexPlusDerivedUnit.app (rX.mapCochainComplexPlus.obj N) =
      qY.inv ≫ fΛ.rightDerivedFunctorPlusUnith.app (rX.mapHomotopyCategoryPlus.obj K) ≫
        fΛ.rightDerivedFunctorPlus.map qX.hom :=
    rfl
  have s1 : rY.mapDerivedCategoryPlus.map qY'.hom ≫
      rY.mapDerivedCategoryPlus.map (f'.mapCochainComplexPlusDerivedUnit.app N) =
      rY.mapDerivedCategoryPlus.map (f'.rightDerivedFunctorPlusUnith.app K) ≫
        rY.mapDerivedCategoryPlus.map (f'.rightDerivedFunctorPlus.map qX'.hom) := by
    rw [hdu', ← Functor.map_comp, Iso.hom_inv_id_assoc]
    exact rY.mapDerivedCategoryPlus.map_comp _ _
  have s2 : rY.mapDerivedCategoryPlus.map (f'.rightDerivedFunctorPlus.map qX'.hom) ≫
      (etaleModuleDerivedDirectImageRestrictScalars ρ f).hom.app (DerivedCategory.Plus.Q.obj N) =
      (etaleModuleDerivedDirectImageRestrictScalars ρ f).hom.app (DerivedCategory.Plus.Qh.obj K) ≫
        fΛ.rightDerivedFunctorPlus.map (rX.mapDerivedCategoryPlus.map qX'.hom) :=
    (etaleModuleDerivedDirectImageRestrictScalars ρ f).hom.naturality qX'.hom
  have s3 := restrictScalars_directImage_unit ρ f K
  rw [hQY, hQX, hdu]
  have L : (rY.mapDerivedCategoryPlusFactorsh.inv.app (f'.mapHomotopyCategoryPlus.obj K) ≫
          rY.mapDerivedCategoryPlus.map qY'.hom) ≫
        rY.mapDerivedCategoryPlus.map (f'.mapCochainComplexPlusDerivedUnit.app N) ≫
          (etaleModuleDerivedDirectImageRestrictScalars ρ f).hom.app
            (DerivedCategory.Plus.Q.obj N) =
      fΛ.rightDerivedFunctorPlusUnith.app (rX.mapHomotopyCategoryPlus.obj K) ≫
        fΛ.rightDerivedFunctorPlus.map (rX.mapDerivedCategoryPlusFactorsh.inv.app K) ≫
        fΛ.rightDerivedFunctorPlus.map (rX.mapDerivedCategoryPlus.map qX'.hom) := by
    let a := rY.mapDerivedCategoryPlusFactorsh.inv.app (f'.mapHomotopyCategoryPlus.obj K)
    let b := rY.mapDerivedCategoryPlus.map qY'.hom
    let c := rY.mapDerivedCategoryPlus.map (f'.mapCochainComplexPlusDerivedUnit.app N)
    let d := (etaleModuleDerivedDirectImageRestrictScalars ρ f).hom.app
      (DerivedCategory.Plus.Q.obj N)
    let u' := rY.mapDerivedCategoryPlus.map (f'.rightDerivedFunctorPlusUnith.app K)
    let x := rY.mapDerivedCategoryPlus.map (f'.rightDerivedFunctorPlus.map qX'.hom)
    let θK := (etaleModuleDerivedDirectImageRestrictScalars ρ f).hom.app
      (DerivedCategory.Plus.Qh.obj K)
    let y := fΛ.rightDerivedFunctorPlus.map (rX.mapDerivedCategoryPlus.map qX'.hom)
    let e := rY.mapDerivedCategoryPlusFactorsh.hom.app (f'.mapHomotopyCategoryPlus.obj K)
    let v := fΛ.rightDerivedFunctorPlusUnith.app (rX.mapHomotopyCategoryPlus.obj K)
    let w := fΛ.rightDerivedFunctorPlus.map (rX.mapDerivedCategoryPlusFactorsh.inv.app K)
    have t1 : (a ≫ b) ≫ c ≫ d = a ≫ (b ≫ c) ≫ d :=
      (Category.assoc a b (c ≫ d)).trans (congrArg (a ≫ ·) (Category.assoc b c d).symm)
    have t2 : a ≫ (b ≫ c) ≫ d = a ≫ u' ≫ x ≫ d :=
      congrArg (a ≫ ·) ((congrArg (· ≫ d) s1).trans (Category.assoc u' x d))
    have t3 : a ≫ u' ≫ x ≫ d = a ≫ (u' ≫ θK) ≫ y :=
      congrArg (a ≫ ·) ((congrArg (u' ≫ ·) s2).trans (Category.assoc u' θK y).symm)
    have t4 : a ≫ (u' ≫ θK) ≫ y = (a ≫ e) ≫ v ≫ w ≫ y :=
      (congrArg (a ≫ ·) ((congrArg (· ≫ y) s3).trans
        ((Category.assoc e (v ≫ w) y).trans (congrArg (e ≫ ·) (Category.assoc v w y))))).trans
        (Category.assoc a e (v ≫ w ≫ y)).symm
    have t5 : a ≫ e = 𝟙 _ := Iso.inv_hom_id_app _ _
    exact t1.trans (t2.trans (t3.trans (t4.trans ((congrArg (· ≫ v ≫ w ≫ y) t5).trans
      (Category.id_comp _)))))
  have R : (fΛ.rightDerivedFunctorPlusUnith.app (rX.mapHomotopyCategoryPlus.obj K) ≫
        fΛ.rightDerivedFunctorPlus.map qX.hom) ≫
      fΛ.rightDerivedFunctorPlus.map (qX.inv ≫
          rX.mapDerivedCategoryPlusFactorsh.inv.app K ≫ rX.mapDerivedCategoryPlus.map qX'.hom) =
      fΛ.rightDerivedFunctorPlusUnith.app (rX.mapHomotopyCategoryPlus.obj K) ≫
        fΛ.rightDerivedFunctorPlus.map (rX.mapDerivedCategoryPlusFactorsh.inv.app K) ≫
        fΛ.rightDerivedFunctorPlus.map (rX.mapDerivedCategoryPlus.map qX'.hom) := by
    refine (Category.assoc _ _ _).trans (whisker_eq _ ?_)
    refine (whisker_eq _ (fΛ.rightDerivedFunctorPlus.map_comp _ _)).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (eq_whisker ((fΛ.rightDerivedFunctorPlus.map_comp _ _).symm.trans
      ((congrArg fΛ.rightDerivedFunctorPlus.map qX.hom_inv_id).trans
        (fΛ.rightDerivedFunctorPlus.map_id _))) _).trans ((Category.id_comp _).trans ?_)
    exact fΛ.rightDerivedFunctorPlus.map_comp _ _
  exact (Category.assoc _ _ _).trans ((congrArg (qY.inv ≫ ·) L).trans
    ((congrArg (qY.inv ≫ ·) R.symm).trans (Category.assoc _ _ _).symm))

/-- On bounded below homotopy categories, `res_ρ` carries the coherence isomorphism of a
composite of direct images to that of the composite for `res_ρ` of the complex. -/
theorem restrictScalars_mapH_compIso_inv_app {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) (K : HomotopyCategory.Plus (EtaleModules.{u, 0} Λ' X)) :
    (etaleModuleRestrictScalars ρ Z).mapHomotopyCategoryPlus.map
        ((Functor.mapHomotopyCategoryPlusCompIso
          (etaleModuleDirectImageComp.{u, 0} Λ' f g fg hfg)).inv.app K) =
      (Functor.mapHomotopyCategoryPlusCompIso
          (etaleModuleDirectImageComp.{u, 0} Λ f g fg hfg)).inv.app
        ((etaleModuleRestrictScalars ρ X).mapHomotopyCategoryPlus.obj K) := by
  obtain ⟨L, rfl⟩ := HomotopyCategory.Plus.quotient_obj_surjective K
  apply (HomotopyCategory.Plus.ι _).map_injective
  rfl

/-- The derived functor of `T ⋙ r` for an exact `r`, transported to `RT ⋙ r⁺`, after the unit:
it is `r⁺` of the unit of `RT`, up to the factorization of `r⁺`. -/
theorem unit_comp_compExact_app {A B C : Type*} [Category* A] [Category* B] [Category* C]
    [Abelian A] [Abelian B] [Abelian C] [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [EnoughInjectives A] [EnoughInjectives B]
    (T : A ⥤ B) (r : B ⥤ C) [T.Additive] [r.Additive] [PreservesFiniteLimits r]
    [PreservesFiniteColimits r] (K : HomotopyCategory.Plus A) :
    (T ⋙ r).rightDerivedFunctorPlusUnith.app K ≫
        (Functor.rightDerivedFunctorPlusComp T r).app (DerivedCategory.Plus.Qh.obj K) ≫
        (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus r).hom.app
          (T.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj K)) =
      r.mapDerivedCategoryPlusFactorsh.inv.app (T.mapHomotopyCategoryPlus.obj K) ≫
        r.mapDerivedCategoryPlus.map (T.rightDerivedFunctorPlusUnith.app K) := by
  have hT := Functor.rightDerivedFunctorPlusComp_fac_app T r K
  have hM := Functor.unit_comp_rightDerivedFunctorPlusIsoMapDerivedCategoryPlus_hom_app r
    (T.mapHomotopyCategoryPlus.obj K)
  have hMn : r.rightDerivedFunctorPlus.map (T.rightDerivedFunctorPlusUnith.app K) ≫
      (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus r).hom.app
        (T.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj K)) =
      (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus r).hom.app
        (DerivedCategory.Plus.Qh.obj (T.mapHomotopyCategoryPlus.obj K)) ≫
      r.mapDerivedCategoryPlus.map (T.rightDerivedFunctorPlusUnith.app K) :=
    (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus r).hom.naturality _
  refine (Category.assoc _ _ _).symm.trans ((eq_whisker hT _).trans ?_)
  refine (Category.assoc _ _ _).trans (Functor.qhMapCompIsoReflInv_comp T r K _ |>.trans ?_)
  refine (Category.assoc _ _ _).trans ((whisker_eq _ hMn).trans ?_)
  exact (Category.assoc _ _ _).symm.trans (eq_whisker hM _)

end Stacks.EtaleCohomology

end
