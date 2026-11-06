module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RightDerivedRestrictionUnit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalarsDerivedUnit

/-!
# `RΓ(S, Rf_* -)` and restriction of scalars on the termwise image of a complex

Let `ρ : Λ →+* Λ'` and `f : Y ⟶ S`.  The canonical maps `Q(Γ(S, f_* N)) ⟶ RΓ(S, Rf_*(Q N))`
for a bounded below complex `N` (the derived unit of `f_*` followed by that of `Γ(S, -)`) are
natural in `N`, and compatible with the comparisons
`RΓ(S, Rf_* -) ∘ res_ρ ≅ res_ρ ∘ RΓ(S, Rf_* -)` of
`Stacks.EtaleCohomology.etaleModuleDerivedDirectImageRestrictScalars` and
`Stacks.EtaleCohomology.etaleModuleDerivedGlobalSectionsRestrictScalars`.

So, on complexes of injective sheaves, where those canonical maps are isomorphisms, the
comparison is read off termwise.

## Main definitions

* `Stacks.EtaleCohomology.directImageSectionsDerivedUnit`: `Q(Γ(S, f_* N)) ⟶ RΓ(S, Rf_*(Q N))`.

## Main results

* `Stacks.EtaleCohomology.restrictScalars_directImageSectionsDerivedUnit`: the compatibility with
  restriction of scalars.

## References

* [Stacks Project, Tag 03V2](https://stacks.math.columbia.edu/tag/03V2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section Unit

variable (Λ : Type) [Ring Λ] {Y S : Scheme.{u}} (f : Y ⟶ S)

/-- The canonical map `Q(Γ(S, f_* N)) ⟶ RΓ(S, Rf_*(Q N))` for a bounded below complex `N`:
the derived unit of `Γ(S, -)` at `f_* N` followed by `RΓ(S, -)` of the derived unit of
`f_*` at `N`. -/
def directImageSectionsDerivedUnit :
    (etaleModuleDirectImage.{u, 0} Λ f).mapCochainComplexPlus ⋙
        (etaleModuleGlobalSections.{u, 0} Λ S).mapCochainComplexPlus ⋙
        DerivedCategory.Plus.Q ⟶
      DerivedCategory.Plus.Q ⋙ etaleModuleDerivedDirectImage.{u, 0} Λ f ⋙
        etaleModuleDerivedGlobalSections.{u, 0} Λ S :=
  Functor.whiskerLeft (etaleModuleDirectImage.{u, 0} Λ f).mapCochainComplexPlus
      (etaleModuleGlobalSections.{u, 0} Λ S).mapCochainComplexPlusDerivedUnit ≫
    Functor.whiskerRight (etaleModuleDirectImage.{u, 0} Λ f).mapCochainComplexPlusDerivedUnit
      (etaleModuleDerivedGlobalSections.{u, 0} Λ S)

/-- The component of `directImageSectionsDerivedUnit` at `N` is the derived unit of `Γ(S, -)` at
`f_* N` followed by `RΓ(S, -)` of the derived unit of `f_*` at `N`. -/
theorem directImageSectionsDerivedUnit_app (N : CochainComplex.Plus (EtaleModules.{u, 0} Λ Y)) :
    (directImageSectionsDerivedUnit Λ f).app N =
      (etaleModuleGlobalSections.{u, 0} Λ S).mapCochainComplexPlusDerivedUnit.app
          ((etaleModuleDirectImage.{u, 0} Λ f).mapCochainComplexPlus.obj N) ≫
        (etaleModuleDerivedGlobalSections.{u, 0} Λ S).map
          ((etaleModuleDirectImage.{u, 0} Λ f).mapCochainComplexPlusDerivedUnit.app N) :=
  rfl

/-- The derived unit of an additive functor is invertible on a bounded below complex of objects
right acyclic for it (Leray's acyclicity lemma, [Stacks, Tag 015E]). -/
theorem isIso_mapCochainComplexPlusDerivedUnit_app_of_rightAcyclic {A B : Type*} [Category* A]
    [Category* B] [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    [EnoughInjectives A] (T : A ⥤ B) [T.Additive] (K : CochainComplex.Plus A)
    (hK : ∀ n, T.rightAcyclic (K.obj.X n)) :
    IsIso (T.mapCochainComplexPlusDerivedUnit.app K) := by
  have hu : IsIso (T.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient A).obj K)) :=
    T.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic _ hK
  rw [Functor.mapCochainComplexPlusDerivedUnit_app]
  have h₃ : IsIso (T.rightDerivedFunctorPlus.map
      ((DerivedCategory.Plus.quotientCompQhIso A).hom.app K)) := inferInstance
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance (@IsIso.comp_isIso _ _ _ _ _ _ _ hu h₃)

/-- The canonical map at `N` is invertible when the terms of `N` are right acyclic for `f_*` and
their direct images are right acyclic for `Γ(S, -)`. -/
private theorem isIso_directImageSectionsDerivedUnit_app_of_rightAcyclic
    (N : CochainComplex.Plus (EtaleModules.{u, 0} Λ Y))
    (h₁ : ∀ n, (etaleModuleDirectImage.{u, 0} Λ f).rightAcyclic (N.obj.X n))
    (h₂ : ∀ n, (etaleModuleGlobalSections.{u, 0} Λ S).rightAcyclic
      ((etaleModuleDirectImage.{u, 0} Λ f).obj (N.obj.X n))) :
    IsIso ((directImageSectionsDerivedUnit Λ f).app N) := by
  have := isIso_mapCochainComplexPlusDerivedUnit_app_of_rightAcyclic _ N h₁
  have := isIso_mapCochainComplexPlusDerivedUnit_app_of_rightAcyclic
    (etaleModuleGlobalSections.{u, 0} Λ S)
    ((etaleModuleDirectImage.{u, 0} Λ f).mapCochainComplexPlus.obj N) h₂
  rw [directImageSectionsDerivedUnit_app]
  infer_instance

/-- **`Q(Γ(S, f_* I)) ≅ RΓ(S, Rf_*(Q I))` on a bounded below complex of injective sheaves.** -/
theorem isIso_directImageSectionsDerivedUnit_app (I : CochainComplex.Plus (EtaleModules.{u, 0} Λ Y))
    (hI : ∀ n, Injective (I.obj.X n)) :
    IsIso ((directImageSectionsDerivedUnit Λ f).app I) :=
  isIso_directImageSectionsDerivedUnit_app_of_rightAcyclic Λ f I
    (fun n => have := hI n; Functor.rightAcyclic_of_injective _ _)
    (fun n => have : Injective ((etaleModuleDirectImage.{u, 0} Λ f).obj (I.obj.X n)) :=
        Functor.PreservesInjectiveObjects.injective_obj (hI n)
      Functor.rightAcyclic_of_injective _ ((etaleModuleDirectImage.{u, 0} Λ f).obj (I.obj.X n)))

end Unit

section RestrictScalars

variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ') {Y S : Scheme.{u}} (f : Y ⟶ S)

/-- The termwise comparison `res_ρ Γ(S, f_* N) ≅ Γ(S, f_* res_ρ N)` of a bounded below complex. -/
def directImageSectionsRestrictScalarsComplexIso
    (N : CochainComplex.Plus (EtaleModules.{u, 0} Λ' Y)) :
    (ModuleCat.restrictScalars.{u + 1} ρ).mapCochainComplexPlus.obj
        ((etaleModuleGlobalSections.{u, 0} Λ' S).mapCochainComplexPlus.obj
          ((etaleModuleDirectImage.{u, 0} Λ' f).mapCochainComplexPlus.obj N)) ≅
      (etaleModuleGlobalSections.{u, 0} Λ S).mapCochainComplexPlus.obj
        ((etaleModuleDirectImage.{u, 0} Λ f).mapCochainComplexPlus.obj
          ((etaleModuleRestrictScalars ρ Y).mapCochainComplexPlus.obj N)) :=
  ObjectProperty.isoMk _ ((NatIso.mapHomologicalComplex
    (etaleModuleGlobalSectionsRestrictScalars ρ S) (ComplexShape.up ℤ)).app
      ((etaleModuleDirectImage.{u, 0} Λ' f).mapCochainComplexPlus.obj N).obj)

/-- The derived unit of `Γ(S, -)` commutes with `res_ρ`: `res_ρ` of it at `L`, followed by the
comparison of `RΓ(S, -)` with `res_ρ`, is the termwise comparison followed by the derived unit
at `res_ρ L`. -/
theorem restrictScalars_globalSections_derivedUnit
    (L : CochainComplex.Plus (EtaleModules.{u, 0} Λ' S)) :
    (Functor.mapDerivedCategoryPlusQIso (ModuleCat.restrictScalars.{u + 1} ρ)).inv.app
        ((etaleModuleGlobalSections.{u, 0} Λ' S).mapCochainComplexPlus.obj L) ≫
      (ModuleCat.restrictScalars.{u + 1} ρ).mapDerivedCategoryPlus.map
        ((etaleModuleGlobalSections.{u, 0} Λ' S).mapCochainComplexPlusDerivedUnit.app L) ≫
      (etaleModuleDerivedGlobalSectionsRestrictScalars ρ S).hom.app
        (DerivedCategory.Plus.Q.obj L) =
    DerivedCategory.Plus.Q.map (ObjectProperty.homMk
        (X := (ModuleCat.restrictScalars.{u + 1} ρ).mapCochainComplexPlus.obj
          ((etaleModuleGlobalSections.{u, 0} Λ' S).mapCochainComplexPlus.obj L))
        (Y := (etaleModuleGlobalSections.{u, 0} Λ S).mapCochainComplexPlus.obj
          ((etaleModuleRestrictScalars ρ S).mapCochainComplexPlus.obj L))
        ((NatTrans.mapHomologicalComplex (etaleModuleGlobalSectionsRestrictScalars ρ S).hom
          (ComplexShape.up ℤ)).app L.obj)) ≫
      (etaleModuleGlobalSections.{u, 0} Λ S).mapCochainComplexPlusDerivedUnit.app
        ((etaleModuleRestrictScalars ρ S).mapCochainComplexPlus.obj L) ≫
      (etaleModuleGlobalSections.{u, 0} Λ S).rightDerivedFunctorPlus.map
        ((Functor.mapDerivedCategoryPlusQIso (etaleModuleRestrictScalars ρ S)).inv.app L) :=
  Functor.mapCochainComplexPlusDerivedUnit_comp_rightDerivedRestrictionIso_hom_app _ _ _ _
    (etaleModuleGlobalSectionsRestrictScalars ρ S)
    (fun I _ => rightAcyclic_globalSections_of_isAcyclicEverywhere _
      (isAcyclicEverywhere_restrictScalars' ρ I)) L

/-- **The canonical map `Q(Γ(S, f_* N)) ⟶ RΓ(S, Rf_*(Q N))` commutes with `res_ρ`**: `res_ρ`
of it, followed by the comparisons of `RΓ(S, -)` and `Rf_*` with `res_ρ`, is the termwise
comparison followed by the canonical map at `res_ρ N`. -/
theorem restrictScalars_directImageSectionsDerivedUnit
    (N : CochainComplex.Plus (EtaleModules.{u, 0} Λ' Y)) :
    (Functor.mapDerivedCategoryPlusQIso (ModuleCat.restrictScalars.{u + 1} ρ)).inv.app
        ((etaleModuleGlobalSections.{u, 0} Λ' S).mapCochainComplexPlus.obj
          ((etaleModuleDirectImage.{u, 0} Λ' f).mapCochainComplexPlus.obj N)) ≫
      (ModuleCat.restrictScalars.{u + 1} ρ).mapDerivedCategoryPlus.map
        ((directImageSectionsDerivedUnit Λ' f).app N) ≫
      (etaleModuleDerivedGlobalSectionsRestrictScalars ρ S).hom.app
        ((etaleModuleDerivedDirectImage.{u, 0} Λ' f).obj (DerivedCategory.Plus.Q.obj N)) ≫
      (etaleModuleDerivedGlobalSections.{u, 0} Λ S).map
        ((etaleModuleDerivedDirectImageRestrictScalars ρ f).hom.app
          (DerivedCategory.Plus.Q.obj N)) =
    DerivedCategory.Plus.Q.map (directImageSectionsRestrictScalarsComplexIso ρ f N).hom ≫
      (directImageSectionsDerivedUnit Λ f).app
        ((etaleModuleRestrictScalars ρ Y).mapCochainComplexPlus.obj N) ≫
      (etaleModuleDerivedGlobalSections.{u, 0} Λ S).map
        ((etaleModuleDerivedDirectImage.{u, 0} Λ f).map
          ((Functor.mapDerivedCategoryPlusQIso (etaleModuleRestrictScalars ρ Y)).inv.app N)) := by
  let rM := ModuleCat.restrictScalars.{u + 1} ρ
  let rS := etaleModuleRestrictScalars ρ S
  let rY := etaleModuleRestrictScalars ρ Y
  let Γ' := etaleModuleGlobalSections.{u, 0} Λ' S
  let Γ := etaleModuleGlobalSections.{u, 0} Λ S
  let f' := etaleModuleDirectImage.{u, 0} Λ' f
  let fΛ := etaleModuleDirectImage.{u, 0} Λ f
  let L := f'.mapCochainComplexPlus.obj N
  let θΓ := etaleModuleDerivedGlobalSectionsRestrictScalars ρ S
  let θf := etaleModuleDerivedDirectImageRestrictScalars ρ f
  have hn : rM.mapDerivedCategoryPlus.map (Γ'.rightDerivedFunctorPlus.map
      (f'.mapCochainComplexPlusDerivedUnit.app N)) ≫ θΓ.hom.app (f'.rightDerivedFunctorPlus.obj
        (DerivedCategory.Plus.Q.obj N)) =
      θΓ.hom.app (DerivedCategory.Plus.Q.obj L) ≫
        Γ.rightDerivedFunctorPlus.map (rS.mapDerivedCategoryPlus.map
          (f'.mapCochainComplexPlusDerivedUnit.app N)) :=
    θΓ.hom.naturality (f'.mapCochainComplexPlusDerivedUnit.app N)
  let a := (Functor.mapDerivedCategoryPlusQIso rM).inv.app (Γ'.mapCochainComplexPlus.obj L)
  let b := rM.mapDerivedCategoryPlus.map (Γ'.mapCochainComplexPlusDerivedUnit.app L)
  let c := rM.mapDerivedCategoryPlus.map (Γ'.rightDerivedFunctorPlus.map
    (f'.mapCochainComplexPlusDerivedUnit.app N))
  let d := θΓ.hom.app (f'.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj N))
  let d₀ := θΓ.hom.app (DerivedCategory.Plus.Q.obj L)
  let x := Γ.rightDerivedFunctorPlus.map (rS.mapDerivedCategoryPlus.map
    (f'.mapCochainComplexPlusDerivedUnit.app N))
  let y := Γ.rightDerivedFunctorPlus.map (θf.hom.app (DerivedCategory.Plus.Q.obj N))
  let qe := DerivedCategory.Plus.Q.map (directImageSectionsRestrictScalarsComplexIso ρ f N).hom
  let uΓ := Γ.mapCochainComplexPlusDerivedUnit.app (rS.mapCochainComplexPlus.obj L)
  let ψS := (Functor.mapDerivedCategoryPlusQIso rS).inv.app L
  let uf := fΛ.mapCochainComplexPlusDerivedUnit.app (rY.mapCochainComplexPlus.obj N)
  let ψY := (Functor.mapDerivedCategoryPlusQIso rY).inv.app N
  have hf' : Γ.rightDerivedFunctorPlus.map ψS ≫ x ≫ y =
      Γ.rightDerivedFunctorPlus.map uf ≫ Γ.rightDerivedFunctorPlus.map
        (fΛ.rightDerivedFunctorPlus.map ψY) := by
    refine ((whisker_eq _ (Γ.rightDerivedFunctorPlus.map_comp _ _).symm).trans
      (Γ.rightDerivedFunctorPlus.map_comp _ _).symm).trans ?_
    exact ((congrArg Γ.rightDerivedFunctorPlus.map
      (restrictScalars_directImage_derivedUnit ρ f N)).trans
      (Γ.rightDerivedFunctorPlus.map_comp _ _))
  calc a ≫ rM.mapDerivedCategoryPlus.map ((directImageSectionsDerivedUnit Λ' f).app N) ≫ d ≫ y
      = a ≫ (b ≫ c) ≫ d ≫ y :=
        congrArg (fun t => a ≫ t ≫ d ≫ y) (rM.mapDerivedCategoryPlus.map_comp _ _)
    _ = (a ≫ b ≫ d₀) ≫ x ≫ y := by
        rw [show (b ≫ c) ≫ d ≫ y = b ≫ (c ≫ d) ≫ y by simp only [Category.assoc], hn]
        simp only [Category.assoc]; rfl
    _ = (qe ≫ uΓ ≫ Γ.rightDerivedFunctorPlus.map ψS) ≫ x ≫ y :=
        congrArg (· ≫ x ≫ y) (restrictScalars_globalSections_derivedUnit ρ L)
    _ = qe ≫ (uΓ ≫ Γ.rightDerivedFunctorPlus.map uf) ≫ Γ.rightDerivedFunctorPlus.map
          (fΛ.rightDerivedFunctorPlus.map ψY) := (Category.assoc _ _ _).trans <| whisker_eq qe <|
        (Category.assoc _ _ _).trans <| (whisker_eq uΓ hf').trans (Category.assoc _ _ _).symm

/-- **The comparison of `RΓ(S, Rf_* -)` with `res_ρ`, read on complexes.** For a morphism
`μ : I ⟶ res_ρ C` of bounded below complexes, `RΓ(S, Rf_*(Q μ))` followed by the comparison
`RΓ(S, Rf_* res_ρ -) ≅ res_ρ RΓ(S, Rf_* -)` is, after the canonical map at `I`, the termwise map
`Γ(S, f_* μ)` followed by `res_ρ` of the canonical map at `C`. -/
theorem directImageSectionsDerivedUnit_comp_map_restrictScalars
    (I : CochainComplex.Plus (EtaleModules.{u, 0} Λ Y))
    (C : CochainComplex.Plus (EtaleModules.{u, 0} Λ' Y))
    (μ : I ⟶ (etaleModuleRestrictScalars ρ Y).mapCochainComplexPlus.obj C) :
    (directImageSectionsDerivedUnit Λ f).app I ≫
      (etaleModuleDerivedGlobalSections.{u, 0} Λ S).map
        ((etaleModuleDerivedDirectImage.{u, 0} Λ f).map (DerivedCategory.Plus.Q.map μ ≫
          (Functor.mapDerivedCategoryPlusQIso (etaleModuleRestrictScalars ρ Y)).inv.app C)) =
    DerivedCategory.Plus.Q.map ((etaleModuleGlobalSections.{u, 0} Λ S).mapCochainComplexPlus.map
        ((etaleModuleDirectImage.{u, 0} Λ f).mapCochainComplexPlus.map μ) ≫
        (directImageSectionsRestrictScalarsComplexIso ρ f C).inv) ≫
      (Functor.mapDerivedCategoryPlusQIso (ModuleCat.restrictScalars.{u + 1} ρ)).inv.app
        ((etaleModuleGlobalSections.{u, 0} Λ' S).mapCochainComplexPlus.obj
          ((etaleModuleDirectImage.{u, 0} Λ' f).mapCochainComplexPlus.obj C)) ≫
      (ModuleCat.restrictScalars.{u + 1} ρ).mapDerivedCategoryPlus.map
        ((directImageSectionsDerivedUnit Λ' f).app C) ≫
      (etaleModuleDerivedGlobalSectionsRestrictScalars ρ S).hom.app
        ((etaleModuleDerivedDirectImage.{u, 0} Λ' f).obj (DerivedCategory.Plus.Q.obj C)) ≫
      (etaleModuleDerivedGlobalSections.{u, 0} Λ S).map
        ((etaleModuleDerivedDirectImageRestrictScalars ρ f).hom.app
          (DerivedCategory.Plus.Q.obj C)) := by
  have hc := restrictScalars_directImageSectionsDerivedUnit ρ f C
  let RΓ := etaleModuleDerivedGlobalSections.{u, 0} Λ S
  let Rf := etaleModuleDerivedDirectImage.{u, 0} Λ f
  let a := (directImageSectionsDerivedUnit Λ f).app I
  let bm := RΓ.map (Rf.map (DerivedCategory.Plus.Q.map μ))
  let cm := RΓ.map (Rf.map
    ((Functor.mapDerivedCategoryPlusQIso (etaleModuleRestrictScalars ρ Y)).inv.app C))
  let gμ := DerivedCategory.Plus.Q.map
      ((etaleModuleGlobalSections.{u, 0} Λ S).mapCochainComplexPlus.map
        ((etaleModuleDirectImage.{u, 0} Λ f).mapCochainComplexPlus.map μ))
  let d := (directImageSectionsDerivedUnit Λ f).app
    ((etaleModuleRestrictScalars ρ Y).mapCochainComplexPlus.obj C)
  let e := DerivedCategory.Plus.Q.map (directImageSectionsRestrictScalarsComplexIso ρ f C).hom
  let e' := DerivedCategory.Plus.Q.map (directImageSectionsRestrictScalarsComplexIso ρ f C).inv
  have hn : gμ ≫ d = a ≫ bm := (directImageSectionsDerivedUnit Λ f).naturality μ
  have hee : e' ≫ e = 𝟙 _ :=
    (directImageSectionsRestrictScalarsComplexIso ρ f C).map_inv_hom_id DerivedCategory.Plus.Q
  have hL : RΓ.map (Rf.map (DerivedCategory.Plus.Q.map μ ≫
      (Functor.mapDerivedCategoryPlusQIso (etaleModuleRestrictScalars ρ Y)).inv.app C)) = bm ≫ cm :=
    (congrArg RΓ.map (Rf.map_comp _ _)).trans (RΓ.map_comp _ _)
  have hR : DerivedCategory.Plus.Q.map
      ((etaleModuleGlobalSections.{u, 0} Λ S).mapCochainComplexPlus.map
        ((etaleModuleDirectImage.{u, 0} Λ f).mapCochainComplexPlus.map μ) ≫
        (directImageSectionsRestrictScalarsComplexIso ρ f C).inv) = gμ ≫ e' :=
    DerivedCategory.Plus.Q.map_comp _ _
  calc a ≫ RΓ.map (Rf.map (DerivedCategory.Plus.Q.map μ ≫
        (Functor.mapDerivedCategoryPlusQIso (etaleModuleRestrictScalars ρ Y)).inv.app C))
      = (a ≫ bm) ≫ cm := (congrArg (a ≫ ·) hL).trans (Category.assoc _ _ _).symm
    _ = gμ ≫ d ≫ cm := (congrArg (· ≫ cm) hn.symm).trans (Category.assoc _ _ _)
    _ = gμ ≫ (e' ≫ e) ≫ d ≫ cm := by rw [hee, Category.id_comp]
    _ = (gμ ≫ e') ≫ e ≫ d ≫ cm := by simp only [Category.assoc]
    _ = _ := by rw [← hR, ← hc]

/-- **`Q(Γ(S, f_* res_ρ C)) ≅ RΓ(S, Rf_*(Q(res_ρ C)))` on a bounded below complex `C` of injective
sheaves of `Λ'`-modules**: restrictions of scalars of injective sheaves are acyclic everywhere,
and so are their direct images. -/
theorem isIso_directImageSectionsDerivedUnit_app_restrictScalars
    (C : CochainComplex.Plus (EtaleModules.{u, 0} Λ' Y)) (hC : ∀ n, Injective (C.obj.X n)) :
    IsIso ((directImageSectionsDerivedUnit Λ f).app
      ((etaleModuleRestrictScalars ρ Y).mapCochainComplexPlus.obj C)) := by
  refine isIso_directImageSectionsDerivedUnit_app_of_rightAcyclic Λ f _
    (fun n => have := hC n; rightAcyclic_directImage_of_isAcyclicEverywhere f _
      (isAcyclicEverywhere_restrictScalars' ρ (C.obj.X n))) (fun n => ?_)
  have : Injective ((etaleModuleDirectImage.{u, 0} Λ' f).obj (C.obj.X n)) :=
    Functor.PreservesInjectiveObjects.injective_obj (hC n)
  exact rightAcyclic_globalSections_of_isAcyclicEverywhere _
    (isAcyclicEverywhere_restrictScalars' ρ ((etaleModuleDirectImage.{u, 0} Λ' f).obj (C.obj.X n)))

end RestrictScalars

end Stacks.EtaleCohomology
