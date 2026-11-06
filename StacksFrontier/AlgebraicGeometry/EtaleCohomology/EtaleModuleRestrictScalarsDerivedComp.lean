module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalarsDerivedUnit

/-!
# Restriction of scalars and the composition of derived direct images

The comparisons `Rf_* ∘ res_ρ ≅ res_ρ ∘ Rf_*` of
`Stacks.EtaleCohomology.etaleModuleDerivedDirectImageRestrictScalars` are compatible with the
composition isomorphisms `R(f ≫ g)_* ≅ Rf_* ⋙ Rg_*` of
`Stacks.EtaleCohomology.etaleModuleDerivedDirectImageComp`.

Both sides of the compatibility are computed after the unit of `R(f ≫ g)_*` at a bounded below
homotopy class `K`, where every comparison is an explicit identification of complexes; the
compatibility itself then follows because the units are a universal arrow.

## References

* [Stacks Project, Tag 03V2](https://stacks.math.columbia.edu/tag/03V2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace CategoryTheory.Functor

variable {A B C : Type*} [Category* A] [Category* B] [Category* C]
  [Abelian A] [Abelian B] [Abelian C] [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory C] [EnoughInjectives A] [EnoughInjectives B]
  (T : A ⥤ B) (r : B ⥤ C) [T.Additive] [r.Additive] [PreservesFiniteLimits r]
  [PreservesFiniteColimits r]

/-- **Transformations out of `RT ⋙ r⁺` are determined after the unit**, for an exact `r`:
`RT ⋙ r⁺` is the right derived functor of `T ⋙ r`, with unit `r⁺` of the unit of `RT`. -/
theorem rightDerivedFunctorPlus_comp_mapDerivedCategoryPlus_ext
    {G : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C}
    (γ₁ γ₂ : T.rightDerivedFunctorPlus ⋙ r.mapDerivedCategoryPlus ⟶ G)
    (h : ∀ K : HomotopyCategory.Plus A,
      r.mapDerivedCategoryPlus.map (T.rightDerivedFunctorPlusUnith.app K) ≫
          γ₁.app (DerivedCategory.Plus.Qh.obj K) =
        r.mapDerivedCategoryPlus.map (T.rightDerivedFunctorPlusUnith.app K) ≫
          γ₂.app (DerivedCategory.Plus.Qh.obj K)) :
    γ₁ = γ₂ := by
  let τ : (T ⋙ r).rightDerivedFunctorPlus ≅ T.rightDerivedFunctorPlus ⋙ r.mapDerivedCategoryPlus :=
    rightDerivedFunctorPlusCompIsoOfRightAcyclic T r (fun _ _ => rightAcyclic_of_exact _ _) ≪≫
      isoWhiskerLeft _ (rightDerivedFunctorPlusIsoMapDerivedCategoryPlus r)
  suffices hτ : τ.hom ≫ γ₁ = τ.hom ≫ γ₂ by simpa using hτ
  refine rightDerived_ext (T ⋙ r).rightDerivedFunctorPlus (T ⋙ r).rightDerivedFunctorPlusUnith
    (HomotopyCategory.Plus.quasiIso A) G _ _ ?_
  refine NatTrans.ext (funext fun K => ?_)
  have hu := Stacks.EtaleCohomology.unit_comp_compExact_app T r K
  have hτ : τ.hom.app (DerivedCategory.Plus.Qh.obj K) =
      (rightDerivedFunctorPlusComp T r).app (DerivedCategory.Plus.Qh.obj K) ≫
        (rightDerivedFunctorPlusIsoMapDerivedCategoryPlus r).hom.app
          (T.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj K)) := rfl
  simp only [NatTrans.comp_app, whiskerLeft_app, hτ, Category.assoc]
  rw [reassoc_of% hu, reassoc_of% hu]
  exact whisker_eq _ (h K)

end CategoryTheory.Functor

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable {Λ Λ' : Type} [Ring Λ] [Ring Λ'] (ρ : Λ →+* Λ')

section Comp

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : fg = f ≫ g)
  (K : HomotopyCategory.Plus (EtaleModules.{u, 0} Λ' X))

/-- `Q` of the coherence isomorphism of a composite of direct images commutes with `res_ρ`. -/
theorem restrictScalars_Qh_map_mapH_compIso_inv_app :
    DerivedCategory.Plus.Qh.map ((etaleModuleRestrictScalars ρ Z).mapHomotopyCategoryPlus.map
        ((Functor.mapHomotopyCategoryPlusCompIso
        (etaleModuleDirectImageComp.{u, 0} Λ' f g fg hfg)).inv.app K)) = DerivedCategory.Plus.Qh.map
        ((Functor.mapHomotopyCategoryPlusCompIso
        (etaleModuleDirectImageComp.{u, 0} Λ f g fg hfg)).inv.app
        ((etaleModuleRestrictScalars ρ X).mapHomotopyCategoryPlus.obj K)) :=
  congrArg _ (restrictScalars_mapH_compIso_inv_app ρ f g fg hfg K)

/-- The coherence isomorphism of a composite of direct images, on the derived category, commutes
with the factorization of the derived action of `res_ρ`. -/
theorem restrictScalars_mapDerivedCategoryPlusFactorsh_compIso :
    (etaleModuleRestrictScalars ρ Z).mapDerivedCategoryPlus.map (DerivedCategory.Plus.Qh.map
        ((Functor.mapHomotopyCategoryPlusCompIso
        (etaleModuleDirectImageComp.{u, 0} Λ' f g fg hfg)).inv.app K)) ≫
        (etaleModuleRestrictScalars ρ Z).mapDerivedCategoryPlusFactorsh.hom.app
            ((etaleModuleDirectImage.{u, 0} Λ' g).mapHomotopyCategoryPlus.obj
            ((etaleModuleDirectImage.{u, 0} Λ' f).mapHomotopyCategoryPlus.obj K)) =
      (etaleModuleRestrictScalars ρ Z).mapDerivedCategoryPlusFactorsh.hom.app
          ((etaleModuleDirectImage.{u, 0} Λ' fg).mapHomotopyCategoryPlus.obj K) ≫
        DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusCompIso
            (etaleModuleDirectImageComp.{u, 0} Λ f g fg hfg)).inv.app
            ((etaleModuleRestrictScalars ρ X).mapHomotopyCategoryPlus.obj K)) :=
  ((etaleModuleRestrictScalars ρ Z).mapDerivedCategoryPlusFactorsh.hom.naturality
      ((Functor.mapHomotopyCategoryPlusCompIso
      (etaleModuleDirectImageComp.{u, 0} Λ' f g fg hfg)).inv.app K)).trans
    (congrArg (_ ≫ ·) (restrictScalars_Qh_map_mapH_compIso_inv_app ρ f g fg hfg K))

/-- `res_ρ` of the composition comparison of `Λ'`-coefficients after the unit. -/
theorem restrictScalars_map_unit_comp_derivedDirectImageComp :
    (etaleModuleRestrictScalars ρ Z).mapDerivedCategoryPlus.map
        ((etaleModuleDirectImage.{u, 0} Λ' fg).rightDerivedFunctorPlusUnith.app K) ≫
        (etaleModuleRestrictScalars ρ Z).mapDerivedCategoryPlus.map
            ((etaleModuleDerivedDirectImageComp.{u, 0} Λ' f g fg hfg).hom.app
            (DerivedCategory.Plus.Qh.obj K)) =
      (etaleModuleRestrictScalars ρ Z).mapDerivedCategoryPlus.map (DerivedCategory.Plus.Qh.map
          ((Functor.mapHomotopyCategoryPlusCompIso
          (etaleModuleDirectImageComp.{u, 0} Λ' f g fg hfg)).inv.app K)) ≫
        (etaleModuleRestrictScalars ρ Z).mapDerivedCategoryPlus.map
            ((etaleModuleDirectImage.{u, 0} Λ' g).rightDerivedFunctorPlusUnith.app
            ((etaleModuleDirectImage.{u, 0} Λ' f).mapHomotopyCategoryPlus.obj K)) ≫
        (etaleModuleRestrictScalars ρ Z).mapDerivedCategoryPlus.map
          ((etaleModuleDirectImage.{u, 0} Λ' g).rightDerivedFunctorPlus.map
              ((etaleModuleDirectImage.{u, 0} Λ' f).rightDerivedFunctorPlusUnith.app K)) :=
  ((etaleModuleRestrictScalars ρ Z).mapDerivedCategoryPlus.map_comp _ _).symm.trans ((congrArg
      (etaleModuleRestrictScalars ρ Z).mapDerivedCategoryPlus.map
    (Functor.unit_comp_rightDerivedFunctorPlusCompIsoOfIso_hom_app _ _ _ _ K)).trans
      (((etaleModuleRestrictScalars ρ Z).mapDerivedCategoryPlus.map_comp _ _).trans
        (congrArg (_ ≫ ·) ((etaleModuleRestrictScalars ρ Z).mapDerivedCategoryPlus.map_comp _ _))))

/-- `Rg_*` of the restriction comparison for `f` after the unit of `Rf_*`. -/
theorem derivedDirectImage_map_restrictScalars_directImage_unit :
    (etaleModuleDirectImage.{u, 0} Λ g).rightDerivedFunctorPlus.map
        ((etaleModuleRestrictScalars ρ Y).mapDerivedCategoryPlusFactorsh.inv.app
        ((etaleModuleDirectImage.{u, 0} Λ' f).mapHomotopyCategoryPlus.obj K)) ≫
        (etaleModuleDirectImage.{u, 0} Λ g).rightDerivedFunctorPlus.map
          ((etaleModuleRestrictScalars ρ Y).mapDerivedCategoryPlus.map
              ((etaleModuleDirectImage.{u, 0} Λ' f).rightDerivedFunctorPlusUnith.app K)) ≫
        (etaleModuleDirectImage.{u, 0} Λ g).rightDerivedFunctorPlus.map
            ((etaleModuleDerivedDirectImageRestrictScalars ρ f).hom.app
            (DerivedCategory.Plus.Qh.obj K)) =
      (etaleModuleDirectImage.{u, 0} Λ g).rightDerivedFunctorPlus.map
          ((etaleModuleDirectImage.{u, 0} Λ f).rightDerivedFunctorPlusUnith.app
          ((etaleModuleRestrictScalars ρ X).mapHomotopyCategoryPlus.obj K)) ≫
        (etaleModuleDirectImage.{u, 0} Λ g).rightDerivedFunctorPlus.map
          ((etaleModuleDirectImage.{u, 0} Λ f).rightDerivedFunctorPlus.map
              ((etaleModuleRestrictScalars ρ X).mapDerivedCategoryPlusFactorsh.inv.app K)) := by
  refine (congrArg (_ ≫ ·)
      ((etaleModuleDirectImage.{u, 0} Λ g).rightDerivedFunctorPlus.map_comp _ _).symm).trans ?_
  refine ((etaleModuleDirectImage.{u, 0} Λ g).rightDerivedFunctorPlus.map_comp _ _).symm.trans ?_
  refine (congrArg (etaleModuleDirectImage.{u, 0} Λ g).rightDerivedFunctorPlus.map ?_).trans
    ((etaleModuleDirectImage.{u, 0} Λ g).rightDerivedFunctorPlus.map_comp _ _)
  exact (congrArg (_ ≫ ·) (restrictScalars_directImage_unit ρ f K)).trans
    (Iso.inv_hom_id_app_assoc _ _ _)

/-- The composite `res_ρ ∘ R(f ≫ g)_* ≅ R(f ≫ g)_* ∘ res_ρ ≅ Rg_* ∘ Rf_* ∘ res_ρ` after the
unit of `R(f ≫ g)_*`. -/
theorem restrictScalars_derivedDirectImageComp_unit_right :
    (etaleModuleRestrictScalars ρ Z).mapDerivedCategoryPlus.map
        ((etaleModuleDirectImage.{u, 0} Λ' fg).rightDerivedFunctorPlusUnith.app K) ≫
        (etaleModuleDerivedDirectImageRestrictScalars ρ fg).hom.app
            (DerivedCategory.Plus.Qh.obj K) ≫
            (etaleModuleDerivedDirectImageComp.{u, 0} Λ f g fg hfg).hom.app
            ((etaleModuleRestrictScalars ρ X).mapDerivedCategoryPlus.obj
            (DerivedCategory.Plus.Qh.obj K)) =
            (etaleModuleRestrictScalars ρ Z).mapDerivedCategoryPlusFactorsh.hom.app
            ((etaleModuleDirectImage.{u, 0} Λ' fg).mapHomotopyCategoryPlus.obj K) ≫
            DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusCompIso
            (etaleModuleDirectImageComp.{u, 0} Λ f g fg hfg)).inv.app
            ((etaleModuleRestrictScalars ρ X).mapHomotopyCategoryPlus.obj K)) ≫
            (etaleModuleDirectImage.{u, 0} Λ g).rightDerivedFunctorPlusUnith.app
            ((etaleModuleDirectImage.{u, 0} Λ f).mapHomotopyCategoryPlus.obj
            ((etaleModuleRestrictScalars ρ X).mapHomotopyCategoryPlus.obj K)) ≫
            (etaleModuleDirectImage.{u, 0} Λ g).rightDerivedFunctorPlus.map
            ((etaleModuleDirectImage.{u, 0} Λ f).rightDerivedFunctorPlusUnith.app
            ((etaleModuleRestrictScalars ρ X).mapHomotopyCategoryPlus.obj K)) ≫
            (etaleModuleDirectImage.{u, 0} Λ g).rightDerivedFunctorPlus.map
            ((etaleModuleDirectImage.{u, 0} Λ f).rightDerivedFunctorPlus.map
            ((etaleModuleRestrictScalars ρ X).mapDerivedCategoryPlusFactorsh.inv.app K)) := by
  let a := (etaleModuleRestrictScalars ρ Z).mapDerivedCategoryPlus.map
      ((etaleModuleDirectImage.{u, 0} Λ' fg).rightDerivedFunctorPlusUnith.app K)
  let t := (etaleModuleDerivedDirectImageRestrictScalars ρ fg).hom.app
      (DerivedCategory.Plus.Qh.obj K)
  let e := (etaleModuleDerivedDirectImageComp.{u, 0} Λ f g fg hfg).hom.app
      ((etaleModuleRestrictScalars ρ X).mapDerivedCategoryPlus.obj (DerivedCategory.Plus.Qh.obj K))
  let F := (etaleModuleRestrictScalars ρ Z).mapDerivedCategoryPlusFactorsh.hom.app
      ((etaleModuleDirectImage.{u, 0} Λ' fg).mapHomotopyCategoryPlus.obj K)
  let v := (etaleModuleDirectImage.{u, 0} Λ fg).rightDerivedFunctorPlusUnith.app
      ((etaleModuleRestrictScalars ρ X).mapHomotopyCategoryPlus.obj K)
  let w := (etaleModuleDirectImage.{u, 0} Λ fg).rightDerivedFunctorPlus.map
      ((etaleModuleRestrictScalars ρ X).mapDerivedCategoryPlusFactorsh.inv.app K)
  let e2 := (etaleModuleDerivedDirectImageComp.{u, 0} Λ f g fg hfg).hom.app
      (DerivedCategory.Plus.Qh.obj ((etaleModuleRestrictScalars ρ X).mapHomotopyCategoryPlus.obj K))
  let z := (etaleModuleDirectImage.{u, 0} Λ g).rightDerivedFunctorPlus.map
    ((etaleModuleDirectImage.{u, 0} Λ f).rightDerivedFunctorPlus.map
        ((etaleModuleRestrictScalars ρ X).mapDerivedCategoryPlusFactorsh.inv.app K))
  let c := DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusCompIso
      (etaleModuleDirectImageComp.{u, 0} Λ f g fg hfg)).inv.app
      ((etaleModuleRestrictScalars ρ X).mapHomotopyCategoryPlus.obj K))
  let ug := (etaleModuleDirectImage.{u, 0} Λ g).rightDerivedFunctorPlusUnith.app
      ((etaleModuleDirectImage.{u, 0} Λ f).mapHomotopyCategoryPlus.obj
      ((etaleModuleRestrictScalars ρ X).mapHomotopyCategoryPlus.obj K))
  let uf := (etaleModuleDirectImage.{u, 0} Λ g).rightDerivedFunctorPlus.map
      ((etaleModuleDirectImage.{u, 0} Λ f).rightDerivedFunctorPlusUnith.app
      ((etaleModuleRestrictScalars ρ X).mapHomotopyCategoryPlus.obj K))
  have h1 : a ≫ t = F ≫ v ≫ w := restrictScalars_directImage_unit ρ fg K
  have h2 : w ≫ e = e2 ≫ z := (etaleModuleDerivedDirectImageComp.{u, 0} Λ f g fg hfg).hom.naturality
      ((etaleModuleRestrictScalars ρ X).mapDerivedCategoryPlusFactorsh.inv.app K)
  have h3 : v ≫ e2 = c ≫ ug ≫ uf :=
    Functor.unit_comp_rightDerivedFunctorPlusCompIsoOfIso_hom_app _ _ _ _ _
  change a ≫ t ≫ e = F ≫ c ≫ ug ≫ uf ≫ z
  erw [reassoc_of% h1, Category.assoc, h2, ← Category.assoc v e2 z, h3,
    Category.assoc, Category.assoc]
  rfl

/-- The restriction comparison for `g` after the unit of `Rg_*` at `f_* K`, with the unit of
`Rg_*` read at `f_*(res_ρ K)`. -/
theorem restrictScalars_directImage_unit_directImage :
    (etaleModuleRestrictScalars ρ Z).mapDerivedCategoryPlus.map
        ((etaleModuleDirectImage.{u, 0} Λ' g).rightDerivedFunctorPlusUnith.app
        ((etaleModuleDirectImage.{u, 0} Λ' f).mapHomotopyCategoryPlus.obj K)) ≫
        (etaleModuleDerivedDirectImageRestrictScalars ρ g).hom.app (DerivedCategory.Plus.Qh.obj
            ((etaleModuleDirectImage.{u, 0} Λ' f).mapHomotopyCategoryPlus.obj K)) =
      (etaleModuleRestrictScalars ρ Z).mapDerivedCategoryPlusFactorsh.hom.app
          ((etaleModuleDirectImage.{u, 0} Λ' g).mapHomotopyCategoryPlus.obj
          ((etaleModuleDirectImage.{u, 0} Λ' f).mapHomotopyCategoryPlus.obj K)) ≫
        (etaleModuleDirectImage.{u, 0} Λ g).rightDerivedFunctorPlusUnith.app
            ((etaleModuleDirectImage.{u, 0} Λ f).mapHomotopyCategoryPlus.obj
            ((etaleModuleRestrictScalars ρ X).mapHomotopyCategoryPlus.obj K)) ≫
        (etaleModuleDirectImage.{u, 0} Λ g).rightDerivedFunctorPlus.map
            ((etaleModuleRestrictScalars ρ Y).mapDerivedCategoryPlusFactorsh.inv.app
            ((etaleModuleDirectImage.{u, 0} Λ' f).mapHomotopyCategoryPlus.obj K)) :=
  restrictScalars_directImage_unit ρ g
      ((etaleModuleDirectImage.{u, 0} Λ' f).mapHomotopyCategoryPlus.obj K)

/-- The composite `res_ρ ∘ R(f ≫ g)_* ≅ res_ρ ∘ Rg_* ∘ Rf_* ≅ Rg_* ∘ res_ρ ∘ Rf_*
≅ Rg_* ∘ Rf_* ∘ res_ρ` after the unit of `R(f ≫ g)_*`. -/
theorem restrictScalars_derivedDirectImageComp_unit_left :
    (etaleModuleRestrictScalars ρ Z).mapDerivedCategoryPlus.map
        ((etaleModuleDirectImage.{u, 0} Λ' fg).rightDerivedFunctorPlusUnith.app K) ≫
        (etaleModuleRestrictScalars ρ Z).mapDerivedCategoryPlus.map
            ((etaleModuleDerivedDirectImageComp.{u, 0} Λ' f g fg hfg).hom.app
            (DerivedCategory.Plus.Qh.obj K)) ≫
        (etaleModuleDerivedDirectImageRestrictScalars ρ g).hom.app
            ((etaleModuleDirectImage.{u, 0} Λ' f).rightDerivedFunctorPlus.obj
            (DerivedCategory.Plus.Qh.obj K)) ≫
        (etaleModuleDirectImage.{u, 0} Λ g).rightDerivedFunctorPlus.map
            ((etaleModuleDerivedDirectImageRestrictScalars ρ f).hom.app
            (DerivedCategory.Plus.Qh.obj K)) =
            (etaleModuleRestrictScalars ρ Z).mapDerivedCategoryPlusFactorsh.hom.app
            ((etaleModuleDirectImage.{u, 0} Λ' fg).mapHomotopyCategoryPlus.obj K) ≫
            DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusCompIso
            (etaleModuleDirectImageComp.{u, 0} Λ f g fg hfg)).inv.app
            ((etaleModuleRestrictScalars ρ X).mapHomotopyCategoryPlus.obj K)) ≫
            (etaleModuleDirectImage.{u, 0} Λ g).rightDerivedFunctorPlusUnith.app
            ((etaleModuleDirectImage.{u, 0} Λ f).mapHomotopyCategoryPlus.obj
            ((etaleModuleRestrictScalars ρ X).mapHomotopyCategoryPlus.obj K)) ≫
            (etaleModuleDirectImage.{u, 0} Λ g).rightDerivedFunctorPlus.map
            ((etaleModuleDirectImage.{u, 0} Λ f).rightDerivedFunctorPlusUnith.app
            ((etaleModuleRestrictScalars ρ X).mapHomotopyCategoryPlus.obj K)) ≫
            (etaleModuleDirectImage.{u, 0} Λ g).rightDerivedFunctorPlus.map
            ((etaleModuleDirectImage.{u, 0} Λ f).rightDerivedFunctorPlus.map
            ((etaleModuleRestrictScalars ρ X).mapDerivedCategoryPlusFactorsh.inv.app K)) := by
  let a := (etaleModuleRestrictScalars ρ Z).mapDerivedCategoryPlus.map
      ((etaleModuleDirectImage.{u, 0} Λ' fg).rightDerivedFunctorPlusUnith.app K)
  let b := (etaleModuleRestrictScalars ρ Z).mapDerivedCategoryPlus.map
      ((etaleModuleDerivedDirectImageComp.{u, 0} Λ' f g fg hfg).hom.app
      (DerivedCategory.Plus.Qh.obj K))
  let t := (etaleModuleDerivedDirectImageRestrictScalars ρ g).hom.app
      ((etaleModuleDirectImage.{u, 0} Λ' f).rightDerivedFunctorPlus.obj
      (DerivedCategory.Plus.Qh.obj K))
  let y := (etaleModuleDirectImage.{u, 0} Λ g).rightDerivedFunctorPlus.map
      ((etaleModuleDerivedDirectImageRestrictScalars ρ f).hom.app (DerivedCategory.Plus.Qh.obj K))
  let p := (etaleModuleRestrictScalars ρ Z).mapDerivedCategoryPlus.map (DerivedCategory.Plus.Qh.map
      ((Functor.mapHomotopyCategoryPlusCompIso
      (etaleModuleDirectImageComp.{u, 0} Λ' f g fg hfg)).inv.app K))
  let q := (etaleModuleRestrictScalars ρ Z).mapDerivedCategoryPlus.map
      ((etaleModuleDirectImage.{u, 0} Λ' g).rightDerivedFunctorPlusUnith.app
      ((etaleModuleDirectImage.{u, 0} Λ' f).mapHomotopyCategoryPlus.obj K))
  let m := (etaleModuleRestrictScalars ρ Z).mapDerivedCategoryPlus.map
    ((etaleModuleDirectImage.{u, 0} Λ' g).rightDerivedFunctorPlus.map
        ((etaleModuleDirectImage.{u, 0} Λ' f).rightDerivedFunctorPlusUnith.app K))
  let s₀ := (etaleModuleDerivedDirectImageRestrictScalars ρ g).hom.app (DerivedCategory.Plus.Qh.obj
      ((etaleModuleDirectImage.{u, 0} Λ' f).mapHomotopyCategoryPlus.obj K))
  let n := (etaleModuleDirectImage.{u, 0} Λ g).rightDerivedFunctorPlus.map
    ((etaleModuleRestrictScalars ρ Y).mapDerivedCategoryPlus.map
        ((etaleModuleDirectImage.{u, 0} Λ' f).rightDerivedFunctorPlusUnith.app K))
  let F' := (etaleModuleRestrictScalars ρ Z).mapDerivedCategoryPlusFactorsh.hom.app
      ((etaleModuleDirectImage.{u, 0} Λ' g).mapHomotopyCategoryPlus.obj
      ((etaleModuleDirectImage.{u, 0} Λ' f).mapHomotopyCategoryPlus.obj K))
  let ug' := (etaleModuleDirectImage.{u, 0} Λ g).rightDerivedFunctorPlusUnith.app
      ((etaleModuleDirectImage.{u, 0} Λ f).mapHomotopyCategoryPlus.obj
      ((etaleModuleRestrictScalars ρ X).mapHomotopyCategoryPlus.obj K))
  let j := (etaleModuleDirectImage.{u, 0} Λ g).rightDerivedFunctorPlus.map
      ((etaleModuleRestrictScalars ρ Y).mapDerivedCategoryPlusFactorsh.inv.app
      ((etaleModuleDirectImage.{u, 0} Λ' f).mapHomotopyCategoryPlus.obj K))
  let F := (etaleModuleRestrictScalars ρ Z).mapDerivedCategoryPlusFactorsh.hom.app
      ((etaleModuleDirectImage.{u, 0} Λ' fg).mapHomotopyCategoryPlus.obj K)
  let c := DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusCompIso
      (etaleModuleDirectImageComp.{u, 0} Λ f g fg hfg)).inv.app
      ((etaleModuleRestrictScalars ρ X).mapHomotopyCategoryPlus.obj K))
  let uf := (etaleModuleDirectImage.{u, 0} Λ g).rightDerivedFunctorPlus.map
      ((etaleModuleDirectImage.{u, 0} Λ f).rightDerivedFunctorPlusUnith.app
      ((etaleModuleRestrictScalars ρ X).mapHomotopyCategoryPlus.obj K))
  let z := (etaleModuleDirectImage.{u, 0} Λ g).rightDerivedFunctorPlus.map
    ((etaleModuleDirectImage.{u, 0} Λ f).rightDerivedFunctorPlus.map
        ((etaleModuleRestrictScalars ρ X).mapDerivedCategoryPlusFactorsh.inv.app K))
  have hab : a ≫ b = p ≫ q ≫ m :=
    restrictScalars_map_unit_comp_derivedDirectImageComp ρ f g fg hfg K
  have hmt : m ≫ t = s₀ ≫ n := (etaleModuleDerivedDirectImageRestrictScalars ρ g).hom.naturality
      ((etaleModuleDirectImage.{u, 0} Λ' f).rightDerivedFunctorPlusUnith.app K)
  have hqs : q ≫ s₀ = F' ≫ ug' ≫ j := restrictScalars_directImage_unit_directImage ρ f g K
  have hjny : j ≫ n ≫ y = uf ≫ z := derivedDirectImage_map_restrictScalars_directImage_unit ρ f g K
  have hpF : p ≫ F' = F ≫ c := restrictScalars_mapDerivedCategoryPlusFactorsh_compIso ρ f g fg hfg K
  change a ≫ b ≫ t ≫ y = F ≫ c ≫ ug' ≫ uf ≫ z
  erw [reassoc_of% hab, reassoc_of% hmt, reassoc_of% hqs, Category.assoc, hjny,
    reassoc_of% hpF, Category.assoc]
  rfl

/-- **The restriction comparison is compatible with the composition of derived direct images**,
after the unit of `R(f ≫ g)_*`. -/
theorem restrictScalars_derivedDirectImageComp_unit :
    (etaleModuleRestrictScalars ρ Z).mapDerivedCategoryPlus.map
        ((etaleModuleDirectImage.{u, 0} Λ' fg).rightDerivedFunctorPlusUnith.app K) ≫
        (etaleModuleRestrictScalars ρ Z).mapDerivedCategoryPlus.map
            ((etaleModuleDerivedDirectImageComp.{u, 0} Λ' f g fg hfg).hom.app
            (DerivedCategory.Plus.Qh.obj K)) ≫
        (etaleModuleDerivedDirectImageRestrictScalars ρ g).hom.app
            ((etaleModuleDirectImage.{u, 0} Λ' f).rightDerivedFunctorPlus.obj
            (DerivedCategory.Plus.Qh.obj K)) ≫
        (etaleModuleDirectImage.{u, 0} Λ g).rightDerivedFunctorPlus.map
            ((etaleModuleDerivedDirectImageRestrictScalars ρ f).hom.app
            (DerivedCategory.Plus.Qh.obj K)) =
      (etaleModuleRestrictScalars ρ Z).mapDerivedCategoryPlus.map
          ((etaleModuleDirectImage.{u, 0} Λ' fg).rightDerivedFunctorPlusUnith.app K) ≫
        (etaleModuleDerivedDirectImageRestrictScalars ρ fg).hom.app
            (DerivedCategory.Plus.Qh.obj K) ≫
            (etaleModuleDerivedDirectImageComp.{u, 0} Λ f g fg hfg).hom.app
            ((etaleModuleRestrictScalars ρ X).mapDerivedCategoryPlus.obj
            (DerivedCategory.Plus.Qh.obj K)) :=
  (restrictScalars_derivedDirectImageComp_unit_left ρ f g fg hfg K).trans
    (restrictScalars_derivedDirectImageComp_unit_right ρ f g fg hfg K).symm

/-- **The restriction comparison is compatible with the composition of derived direct images**:
for `M` in `D⁺(X_étale, Λ')`, the two identifications of `res_ρ R(f ≫ g)_* M` with
`Rg_* Rf_* res_ρ M` agree. -/
theorem restrictScalars_derivedDirectImageComp (M : DerivedCategory.Plus
    (EtaleModules.{u, 0} Λ' X)) :
    (etaleModuleRestrictScalars ρ Z).mapDerivedCategoryPlus.map
        ((etaleModuleDerivedDirectImageComp.{u, 0} Λ' f g fg hfg).hom.app M) ≫
        (etaleModuleDerivedDirectImageRestrictScalars ρ g).hom.app
            ((etaleModuleDirectImage.{u, 0} Λ' f).rightDerivedFunctorPlus.obj M) ≫
        (etaleModuleDirectImage.{u, 0} Λ g).rightDerivedFunctorPlus.map
            ((etaleModuleDerivedDirectImageRestrictScalars ρ f).hom.app M) =
      (etaleModuleDerivedDirectImageRestrictScalars ρ fg).hom.app M ≫
          (etaleModuleDerivedDirectImageComp.{u, 0} Λ f g fg hfg).hom.app
          ((etaleModuleRestrictScalars ρ X).mapDerivedCategoryPlus.obj M) := by
  have h := Functor.rightDerivedFunctorPlus_comp_mapDerivedCategoryPlus_ext
      (etaleModuleDirectImage.{u, 0} Λ' fg) (etaleModuleRestrictScalars ρ Z)
    (Functor.whiskerRight (etaleModuleDerivedDirectImageComp.{u, 0} Λ' f g fg hfg).hom
        (etaleModuleRestrictScalars ρ Z).mapDerivedCategoryPlus ≫ (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (etaleModuleDirectImage.{u, 0} Λ' f).rightDerivedFunctorPlus
          (etaleModuleDerivedDirectImageRestrictScalars ρ g).hom ≫ (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (etaleModuleDerivedDirectImageRestrictScalars ρ f).hom
          (etaleModuleDirectImage.{u, 0} Λ g).rightDerivedFunctorPlus)
    ((etaleModuleDerivedDirectImageRestrictScalars ρ fg).hom ≫ Functor.whiskerLeft
        (etaleModuleRestrictScalars ρ X).mapDerivedCategoryPlus
        (etaleModuleDerivedDirectImageComp.{u, 0} Λ f g fg hfg).hom ≫
        (Functor.associator _ _ _).inv)
    (fun K => by
      simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
        Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
        Category.comp_id]
      exact restrictScalars_derivedDirectImageComp_unit ρ f g fg hfg K)
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id] using NatTrans.congr_app h M

/-- The compatibility of the restriction comparison with the composition of derived direct
images, for the inverse of the composition isomorphisms. -/
theorem restrictScalars_derivedDirectImageComp_inv
    (M : DerivedCategory.Plus (EtaleModules.{u, 0} Λ' X)) :
    (etaleModuleRestrictScalars ρ Z).mapDerivedCategoryPlus.map
        ((etaleModuleDerivedDirectImageComp.{u, 0} Λ' f g fg hfg).inv.app M) ≫
            (etaleModuleDerivedDirectImageRestrictScalars ρ fg).hom.app M =
      (etaleModuleDerivedDirectImageRestrictScalars ρ g).hom.app
          ((etaleModuleDirectImage.{u, 0} Λ' f).rightDerivedFunctorPlus.obj M) ≫
        (etaleModuleDirectImage.{u, 0} Λ g).rightDerivedFunctorPlus.map
            ((etaleModuleDerivedDirectImageRestrictScalars ρ f).hom.app M) ≫
        (etaleModuleDerivedDirectImageComp.{u, 0} Λ f g fg hfg).inv.app
          ((etaleModuleRestrictScalars ρ X).mapDerivedCategoryPlus.obj M) := by
  have h' : (etaleModuleRestrictScalars ρ Z).mapDerivedCategoryPlus.map
      ((etaleModuleDerivedDirectImageComp.{u, 0} Λ' f g fg hfg).hom.app M) ≫
      (etaleModuleDerivedDirectImageRestrictScalars ρ g).hom.app
          ((etaleModuleDirectImage.{u, 0} Λ' f).rightDerivedFunctorPlus.obj M) ≫
      (etaleModuleDirectImage.{u, 0} Λ g).rightDerivedFunctorPlus.map
          ((etaleModuleDerivedDirectImageRestrictScalars ρ f).hom.app M) ≫
      (etaleModuleDerivedDirectImageComp.{u, 0} Λ f g fg hfg).inv.app
        ((etaleModuleRestrictScalars ρ X).mapDerivedCategoryPlus.obj M) =
            (etaleModuleDerivedDirectImageRestrictScalars ρ fg).hom.app M := by
    rw [reassoc_of% restrictScalars_derivedDirectImageComp ρ f g fg hfg M, Iso.hom_inv_id_app,
      Category.comp_id]
  rw [← h', ← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]

end Comp

end Stacks.EtaleCohomology

end
