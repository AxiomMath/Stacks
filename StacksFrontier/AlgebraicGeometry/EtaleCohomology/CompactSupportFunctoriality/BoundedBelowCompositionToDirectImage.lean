module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactSupportFunctoriality.BoundedBelowToDirectImage
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedBaseChangePlusPasting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.UnderivedExtensionByZeroPasting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.CompositionIsoNaturality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ExtensionByZeroRestrict
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.OpenImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleDerivedIdentity
import StacksCore.Tactic.StacksAttribute

/-!
# The map `Rf_! ⟶ Rf_*` and composition, on `D⁺_tors`

The map `Rf_! ⟶ Rf_*` of [Stacks, Tag 0H6X]
(`Stacks.EtaleCohomology.derivedLowerShriekToDirectImage`) is compatible with the isomorphism
`R(g ∘ f)_! ≅ Rg_! ∘ Rf_!` of [Stacks, Tag 0F7J] and the composition isomorphism
`R(g ∘ f)_* ≅ Rg_* ∘ Rf_*` of Cohomology on Sites, Tag 0D6E: this is compatibility (1) of the
remark, whose proof the source omits.

## Main results

* `Stacks.Cohomology.DerivedBaseChangePlus.derivedBaseChangePlus_natTrans`: the base change map
  on `D⁺` is natural in the vertical functors.
* `Stacks.EtaleCohomology.etaleModuleDerivedExtensionByZeroToDirectImagePlus_baseChange`: the map
  `Rj_! ⟶ Rj_*` commutes with base change along a cartesian square.

## References

* [Stacks Project, Tag 0H6X](https://stacks.math.columbia.edu/tag/0H6X)
* [Stacks Project, Tag 0F7J](https://stacks.math.columbia.edu/tag/0F7J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

/-! ### Naturality of the base change map in the vertical functors -/

namespace Stacks.Cohomology.DerivedBaseChangePlus

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

open Stacks.DerivedIndexing

section NatTrans

variable {A A' B B' : Type*} [Category* A] [Category* A'] [Category* B] [Category* B']
  [Abelian A] [Abelian A'] [Abelian B] [Abelian B']
  [HasDerivedCategory A] [HasDerivedCategory A'] [HasDerivedCategory B] [HasDerivedCategory B']
  [EnoughInjectives A] [EnoughInjectives A']
  {F F₀ : A ⥤ B} {F' F₀' : A' ⥤ B'} (G : B ⥤ B') (G' : A ⥤ A')
  [F.Additive] [F₀.Additive] [F'.Additive] [F₀'.Additive] [G.Additive] [G'.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']

omit [HasDerivedCategory A] [HasDerivedCategory A'] [HasDerivedCategory B]
  [HasDerivedCategory B'] [EnoughInjectives A] [EnoughInjectives A'] [PreservesFiniteLimits G]
  [PreservesFiniteColimits G] [PreservesFiniteLimits G'] [PreservesFiniteColimits G'] in
/-- The homotopy-level form of a compatibility `e ≫ α₀ = α ≫ e'` of base change squares, for
natural transformations `e` and `e'`. -/
lemma mapHomotopyCategoryPlus_natTrans_square (e : F ⟶ F₀) (e' : F' ⟶ F₀')
    (α : F ⋙ G ⟶ G' ⋙ F') (α₀ : F₀ ⋙ G ⟶ G' ⋙ F₀')
    (h : Functor.whiskerRight e G ≫ α₀ = α ≫ Functor.whiskerLeft G' e')
    (K : HomotopyCategory.Plus A) :
    G.mapHomotopyCategoryPlus.map ((Functor.mapHomotopyCategoryPlusNatTrans e).app K) ≫
        hmap G G' α₀ K =
      hmap G G' α K ≫
        (Functor.mapHomotopyCategoryPlusNatTrans e').app (G'.mapHomotopyCategoryPlus.obj K) := by
  apply (HomotopyCategory.Plus.ι B').map_injective
  change (NatTrans.mapHomotopyCategory (Functor.whiskerRight e G) (ComplexShape.up ℤ)).app
      K.obj ≫ (NatTrans.mapHomotopyCategory α₀ (ComplexShape.up ℤ)).app K.obj =
    (NatTrans.mapHomotopyCategory α (ComplexShape.up ℤ)).app K.obj ≫
      (NatTrans.mapHomotopyCategory (Functor.whiskerLeft G' e') (ComplexShape.up ℤ)).app
        K.obj
  rw [← NatTrans.comp_app, ← NatTrans.mapHomotopyCategory_comp, h,
    NatTrans.mapHomotopyCategory_comp, NatTrans.comp_app]

/-- **Naturality of the base change map in the vertical functors**, for natural transformations:
if `e : F ⟶ F₀` and `e' : F' ⟶ F₀'` carry `α` to `α₀`, then the base change maps of `α` and of
`α₀` correspond under `Re` and `Re'`. -/
theorem derivedBaseChangePlus_natTrans (e : F ⟶ F₀) (e' : F' ⟶ F₀') (α : F ⋙ G ⟶ G' ⋙ F')
    (α₀ : F₀ ⋙ G ⟶ G' ⋙ F₀')
    (h : Functor.whiskerRight e G ≫ α₀ = α ≫ Functor.whiskerLeft G' e') :
    Functor.whiskerRight (rightDerivedFunctorPlusNatTrans e) G.mapDerivedCategoryPlus ≫
        derivedBaseChangePlus F₀ F₀' G G' α₀ =
      derivedBaseChangePlus F F' G G' α ≫
        Functor.whiskerLeft G'.mapDerivedCategoryPlus (rightDerivedFunctorPlusNatTrans e') := by
  refine (F.rightDerivedFunctorPlus ⋙ G.mapDerivedCategoryPlus).rightDerived_ext
    (derivedBaseChangePlusUnit F G) (HomotopyCategory.Plus.quasiIso A) _ _ _
    (NatTrans.ext (funext fun K => ?_))
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  have hL : G.mapDerivedCategoryPlus.map (F.rightDerivedFunctorPlusUnith.app K) ≫
      G.mapDerivedCategoryPlus.map
        ((rightDerivedFunctorPlusNatTrans e).app (DerivedCategory.Plus.Qh.obj K)) ≫
      (derivedBaseChangePlus F₀ F₀' G G' α₀).app (DerivedCategory.Plus.Qh.obj K) =
      G.mapDerivedCategoryPlus.map (DerivedCategory.Plus.Qh.map
        ((Functor.mapHomotopyCategoryPlusNatTrans e).app K)) ≫
        (derivedBaseChangePlusAux F₀ F₀' G G' α₀).app K := by
    rw [← Category.assoc, ← Functor.map_comp, rightDerivedFunctorPlusNatTrans_app,
      Functor.map_comp, Category.assoc, derivedBaseChangePlus_fac]
  have hR : G.mapDerivedCategoryPlus.map (F.rightDerivedFunctorPlusUnith.app K) ≫
      (derivedBaseChangePlus F F' G G' α).app (DerivedCategory.Plus.Qh.obj K) ≫
      (rightDerivedFunctorPlusNatTrans e').app
        (G'.mapDerivedCategoryPlus.obj (DerivedCategory.Plus.Qh.obj K)) =
      (derivedBaseChangePlusAux F F' G G' α).app K ≫
      (rightDerivedFunctorPlusNatTrans e').app
        (G'.mapDerivedCategoryPlus.obj (DerivedCategory.Plus.Qh.obj K)) := by
    rw [← Category.assoc, derivedBaseChangePlus_fac]
  rw [hL, hR, derivedBaseChangePlusAux_app', derivedBaseChangePlusAux_app']
  have n₁ := G.mapDerivedCategoryPlusFactorsh.hom.naturality
    ((Functor.mapHomotopyCategoryPlusNatTrans e).app K)
  have n₂ := (rightDerivedFunctorPlusNatTrans e').naturality
    (G'.mapDerivedCategoryPlusFactorsh.inv.app K)
  have f₂ := rightDerivedFunctorPlusNatTrans_app e' (G'.mapHomotopyCategoryPlus.obj K)
  have hsq : DerivedCategory.Plus.Qh.map (G.mapHomotopyCategoryPlus.map
        ((Functor.mapHomotopyCategoryPlusNatTrans e).app K)) ≫
        DerivedCategory.Plus.Qh.map (hmap G G' α₀ K) =
      DerivedCategory.Plus.Qh.map (hmap G G' α K) ≫ DerivedCategory.Plus.Qh.map
        ((Functor.mapHomotopyCategoryPlusNatTrans e').app (G'.mapHomotopyCategoryPlus.obj K)) := by
    rw [← Functor.map_comp, ← Functor.map_comp,
      mapHomotopyCategoryPlus_natTrans_square G G' e e' α α₀ h K]
  simp only [Functor.comp_map, Functor.comp_obj] at n₁ n₂
  simp only [Category.assoc]
  rw [reassoc_of% n₁, reassoc_of% hsq, n₂, reassoc_of% f₂]

end NatTrans

section Restriction

variable {A B C : Type*} [Category* A] [Category* B] [Category* C] [Abelian A] [Abelian B]
  [Abelian C] (P : A ⥤ B) (E S : B ⥤ C) (R : C ⥤ B) (T : A ⥤ C) (U : A ⥤ A)
  [P.Additive] [E.Additive] [S.Additive] [R.Additive] [T.Additive] [U.Additive]

/-- **A pasting of natural transformations, read on bounded below complexes.** If
`ζ⁻¹ P`, `(ε R) P`, `e R` and `α` compose to `P ξ⁻¹`, for `ζ : E ⋙ R ≅ 𝟭`, `ε : E ⟶ S`,
`e : P ⋙ S ≅ T`, `α : T ⋙ R ⟶ U ⋙ P` and `ξ : U ≅ 𝟭`, then so do their degreewise actions on a
bounded below complex `L`, spelled through the induced functors of the factors. -/
theorem mapHomotopyCategoryPlus_paste_app {ζ : E ⋙ R ≅ 𝟭 B} {ε : E ⟶ S} {e : P ⋙ S ≅ T}
    {α : T ⋙ R ⟶ U ⋙ P} {ξ : U ≅ 𝟭 A}
    (h : Functor.whiskerLeft P ζ.inv ≫ Functor.whiskerLeft P (Functor.whiskerRight ε R) ≫
      Functor.whiskerRight e.hom R ≫ α = Functor.whiskerRight ξ.inv P)
    (L : HomotopyCategory.Plus A) :
    (Functor.mapHomotopyCategoryPlusNatIso ζ).inv.app (P.mapHomotopyCategoryPlus.obj L) ≫
        R.mapHomotopyCategoryPlus.map
          ((Functor.mapHomotopyCategoryPlusNatTrans ε).app (P.mapHomotopyCategoryPlus.obj L)) ≫
        R.mapHomotopyCategoryPlus.map ((Functor.mapHomotopyCategoryPlusNatIso e).hom.app L) ≫
        hmap R U α L =
      P.mapHomotopyCategoryPlus.map ((Functor.mapHomotopyCategoryPlusNatIso ξ).inv.app L) := by
  have h' := congrArg (fun t => (Functor.mapHomotopyCategoryPlusNatTrans t).app L) h
  simp only [Functor.mapHomotopyCategoryPlusNatTrans_comp_app,
    Functor.mapHomotopyCategoryPlusNatTrans_whiskerLeft_app,
    Functor.mapHomotopyCategoryPlusNatTrans_whiskerRight_app] at h'
  exact h'

end Restriction

end Stacks.Cohomology.DerivedBaseChangePlus

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

open Stacks.DerivedIndexing Stacks.Cohomology.DerivedBaseChangePlus

variable (Λ : Type) [Ring Λ]

/-! ### `Rj_! ⟶ Rj_*` and base change -/

section BaseChange

variable {X X' Xb Xb' : Scheme.{u}} {g' : X' ⟶ X} {j : X ⟶ Xb} {j' : X' ⟶ Xb'} {φ : Xb' ⟶ Xb}
  [IsOpenImmersion j] [IsOpenImmersion j']

/-- **The map `Rj_! ⟶ Rj_*` commutes with base change** on `D⁺`: for a cartesian square
`g' ≫ j = j' ≫ φ` with `j`, `j'` open immersions, `φ^{-1}` of `Rj_! ⟶ Rj_*` followed by the base
change map `φ^{-1} Rj_* ⟶ Rj'_* g'^{-1}` is the isomorphism `φ^{-1} Rj_! ≅ Rj'_! g'^{-1}` of
[Stacks, Tag 03S6] followed by `Rj'_! ⟶ Rj'_*`. -/
theorem etaleModuleDerivedExtensionByZeroToDirectImagePlus_baseChange (hc : IsPullback g' j' j φ) :
    Functor.whiskerRight (etaleModuleDerivedExtensionByZeroToDirectImagePlus.{u, 0} Λ j)
        (etaleModuleDerivedInverseImagePlus.{u, 0} Λ φ) ≫
      etaleModuleDerivedBaseChange.{u, 0} Λ j j' φ g' hc.w.symm =
    (etaleModuleDerivedExtensionByZeroCubeIso Λ hc).inv ≫
      Functor.whiskerLeft (etaleModuleDerivedInverseImagePlus.{u, 0} Λ g')
        (etaleModuleDerivedExtensionByZeroToDirectImagePlus.{u, 0} Λ j') := by
  rw [etaleModuleDerivedExtensionByZeroCubeIso_inv]
  refine derivedBaseChangePlus_natTrans _ _ _ _ _ _ ?_
  ext F : 2
  exact ExtensionByZeroPasting.map_extensionByZeroToDirectImage_comp_baseChange Λ hc F

end BaseChange

/-! ### Underived inputs -/

section Underived

variable (Λ : Type) [Ring Λ]

/-- `h_*` of the unit of `(𝟙)^{-1} ⊣ 𝟙_*`, read through `𝟙_* ⋙ h_* ≅ h_*`, is `h_*` of the
inverse of `(𝟙)^{-1} ≅ 𝟭`. -/
lemma etaleModuleDirectImage_map_inverseImageAdj_id_unit {X Y : Scheme.{u}} (h : X ⟶ Y)
    (w : h = 𝟙 X ≫ h) (F : EtaleModules.{u, 0} Λ X) :
    (etaleModuleDirectImage.{u, 0} Λ h).map
        ((etaleModuleInverseImageAdj.{u, 0} Λ (𝟙 X)).unit.app F) ≫
      (etaleModuleDirectImageComp.{u, 0} Λ (𝟙 X) h h w).hom.app
        ((etaleModuleInverseImage.{u, 0} Λ (𝟙 X)).obj F) =
    (etaleModuleDirectImage.{u, 0} Λ h).map
        ((etaleModuleInverseImageIdIso.{u, 0} Λ X).inv.app F) := by
  let A₁ : 𝟭 (EtaleModules.{u, 0} Λ X) ⊣ etaleModuleDirectImage.{u, 0} Λ (𝟙 X) :=
    Adjunction.id.ofNatIsoRight
      (Functor.sheafPushforwardContinuousId' (smallEtaleBaseChangeId X) _ _).symm
  have u := Adjunction.unit_leftAdjointUniq_hom_app A₁ (etaleModuleInverseImageAdj.{u, 0} Λ (𝟙 X)) F
  have hξ : (etaleModuleInverseImageIdIso.{u, 0} Λ X).inv.app F =
      (Adjunction.leftAdjointUniq A₁ (etaleModuleInverseImageAdj.{u, 0} Λ (𝟙 X))).hom.app F :=
    Adjunction.leftAdjointUniq_inv_app _ _ F
  have n := (etaleModuleDirectImageComp.{u, 0} Λ (𝟙 X) h h w).hom.naturality
    ((Adjunction.leftAdjointUniq A₁ (etaleModuleInverseImageAdj.{u, 0} Λ (𝟙 X))).hom.app F)
  have key : (etaleModuleDirectImage.{u, 0} Λ h).map (A₁.unit.app F) ≫
      (etaleModuleDirectImageComp.{u, 0} Λ (𝟙 X) h h w).hom.app F = 𝟙 _ := by
    refine Sheaf.hom_ext (NatTrans.ext (funext fun U => ?_))
    simp only [A₁, Adjunction.ofNatIsoRight_unit, Adjunction.id_unit, NatTrans.comp_app,
      Functor.whiskerLeft_app, Iso.symm_hom, ObjectProperty.FullSubcategory.comp_hom,
      Category.id_comp]
    simp only [Functor.id_obj, Functor.comp_obj, Functor.sheafPushforwardContinuous_map_hom_app,
      Functor.sheafPushforwardContinuousId'_inv_app_hom_app, etaleModuleDirectImageComp,
      smallEtalePushforwardComp'_hom_app_hom_app,
      smallEtaleBaseChangeComp'_id_left_hom_app (𝟙 X) rfl, smallEtaleBaseChangeIdOf, eqToIso_refl,
      Iso.refl_trans, ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app]
    exact (F.obj.map_comp _ _).symm.trans ((congrArg F.obj.map (op_comp.symm.trans
      ((congrArg Quiver.Hom.op (Iso.inv_hom_id_app (smallEtaleBaseChangeId X) _)).trans
        op_id))).trans (F.obj.map_id _))
  rw [← u, hξ, Functor.map_comp, Category.assoc]
  simp only [Functor.comp_map] at n
  rw [n, ← Category.assoc]
  exact (eq_whisker key _).trans (Category.id_comp _)

/-- Restricted to `U`, the map `j_! ⟶ j_*` is the identity, with `j^{-1}` the inverse image:
`F ≅ j^{-1} j_! F ⟶ j^{-1} j_* F ⟶ F` is the identity. -/
lemma etaleModuleExtensionByZeroInverseImageIso_inv_comp_counit {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (F : EtaleModules.{u, 0} Λ U) :
    (etaleModuleExtensionByZeroInverseImageIso Λ j).inv.app F ≫
      (etaleModuleInverseImage.{u, 0} Λ j).map
        ((etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ j).app F) ≫
      (etaleModuleInverseImageAdj.{u, 0} Λ j).counit.app F = 𝟙 F := by
  have nρ := (etaleModuleInverseImageRestrictionIso.{u, 0} Λ j).inv.naturality
    ((etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ j).app F)
  have cρ : (etaleModuleInverseImageRestrictionIso.{u, 0} Λ j).inv.app
        ((etaleModuleDirectImage.{u, 0} Λ j).obj F) ≫
        (etaleModuleInverseImageAdj.{u, 0} Λ j).counit.app F =
      (etaleModuleRestrictionDirectImageAdj.{u, 0} Λ j).counit.app F := by
    rw [etaleModuleInverseImageRestrictionIso, Adjunction.leftAdjointUniq_inv_app,
      Adjunction.leftAdjointUniq_hom_app_counit]
  simp only [etaleModuleExtensionByZeroInverseImageIso, Iso.trans_inv, NatTrans.comp_app,
    Iso.symm_inv, asIso_hom, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, Category.assoc]
  rw [← reassoc_of% nρ, cρ]
  exact ExtensionByZeroPasting.unit_comp_map_extensionByZeroToDirectImage_comp_counit Λ j F

/-- **The underived form of
`Stacks.EtaleCohomology.etaleModuleDerivedExtensionByZeroToDirectImagePlus_comp_baseChange`.** -/
lemma etaleModuleExtensionByZeroToDirectImage_comp_baseChange {X Y Ub : Scheme.{u}} (f : X ⟶ Y)
    (i : Y ⟶ Ub) [IsOpenImmersion i] (F : EtaleModules.{u, 0} Λ X) :
    (etaleModuleExtensionByZeroInverseImageIso Λ i).inv.app
        ((etaleModuleDirectImage.{u, 0} Λ f).obj F) ≫
      (etaleModuleInverseImage.{u, 0} Λ i).map
        ((etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ i).app
          ((etaleModuleDirectImage.{u, 0} Λ f).obj F)) ≫
      (etaleModuleInverseImage.{u, 0} Λ i).map
        ((etaleModuleDirectImageComp.{u, 0} Λ f i (f ≫ i) rfl).hom.app F) ≫
      (etaleModuleBaseChange Λ (f ≫ i) f i (𝟙 X) (Category.id_comp _).symm).app F =
    (etaleModuleDirectImage.{u, 0} Λ f).map
        ((etaleModuleInverseImageIdIso.{u, 0} Λ X).inv.app F) := by
  let adj := etaleModuleInverseImageAdj.{u, 0} Λ i
  let e := etaleModuleDirectImageComp.{u, 0} Λ f i (f ≫ i) rfl
  let ξi := (etaleModuleInverseImageIdIso.{u, 0} Λ X).inv.app F
  have hu := ExtensionByZeroPasting.unit_comp_map_etaleModuleBaseChange Λ (f ≫ i) f i (𝟙 X)
    (Category.id_comp _).symm F
  have hΘ := etaleModuleDirectImage_map_inverseImageAdj_id_unit Λ (f ≫ i)
    (Category.id_comp _).symm F
  have ne := e.hom.naturality ξi
  simp only [Functor.comp_map] at ne
  -- the base change map through the adjunction
  have hBC : (etaleModuleBaseChange Λ (f ≫ i) f i (𝟙 X) (Category.id_comp _).symm).app F =
      (etaleModuleInverseImage.{u, 0} Λ i).map
          (adj.unit.app ((etaleModuleDirectImage.{u, 0} Λ (f ≫ i)).obj F) ≫
            (etaleModuleDirectImage.{u, 0} Λ i).map
              ((etaleModuleBaseChange Λ (f ≫ i) f i (𝟙 X) (Category.id_comp _).symm).app F)) ≫
        adj.counit.app _ := by
    rw [Functor.map_comp, Category.assoc]
    exact ((whisker_eq _ (adj.counit_naturality _)).trans ((Category.assoc _ _ _).symm.trans
      ((eq_whisker (adj.left_triangle_components _) _).trans (Category.id_comp _)))).symm
  have hmid : e.hom.app F ≫ adj.unit.app ((etaleModuleDirectImage.{u, 0} Λ (f ≫ i)).obj F) ≫
      (etaleModuleDirectImage.{u, 0} Λ i).map
        ((etaleModuleBaseChange Λ (f ≫ i) f i (𝟙 X) (Category.id_comp _).symm).app F) =
      (etaleModuleDirectImage.{u, 0} Λ i).map ((etaleModuleDirectImage.{u, 0} Λ f).map ξi) := by
    rw [hu, NatTrans.comp_app, reassoc_of% hΘ]
    have ne' : e.hom.app F ≫ (etaleModuleDirectImage.{u, 0} Λ (f ≫ i)).map
        ((etaleModuleInverseImageIdIso.{u, 0} Λ X).inv.app F) =
        (etaleModuleDirectImage.{u, 0} Λ i).map ((etaleModuleDirectImage.{u, 0} Λ f).map ξi) ≫
          e.hom.app _ := ne.symm
    rw [reassoc_of% ne', Iso.hom_inv_id_app]
    exact Category.comp_id _
  rw [hBC, ← Category.assoc ((etaleModuleInverseImage.{u, 0} Λ i).map _),
    ← Functor.map_comp, ← Category.assoc ((etaleModuleInverseImage.{u, 0} Λ i).map _),
    ← Functor.map_comp, Category.assoc, hmid, Functor.map_comp, Category.assoc]
  exact (whisker_eq _ (whisker_eq _ (adj.counit_naturality _))).trans
    (((Category.assoc _ _ _).trans (whisker_eq _ (Category.assoc _ _ _))).symm.trans
      ((eq_whisker (etaleModuleExtensionByZeroInverseImageIso_inv_comp_counit Λ i _) _).trans
        (Category.id_comp _)))

end Underived

/-! ### The map `Rf_! ⟶ Rf_*` restricted along an open immersion -/

section Restriction

variable {X Y Ub : Scheme.{u}} (f : X ⟶ Y) (i : Y ⟶ Ub) [IsOpenImmersion i]

/-- **`Ri_! ⟶ Ri_*`, followed by `Ri_* ∘ Rf_* ≅ R(f ≫ i)_*`, restricted along `i`.** For an open
immersion `i` and any `f`, the composite
`Rf_* K ≅ i^{-1} Ri_! Rf_* K ⟶ i^{-1} Ri_* Rf_* K ≅ i^{-1} R(f ≫ i)_* K ⟶ Rf_* (𝟙)^{-1} K`, whose
last arrow is the base change map of the square `f ≫ i = 𝟙 ≫ (f ≫ i)`, is `Rf_*` of
`K ≅ (𝟙)^{-1} K`. -/
theorem etaleModuleDerivedExtensionByZeroToDirectImagePlus_comp_baseChange
    (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X)) :
    (etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ i).inv.app
        ((etaleModuleDerivedDirectImage.{u, 0} Λ f).obj K) ≫
      (etaleModuleDerivedInverseImagePlus.{u, 0} Λ i).map
        ((etaleModuleDerivedExtensionByZeroToDirectImagePlus.{u, 0} Λ i).app
          ((etaleModuleDerivedDirectImage.{u, 0} Λ f).obj K)) ≫
      (etaleModuleDerivedInverseImagePlus.{u, 0} Λ i).map
        ((etaleModuleDerivedDirectImageComp.{u, 0} Λ f i (f ≫ i) rfl).inv.app K) ≫
      (etaleModuleDerivedBaseChange.{u, 0} Λ (f ≫ i) f i (𝟙 X) (Category.id_comp _).symm).app K =
    (etaleModuleDerivedDirectImage.{u, 0} Λ f).map
      ((etaleModuleDerivedInverseImagePlusIdIso Λ X).inv.app K) := by
  -- the underived identity, as an identity of natural transformations
  have h₀ : Functor.whiskerLeft (etaleModuleDirectImage.{u, 0} Λ f)
        (etaleModuleExtensionByZeroInverseImageIso Λ i).inv ≫
      Functor.whiskerLeft (etaleModuleDirectImage.{u, 0} Λ f)
        (Functor.whiskerRight (etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ i)
          (etaleModuleInverseImage.{u, 0} Λ i)) ≫
      Functor.whiskerRight (etaleModuleDirectImageComp.{u, 0} Λ f i (f ≫ i) rfl).hom
        (etaleModuleInverseImage.{u, 0} Λ i) ≫
      etaleModuleBaseChange Λ (f ≫ i) f i (𝟙 X) (Category.id_comp _).symm =
      Functor.whiskerRight (etaleModuleInverseImageIdIso.{u, 0} Λ X).inv
        (etaleModuleDirectImage.{u, 0} Λ f) := by
    ext F : 2
    exact etaleModuleExtensionByZeroToDirectImage_comp_baseChange Λ f i F
  have key : Functor.whiskerLeft (etaleModuleDerivedDirectImage.{u, 0} Λ f)
        (etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ i).inv ≫
      Functor.whiskerLeft (etaleModuleDerivedDirectImage.{u, 0} Λ f)
        (Functor.whiskerRight (etaleModuleDerivedExtensionByZeroToDirectImagePlus.{u, 0} Λ i)
          (etaleModuleDerivedInverseImagePlus.{u, 0} Λ i)) ≫
      Functor.whiskerRight (etaleModuleDerivedDirectImageComp.{u, 0} Λ f i (f ≫ i) rfl).inv
        (etaleModuleDerivedInverseImagePlus.{u, 0} Λ i) ≫
      etaleModuleDerivedBaseChange.{u, 0} Λ (f ≫ i) f i (𝟙 X) (Category.id_comp _).symm =
      Functor.whiskerRight (etaleModuleDerivedInverseImagePlusIdIso Λ X).inv
        (etaleModuleDerivedDirectImage.{u, 0} Λ f) := by
    refine Functor.rightDerived_ext (etaleModuleDerivedDirectImage.{u, 0} Λ f)
      (etaleModuleDirectImage.{u, 0} Λ f).rightDerivedFunctorPlusUnith
      (HomotopyCategory.Plus.quasiIso _) _ _ _ (NatTrans.ext (funext fun L => ?_))
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    -- notation: `M = f_* L`; the units of `Rf_*`, `Ri_!`, `Ri_*`, `R(f ≫ i)_*`
    have s1 := (etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ i).inv.naturality
      ((etaleModuleDirectImage.{u, 0} Λ f).rightDerivedFunctorPlusUnith.app L)
    have s2 := congrArg (etaleModuleDerivedInverseImagePlus.{u, 0} Λ i).map
      ((etaleModuleDerivedExtensionByZeroToDirectImagePlus.{u, 0} Λ i).naturality
        ((etaleModuleDirectImage.{u, 0} Λ f).rightDerivedFunctorPlusUnith.app L))
    simp only [Functor.map_comp] at s2
    have s4 := etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso_hom_app_Qh Λ i
      ((etaleModuleDirectImage.{u, 0} Λ f).mapHomotopyCategoryPlus.obj L)
    have s5 := rightDerivedFunctorPlusNatTrans_app
      (etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ i)
      ((etaleModuleDirectImage.{u, 0} Λ f).mapHomotopyCategoryPlus.obj L)
    have s3a := Functor.rightDerivedFunctorPlusNatIso_inv_fac_app
      (etaleModuleDirectImageComp.{u, 0} Λ f i (f ≫ i) rfl) L
    have s3b := Functor.unit_comp_rightDerivedFunctorPlusComp_app
      (etaleModuleDirectImage.{u, 0} Λ f) (etaleModuleDirectImage.{u, 0} Λ i) L
    have s6 := (etaleModuleDerivedBaseChange_fac Λ (f ≫ i) f i (𝟙 X) (Category.id_comp _).symm
      L).trans (Stacks.Cohomology.DerivedBaseChangePlus.derivedBaseChangePlusAux_app' _ _ _ L)
    have s7 := etaleModuleDerivedInverseImagePlusIdIso_hom_app_Qh Λ X L
    have s8 := (etaleModuleDirectImage.{u, 0} Λ f).rightDerivedFunctorPlusUnith.naturality
      ((Functor.mapHomotopyCategoryPlusNatIso (etaleModuleInverseImageIdIso.{u, 0} Λ X)).inv.app L)
    dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_map, Functor.id_obj]
      at s1 s2 s3a s3b s4 s5 s6 s7 s8 ⊢
    -- (A) move the unit of `Rf_*` past `ζ⁻¹` and `Rj_! ⟶ Rj_*`
    have hA := ((reassoc_of% s1) _).trans (whisker_eq _ s2)
    -- (B) the unit of `Ri_*` against the composition isomorphism
    have hB0 : (etaleModuleDirectImage.{u, 0} Λ (f ≫ i)).rightDerivedFunctorPlusUnith.app L ≫
        (etaleModuleDerivedDirectImageComp.{u, 0} Λ f i (f ≫ i) rfl).hom.app
          (DerivedCategory.Plus.Qh.obj L) =
        DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusNatIso
            (etaleModuleDirectImageComp.{u, 0} Λ f i (f ≫ i) rfl)).inv.app L) ≫
          (etaleModuleDirectImage.{u, 0} Λ i).rightDerivedFunctorPlusUnith.app
            ((etaleModuleDirectImage.{u, 0} Λ f).mapHomotopyCategoryPlus.obj L) ≫
          (etaleModuleDirectImage.{u, 0} Λ i).rightDerivedFunctorPlus.map
            ((etaleModuleDirectImage.{u, 0} Λ f).rightDerivedFunctorPlusUnith.app L) := by
      rw [etaleModuleDerivedDirectImageComp_hom_eq_univ, NatTrans.comp_app]
      exact ((reassoc_of% s3a) _).trans (whisker_eq _ s3b)
    have hB : (etaleModuleDirectImage.{u, 0} Λ i).rightDerivedFunctorPlusUnith.app
          ((etaleModuleDirectImage.{u, 0} Λ f).mapHomotopyCategoryPlus.obj L) ≫
        (etaleModuleDirectImage.{u, 0} Λ i).rightDerivedFunctorPlus.map
          ((etaleModuleDirectImage.{u, 0} Λ f).rightDerivedFunctorPlusUnith.app L) ≫
        (etaleModuleDerivedDirectImageComp.{u, 0} Λ f i (f ≫ i) rfl).inv.app
          (DerivedCategory.Plus.Qh.obj L) =
        DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusNatIso
            (etaleModuleDirectImageComp.{u, 0} Λ f i (f ≫ i) rfl)).hom.app L) ≫
          (etaleModuleDirectImage.{u, 0} Λ (f ≫ i)).rightDerivedFunctorPlusUnith.app L := by
      refine (cancel_mono ((etaleModuleDerivedDirectImageComp.{u, 0} Λ f i (f ≫ i) rfl).hom.app
        (DerivedCategory.Plus.Qh.obj L))).1 ?_
      refine ((Category.assoc _ _ _).trans (whisker_eq _ ((Category.assoc _ _ _).trans
        ((whisker_eq _ (Iso.inv_hom_id_app
          (etaleModuleDerivedDirectImageComp.{u, 0} Λ f i (f ≫ i) rfl) _)).trans
            (Category.comp_id _))))).trans ?_
      refine Eq.symm ((Category.assoc _ _ _).trans ((whisker_eq _ hB0).trans ?_))
      exact (Functor.map_comp_assoc _ _ _ _).symm.trans ((eq_whisker ((congrArg _
        (Iso.hom_inv_id_app _ _)).trans (CategoryTheory.Functor.map_id _ _)) _).trans
          (Category.id_comp _))
    -- (C) the unit of `Ri_!` through `Rj_! ⟶ Rj_*` and the composition isomorphism
    have hC := ((reassoc_of% s5) _).trans (whisker_eq _ hB)
    -- (D) `ζ⁻¹` at the image of a complex
    have hD : (etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ i).inv.app
          (DerivedCategory.Plus.Qh.obj
            ((etaleModuleDirectImage.{u, 0} Λ f).mapHomotopyCategoryPlus.obj L)) =
        DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusNatIso
            (etaleModuleExtensionByZeroInverseImageIso Λ i)).inv.app
              ((etaleModuleDirectImage.{u, 0} Λ f).mapHomotopyCategoryPlus.obj L)) ≫
          (etaleModuleInverseImage.{u, 0} Λ i).mapDerivedCategoryPlusFactorsh.inv.app
            ((etaleModuleExtensionByZero.{u, 0} Λ i).mapHomotopyCategoryPlus.obj
              ((etaleModuleDirectImage.{u, 0} Λ f).mapHomotopyCategoryPlus.obj L)) ≫
          (etaleModuleDerivedInverseImagePlus.{u, 0} Λ i).map
            ((etaleModuleExtensionByZero.{u, 0} Λ i).rightDerivedFunctorPlusUnith.app
              ((etaleModuleDirectImage.{u, 0} Λ f).mapHomotopyCategoryPlus.obj L)) := by
      refine (cancel_mono ((etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ i).hom.app
        (DerivedCategory.Plus.Qh.obj
          ((etaleModuleDirectImage.{u, 0} Λ f).mapHomotopyCategoryPlus.obj L)))).1 ?_
      refine (Iso.inv_hom_id_app _ _).trans (Eq.symm ((Category.assoc _ _ _).trans
        ((whisker_eq _ ((Category.assoc _ _ _).trans ((whisker_eq _ s4).trans
          (Iso.inv_hom_id_app_assoc _ _ _)))).trans ?_)))
      exact (Functor.map_comp _ _ _).symm.trans ((congrArg _ (Iso.inv_hom_id_app _ _)).trans
        (CategoryTheory.Functor.map_id _ _))
    -- (I) the inverse of `(𝟙)^{-1} ≅ 𝟭` at the image of a complex
    have hI : (etaleModuleDerivedInverseImagePlusIdIso Λ X).inv.app
        (DerivedCategory.Plus.Qh.obj L) =
        DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusNatIso
            (etaleModuleInverseImageIdIso.{u, 0} Λ X)).inv.app L) ≫
          (etaleModuleInverseImage.{u, 0} Λ (𝟙 X)).mapDerivedCategoryPlusFactorsh.inv.app L := by
      refine (cancel_mono ((etaleModuleDerivedInverseImagePlusIdIso Λ X).hom.app
        (DerivedCategory.Plus.Qh.obj L))).1 ?_
      refine (Iso.inv_hom_id_app _ _).trans (Eq.symm ((Category.assoc _ _ _).trans
        ((whisker_eq _ s7).trans ?_)))
      exact (Functor.map_comp _ _ _).symm.trans ((congrArg _ (Iso.inv_hom_id_app _ _)).trans
        (CategoryTheory.Functor.map_id _ _))
    -- (H) the underived identity on complexes
    have hH : (Functor.mapHomotopyCategoryPlusNatIso
          (etaleModuleExtensionByZeroInverseImageIso Λ i)).inv.app
            ((etaleModuleDirectImage.{u, 0} Λ f).mapHomotopyCategoryPlus.obj L) ≫
        (etaleModuleInverseImage.{u, 0} Λ i).mapHomotopyCategoryPlus.map
          ((Functor.mapHomotopyCategoryPlusNatTrans
            (etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ i)).app
              ((etaleModuleDirectImage.{u, 0} Λ f).mapHomotopyCategoryPlus.obj L)) ≫
        (etaleModuleInverseImage.{u, 0} Λ i).mapHomotopyCategoryPlus.map
          ((Functor.mapHomotopyCategoryPlusNatIso
            (etaleModuleDirectImageComp.{u, 0} Λ f i (f ≫ i) rfl)).hom.app L) ≫
        hmap (etaleModuleInverseImage.{u, 0} Λ i) (etaleModuleInverseImage.{u, 0} Λ (𝟙 X))
          (etaleModuleBaseChange Λ (f ≫ i) f i (𝟙 X) (Category.id_comp _).symm) L =
        (etaleModuleDirectImage.{u, 0} Λ f).mapHomotopyCategoryPlus.map
          ((Functor.mapHomotopyCategoryPlusNatIso
            (etaleModuleInverseImageIdIso.{u, 0} Λ X)).inv.app L) :=
      mapHomotopyCategoryPlus_paste_app _ _ _ _ _ _ h₀ L
    have s9a := (etaleModuleInverseImage.{u, 0} Λ i).mapDerivedCategoryPlusFactorsh.hom.naturality
      ((Functor.mapHomotopyCategoryPlusNatTrans
        (etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ i)).app
          ((etaleModuleDirectImage.{u, 0} Λ f).mapHomotopyCategoryPlus.obj L))
    have s9b := (etaleModuleInverseImage.{u, 0} Λ i).mapDerivedCategoryPlusFactorsh.hom.naturality
      ((Functor.mapHomotopyCategoryPlusNatIso
        (etaleModuleDirectImageComp.{u, 0} Λ f i (f ≫ i) rfl)).hom.app L)
    dsimp only [Functor.comp_map] at s9a s9b
    -- (L3) `i^{-1}` of (C)
    have hL3 : (etaleModuleDerivedInverseImagePlus.{u, 0} Λ i).map
          ((etaleModuleExtensionByZero.{u, 0} Λ i).rightDerivedFunctorPlusUnith.app
            ((etaleModuleDirectImage.{u, 0} Λ f).mapHomotopyCategoryPlus.obj L)) ≫
        (etaleModuleDerivedInverseImagePlus.{u, 0} Λ i).map
          ((etaleModuleDerivedExtensionByZeroToDirectImagePlus.{u, 0} Λ i).app
            (DerivedCategory.Plus.Qh.obj
              ((etaleModuleDirectImage.{u, 0} Λ f).mapHomotopyCategoryPlus.obj L))) ≫
        (etaleModuleDerivedInverseImagePlus.{u, 0} Λ i).map
          ((etaleModuleDerivedDirectImage.{u, 0} Λ i).map
            ((etaleModuleDirectImage.{u, 0} Λ f).rightDerivedFunctorPlusUnith.app L)) ≫
        (etaleModuleDerivedInverseImagePlus.{u, 0} Λ i).map
          ((etaleModuleDerivedDirectImageComp.{u, 0} Λ f i (f ≫ i) rfl).inv.app
            (DerivedCategory.Plus.Qh.obj L)) =
        (etaleModuleDerivedInverseImagePlus.{u, 0} Λ i).map
          (DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusNatTrans
            (etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ i)).app
              ((etaleModuleDirectImage.{u, 0} Λ f).mapHomotopyCategoryPlus.obj L))) ≫
        (etaleModuleDerivedInverseImagePlus.{u, 0} Λ i).map
          (DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusNatIso
            (etaleModuleDirectImageComp.{u, 0} Λ f i (f ≫ i) rfl)).hom.app L)) ≫
        (etaleModuleDerivedInverseImagePlus.{u, 0} Λ i).map
          ((etaleModuleDirectImage.{u, 0} Λ (f ≫ i)).rightDerivedFunctorPlusUnith.app L) := by
      refine (whisker_eq _ (whisker_eq _ (Functor.map_comp _ _ _).symm)).trans
        ((whisker_eq _ (Functor.map_comp _ _ _).symm).trans
          ((Functor.map_comp _ _ _).symm.trans ((congrArg _ hC).trans ?_)))
      exact (Functor.map_comp _ _ _).trans (whisker_eq _ (Functor.map_comp _ _ _))
    -- (QH) the localization of (H)
    have hQH : DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusNatIso
          (etaleModuleExtensionByZeroInverseImageIso Λ i)).inv.app
            ((etaleModuleDirectImage.{u, 0} Λ f).mapHomotopyCategoryPlus.obj L)) ≫
        DerivedCategory.Plus.Qh.map
          ((etaleModuleInverseImage.{u, 0} Λ i).mapHomotopyCategoryPlus.map
          ((Functor.mapHomotopyCategoryPlusNatTrans
            (etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ i)).app
              ((etaleModuleDirectImage.{u, 0} Λ f).mapHomotopyCategoryPlus.obj L))) ≫
        DerivedCategory.Plus.Qh.map
          ((etaleModuleInverseImage.{u, 0} Λ i).mapHomotopyCategoryPlus.map
          ((Functor.mapHomotopyCategoryPlusNatIso
            (etaleModuleDirectImageComp.{u, 0} Λ f i (f ≫ i) rfl)).hom.app L)) ≫
        DerivedCategory.Plus.Qh.map (hmap (etaleModuleInverseImage.{u, 0} Λ i)
          (etaleModuleInverseImage.{u, 0} Λ (𝟙 X))
          (etaleModuleBaseChange Λ (f ≫ i) f i (𝟙 X) (Category.id_comp _).symm) L) =
        DerivedCategory.Plus.Qh.map ((etaleModuleDirectImage.{u, 0} Λ f).mapHomotopyCategoryPlus.map
          ((Functor.mapHomotopyCategoryPlusNatIso
            (etaleModuleInverseImageIdIso.{u, 0} Λ X)).inv.app L)) :=
      (whisker_eq _ (whisker_eq _ (Functor.map_comp _ _ _).symm)).trans
        ((whisker_eq _ (Functor.map_comp _ _ _).symm).trans
          ((Functor.map_comp _ _ _).symm.trans (congrArg _ hH)))
    -- (R) the right-hand side
    have hR := (whisker_eq ((etaleModuleDirectImage.{u, 0} Λ f).rightDerivedFunctorPlusUnith.app L)
      ((congrArg (etaleModuleDerivedDirectImage.{u, 0} Λ f).map hI).trans
        (Functor.map_comp _ _ _))).trans ((reassoc_of% s8) _).symm
    -- the left-hand side
    refine ((reassoc_of% hA) _).trans ?_
    refine (eq_whisker hD _).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (whisker_eq _ (Category.assoc _ _ _)).trans ?_
    refine (whisker_eq _ (whisker_eq _ ((reassoc_of% hL3) _))).trans ?_
    refine (whisker_eq _ (whisker_eq _ (whisker_eq _ (whisker_eq _ s6)))).trans ?_
    refine (whisker_eq _ (whisker_eq _ (whisker_eq _ ((reassoc_of% s9b) _)))).trans ?_
    refine (whisker_eq _ (whisker_eq _ ((reassoc_of% s9a) _))).trans ?_
    refine (whisker_eq _ (Iso.inv_hom_id_app_assoc
      (etaleModuleInverseImage.{u, 0} Λ i).mapDerivedCategoryPlusFactorsh _ _)).trans ?_
    refine ((reassoc_of% hQH) _).trans ?_
    exact hR.symm
  exact NatTrans.congr_app key K

end Restriction

/-! ### Compatibility with the composition isomorphism of [Stacks, Tag 0F7J] -/

section Composition

attribute [local instance high] CompactificationOf.etale_restrictBaseι
  CompactificationOf.etale_overBar_immersion

variable {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} (jg : CompactificationOf (Over.mk g))
  (jX : CompactificationOf (Over.mk (f ≫ jg.immersion)))

/-- **The map `Rf_! ⟶ Rf_*` is compatible with `Ψ : R(f ≫ i)_! ≅ i_! ∘ Rf_!`**, for `i : Y ⟶ Ȳ`
the compactification of `g` and the compactifications of the proof of [Stacks, Tag 0F7J]:
`Ψ` followed by `i_!` of `Rf_! ⟶ Rf_*`, by `Ri_! ⟶ Ri_*` and by `Ri_* ∘ Rf_* ≅ R(f ≫ i)_*` is the
map `R(f ≫ i)_! ⟶ R(f ≫ i)_*`. -/
theorem derivedLowerShriekRestrictBaseIso_hom_comp_toDirectImage
    (K : (isTorsionPlus.{u, 0} Λ X).FullSubcategory) :
    (derivedLowerShriekRestrictBaseIso Λ jg jX).hom.app K ≫
        (etaleModuleDerivedExtensionByZero.{u, 0} Λ jg.immersion).map
          ((derivedLowerShriekToDirectImage.{u, 0} Λ f
            (CompactificationOf.restrictBase jg jX)).app K.obj) ≫
        (etaleModuleDerivedExtensionByZeroToDirectImagePlus.{u, 0} Λ jg.immersion).app
          ((etaleModuleDerivedDirectImage.{u, 0} Λ f).obj K.obj) ≫
        (etaleModuleDerivedDirectImageComp.{u, 0} Λ f jg.immersion (f ≫ jg.immersion) rfl).inv.app
          K.obj =
      (derivedLowerShriekToDirectImage.{u, 0} Λ (f ≫ jg.immersion)
        (CompactificationOf.overBar jg jX)).app K.obj := by
  have hw : (CompactificationOf.restrictBase jg jX).toBase ≫ jg.immersion =
      CompactificationOf.restrictBaseι jg jX ≫ jX.toBase :=
    (IsPullback.of_hasPullback jX.toBase jg.immersion).w.symm
  have hab : f ≫ jg.immersion = ((CompactificationOf.restrictBase jg jX).immersion ≫
      (CompactificationOf.restrictBaseι jg jX)) ≫ jX.toBase :=
    (CompactificationOf.immersion_toBase (CompactificationOf.overBar jg jX)).symm
  have haf : f = (CompactificationOf.restrictBase jg jX).immersion ≫
      (CompactificationOf.restrictBase jg jX).toBase := (CompactificationOf.immersion_toBase _).symm
  have hc : IsPullback (𝟙 (Over.mk f).left) (CompactificationOf.restrictBase jg jX).immersion
      ((CompactificationOf.restrictBase jg jX).immersion ≫ (CompactificationOf.restrictBaseι jg jX))
      (CompactificationOf.restrictBaseι jg jX) := by
    have h0 := CompactificationOf.isPullback_baseChangeImmersion
      (CompactificationOf.isPullback_id_comp_immersion jg) jX
    have e : jX.immersion = (CompactificationOf.restrictBase jg jX).immersion ≫
        (CompactificationOf.restrictBaseι jg jX) := by
      simp [CompactificationOf.restrictBase, CompactificationOf.restrictBaseι]
    rw [e] at h0
    exact h0
  have : IsIso ((etaleModuleDerivedBaseChange.{u, 0} Λ (f ≫ jg.immersion) f jg.immersion
      (𝟙 (Over.mk f).left) (Category.id_comp _).symm).app K.obj) :=
    isIso_etaleModuleDerivedBaseChange_of_isOpenImmersion Λ (f ≫ jg.immersion)
      (CompactificationOf.isPullback_id_comp_immersion jg) K.obj
  have : IsIso ((etaleModuleDerivedBaseChange.{u, 0} Λ jX.toBase
      (CompactificationOf.restrictBase jg jX).toBase jg.immersion
      (CompactificationOf.restrictBaseι jg jX) hw).app
      ((etaleModuleDerivedExtensionByZero.{u, 0} Λ
      ((CompactificationOf.restrictBase jg jX).immersion ≫
      (CompactificationOf.restrictBaseι jg jX))).obj K.obj)) :=
    isIso_etaleModuleDerivedBaseChange_of_isOpenImmersion Λ jX.toBase
      (IsPullback.of_hasPullback jX.toBase jg.immersion) _
  -- the map `Rf_! ⟶ Rf_*` of the induced compactification and the map of `overBar`
  have hτa : (derivedLowerShriekToDirectImage.{u, 0} Λ f
      (CompactificationOf.restrictBase jg jX)).app K.obj =
      (etaleModuleDerivedDirectImage.{u, 0} Λ (CompactificationOf.restrictBase jg jX).toBase).map
          ((etaleModuleDerivedExtensionByZeroToDirectImagePlus.{u, 0} Λ
              (CompactificationOf.restrictBase jg jX).immersion).app K.obj) ≫
        (etaleModuleDerivedDirectImageComp.{u, 0} Λ
            (CompactificationOf.restrictBase jg jX).immersion
            (CompactificationOf.restrictBase jg jX).toBase f haf).inv.app K.obj := rfl
  have hτb : (derivedLowerShriekToDirectImage.{u, 0} Λ (f ≫ jg.immersion)
      (CompactificationOf.overBar jg jX)).app K.obj =
      (etaleModuleDerivedDirectImage.{u, 0} Λ jX.toBase).map
          ((etaleModuleDerivedExtensionByZeroToDirectImagePlus.{u, 0} Λ
              ((CompactificationOf.restrictBase jg jX).immersion ≫
              (CompactificationOf.restrictBaseι jg jX))).app K.obj) ≫
        (etaleModuleDerivedDirectImageComp.{u, 0} Λ
            ((CompactificationOf.restrictBase jg jX).immersion ≫
            (CompactificationOf.restrictBaseι jg jX)) jX.toBase (f ≫ jg.immersion)
          hab).inv.app
            K.obj := rfl
  have hR := derivedLowerShriekRestrictBaseIso_restrict Λ jg jX K
  have hρ : (etaleModuleDerivedExtensionByZeroRestrictIso Λ
      (CompactificationOf.restrictBase jg jX).immersion
      (CompactificationOf.restrictBaseι jg jX)).hom.app K.obj ≫
      (etaleModuleDerivedExtensionByZero.{u, 0} Λ
          (CompactificationOf.restrictBase jg jX).immersion).map
        ((etaleModuleDerivedInverseImagePlusIdIso Λ (Over.mk f).left).inv.app K.obj) =
      (etaleModuleDerivedExtensionByZeroCubeIso Λ hc).inv.app K.obj := by
    rw [etaleModuleDerivedExtensionByZeroRestrictIso_hom Λ
        (CompactificationOf.restrictBase jg jX).immersion (CompactificationOf.restrictBaseι jg jX)
        hc]
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
      Category.assoc]
    refine (whisker_eq _ ?_).trans (Category.comp_id _)
    exact (whisker_eq _ (Category.id_comp _)).trans ((Functor.map_comp _ _ _).symm.trans
      ((congrArg _ (Iso.hom_inv_id_app _ _)).trans (CategoryTheory.Functor.map_id _ _)))
  have hP := NatTrans.congr_app (etaleModuleDerivedBaseChange_comp Λ
      ((CompactificationOf.restrictBase jg jX).immersion ≫ (CompactificationOf.restrictBaseι jg jX))
      jX.toBase (f ≫ jg.immersion)
    hab (CompactificationOf.restrictBase jg jX).immersion
        (CompactificationOf.restrictBase jg jX).toBase f
    haf (𝟙 (Over.mk f).left) (CompactificationOf.restrictBaseι jg jX) jg.immersion hc.w.symm
    hw (Category.id_comp _).symm) K.obj
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id] at hP
  have hε := NatTrans.congr_app
    (etaleModuleDerivedExtensionByZeroToDirectImagePlus_baseChange Λ hc) K.obj
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hε
  have hO := etaleModuleDerivedExtensionByZeroToDirectImagePlus_comp_baseChange Λ
      (X := (Over.mk f).left) f jg.immersion K.obj
  have hT' : (etaleModuleDerivedInverseImagePlus.{u, 0} Λ jg.immersion).map
      ((etaleModuleDerivedDirectImage.{u, 0} Λ jX.toBase).map
          ((etaleModuleDerivedExtensionByZeroToDirectImagePlus.{u, 0} Λ
              ((CompactificationOf.restrictBase jg jX).immersion ≫
              (CompactificationOf.restrictBaseι jg jX))).app K.obj) ≫
        (etaleModuleDerivedDirectImageComp.{u, 0} Λ
            ((CompactificationOf.restrictBase jg jX).immersion ≫
            (CompactificationOf.restrictBaseι jg jX)) jX.toBase (f ≫ jg.immersion) hab).inv.app
            K.obj) ≫
      (etaleModuleDerivedBaseChange.{u, 0} Λ (f ≫ jg.immersion) f jg.immersion (𝟙 (Over.mk f).left)
          (Category.id_comp _).symm).app K.obj =
      (etaleModuleDerivedBaseChange.{u, 0} Λ jX.toBase
          (CompactificationOf.restrictBase jg jX).toBase jg.immersion
          (CompactificationOf.restrictBaseι jg jX) hw).app
          ((etaleModuleDerivedExtensionByZero.{u, 0} Λ
          ((CompactificationOf.restrictBase jg jX).immersion ≫
          (CompactificationOf.restrictBaseι jg jX))).obj K.obj) ≫
        (etaleModuleDerivedDirectImage.{u, 0} Λ (CompactificationOf.restrictBase jg jX).toBase).map
          ((etaleModuleDerivedExtensionByZeroRestrictIso Λ
              (CompactificationOf.restrictBase jg jX).immersion
              (CompactificationOf.restrictBaseι jg jX)).hom.app K.obj) ≫
        (etaleModuleDerivedDirectImage.{u, 0} Λ (CompactificationOf.restrictBase jg jX).toBase).map
          ((etaleModuleDerivedExtensionByZeroToDirectImagePlus.{u, 0} Λ
              (CompactificationOf.restrictBase jg jX).immersion).app K.obj) ≫
        (etaleModuleDerivedDirectImageComp.{u, 0} Λ
            (CompactificationOf.restrictBase jg jX).immersion
            (CompactificationOf.restrictBase jg jX).toBase f haf).inv.app K.obj ≫
        (etaleModuleDerivedDirectImage.{u, 0} Λ f).map
          ((etaleModuleDerivedInverseImagePlusIdIso Λ (Over.mk f).left).inv.app K.obj) := by
    have hP' : (etaleModuleDerivedInverseImagePlus.{u, 0} Λ jg.immersion).map
        ((etaleModuleDerivedDirectImageComp.{u, 0} Λ
            ((CompactificationOf.restrictBase jg jX).immersion ≫
            (CompactificationOf.restrictBaseι jg jX)) jX.toBase (f ≫ jg.immersion)
          hab).inv.app
            K.obj) ≫ (etaleModuleDerivedBaseChange.{u, 0} Λ (f ≫ jg.immersion) f jg.immersion
                (𝟙 (Over.mk f).left) (Category.id_comp _).symm).app K.obj =
        (etaleModuleDerivedBaseChange.{u, 0} Λ jX.toBase
            (CompactificationOf.restrictBase jg jX).toBase jg.immersion
            (CompactificationOf.restrictBaseι jg jX) hw).app
            ((etaleModuleDerivedDirectImage.{u, 0} Λ
            ((CompactificationOf.restrictBase jg jX).immersion ≫
            (CompactificationOf.restrictBaseι jg jX))).obj K.obj) ≫
          (etaleModuleDerivedDirectImage.{u, 0} Λ
              (CompactificationOf.restrictBase jg jX).toBase).map
            ((etaleModuleDerivedBaseChange.{u, 0} Λ
                ((CompactificationOf.restrictBase jg jX).immersion ≫
                (CompactificationOf.restrictBaseι jg jX))
                (CompactificationOf.restrictBase jg jX).immersion
                (CompactificationOf.restrictBaseι jg jX) (𝟙 (Over.mk f).left) hc.w.symm).app
                K.obj) ≫
          (etaleModuleDerivedDirectImageComp.{u, 0} Λ
              (CompactificationOf.restrictBase jg jX).immersion
              (CompactificationOf.restrictBase jg jX).toBase f haf).inv.app
              ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ (𝟙 (Over.mk f).left)).obj K.obj) := by
      rw [← cancel_mono ((etaleModuleDerivedDirectImageComp.{u, 0} Λ
          (CompactificationOf.restrictBase jg jX).immersion
          (CompactificationOf.restrictBase jg jX).toBase f haf).hom.app _)]
      refine (Category.assoc _ _ _).trans ((whisker_eq _ hP).trans ?_)
      simp only [Over.mk_left, CompactificationOf.baseChange_space,
        CompactificationOf.baseChange_immersion, Functor.comp_obj,
        CompactificationOf.baseChange_toBase, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
        CategoryTheory.Functor.map_id, Category.id_comp, Category.assoc]
      exact (whisker_eq _ (Category.comp_id _)).symm
    have nB := (etaleModuleDerivedBaseChange.{u, 0} Λ jX.toBase
        (CompactificationOf.restrictBase jg jX).toBase jg.immersion
        (CompactificationOf.restrictBaseι jg jX) hw).naturality
      ((etaleModuleDerivedExtensionByZeroToDirectImagePlus.{u, 0} Λ
          ((CompactificationOf.restrictBase jg jX).immersion ≫
          (CompactificationOf.restrictBaseι jg jX))).app K.obj)
    have nE := (etaleModuleDerivedExtensionByZeroToDirectImagePlus.{u, 0} Λ
        (CompactificationOf.restrictBase jg jX).immersion).naturality
      ((etaleModuleDerivedInverseImagePlusIdIso Λ (Over.mk f).left).inv.app K.obj)
    have nC := (etaleModuleDerivedDirectImageComp.{u, 0} Λ
        (CompactificationOf.restrictBase jg jX).immersion
        (CompactificationOf.restrictBase jg jX).toBase f haf).inv.naturality
        ((etaleModuleDerivedInverseImagePlusIdIso Λ (Over.mk f).left).inv.app K.obj)
    simp only [Functor.comp_map] at nB nC
    rw [Functor.map_comp, Category.assoc, hP']
    refine ((Category.assoc _ _ _).symm.trans
        ((eq_whisker nB _).trans (Category.assoc _ _ _))).trans ?_
    rw [← Functor.map_comp_assoc, hε, ← hρ]
    simp only [Functor.map_comp, Category.assoc]
    refine whisker_eq _ (whisker_eq _ ?_)
    rw [← Functor.map_comp_assoc, nE, Functor.map_comp_assoc, nC]
    rfl
  have hT : (etaleModuleDerivedInverseImagePlus.{u, 0} Λ jg.immersion).map
      ((derivedLowerShriekToDirectImage.{u, 0} Λ (f ≫ jg.immersion)
        (CompactificationOf.overBar jg jX)).app K.obj) ≫
      (etaleModuleDerivedBaseChange.{u, 0} Λ (f ≫ jg.immersion) f jg.immersion (𝟙 (Over.mk f).left)
          (Category.id_comp _).symm).app K.obj =
      (etaleModuleDerivedBaseChange.{u, 0} Λ jX.toBase
          (CompactificationOf.restrictBase jg jX).toBase jg.immersion
          (CompactificationOf.restrictBaseι jg jX) hw).app
          ((etaleModuleDerivedExtensionByZero.{u, 0} Λ
          ((CompactificationOf.restrictBase jg jX).immersion ≫
          (CompactificationOf.restrictBaseι jg jX))).obj K.obj) ≫
        (etaleModuleDerivedDirectImage.{u, 0} Λ (CompactificationOf.restrictBase jg jX).toBase).map
          ((etaleModuleDerivedExtensionByZeroRestrictIso Λ
              (CompactificationOf.restrictBase jg jX).immersion
              (CompactificationOf.restrictBaseι jg jX)).hom.app K.obj) ≫
        (derivedLowerShriekToDirectImage.{u, 0} Λ f
          (CompactificationOf.restrictBase jg jX)).app K.obj ≫
        (etaleModuleDerivedDirectImage.{u, 0} Λ f).map
          ((etaleModuleDerivedInverseImagePlusIdIso Λ (Over.mk f).left).inv.app K.obj) :=
    hT'.trans (whisker_eq _ (whisker_eq _ (Category.assoc _ _ _).symm))
  -- transport to the source `Ri_! Rf_! K`, where maps are determined over the open `Y`
  rw [← Iso.app_hom, ← Iso.eq_inv_comp, Iso.app_inv]
  refine eq_of_etaleModuleDerivedInverseImagePlus_map_eq_of_source Λ jg.immersion _ _ ?_
  rw [← cancel_mono ((etaleModuleDerivedBaseChange.{u, 0} Λ (f ≫ jg.immersion) f jg.immersion
      (𝟙 (Over.mk f).left) (Category.id_comp _).symm).app K.obj)]
  have hRinv : (etaleModuleDerivedInverseImagePlus.{u, 0} Λ jg.immersion).map
      ((derivedLowerShriekRestrictBaseIso Λ jg jX).inv.app K) ≫
      (etaleModuleDerivedBaseChange.{u, 0} Λ jX.toBase
          (CompactificationOf.restrictBase jg jX).toBase jg.immersion
          (CompactificationOf.restrictBaseι jg jX) hw).app
          ((etaleModuleDerivedExtensionByZero.{u, 0} Λ
          ((CompactificationOf.restrictBase jg jX).immersion ≫
          (CompactificationOf.restrictBaseι jg jX))).obj K.obj) ≫
        (etaleModuleDerivedDirectImage.{u, 0} Λ (CompactificationOf.restrictBase jg jX).toBase).map
          ((etaleModuleDerivedExtensionByZeroRestrictIso Λ
              (CompactificationOf.restrictBase jg jX).immersion
              (CompactificationOf.restrictBaseι jg jX)).hom.app K.obj) =
      (etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ jg.immersion).hom.app
          ((derivedLowerShriek.{u, 0} f (CompactificationOf.restrictBase jg jX) Λ).obj
        K.obj) := by
    have key : (etaleModuleDerivedBaseChange.{u, 0} Λ jX.toBase
        (CompactificationOf.restrictBase jg jX).toBase jg.immersion
        (CompactificationOf.restrictBaseι jg jX) hw).app
          ((etaleModuleDerivedExtensionByZero.{u, 0} Λ
              ((CompactificationOf.restrictBase jg jX).immersion ≫
              (CompactificationOf.restrictBaseι jg jX))).obj K.obj) ≫
        (etaleModuleDerivedDirectImage.{u, 0} Λ (CompactificationOf.restrictBase jg jX).toBase).map
          ((etaleModuleDerivedExtensionByZeroRestrictIso Λ
              (CompactificationOf.restrictBase jg jX).immersion
              (CompactificationOf.restrictBaseι jg jX)).hom.app K.obj) =
        (etaleModuleDerivedInverseImagePlus.{u, 0} Λ jg.immersion).map
          ((derivedLowerShriekRestrictBaseIso Λ jg jX).hom.app K) ≫
        (etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ jg.immersion).hom.app _ :=
      hR.symm
    refine (whisker_eq _ key).trans ?_
    exact (Category.assoc _ _ _).symm.trans ((eq_whisker ((Functor.map_comp _ _ _).symm.trans
      ((congrArg _ (Iso.inv_hom_id_app _ _)).trans (CategoryTheory.Functor.map_id _ _))) _).trans
        (Category.id_comp _))
  have e1 : (etaleModuleDerivedInverseImagePlus.{u, 0} Λ jg.immersion).map
      ((etaleModuleDerivedExtensionByZero.{u, 0} Λ jg.immersion).map
        ((derivedLowerShriekToDirectImage.{u, 0} Λ f
          (CompactificationOf.restrictBase jg jX)).app K.obj)) =
      (etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ jg.immersion).hom.app _ ≫
          (derivedLowerShriekToDirectImage.{u, 0} Λ f
          (CompactificationOf.restrictBase jg jX)).app K.obj ≫
              (etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ jg.immersion).inv.app _ :=
    ((whisker_eq _
      ((etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ jg.immersion).inv.naturality
      ((derivedLowerShriekToDirectImage.{u, 0} Λ f
          (CompactificationOf.restrictBase jg jX)).app K.obj))).trans
      (Iso.hom_inv_id_app_assoc _ _ _)).symm
  refine Eq.trans
      (b := (etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ jg.immersion).hom.app
      ((derivedLowerShriek.{u, 0} f (CompactificationOf.restrictBase jg jX) Λ).obj K.obj) ≫
    (derivedLowerShriekToDirectImage.{u, 0} Λ f (CompactificationOf.restrictBase jg jX)).app K.obj ≫
    (etaleModuleDerivedDirectImage.{u, 0} Λ f).map
      ((etaleModuleDerivedInverseImagePlusIdIso Λ (Over.mk f).left).inv.app K.obj)) ?_ ?_
  · rw [Functor.map_comp, Functor.map_comp, e1]
    simp only [Category.assoc]
    exact whisker_eq _ (whisker_eq _ hO)
  · refine Eq.symm ?_
    rw [Functor.map_comp, Category.assoc]
    refine (whisker_eq _ hT).trans ?_
    refine (((Category.assoc _ _ _).trans (whisker_eq _ (Category.assoc _ _ _))).symm).trans ?_
    exact eq_whisker hRinv _

end Composition

/-! ### Independence of the compactification, for the coefficients of Tag 0F7J -/

section IndependenceType

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- **The map `Rf_! ⟶ Rf_*` does not depend on the compactification** on
`D⁺_tors(X_étale, Λ)`, for the canonical isomorphism
`Stacks.EtaleCohomology.derivedLowerShriekCompactificationIso` of [Stacks, Tag 0F7I]. -/
theorem derivedLowerShriekCompactificationIso_hom_comp_toDirectImage [CompactSpace Y]
    [QuasiSeparatedSpace Y] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (j₁ j₂ : CompactificationOf (Over.mk f)) :
    (derivedLowerShriekCompactificationIso f j₁ j₂ Λ).hom ≫
        Functor.whiskerLeft (isTorsionPlus.{u, 0} Λ X).ι
          (derivedLowerShriekToDirectImage.{u, 0} Λ f j₂) =
      Functor.whiskerLeft (isTorsionPlus.{u, 0} Λ X).ι
        (derivedLowerShriekToDirectImage.{u, 0} Λ f j₁) :=
  IsCofiltered.isoSystemComparison_hom_comp _
    (fun j => Functor.whiskerLeft (isTorsionPlus.{u, 0} Λ X).ι
      (derivedLowerShriekToDirectImage.{u, 0} Λ f j))
    (fun g => NatTrans.ext (funext fun K =>
      NatTrans.congr_app (derivedLowerShriekHomUniv_comp_toDirectImage Λ g) K.obj)) j₁ j₂

end IndependenceType

/-! ### [Stacks, Tag 0H6X], compatibility (1), on `D⁺_tors` -/

section CompatibilityOne

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [CompactSpace X] [QuasiSeparatedSpace X]
  [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace Z] [QuasiSeparatedSpace Z]
  [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g]

attribute [local instance high] CompactificationOf.etale_restrictBaseι
  CompactificationOf.etale_overBar_immersion

/-- **[Stacks, Tag 0H6X], compatibility (1), on `D⁺_tors(X_étale, Λ)`**: the map `Rf_! ⟶ Rf_*`
is compatible with the isomorphism `R(g ∘ f)_! ≅ Rg_! ∘ Rf_!` of [Stacks, Tag 0F7J]
(`Stacks.EtaleCohomology.derivedLowerShriekCompIso`) and the composition isomorphism
`R(g ∘ f)_* ≅ Rg_* ∘ Rf_*` of Cohomology on Sites, Tag 0D6E, for arbitrary compactifications
`jf`, `jg`, `j` of `f`, `g` and `g ∘ f`: for `K` in `D⁺_tors(X_étale, Λ)`,
`R(g ∘ f)_! K ≅ Rg_! Rf_! K ⟶ Rg_! Rf_* K ⟶ Rg_* Rf_* K ≅ R(g ∘ f)_* K` is the map
`R(g ∘ f)_! K ⟶ R(g ∘ f)_* K`. -/
@[stacks 0H6X "(1), on D⁺_tors"]
theorem derivedLowerShriekCompIso_hom_comp_toDirectImage (jf : CompactificationOf (Over.mk f))
    (jg : CompactificationOf (Over.mk g)) (j : CompactificationOf (Over.mk (f ≫ g)))
    (K : (isTorsionPlus.{u, 0} Λ X).FullSubcategory) :
    (derivedLowerShriekCompIso Λ f g jf jg j).hom.app K ≫
        (derivedLowerShriek.{u, 0} g jg Λ).map
          ((derivedLowerShriekToDirectImage.{u, 0} Λ f jf).app K.obj) ≫
        (derivedLowerShriekToDirectImage.{u, 0} Λ g jg).app
          ((etaleModuleDerivedDirectImage.{u, 0} Λ f).obj K.obj) ≫
        (etaleModuleDerivedDirectImageComp.{u, 0} Λ f g (f ≫ g) rfl).inv.app K.obj =
      (derivedLowerShriekToDirectImage.{u, 0} Λ (f ≫ g) j).app K.obj := by
  have : QuasiCompact f := quasiCompact_of_compactSpace f
  have : QuasiCompact (f ≫ g) := quasiCompact_of_compactSpace _
  let jX := (nonempty_compactificationOf_comp_immersion f g jg).some
  have hiso : (derivedLowerShriekCompIso Λ f g jf jg j).hom.app K =
      (derivedLowerShriekCompactificationIso (f ≫ g) j (CompactificationOf.compOver jg jX)
          Λ).hom.app K ≫
        (derivedLowerShriekCompOverIso Λ f g jg jX).hom.app K ≫
        (derivedLowerShriek.{u, 0} g jg Λ).map
          ((derivedLowerShriekCompactificationIso f (CompactificationOf.restrictBase jg jX) jf
            Λ).hom.app K) := rfl
  have i₁ := NatTrans.congr_app (derivedLowerShriekCompactificationIso_hom_comp_toDirectImage Λ j
    (CompactificationOf.compOver jg jX)) K
  have i₂ := NatTrans.congr_app (derivedLowerShriekCompactificationIso_hom_comp_toDirectImage Λ
    (CompactificationOf.restrictBase jg jX) jf) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at i₁ i₂
  have hco_app_eq := derivedLowerShriekCompOverIso_hom_app Λ jg jX K
  have core := derivedLowerShriekRestrictBaseIso_hom_comp_toDirectImage Λ jg jX K
  have core' : (derivedLowerShriekRestrictBaseIso Λ jg jX).hom.app K ≫
      (etaleModuleDerivedExtensionByZero.{u, 0} Λ jg.immersion).map
        ((derivedLowerShriekToDirectImage.{u, 0} Λ f
          (CompactificationOf.restrictBase jg jX)).app K.obj) ≫
      (etaleModuleDerivedExtensionByZeroToDirectImagePlus.{u, 0} Λ jg.immersion).app
        ((etaleModuleDerivedDirectImage.{u, 0} Λ f).obj K.obj) =
      (derivedLowerShriekToDirectImage.{u, 0} Λ (f ≫ jg.immersion)
          (CompactificationOf.overBar jg jX)).app K.obj ≫
        (etaleModuleDerivedDirectImageComp.{u, 0} Λ f jg.immersion (f ≫ jg.immersion) rfl).hom.app
          K.obj := by
    rw [← core]
    simp only [Category.assoc]
    exact whisker_eq _ (whisker_eq _ ((Category.comp_id _).symm.trans
      (whisker_eq _ (Iso.inv_hom_id_app (etaleModuleDerivedDirectImageComp.{u, 0} Λ f jg.immersion
        (f ≫ jg.immersion) rfl) K.obj).symm)))
  have A1 := etaleModuleDerivedDirectImageComp_assoc_univ_app Λ f jg.immersion jg.toBase
    (f ≫ jg.immersion) rfl g (CompactificationOf.immersion_toBase jg).symm (f ≫ g)
    (by simp) rfl K.obj
  have A1' : (etaleModuleDerivedDirectImage.{u, 0} Λ jg.toBase).map
        ((etaleModuleDerivedDirectImageComp.{u, 0} Λ f jg.immersion (f ≫ jg.immersion)
          rfl).hom.app K.obj) ≫
      (etaleModuleDerivedDirectImageComp.{u, 0} Λ jg.immersion jg.toBase g
          (CompactificationOf.immersion_toBase jg).symm).inv.app
        ((etaleModuleDerivedDirectImage.{u, 0} Λ f).obj K.obj) ≫
      (etaleModuleDerivedDirectImageComp.{u, 0} Λ f g (f ≫ g) rfl).inv.app K.obj =
      (etaleModuleDerivedDirectImageComp.{u, 0} Λ (f ≫ jg.immersion) jg.toBase (f ≫ g)
        (by simp)).inv.app K.obj := by
    rw [← cancel_epi ((etaleModuleDerivedDirectImageComp.{u, 0} Λ (f ≫ jg.immersion) jg.toBase
      (f ≫ g) (by simp)).hom.app K.obj), reassoc_of% A1]
    simp
  -- the part over `Ȳ` before `Rḡ_*`
  have T1 : (etaleModuleDerivedDirectImage.{u, 0} Λ jg.toBase).map
        ((derivedLowerShriekRestrictBaseIso Λ jg jX).hom.app K) ≫
      (derivedLowerShriek.{u, 0} g jg Λ).map
        ((derivedLowerShriekToDirectImage.{u, 0} Λ f
          (CompactificationOf.restrictBase jg jX)).app K.obj) ≫
      (derivedLowerShriekToDirectImage.{u, 0} Λ g jg).app
        ((etaleModuleDerivedDirectImage.{u, 0} Λ f).obj K.obj) ≫
      (etaleModuleDerivedDirectImageComp.{u, 0} Λ f g (f ≫ g) rfl).inv.app K.obj =
      (etaleModuleDerivedDirectImage.{u, 0} Λ jg.toBase).map
        ((derivedLowerShriekToDirectImage.{u, 0} Λ (f ≫ jg.immersion)
          (CompactificationOf.overBar jg jX)).app K.obj) ≫
      (etaleModuleDerivedDirectImageComp.{u, 0} Λ (f ≫ jg.immersion) jg.toBase (f ≫ g)
        (by simp)).inv.app K.obj := by
    have e : (derivedLowerShriekToDirectImage.{u, 0} Λ g jg).app
        ((etaleModuleDerivedDirectImage.{u, 0} Λ f).obj K.obj) =
        (etaleModuleDerivedDirectImage.{u, 0} Λ jg.toBase).map
          ((etaleModuleDerivedExtensionByZeroToDirectImagePlus.{u, 0} Λ jg.immersion).app
            ((etaleModuleDerivedDirectImage.{u, 0} Λ f).obj K.obj)) ≫
        (etaleModuleDerivedDirectImageComp.{u, 0} Λ jg.immersion jg.toBase g
          (CompactificationOf.immersion_toBase jg).symm).inv.app
            ((etaleModuleDerivedDirectImage.{u, 0} Λ f).obj K.obj) := rfl
    rw [e, Category.assoc, ← A1']
    have e2 : (derivedLowerShriek.{u, 0} g jg Λ).map
        ((derivedLowerShriekToDirectImage.{u, 0} Λ f
          (CompactificationOf.restrictBase jg jX)).app K.obj) =
        (etaleModuleDerivedDirectImage.{u, 0} Λ jg.toBase).map
          ((etaleModuleDerivedExtensionByZero.{u, 0} Λ jg.immersion).map
            ((derivedLowerShriekToDirectImage.{u, 0} Λ f
              (CompactificationOf.restrictBase jg jX)).app K.obj)) := rfl
    rw [e2]
    simp only [← Functor.map_comp_assoc]
    rw [core']
  -- the part over `Z`, in the vocabulary of `X̄`
  have hab : f ≫ jg.immersion = ((CompactificationOf.restrictBase jg jX).immersion ≫
      CompactificationOf.restrictBaseι jg jX) ≫ jX.toBase :=
    (CompactificationOf.immersion_toBase (CompactificationOf.overBar jg jX)).symm
  have hco : f ≫ g = ((CompactificationOf.restrictBase jg jX).immersion ≫
      CompactificationOf.restrictBaseι jg jX) ≫ (jX.toBase ≫ jg.toBase) :=
    (CompactificationOf.immersion_toBase (CompactificationOf.compOver jg jX)).symm
  have A2 := etaleModuleDerivedDirectImageComp_assoc_univ_app Λ
    ((CompactificationOf.restrictBase jg jX).immersion ≫ CompactificationOf.restrictBaseι jg jX)
    jX.toBase jg.toBase (f ≫ jg.immersion) hab (jX.toBase ≫ jg.toBase) rfl (f ≫ g) (by simp)
    hco K.obj
  have n₂ := (etaleModuleDerivedDirectImageComp.{u, 0} Λ jX.toBase jg.toBase
    (jX.toBase ≫ jg.toBase) rfl).hom.naturality
      ((etaleModuleDerivedExtensionByZeroToDirectImagePlus.{u, 0} Λ
        ((CompactificationOf.restrictBase jg jX).immersion ≫
          CompactificationOf.restrictBaseι jg jX)).app K.obj)
  simp only [Functor.comp_map] at n₂
  have T2 : (etaleModuleDerivedDirectImageComp.{u, 0} Λ jX.toBase jg.toBase
        (jX.toBase ≫ jg.toBase) rfl).hom.app
        ((etaleModuleDerivedExtensionByZero.{u, 0} Λ
            ((CompactificationOf.restrictBase jg jX).immersion ≫
          CompactificationOf.restrictBaseι jg jX)).obj K.obj) ≫
      (etaleModuleDerivedDirectImage.{u, 0} Λ jg.toBase).map
        ((etaleModuleDerivedDirectImage.{u, 0} Λ jX.toBase).map
          ((etaleModuleDerivedExtensionByZeroToDirectImagePlus.{u, 0} Λ
            ((CompactificationOf.restrictBase jg jX).immersion ≫
              CompactificationOf.restrictBaseι jg jX)).app K.obj) ≫
          (etaleModuleDerivedDirectImageComp.{u, 0} Λ
              ((CompactificationOf.restrictBase jg jX).immersion ≫
            CompactificationOf.restrictBaseι jg jX) jX.toBase (f ≫ jg.immersion) hab).inv.app
                K.obj) ≫
      (etaleModuleDerivedDirectImageComp.{u, 0} Λ (f ≫ jg.immersion) jg.toBase (f ≫ g)
        (by simp)).inv.app K.obj =
      (etaleModuleDerivedDirectImage.{u, 0} Λ (jX.toBase ≫ jg.toBase)).map
          ((etaleModuleDerivedExtensionByZeroToDirectImagePlus.{u, 0} Λ
            ((CompactificationOf.restrictBase jg jX).immersion ≫
              CompactificationOf.restrictBaseι jg jX)).app K.obj) ≫
        (etaleModuleDerivedDirectImageComp.{u, 0} Λ
            ((CompactificationOf.restrictBase jg jX).immersion ≫
          CompactificationOf.restrictBaseι jg jX) (jX.toBase ≫ jg.toBase) (f ≫ g) hco).inv.app
            K.obj := by
    rw [Functor.map_comp, Category.assoc, ← reassoc_of% n₂]
    refine whisker_eq _ ?_
    rw [← cancel_epi ((etaleModuleDerivedDirectImageComp.{u, 0} Λ
      ((CompactificationOf.restrictBase jg jX).immersion ≫ CompactificationOf.restrictBaseι jg jX)
      (jX.toBase ≫ jg.toBase) (f ≫ g) hco).hom.app K.obj)]
    refine (Category.assoc _ _ _).symm.trans ((eq_whisker A2.symm _).trans ?_)
    simp [← Functor.map_comp_assoc]
  rw [hiso]
  refine Eq.trans ?_ i₁
  simp only [Category.assoc]
  refine whisker_eq _ ?_
  rw [← Functor.map_comp_assoc]
  refine (whisker_eq _ (eq_whisker (congrArg _ i₂) _)).trans ?_
  rw [hco_app_eq]
  refine ((Category.assoc _ _ _).trans (whisker_eq _ T1)).trans ?_
  exact T2

end CompatibilityOne

end Stacks.EtaleCohomology

end
