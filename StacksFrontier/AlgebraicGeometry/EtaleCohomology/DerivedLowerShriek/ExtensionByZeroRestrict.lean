module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ExtensionByZeroValues
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.BaseChangeCube
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.UnderivedExtensionByZeroPasting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.CompositionBaseChange

/-!
# Restricting an extension by zero to an intermediate open

For open immersions `a : X ⟶ U` and `b : U ⟶ X̄`, the isomorphism
`b^{-1} (b ∘ a)_! ≅ b^{-1} b_! a_! ≅ a_!` on `D⁺` is the isomorphism of [Stacks, Tag 03S6] for the
cartesian square `X = X ×_{X̄} U` followed by `(𝟙_X)^{-1} ≅ 𝟭`.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleDerivedExtensionByZeroRestrictIso`.

## Main results

* `Stacks.EtaleCohomology.etaleModuleExtensionByZeroRestrictIso_hom`: the statement on sheaves.
* `Stacks.EtaleCohomology.etaleModuleDerivedExtensionByZeroRestrictIso_hom`: the statement on
  `D⁺`.
* `Stacks.EtaleCohomology.restrictBaseExtensionByZeroIso_eq`:
  `Stacks.EtaleCohomology.restrictBaseExtensionByZeroIso` is an instance of
  `Stacks.EtaleCohomology.etaleModuleDerivedExtensionByZeroRestrictIso`.

## Implementation notes

The statement on sheaves is proved by passing to conjugates, where it becomes an identity of
restrictions of sections; the statement on `D⁺` is reduced to it at the image of a complex.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Cohomology.DerivedBaseChangePlus

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type) [Ring Λ] {X U Xb : Scheme.{u}} (a : X ⟶ U) (b : U ⟶ Xb)
  [IsOpenImmersion a] [IsOpenImmersion b]

/-- The underived isomorphism `b^{-1} (b ∘ a)_! ≅ a_!`. -/
def etaleModuleExtensionByZeroRestrictIso :
    etaleModuleExtensionByZero.{u, 0} Λ (a ≫ b) ⋙ etaleModuleInverseImage.{u, 0} Λ b ≅
      etaleModuleExtensionByZero.{u, 0} Λ a :=
  Functor.isoWhiskerRight (etaleModuleExtensionByZeroCompIso.{u, 0} Λ a b) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (etaleModuleExtensionByZeroInverseImageIso Λ b) ≪≫
    Functor.rightUnitor _

/-- **`b^{-1} (b ∘ a)_! ≅ a_!` on `D⁺`**: the composition of derived extensions by zero followed
by `b^{-1} Rb_! ≅ 𝟭`. -/
def etaleModuleDerivedExtensionByZeroRestrictIso :
    etaleModuleDerivedExtensionByZero.{u, 0} Λ (a ≫ b) ⋙
        etaleModuleDerivedInverseImagePlus.{u, 0} Λ b ≅
      etaleModuleDerivedExtensionByZero.{u, 0} Λ a :=
  Functor.isoWhiskerRight (Functor.rightDerivedFunctorPlusCompIsoOfExact
    (etaleModuleExtensionByZero.{u, 0} Λ a) (etaleModuleExtensionByZero.{u, 0} Λ b)
    (etaleModuleExtensionByZero.{u, 0} Λ (a ≫ b))
    (etaleModuleExtensionByZeroCompIso.{u, 0} Λ a b).symm).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ b) ≪≫
    Functor.rightUnitor _

omit [IsOpenImmersion a] [IsOpenImmersion b] in
/-- The four-fold composite `A ≫ B ≫ c ≫ d` equals `fh ≫ x ≫ y ≫ u`, pasting three commuting
squares. -/
lemma restrict_chain_left {C : Type*} [Category* C] {X₀ X₁ X₂ X₃ X₄ Y₁ Y₂ Y₃ : C}
    (A : X₀ ⟶ X₁) (B : X₁ ⟶ X₂) (c : X₂ ⟶ X₃) (d : X₃ ⟶ X₄) (d' : X₂ ⟶ Y₃) (u : Y₃ ⟶ X₄)
    (fh' : X₁ ⟶ Y₂) (y : Y₂ ⟶ Y₃) (fh : X₀ ⟶ Y₁) (x : Y₁ ⟶ Y₂)
    (h1 : c ≫ d = d' ≫ u) (h2 : B ≫ d' = fh' ≫ y) (h3 : A ≫ fh' = fh ≫ x) :
    A ≫ B ≫ c ≫ d = fh ≫ x ≫ y ≫ u := by
  rw [h1, reassoc_of% h2, reassoc_of% h3]

omit [IsOpenImmersion a] [IsOpenImmersion b] in
/-- Rewriting the last two factors of `fh ≫ x ≫ u' ≫ r` along the commuting square
`u' ≫ r = y ≫ u`. -/
lemma restrict_chain_right {C : Type*} [Category* C] {X₀ X₁ X₂ X₃ X₄ Y₃ : C}
    (fh : X₀ ⟶ X₁) (x : X₁ ⟶ X₂) (u' : X₂ ⟶ X₃) (r : X₃ ⟶ X₄) (y : X₂ ⟶ Y₃) (u : Y₃ ⟶ X₄)
    (h : u' ≫ r = y ≫ u) : fh ≫ x ≫ u' ≫ r = fh ≫ x ≫ y ≫ u := by
  rw [h]

section Conjugate

open Stacks.CategoryTheory.LeftAdjointUniqPasting

variable {C D : Type*} [Category* C] [Category* D]

omit [IsOpenImmersion a] [IsOpenImmersion b] in
/-- The conjugate of a comparison of left adjoints obtained by uniqueness is the identity. -/
lemma conjugateEquiv_leftAdjointUniq_hom_eq_id {L L' : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (adj' : L' ⊣ R) : conjugateEquiv adj' adj (Adjunction.leftAdjointUniq adj adj').hom = 𝟙 R := by
  simp [Adjunction.leftAdjointUniq]

end Conjugate

/-- The conjugate of `b^{-1} b_! ≅ 𝟭` is a section of the counit of `b^{-1} ⊣ b_*`. -/
lemma conjugateEquiv_etaleModuleExtensionByZeroInverseImageIso_hom_comp_counit :
    conjugateEquiv Adjunction.id ((etaleModuleExtensionByZeroAdj.{u, 0} Λ b).comp
        (etaleModuleInverseImageAdj.{u, 0} Λ b))
      (etaleModuleExtensionByZeroInverseImageIso Λ b).hom ≫
      (etaleModuleRestrictionDirectImageAdj.{u, 0} Λ b).counit = 𝟙 _ := by
  have e2 : (etaleModuleRestrictionDirectImageAdj.{u, 0} Λ b).counit =
      conjugateEquiv ((etaleModuleExtensionByZeroAdj.{u, 0} Λ b).comp
        (etaleModuleRestrictionDirectImageAdj.{u, 0} Λ b)) Adjunction.id
        (etaleModuleExtensionByZeroAdj.{u, 0} Λ b).unit := by
    ext F
    simp
  have e3 := conjugateEquiv_leftAdjointUniq_hom_eq_id (etaleModuleInverseImageAdj.{u, 0} Λ b)
    (etaleModuleRestrictionDirectImageAdj.{u, 0} Λ b)
  rw [e2]
  simp only [etaleModuleExtensionByZeroInverseImageIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom]
  rw [← conjugateEquiv_comp Adjunction.id ((etaleModuleExtensionByZeroAdj.{u, 0} Λ b).comp
      (etaleModuleRestrictionDirectImageAdj.{u, 0} Λ b)),
    conjugateEquiv_whiskerLeft]
  simp only [etaleModuleInverseImageRestrictionIso] at e3 ⊢
  rw [e3, Functor.whiskerRight_id', Category.comp_id, conjugateEquiv_comp]
  simp

variable (hc : IsPullback (𝟙 X) a (a ≫ b) b)

open AlgebraicGeometry.Scheme.Etale in
/-- The identity of morphisms of small étale sites behind
`Stacks.EtaleCohomology.etaleModuleExtensionByZeroRestrictIso_hom`. -/
lemma smallEtale_baseChange_composeCompIso_eq (V : X.Etale) :
    (smallEtaleBaseChange b).map ((smallEtaleComposeCompIso a b).hom.app V) =
      (smallEtaleComposeBaseChangeIsoOfIsPullback hc).hom.app V ≫
        (smallEtaleCompose a).map ((smallEtaleBaseChangeId X).hom.app V) ≫
        (smallEtaleComposeBaseChangeAdj b).unit.app ((smallEtaleCompose a).obj V) := by
  refine MorphismProperty.Over.Hom.ext (pullback.hom_ext ?_ ?_)
  · have h1 := ExtensionByZeroPasting.smallEtaleComposeBaseChangeIsoOfIsPullback_hom_app_left_fst
      hc V
    have h2 := ExtensionByZeroPasting.smallEtaleComposeBaseChangeAdj_unit_app_left_fst b
      ((smallEtaleCompose a).obj V)
    refine (smallEtaleBaseChange_map_left_fst b _).trans ?_
    refine (Category.comp_id _).trans ?_
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    refine Eq.trans ?_ (congrArg (fun z => _ ≫ z) (Category.assoc _ _ _)).symm
    refine Eq.trans ?_ (congrArg (fun z => _ ≫ _ ≫ z) h2).symm
    refine Eq.trans ?_ (congrArg (fun z => _ ≫ z) (Category.comp_id _)).symm
    exact h1.symm
  · exact (MorphismProperty.Over.w _).trans (MorphismProperty.Over.w _).symm

/-- **`b^{-1} (b ∘ a)_! ≅ a_!` is the isomorphism of [Stacks, Tag 03S6]**, read through
`(𝟙_X)^{-1} ≅ 𝟭`, on sheaves. -/
theorem etaleModuleExtensionByZeroRestrictIso_hom :
    (etaleModuleExtensionByZeroRestrictIso Λ a b).hom =
      (etaleModuleInverseImageExtensionByZeroIso.{u, 0} Λ hc).inv ≫
        Functor.whiskerRight (etaleModuleInverseImageIdIso.{u, 0} Λ X).hom _ ≫
        (Functor.leftUnitor _).hom := by
  apply (conjugateEquiv (etaleModuleExtensionByZeroAdj.{u, 0} Λ a)
    ((etaleModuleExtensionByZeroAdj.{u, 0} Λ (a ≫ b)).comp
      (etaleModuleInverseImageAdj.{u, 0} Λ b))).injective
  have cL : conjugateEquiv (etaleModuleExtensionByZeroAdj.{u, 0} Λ a)
      ((etaleModuleExtensionByZeroAdj.{u, 0} Λ (a ≫ b)).comp
        (etaleModuleInverseImageAdj.{u, 0} Λ b)) (etaleModuleExtensionByZeroRestrictIso Λ a b).hom =
      conjugateEquiv (etaleModuleExtensionByZeroAdj.{u, 0} Λ a)
          ((etaleModuleExtensionByZeroAdj.{u, 0} Λ a).comp Adjunction.id)
          (Functor.rightUnitor _).hom ≫
        conjugateEquiv ((etaleModuleExtensionByZeroAdj.{u, 0} Λ a).comp Adjunction.id)
          ((etaleModuleExtensionByZeroAdj.{u, 0} Λ a).comp
            ((etaleModuleExtensionByZeroAdj.{u, 0} Λ b).comp
              (etaleModuleInverseImageAdj.{u, 0} Λ b)))
          (Functor.whiskerLeft _ (etaleModuleExtensionByZeroInverseImageIso Λ b).hom) ≫
        conjugateEquiv ((etaleModuleExtensionByZeroAdj.{u, 0} Λ a).comp
            ((etaleModuleExtensionByZeroAdj.{u, 0} Λ b).comp
              (etaleModuleInverseImageAdj.{u, 0} Λ b)))
          (((etaleModuleExtensionByZeroAdj.{u, 0} Λ a).comp
            (etaleModuleExtensionByZeroAdj.{u, 0} Λ b)).comp
              (etaleModuleInverseImageAdj.{u, 0} Λ b))
          (Functor.associator _ _ _).hom ≫
        conjugateEquiv (((etaleModuleExtensionByZeroAdj.{u, 0} Λ a).comp
            (etaleModuleExtensionByZeroAdj.{u, 0} Λ b)).comp
              (etaleModuleInverseImageAdj.{u, 0} Λ b))
          ((etaleModuleExtensionByZeroAdj.{u, 0} Λ (a ≫ b)).comp
            (etaleModuleInverseImageAdj.{u, 0} Λ b))
          (Functor.whiskerRight (etaleModuleExtensionByZeroCompIso.{u, 0} Λ a b).hom _) := by
    simp only [conjugateEquiv_comp]
    rfl
  have cR : conjugateEquiv (etaleModuleExtensionByZeroAdj.{u, 0} Λ a)
      ((etaleModuleExtensionByZeroAdj.{u, 0} Λ (a ≫ b)).comp
        (etaleModuleInverseImageAdj.{u, 0} Λ b))
      ((etaleModuleInverseImageExtensionByZeroIso.{u, 0} Λ hc).inv ≫
        Functor.whiskerRight (etaleModuleInverseImageIdIso.{u, 0} Λ X).hom _ ≫
        (Functor.leftUnitor _).hom) =
      conjugateEquiv (etaleModuleExtensionByZeroAdj.{u, 0} Λ a)
          (Adjunction.id.comp (etaleModuleExtensionByZeroAdj.{u, 0} Λ a))
          (Functor.leftUnitor _).hom ≫
        conjugateEquiv (Adjunction.id.comp (etaleModuleExtensionByZeroAdj.{u, 0} Λ a))
          ((etaleModuleInverseImageAdj.{u, 0} Λ (𝟙 X)).comp
            (etaleModuleExtensionByZeroAdj.{u, 0} Λ a))
          (Functor.whiskerRight (etaleModuleInverseImageIdIso.{u, 0} Λ X).hom _) ≫
        conjugateEquiv ((etaleModuleInverseImageAdj.{u, 0} Λ (𝟙 X)).comp
            (etaleModuleExtensionByZeroAdj.{u, 0} Λ a))
          ((etaleModuleExtensionByZeroAdj.{u, 0} Λ (a ≫ b)).comp
            (etaleModuleInverseImageAdj.{u, 0} Λ b))
          (etaleModuleInverseImageExtensionByZeroIso.{u, 0} Λ hc).inv := by
    simp only [conjugateEquiv_comp, Category.assoc]
  rw [cL, cR, conjugateEquiv_rightUnitor_hom, conjugateEquiv_whiskerLeft,
    conjugateEquiv_associator_hom, conjugateEquiv_whiskerRight, conjugateEquiv_leftUnitor_hom,
    conjugateEquiv_whiskerRight]
  simp only [etaleModuleExtensionByZeroCompIso, etaleModuleInverseImageIdIso,
    etaleModuleInverseImageExtensionByZeroIso,
    Stacks.CategoryTheory.LeftAdjointUniqPasting.conjugateEquiv_leftAdjointUniq_hom,
    Stacks.CategoryTheory.LeftAdjointUniqPasting.conjugateEquiv_leftAdjointUniq_inv]
  refine NatTrans.ext (funext fun F => ?_)
  have hσ := congrArg (fun t => NatTrans.app t F)
    (conjugateEquiv_etaleModuleExtensionByZeroInverseImageIso_hom_comp_counit Λ b)
  simp only [NatTrans.comp_app, NatTrans.id_app] at hσ
  replace hσ := IsIso.eq_inv_of_inv_hom_id hσ
  simp only [NatTrans.comp_app, Functor.leftUnitor_inv_app, Functor.rightUnitor_inv_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Category.id_comp, hσ, Functor.map_inv, IsIso.inv_comp_eq]
  refine Sheaf.hom_ext (NatTrans.ext (funext fun V => ?_))
  simp only [NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom]
  simp only [Iso.symm_hom, Iso.symm_inv, etaleModuleRestrictionCompIso,
    Functor.sheafPushforwardContinuousComp'_hom_app_hom_app,
    Functor.sheafPushforwardContinuousId'_inv_app_hom_app,
    ExtensionByZeroPasting.etaleRestrictionPushforwardIsoOfIsPullback_hom_app_hom_app]
  have key := congrArg (fun z => F.obj.map (Quiver.Hom.op z))
    (smallEtale_baseChange_composeCompIso_eq a b hc V.unop)
  simp only [op_comp, Functor.map_comp] at key
  exact key


/-- **`b^{-1} (b ∘ a)_! ≅ a_!` is the isomorphism of [Stacks, Tag 03S6]**, read through
`(𝟙_X)^{-1} ≅ 𝟭`, given the underived statement. -/
theorem etaleModuleDerivedExtensionByZeroRestrictIso_hom_of
    (hU : (etaleModuleExtensionByZeroRestrictIso Λ a b).hom =
      (etaleModuleInverseImageExtensionByZeroIso.{u, 0} Λ hc).inv ≫
        Functor.whiskerRight (etaleModuleInverseImageIdIso.{u, 0} Λ X).hom _ ≫
        (Functor.leftUnitor _).hom) :
    (etaleModuleDerivedExtensionByZeroRestrictIso Λ a b).hom =
      (etaleModuleDerivedExtensionByZeroCubeIso Λ hc).inv ≫
        Functor.whiskerRight (etaleModuleDerivedInverseImagePlusIdIso Λ X).hom _ ≫
        (Functor.leftUnitor _).hom := by
  refine ((etaleModuleExtensionByZero.{u, 0} Λ (a ≫ b)).rightDerivedFunctorPlus ⋙
    (etaleModuleInverseImage.{u, 0} Λ b).mapDerivedCategoryPlus).rightDerived_ext
    (derivedBaseChangePlusUnit _ _) (HomotopyCategory.Plus.quasiIso _) _ _ _
    (NatTrans.ext (funext fun K => ?_))
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.leftUnitor_hom_app]
  let N := (etaleModuleExtensionByZero.{u, 0} Λ a).mapHomotopyCategoryPlus.obj K
  let RCO := Functor.rightDerivedFunctorPlusCompIsoOfExact
    (etaleModuleExtensionByZero.{u, 0} Λ a) (etaleModuleExtensionByZero.{u, 0} Λ b)
    (etaleModuleExtensionByZero.{u, 0} Λ (a ≫ b))
    (etaleModuleExtensionByZeroCompIso.{u, 0} Λ a b).symm
  have hdef : (etaleModuleDerivedExtensionByZeroRestrictIso Λ a b).hom.app
      (DerivedCategory.Plus.Qh.obj K) =
      (etaleModuleDerivedInverseImagePlus.{u, 0} Λ b).map
          (RCO.inv.app (DerivedCategory.Plus.Qh.obj K)) ≫
        (etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ b).hom.app
          ((etaleModuleDerivedExtensionByZero.{u, 0} Λ a).obj (DerivedCategory.Plus.Qh.obj K)) := by
    simp [etaleModuleDerivedExtensionByZeroRestrictIso, RCO]
  have f1 := Functor.rightDerivedFunctorPlusCompIsoOfExact_fac
    (etaleModuleExtensionByZero.{u, 0} Λ a) (etaleModuleExtensionByZero.{u, 0} Λ b)
    (etaleModuleExtensionByZero.{u, 0} Λ (a ≫ b))
    (etaleModuleExtensionByZeroCompIso.{u, 0} Λ a b).symm K
  have f1' : (etaleModuleExtensionByZero.{u, 0} Λ (a ≫ b)).rightDerivedFunctorPlusUnith.app K ≫
      RCO.inv.app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusCompIso
          (etaleModuleExtensionByZeroCompIso.{u, 0} Λ a b).symm).inv.app K) ≫
        (etaleModuleExtensionByZero.{u, 0} Λ b).rightDerivedFunctorPlusUnith.app N ≫
        (etaleModuleExtensionByZero.{u, 0} Λ b).rightDerivedFunctorPlus.map
          ((etaleModuleExtensionByZero.{u, 0} Λ a).rightDerivedFunctorPlusUnith.app K) := by
    rw [← cancel_epi (DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusCompIso
          (etaleModuleExtensionByZeroCompIso.{u, 0} Λ a b).symm).hom.app K)),
      ← Category.assoc, ← f1]
    simp [RCO, N]
  have L : (etaleModuleInverseImage.{u, 0} Λ b).mapDerivedCategoryPlus.map
        ((etaleModuleExtensionByZero.{u, 0} Λ (a ≫ b)).rightDerivedFunctorPlusUnith.app K) ≫
      (etaleModuleDerivedExtensionByZeroRestrictIso Λ a b).hom.app (DerivedCategory.Plus.Qh.obj K) =
      (etaleModuleInverseImage.{u, 0} Λ b).mapDerivedCategoryPlusFactorsh.hom.app
          ((etaleModuleExtensionByZero.{u, 0} Λ (a ≫ b)).mapHomotopyCategoryPlus.obj K) ≫
        DerivedCategory.Plus.Qh.map
          ((etaleModuleInverseImage.{u, 0} Λ b).mapHomotopyCategoryPlus.map
          ((Functor.mapHomotopyCategoryPlusCompIso
            (etaleModuleExtensionByZeroCompIso.{u, 0} Λ a b).symm).inv.app K)) ≫
        DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusNatIso
          (etaleModuleExtensionByZeroInverseImageIso Λ b)).hom.app N : _ ⟶ N) ≫
        (etaleModuleExtensionByZero.{u, 0} Λ a).rightDerivedFunctorPlusUnith.app K := by
    rw [hdef, ← Functor.map_comp_assoc, f1', Functor.map_comp_assoc, Functor.map_comp_assoc]
    have n03 := (etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ b).hom.naturality
      ((etaleModuleExtensionByZero.{u, 0} Λ a).rightDerivedFunctorPlusUnith.app K)
    have v03 := etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso_hom_app_Qh Λ b N
    have nfh := (etaleModuleInverseImage.{u, 0} Λ b).mapDerivedCategoryPlusFactorsh.hom.naturality
      ((Functor.mapHomotopyCategoryPlusCompIso
            (etaleModuleExtensionByZeroCompIso.{u, 0} Λ a b).symm).inv.app K)
    simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at n03 nfh
    exact restrict_chain_left _ _ _ _ _ _ _ _ _ _ n03 v03 nfh
  have R : (etaleModuleInverseImage.{u, 0} Λ b).mapDerivedCategoryPlus.map
        ((etaleModuleExtensionByZero.{u, 0} Λ (a ≫ b)).rightDerivedFunctorPlusUnith.app K) ≫
      (etaleModuleDerivedExtensionByZeroCubeIso Λ hc).inv.app (DerivedCategory.Plus.Qh.obj K) ≫
        (etaleModuleDerivedExtensionByZero.{u, 0} Λ a).map
          ((etaleModuleDerivedInverseImagePlusIdIso Λ X).hom.app (DerivedCategory.Plus.Qh.obj K)) =
      (etaleModuleInverseImage.{u, 0} Λ b).mapDerivedCategoryPlusFactorsh.hom.app
          ((etaleModuleExtensionByZero.{u, 0} Λ (a ≫ b)).mapHomotopyCategoryPlus.obj K) ≫
        DerivedCategory.Plus.Qh.map (hmap (etaleModuleInverseImage.{u, 0} Λ b)
          (etaleModuleInverseImage.{u, 0} Λ (𝟙 X))
          (etaleModuleInverseImageExtensionByZeroIso.{u, 0} Λ hc).inv K) ≫
        DerivedCategory.Plus.Qh.map
          ((etaleModuleExtensionByZero.{u, 0} Λ a).mapHomotopyCategoryPlus.map
          ((Functor.mapHomotopyCategoryPlusNatIso
            (etaleModuleInverseImageIdIso.{u, 0} Λ X)).hom.app K : _ ⟶ K)) ≫
        (etaleModuleExtensionByZero.{u, 0} Λ a).rightDerivedFunctorPlusUnith.app K := by
    have dfac := derivedBaseChangePlus_fac (etaleModuleExtensionByZero.{u, 0} Λ (a ≫ b))
      (etaleModuleExtensionByZero.{u, 0} Λ a) (etaleModuleInverseImage.{u, 0} Λ b)
      (etaleModuleInverseImage.{u, 0} Λ (𝟙 X))
      (etaleModuleInverseImageExtensionByZeroIso.{u, 0} Λ hc).inv K
    rw [etaleModuleDerivedExtensionByZeroCubeIso_inv, reassoc_of% dfac,
      derivedBaseChangePlusAux_app']
    simp only [Category.assoc]
    rw [← Functor.map_comp, etaleModuleDerivedInverseImagePlusIdIso_hom_app_Qh]
    have nu := (etaleModuleExtensionByZero.{u, 0} Λ a).rightDerivedFunctorPlusUnith.naturality
      ((Functor.mapHomotopyCategoryPlusNatIso
            (etaleModuleInverseImageIdIso.{u, 0} Λ X)).hom.app K : _ ⟶ K)
    simp only [Functor.comp_map, Functor.comp_obj] at nu
    exact restrict_chain_right _ _ _ _ _ _ nu.symm
  have H : ((etaleModuleInverseImage.{u, 0} Λ b).mapHomotopyCategoryPlus.map
        ((Functor.mapHomotopyCategoryPlusCompIso
          (etaleModuleExtensionByZeroCompIso.{u, 0} Λ a b).symm).inv.app K) ≫
      (Functor.mapHomotopyCategoryPlusNatIso
          (etaleModuleExtensionByZeroInverseImageIso Λ b)).hom.app N :
        (etaleModuleInverseImage.{u, 0} Λ b).mapHomotopyCategoryPlus.obj
          ((etaleModuleExtensionByZero.{u, 0} Λ (a ≫ b)).mapHomotopyCategoryPlus.obj K) ⟶ N) =
      hmap (etaleModuleInverseImage.{u, 0} Λ b) (etaleModuleInverseImage.{u, 0} Λ (𝟙 X))
          (etaleModuleInverseImageExtensionByZeroIso.{u, 0} Λ hc).inv K ≫
        (etaleModuleExtensionByZero.{u, 0} Λ a).mapHomotopyCategoryPlus.map
          ((Functor.mapHomotopyCategoryPlusNatIso
            (etaleModuleInverseImageIdIso.{u, 0} Λ X)).hom.app K : _ ⟶ K) := by
    apply (HomotopyCategory.Plus.ι _).map_injective
    show ((etaleModuleInverseImage.{u, 0} Λ b).mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((Functor.mapHomotopyCategoryCompIso (etaleModuleExtensionByZeroCompIso.{u, 0} Λ a b).symm
          (ComplexShape.up ℤ)).inv.app K.obj) ≫
        (NatTrans.mapHomotopyCategory (etaleModuleExtensionByZeroInverseImageIso Λ b).hom
          (ComplexShape.up ℤ)).app
          (((etaleModuleExtensionByZero.{u, 0} Λ a).mapHomotopyCategory (ComplexShape.up ℤ)).obj
            K.obj) =
      (NatTrans.mapHomotopyCategory (etaleModuleInverseImageExtensionByZeroIso.{u, 0} Λ hc).inv
          (ComplexShape.up ℤ)).app K.obj ≫
        ((etaleModuleExtensionByZero.{u, 0} Λ a).mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomotopyCategory (etaleModuleInverseImageIdIso.{u, 0} Λ X).hom
            (ComplexShape.up ℤ)).app K.obj)
    obtain ⟨K₀⟩ := K.obj
    show (HomotopyCategory.quotient _ _).map
        (((etaleModuleInverseImage.{u, 0} Λ b).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((Functor.mapHomologicalComplexCompIso
            (etaleModuleExtensionByZeroCompIso.{u, 0} Λ a b).symm
            (ComplexShape.up ℤ)).inv.app K₀)) ≫
        (HomotopyCategory.quotient _ _).map
          ((NatTrans.mapHomologicalComplex (etaleModuleExtensionByZeroInverseImageIso Λ b).hom
            (ComplexShape.up ℤ)).app
            (((etaleModuleExtensionByZero.{u, 0} Λ a).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K₀)) =
      (HomotopyCategory.quotient _ _).map
          ((NatTrans.mapHomologicalComplex
            (etaleModuleInverseImageExtensionByZeroIso.{u, 0} Λ hc).inv
            (ComplexShape.up ℤ)).app K₀) ≫
        (HomotopyCategory.quotient _ _).map
          (((etaleModuleExtensionByZero.{u, 0} Λ a).mapHomologicalComplex (ComplexShape.up ℤ)).map
            ((NatTrans.mapHomologicalComplex (etaleModuleInverseImageIdIso.{u, 0} Λ X).hom
              (ComplexShape.up ℤ)).app K₀))
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    ext n
    have hn := congrArg (fun t => NatTrans.app t (K₀.X n)) hU
    simp [etaleModuleExtensionByZeroRestrictIso] at hn
    simp [hn]
  have H' := (DerivedCategory.Plus.Qh.map_comp _ _).symm.trans
    ((congrArg (fun t => DerivedCategory.Plus.Qh.map t) H).trans
      (DerivedCategory.Plus.Qh.map_comp _ _))
  refine L.trans (Eq.trans (whisker_eq _ ((reassoc_of% H') _)) (R.symm.trans ?_))
  exact whisker_eq _ (whisker_eq _ (Category.comp_id _)).symm

/-- **`b^{-1} (b ∘ a)_! ≅ a_!` on `D⁺` is the isomorphism of [Stacks, Tag 03S6]** for the cartesian
square `X = X ×_{X̄} U`, read through `(𝟙_X)^{-1} ≅ 𝟭`. -/
theorem etaleModuleDerivedExtensionByZeroRestrictIso_hom :
    (etaleModuleDerivedExtensionByZeroRestrictIso Λ a b).hom =
      (etaleModuleDerivedExtensionByZeroCubeIso Λ hc).inv ≫
        Functor.whiskerRight (etaleModuleDerivedInverseImagePlusIdIso Λ X).hom _ ≫
        (Functor.leftUnitor _).hom :=
  etaleModuleDerivedExtensionByZeroRestrictIso_hom_of Λ a b hc
    (etaleModuleExtensionByZeroRestrictIso_hom Λ a b hc)

omit [IsOpenImmersion a] [IsOpenImmersion b] in
/-- `Stacks.EtaleCohomology.restrictBaseExtensionByZeroIso` is
`Stacks.EtaleCohomology.etaleModuleDerivedExtensionByZeroRestrictIso` for `a` the open immersion of
`X` into `X̄ ×_Ȳ Y` and `b` the open immersion `X̄ ×_Ȳ Y ⟶ X̄`. -/
theorem restrictBaseExtensionByZeroIso_eq {Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (jg : CompactificationOf (Over.mk g)) (jX : CompactificationOf (Over.mk (f ≫ jg.immersion))) :
    restrictBaseExtensionByZeroIso Λ jg jX =
      etaleModuleDerivedExtensionByZeroRestrictIso Λ
        (CompactificationOf.restrictBase jg jX).immersion
        (CompactificationOf.restrictBaseι jg jX) :=
  rfl

end Stacks.EtaleCohomology
