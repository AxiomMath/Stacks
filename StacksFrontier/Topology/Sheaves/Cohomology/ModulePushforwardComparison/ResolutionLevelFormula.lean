module

public import StacksFrontier.Topology.Sheaves.Cohomology.ModulePushforwardComparison.CocycleFormula

/-!
# The resolution-level formula for the comparison of right derived functors

Let `T` be an additive functor between abelian categories, `I` an injective resolution of `M`,
`J` an injective resolution of `T M`, and `φ` a comparison of the two extending the identity.
This file computes the comparisons of bounded below right derived functors attached to `T` on the
pair `(I, J)` by `φ`, and applies this to the forgetful functor from sheaves of modules to abelian
sheaves on a ringed space to identify the effect on cocycles of the comparison between the higher
direct images of modules and of abelian sheaves.

## Main results

* `extendSingle_derivedMapExtend_extendMap`: transporting the single complex on `M` in degree zero
  from `ℕ` to `ℤ` and then comparing the image under `T` of an extension with the extension of an
  image agrees with applying `CategoryTheory.HomologicalComplex.singleMapHomologicalComplex`
  first.
* `singleMapHomologicalComplex_comp_resolutionSingleHom`: the cochain-level compatibility of
  `Stacks.Cohomology.HigherDirectImagePresheaf.resolutionSingleHom` with
  `resolutionExtendComparison`.
* `resolutionExtendPlusHom`: `resolutionExtendComparison` read in the bounded below homotopy
  category, and `singleMapPlusHom_comp_resolutionSingleQhHom`: the compatibility there.
* `singleFunctorPlusRightDerivedIso`: for an exact `T`, the bounded below right derived functor
  of `T` on `M` placed in degree zero is `T M` placed in degree zero.
* `rightDerivedFunctorPlusUnit_comp_singleFunctorIso_eq`: the composite of the unit of `T`'s
  right derived functor with `singleFunctorPlusRightDerivedIso` and the two
  `Stacks.Cohomology.HigherDirectImagePresheaf.resolutionDerivedIso`s is
  `DerivedCategory.Plus.Qh` of `resolutionExtendPlusHom`.
* `derivedPlusToStandard_trans_hom_app_eq`: for an exact `T` and a comparison
  `dc : R(A ∘ T) ⟶ RA ∘ RT`, the induced comparison `(A ∘ T).rightDerived n ≅ T ⋙ A.rightDerived n`
  is computed at `M` on `(I, J)` by `φ`.
* `rightDerived_modulePushforward_forget_iso_cocycles`: the comparison between the higher direct
  images of a sheaf of modules and of its underlying abelian sheaf acts on cocycles as any
  comparison of injective resolutions extending the identity does.

## References

* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.HigherDirectImagePresheaf

namespace Stacks.Cohomology.ModulePushforwardComparison

/-! ### The `eqToHom` collapse, and the cochain-level compatibility -/

section CochainLevel

open HomologicalComplex

variable {C₁ : Type*} {C₂ : Type*} [Category* C₁] [Category* C₂] [Abelian C₁] [Abelian C₂]
  (T : C₁ ⥤ C₂) [T.Additive]

/-- Extending the single complex on `M` in degree zero from `ℕ` to
`ℤ`, pushing it through `T` and comparing with the extension of the image agrees with applying
`CategoryTheory.HomologicalComplex.singleMapHomologicalComplex` in the `ℤ`-indexed world and
extending there. -/
theorem extendSingle_derivedMapExtend_extendMap (M : C₁) :
    (T.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (extendSingleIso ComplexShape.embeddingUpNat M 0 0 (by simp)).inv ≫
        (derivedMapExtendIso T ComplexShape.embeddingUpNat
          ((single C₁ (ComplexShape.up ℕ) 0).obj M)).hom ≫
        extendMap ((singleMapHomologicalComplex T (ComplexShape.up ℕ) 0).hom.app M)
          ComplexShape.embeddingUpNat =
      (singleMapHomologicalComplex T (ComplexShape.up ℤ) 0).hom.app M ≫
        (extendSingleIso ComplexShape.embeddingUpNat (T.obj M) 0 0 (by simp)).inv := by
  have h0 : ComplexShape.embeddingUpNat.f (0 : ℕ) = (0 : ℤ) := by simp
  ext j
  by_cases hj : j = 0
  · subst hj
    rw [comp_f, comp_f, comp_f, Functor.mapHomologicalComplex_map_f,
      extendSingleIso_inv_f _ _ _ _ h0, extendSingleIso_inv_f _ _ _ _ h0,
      derivedMapExtendIso_hom_f T _ _ h0, extendMap_f _ _ h0,
      singleMapHomologicalComplex_hom_app_self, singleMapHomologicalComplex_hom_app_self]
    simp only [Functor.comp_obj, Category.assoc]
    rw [Iso.inv_hom_id_assoc, ← Functor.map_comp_assoc]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp_assoc,
      Iso.inv_hom_id, Category.comp_id]
  · exact (T.map_isZero (isZero_single_obj_X (ComplexShape.up ℤ) 0 M j hj)).eq_of_src _ _

/-- **The cochain-level compatibility.**  The quasi-isomorphism comparing `T M` placed in degree
zero with the extension of `J`, precomposed with
`CategoryTheory.HomologicalComplex.singleMapHomologicalComplex`, is the image under `T` of the
corresponding quasi-isomorphism for `I` followed by `resolutionExtendComparison`. -/
theorem singleMapHomologicalComplex_comp_resolutionSingleHom {M : C₁}
    (I : InjectiveResolution M) (J : InjectiveResolution (T.obj M))
    (φ : (T.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex ⟶ J.cocomplex)
    (hφ : T.map (I.ι.f 0) ≫ φ.f 0 = J.ι.f 0) :
    (singleMapHomologicalComplex T (ComplexShape.up ℤ) 0).hom.app M ≫
        resolutionSingleHom J =
      (T.mapHomologicalComplex (ComplexShape.up ℤ)).map (resolutionSingleHom I) ≫
        resolutionExtendComparison T I J φ := by
  dsimp only [resolutionSingleHom, resolutionExtendComparison]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (derivedMapExtendIso_naturality T I.ι), ← extendMap_comp,
    singleMapHomologicalComplex_comp_ι T I J φ hφ, extendMap_comp,
    reassoc_of% (extendSingle_derivedMapExtend_extendMap T M)]

end CochainLevel

/-! ### The compatibility in the bounded below homotopy category -/

section HomotopyLevel

open HomologicalComplex

variable {C₁ : Type*} {C₂ : Type*} [Category* C₁] [Category* C₂] [Abelian C₁] [Abelian C₂]
  (T : C₁ ⥤ C₂) [T.Additive]

/-- `CategoryTheory.Functor.mapHomotopyCategorySingleFunctor` is
`CategoryTheory.HomologicalComplex.singleMapHomologicalComplex` read in the homotopy
category. -/
theorem mapHomotopyCategorySingleFunctor_hom_app (M : C₁) :
    (T.mapHomotopyCategorySingleFunctor 0).hom.app M =
      (HomotopyCategory.quotient C₂ (ComplexShape.up ℤ)).map
        ((singleMapHomologicalComplex T (ComplexShape.up ℤ) 0).hom.app M) := by
  have h1 : (HomotopyCategory.singleFunctorPostcompQuotientIso C₁ 0).hom.app M = 𝟙 _ := rfl
  have h2 : (T.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app
      ((CochainComplex.singleFunctor C₁ 0).obj M) = 𝟙 _ := rfl
  have h3 : (HomotopyCategory.singleFunctorPostcompQuotientIso C₂ 0).inv.app (T.obj M)
      = 𝟙 _ := rfl
  dsimp only [Functor.mapHomotopyCategorySingleFunctor]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.associator_inv_app, Iso.symm_hom, h1, h2, h3]
  show (T.mapHomotopyCategory (ComplexShape.up ℤ)).map (𝟙 _) ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫
      (HomotopyCategory.quotient C₂ (ComplexShape.up ℤ)).map
        ((singleMapHomologicalComplex T (ComplexShape.up ℤ) 0).hom.app M) ≫ 𝟙 _ ≫ 𝟙 _ = _
  refine Eq.trans (congrArg (fun g ↦ g ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫
    (HomotopyCategory.quotient C₂ (ComplexShape.up ℤ)).map
      ((singleMapHomologicalComplex T (ComplexShape.up ℤ) 0).hom.app M) ≫ 𝟙 _ ≫ 𝟙 _)
    ((T.mapHomotopyCategory (ComplexShape.up ℤ)).map_id _)) ?_
  simp only [Category.comp_id, Category.id_comp]

/-- `resolutionExtendComparison` read in the bounded below homotopy category, as the preimage
under the fully faithful `CategoryTheory.HomotopyCategory.Plus.ι`. -/
noncomputable def resolutionExtendPlusHom {M : C₁} (I : InjectiveResolution M)
    (J : InjectiveResolution (T.obj M))
    (φ : (T.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex ⟶ J.cocomplex) :
    T.mapHomotopyCategoryPlus.obj
        ((HomotopyCategory.Plus.quotient C₁).obj (resolutionCochainPlus I)) ⟶
      (HomotopyCategory.Plus.quotient C₂).obj (resolutionCochainPlus J) :=
  (HomotopyCategory.Plus.ι C₂).preimage
    ((HomotopyCategory.quotient C₂ (ComplexShape.up ℤ)).map
      (resolutionExtendComparison T I J φ))

/-- `resolutionExtendPlusHom` is `resolutionExtendComparison` in the homotopy category. -/
private theorem map_resolutionExtendPlusHom {M : C₁} (I : InjectiveResolution M)
    (J : InjectiveResolution (T.obj M))
    (φ : (T.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex ⟶ J.cocomplex) :
    (HomotopyCategory.Plus.ι C₂).map (resolutionExtendPlusHom T I J φ) =
      (HomotopyCategory.quotient C₂ (ComplexShape.up ℤ)).map
        (resolutionExtendComparison T I J φ) :=
  Functor.map_preimage _ _

/-- **The compatibility in the bounded below homotopy category.**  The augmentation of `J`,
precomposed with `singleMapPlusHom`, is the image under `T` of the augmentation of `I` followed
by `resolutionExtendPlusHom`. -/
theorem singleMapPlusHom_comp_resolutionSingleQhHom {M : C₁} (I : InjectiveResolution M)
    (J : InjectiveResolution (T.obj M))
    (φ : (T.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex ⟶ J.cocomplex)
    (hφ : T.map (I.ι.f 0) ≫ φ.f 0 = J.ι.f 0) :
    singleMapPlusHom T M ≫ resolutionSingleQhHom J =
      T.mapHomotopyCategoryPlus.map (resolutionSingleQhHom I) ≫
        resolutionExtendPlusHom T I J φ := by
  apply (HomotopyCategory.Plus.ι C₂).map_injective
  have hl : (HomotopyCategory.Plus.ι C₂).map (singleMapPlusHom T M ≫
        resolutionSingleQhHom J) =
      (HomotopyCategory.quotient C₂ (ComplexShape.up ℤ)).map
        ((singleMapHomologicalComplex T (ComplexShape.up ℤ) 0).hom.app M ≫
          resolutionSingleHom J) := by
    rw [Functor.map_comp, ι_map_singleMapPlusHom, ι_map_resolutionSingleQhHom,
      mapHomotopyCategorySingleFunctor_hom_app, Functor.map_comp]
    exact congrArg (fun g ↦ (HomotopyCategory.quotient C₂ (ComplexShape.up ℤ)).map
      ((singleMapHomologicalComplex T (ComplexShape.up ℤ) 0).hom.app M) ≫ g)
      (Category.id_comp _)
  have hq : (HomotopyCategory.Plus.ι C₂).map
        (T.mapHomotopyCategoryPlus.map (resolutionSingleQhHom I)) =
      (HomotopyCategory.quotient C₂ (ComplexShape.up ℤ)).map
        ((T.mapHomologicalComplex (ComplexShape.up ℤ)).map (resolutionSingleHom I)) := by
    show (T.mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((HomotopyCategory.Plus.ι C₁).map (resolutionSingleQhHom I)) = _
    rw [ι_map_resolutionSingleQhHom]
    exact congrArg ((T.mapHomotopyCategory (ComplexShape.up ℤ)).map) (Category.id_comp _)
  have hr : (HomotopyCategory.Plus.ι C₂).map
        (T.mapHomotopyCategoryPlus.map (resolutionSingleQhHom I) ≫
          resolutionExtendPlusHom T I J φ) =
      (HomotopyCategory.quotient C₂ (ComplexShape.up ℤ)).map
        ((T.mapHomologicalComplex (ComplexShape.up ℤ)).map (resolutionSingleHom I) ≫
          resolutionExtendComparison T I J φ) := by
    rw [Functor.map_comp, hq, map_resolutionExtendPlusHom]
    exact ((HomotopyCategory.quotient C₂ (ComplexShape.up ℤ)).map_comp _ _).symm
  rw [hl, hr]
  exact congrArg ((HomotopyCategory.quotient C₂ (ComplexShape.up ℤ)).map)
    (singleMapHomologicalComplex_comp_resolutionSingleHom T I J φ hφ)

end HomotopyLevel

/-! ### The comparison in the derived category -/

section DerivedLevel

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {C₁ : Type*} {C₂ : Type*} [Category* C₁] [Category* C₂] [Abelian C₁] [Abelian C₂]
  [HasDerivedCategory C₁] [HasDerivedCategory C₂] [EnoughInjectives C₁]
  (T : C₁ ⥤ C₂) [T.Additive]

/-- **`T` commutes with placing an object in degree zero**, for a `T` whose bounded below right
derived functor has an invertible unit, that is, an exact `T`. -/
noncomputable def singleFunctorPlusRightDerivedIso [IsIso T.rightDerivedFunctorPlusUnith] :
    DerivedCategory.Plus.singleFunctor C₁ 0 ⋙ T.rightDerivedFunctorPlus ≅
      T ⋙ DerivedCategory.Plus.singleFunctor C₂ 0 :=
  Functor.isoWhiskerRight (Functor.singleFunctorPlusIsoCompQh 0)
      T.rightDerivedFunctorPlus ≪≫
    Functor.isoWhiskerLeft (HomotopyCategory.Plus.singleFunctor C₁ 0)
      (asIso T.rightDerivedFunctorPlusUnith).symm ≪≫
    Functor.mapSingleFunctorCompQhIso T

/-- Three applications of a functor to morphisms whose composite is the identity cancel. -/
private theorem map_collapse_three {Ca Cb : Type*} [Category* Ca] [Category* Cb] (F : Ca ⥤ Cb)
    {X Y Z : Ca} (a : X ⟶ Y) (b : Y ⟶ Z) (c : Z ⟶ X) (h : a ≫ b ≫ c = 𝟙 X)
    {R : Cb} (k : F.obj X ⟶ R) :
    F.map a ≫ F.map b ≫ F.map c ≫ k = k := by
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc, h,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- For an exact `T`, the unit of `T`'s bounded below right derived functor at the
extension of `I`, transported back along
`Stacks.Cohomology.HigherDirectImagePresheaf.resolutionDerivedIso`, read through
`singleFunctorPlusRightDerivedIso` and transported forward along the corresponding isomorphism
for `J`, is `DerivedCategory.Plus.Qh` of `resolutionExtendPlusHom`. -/
theorem rightDerivedFunctorPlusUnit_comp_singleFunctorIso_eq
    [IsIso T.rightDerivedFunctorPlusUnith] {M : C₁} (I : InjectiveResolution M)
    (J : InjectiveResolution (T.obj M))
    (φ : (T.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex ⟶ J.cocomplex)
    (hφ : T.map (I.ι.f 0) ≫ φ.f 0 = J.ι.f 0) :
    T.rightDerivedFunctorPlusUnith.app
          ((HomotopyCategory.Plus.quotient C₁).obj (resolutionCochainPlus I)) ≫
        T.rightDerivedFunctorPlus.map (resolutionDerivedIso I).inv ≫
          (singleFunctorPlusRightDerivedIso T).hom.app M ≫ (resolutionDerivedIso J).hom =
      DerivedCategory.Plus.Qh.map (resolutionExtendPlusHom T I J φ) := by
  set g := resolutionSingleQhHom I with hg
  have hiso : IsIso (DerivedCategory.Plus.Qh.map g) := by
    have e : g = (singlePlusToCochainQuotientIso (A := C₁)).hom.app M ≫
        (HomotopyCategory.Plus.quotient C₁).map (resolutionSinglePlusHom I) := rfl
    have := resolutionSinglePlusHom_qh_isIso I
    rw [e, Functor.map_comp]
    infer_instance
  have hnat : DerivedCategory.Plus.Qh.map (T.mapHomotopyCategoryPlus.map g) ≫
      T.rightDerivedFunctorPlusUnith.app
        ((HomotopyCategory.Plus.quotient C₁).obj (resolutionCochainPlus I)) =
      T.rightDerivedFunctorPlusUnith.app
          ((HomotopyCategory.Plus.singleFunctor C₁ 0).obj M) ≫
        T.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map g) :=
    T.rightDerivedFunctorPlusUnith.naturality g
  have h3 : IsIso (T.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.singleFunctor C₁ 0).obj M)) :=
    NatIso.isIso_app_of_isIso _ _
  have h5 : IsIso (T.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.quotient C₁).obj (resolutionCochainPlus I))) :=
    NatIso.isIso_app_of_isIso _ _
  have hepi : IsIso (DerivedCategory.Plus.Qh.map (T.mapHomotopyCategoryPlus.map g)) := by
    have h4 : IsIso (DerivedCategory.Plus.Qh.map (T.mapHomotopyCategoryPlus.map g) ≫
        T.rightDerivedFunctorPlusUnith.app
          ((HomotopyCategory.Plus.quotient C₁).obj (resolutionCochainPlus I))) := by
      rw [hnat]
      exact IsIso.comp_isIso
    exact IsIso.of_isIso_comp_right
      (DerivedCategory.Plus.Qh.map (T.mapHomotopyCategoryPlus.map g))
      (T.rightDerivedFunctorPlusUnith.app
        ((HomotopyCategory.Plus.quotient C₁).obj (resolutionCochainPlus I)))
  have hB : DerivedCategory.Plus.Qh.map g ≫ (resolutionDerivedIso I).inv =
      (Functor.singleFunctorPlusIsoCompQh (A := C₁) 0).inv.app M := by
    refine (cancel_epi ((Functor.singleFunctorPlusIsoCompQh (A := C₁) 0).hom.app M)).1 ?_
    rw [← Category.assoc, ← resolutionDerivedIso_hom_eq I, Iso.hom_inv_id,
      Iso.hom_inv_id_app]
  have hB2 : DerivedCategory.Plus.Qh.map g ≫ (resolutionDerivedIso I).inv ≫
      (Functor.singleFunctorPlusIsoCompQh (A := C₁) 0).hom.app M = 𝟙 _ := by
    rw [← Category.assoc, hB, Iso.inv_hom_id_app]
    rfl
  have hts : (singleFunctorPlusRightDerivedIso T).hom.app M =
      T.rightDerivedFunctorPlus.map
          ((Functor.singleFunctorPlusIsoCompQh (A := C₁) 0).hom.app M) ≫
        (asIso T.rightDerivedFunctorPlusUnith).inv.app
          ((HomotopyCategory.Plus.singleFunctor C₁ 0).obj M) ≫
          (Functor.mapSingleFunctorCompQhIso T).hom.app M := rfl
  have hu : T.rightDerivedFunctorPlusUnith.app
        ((HomotopyCategory.Plus.singleFunctor C₁ 0).obj M) ≫
      (asIso T.rightDerivedFunctorPlusUnith).inv.app
        ((HomotopyCategory.Plus.singleFunctor C₁ 0).obj M) = 𝟙 _ :=
    Iso.hom_inv_id_app (asIso T.rightDerivedFunctorPlusUnith) _
  have hR : DerivedCategory.Plus.Qh.map (T.mapHomotopyCategoryPlus.map g) ≫
        DerivedCategory.Plus.Qh.map (resolutionExtendPlusHom T I J φ) =
      DerivedCategory.Plus.Qh.map (singleMapPlusHom T M) ≫
        DerivedCategory.Plus.Qh.map (resolutionSingleQhHom J) := by
    rw [← Functor.map_comp, ← singleMapPlusHom_comp_resolutionSingleQhHom T I J φ hφ,
      Functor.map_comp]
  have hL : DerivedCategory.Plus.Qh.map (T.mapHomotopyCategoryPlus.map g) ≫
        (T.rightDerivedFunctorPlusUnith.app
            ((HomotopyCategory.Plus.quotient C₁).obj (resolutionCochainPlus I)) ≫
          T.rightDerivedFunctorPlus.map (resolutionDerivedIso I).inv ≫
            (singleFunctorPlusRightDerivedIso T).hom.app M ≫
              (resolutionDerivedIso J).hom) =
      DerivedCategory.Plus.Qh.map (singleMapPlusHom T M) ≫
        DerivedCategory.Plus.Qh.map (resolutionSingleQhHom J) := by
    rw [← Category.assoc, hnat, Category.assoc, hts]
    simp only [Category.assoc]
    refine Eq.trans (congrArg (fun z ↦ T.rightDerivedFunctorPlusUnith.app
        ((HomotopyCategory.Plus.singleFunctor C₁ 0).obj M) ≫ z)
      (map_collapse_three T.rightDerivedFunctorPlus _ _ _ hB2 _)) ?_
    rw [← Category.assoc, hu, Category.id_comp, resolutionDerivedIso_hom_eq J,
      ← Category.assoc, mapSingleFunctorCompQhIso_hom_app_comp T M]
  exact (cancel_epi (DerivedCategory.Plus.Qh.map
    (T.mapHomotopyCategoryPlus.map g))).1 (hL.trans hR.symm)

end DerivedLevel

/-! ### The resolution-level formula for a two-step comparison -/

section TwoStepComparison

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {C₁ : Type*} {C₂ : Type*} {C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
  [Abelian C₁] [Abelian C₂] [Abelian C₃]
  [HasDerivedCategory C₁] [HasDerivedCategory C₂] [HasDerivedCategory C₃]
  [EnoughInjectives C₁] [EnoughInjectives C₂]
  (T : C₁ ⥤ C₂) (A : C₂ ⥤ C₃) [T.Additive] [A.Additive]

/-- The transformation `(A ∘ T)⁺ ⋙ Qh ⟶ Qh ⋙ RT ⋙ RA` assembled from the units of the bounded
below right derived functors of `T` and of `A`. -/
noncomputable def derivedCompositionUnitOf :
    (T ⋙ A).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙ T.rightDerivedFunctorPlus ⋙ A.rightDerivedFunctorPlus :=
  Functor.whiskerRight (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (T ⋙ A))).inv
      DerivedCategory.Plus.Qh ≫
    Functor.whiskerLeft T.mapHomotopyCategoryPlus A.rightDerivedFunctorPlusUnith ≫
    Functor.whiskerRight T.rightDerivedFunctorPlusUnith A.rightDerivedFunctorPlus

omit [HasDerivedCategory C₁] [HasDerivedCategory C₂] [HasDerivedCategory C₃]
  [EnoughInjectives C₁] [EnoughInjectives C₂] in
/-- **The comparison of `A ∘ T` with `A` after `T` on the extension of an injective resolution
is the identity.** -/
theorem mapHomotopyCategoryPlusCompIso_inv_app_resolution {M : C₁}
    (I : InjectiveResolution M) :
    (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (T ⋙ A))).inv.app
        ((HomotopyCategory.Plus.quotient C₁).obj (resolutionCochainPlus I)) = 𝟙 _ := by
  apply (HomotopyCategory.Plus.ι C₃).map_injective
  have e1 : (HomotopyCategory.Plus.ι C₃).map
        ((Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (T ⋙ A))).inv.app
          ((HomotopyCategory.Plus.quotient C₁).obj (resolutionCochainPlus I))) =
      (HomotopyCategory.quotient C₃ (ComplexShape.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso (Iso.refl (T ⋙ A))
          (ComplexShape.up ℤ)).inv.app (resolutionCochainPlus I).obj) :=
    (HomotopyCategory.plus C₃).fullyFaithfulι.map_preimage _
  have e2 : (Functor.mapHomologicalComplexCompIso (Iso.refl (T ⋙ A))
      (ComplexShape.up ℤ)).inv.app (resolutionCochainPlus I).obj = 𝟙 _ := by ext j; simp
  rw [e1, e2]
  exact (((HomotopyCategory.quotient C₃ (ComplexShape.up ℤ))).map_id _).trans
    (CategoryTheory.Functor.map_id _ _).symm

/-- Four applications of a functor, after a morphism `u`, collapse to the application to their
composite. -/
private theorem unit_collapse {Ca Cb : Type*} [Category* Ca] [Category* Cb] (F : Ca ⥤ Cb)
    {X Y Z W V : Ca} (a : X ⟶ Y) (b : Y ⟶ Z) (c : Z ⟶ W) (d : W ⟶ V) (m : X ⟶ V)
    (h : a ≫ b ≫ c ≫ d = m) {P R : Cb} (u : P ⟶ F.obj X) (k : F.obj V ⟶ R) :
    (u ≫ F.map a) ≫ F.map b ≫ F.map c ≫ F.map d ≫ k = u ≫ F.map m ≫ k := by
  rw [← h]; simp

/-- **The two-step comparison on a resolution, in the derived category.**  Let `dc` be a
transformation `R(A ∘ T) ⟶ RA ∘ RT` whose composite with the unit of `R(A ∘ T)` is
`derivedCompositionUnitOf`.  Then the comparison, read at `M` placed in degree zero and
transported along the two `Stacks.Cohomology.HigherDirectImagePresheaf.resolutionDerivedIso`s,
is `DerivedCategory.Plus.Qh` of `A.mapHomotopyCategoryPlus` applied to
`resolutionExtendPlusHom`. -/
theorem derivedComposition_app_eq_qh_resolutionExtendPlusHom
    [IsIso T.rightDerivedFunctorPlusUnith]
    (dc : (T ⋙ A).rightDerivedFunctorPlus ⟶
      T.rightDerivedFunctorPlus ⋙ A.rightDerivedFunctorPlus)
    (hdc : (T ⋙ A).rightDerivedFunctorPlusUnith ≫
      Functor.whiskerLeft DerivedCategory.Plus.Qh dc = derivedCompositionUnitOf T A)
    {M : C₁} (I : InjectiveResolution M) (J : InjectiveResolution (T.obj M))
    (φ : (T.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex ⟶ J.cocomplex)
    (hφ : T.map (I.ι.f 0) ≫ φ.f 0 = J.ι.f 0) :
    (T ⋙ A).rightDerivedFunctorPlusUnith.app
          ((HomotopyCategory.Plus.quotient C₁).obj (resolutionCochainPlus I)) ≫
        (T ⋙ A).rightDerivedFunctorPlus.map (resolutionDerivedIso I).inv ≫
          dc.app ((DerivedCategory.Plus.singleFunctor C₁ 0).obj M) ≫
            A.rightDerivedFunctorPlus.map ((singleFunctorPlusRightDerivedIso T).hom.app M) ≫
              A.rightDerivedFunctorPlus.map (resolutionDerivedIso J).hom ≫
                (asIso (A.rightDerivedFunctorPlusUnith.app
                  ((HomotopyCategory.Plus.quotient C₂).obj (resolutionCochainPlus J)))).inv =
      DerivedCategory.Plus.Qh.map
        (A.mapHomotopyCategoryPlus.map (resolutionExtendPlusHom T I J φ)) := by
  have hdcu : (derivedCompositionUnitOf T A).app
        ((HomotopyCategory.Plus.quotient C₁).obj (resolutionCochainPlus I)) =
      A.rightDerivedFunctorPlusUnith.app (T.mapHomotopyCategoryPlus.obj
          ((HomotopyCategory.Plus.quotient C₁).obj (resolutionCochainPlus I))) ≫
        A.rightDerivedFunctorPlus.map (T.rightDerivedFunctorPlusUnith.app
          ((HomotopyCategory.Plus.quotient C₁).obj (resolutionCochainPlus I))) := by
    rw [show (derivedCompositionUnitOf T A).app
          ((HomotopyCategory.Plus.quotient C₁).obj (resolutionCochainPlus I)) =
        DerivedCategory.Plus.Qh.map
            ((Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (T ⋙ A))).inv.app
              ((HomotopyCategory.Plus.quotient C₁).obj (resolutionCochainPlus I))) ≫
          A.rightDerivedFunctorPlusUnith.app (T.mapHomotopyCategoryPlus.obj
              ((HomotopyCategory.Plus.quotient C₁).obj (resolutionCochainPlus I))) ≫
            A.rightDerivedFunctorPlus.map (T.rightDerivedFunctorPlusUnith.app
              ((HomotopyCategory.Plus.quotient C₁).obj (resolutionCochainPlus I)))
        from rfl, mapHomotopyCategoryPlusCompIso_inv_app_resolution]
    exact (congrArg (fun z ↦ z ≫ A.rightDerivedFunctorPlusUnith.app
          (T.mapHomotopyCategoryPlus.obj
            ((HomotopyCategory.Plus.quotient C₁).obj (resolutionCochainPlus I))) ≫
        A.rightDerivedFunctorPlus.map (T.rightDerivedFunctorPlusUnith.app
          ((HomotopyCategory.Plus.quotient C₁).obj (resolutionCochainPlus I))))
      (DerivedCategory.Plus.Qh.map_id _)).trans (Category.id_comp _)
  rw [reassoc_of% (rightDerivedFunctorPlusUnit_comp_app_singleFunctor_obj T A dc
    (derivedCompositionUnitOf T A) hdc I)]
  refine Eq.trans (congrArg (fun z ↦ z ≫
      (T.rightDerivedFunctorPlus ⋙ A.rightDerivedFunctorPlus).map
        (resolutionDerivedIso I).inv ≫
      A.rightDerivedFunctorPlus.map ((singleFunctorPlusRightDerivedIso T).hom.app M) ≫
      A.rightDerivedFunctorPlus.map (resolutionDerivedIso J).hom ≫
        (asIso (A.rightDerivedFunctorPlusUnith.app
          ((HomotopyCategory.Plus.quotient C₂).obj (resolutionCochainPlus J)))).inv) hdcu) ?_
  refine Eq.trans (unit_collapse A.rightDerivedFunctorPlus _ _ _ _ _
    (rightDerivedFunctorPlusUnit_comp_singleFunctorIso_eq T I J φ hφ) _ _) ?_
  have hn := A.rightDerivedFunctorPlusUnith.naturality (resolutionExtendPlusHom T I J φ)
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun z ↦ z ≫ (asIso (A.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.quotient C₂).obj (resolutionCochainPlus J)))).inv) hn.symm) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun z ↦ DerivedCategory.Plus.Qh.map
      (A.mapHomotopyCategoryPlus.map (resolutionExtendPlusHom T I J φ)) ≫ z)
    (Iso.hom_inv_id (asIso (A.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.quotient C₂).obj (resolutionCochainPlus J)))))) ?_
  exact Category.comp_id _

omit [HasDerivedCategory C₁] [HasDerivedCategory C₂]
  [EnoughInjectives C₁] [EnoughInjectives C₂] in
/-- **The cohomology of `resolutionExtendPlusHom` is the cohomology of `φ`.**  Reading the
degree-`n` cohomology of the extension through
`Stacks.Cohomology.HigherDirectImagePresheaf.extendedHomologyIso` turns
`resolutionExtendPlusHom` into `CategoryTheory.HomologicalComplex.homologyMap` of `φ`. -/
theorem homologyFunctor_map_qh_resolutionExtendPlusHom {M : C₁} (I : InjectiveResolution M)
    (J : InjectiveResolution (T.obj M))
    (φ : (T.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex ⟶ J.cocomplex)
    (n : ℕ) :
    (DerivedCategory.Plus.homologyFunctor C₃ (n : ℤ)).map
          (DerivedCategory.Plus.Qh.map (A.mapHomotopyCategoryPlus.map
            (resolutionExtendPlusHom T I J φ))) ≫
        (extendedHomologyIso A J.cocomplex n).hom =
      (extendedHomologyIso (T ⋙ A) I.cocomplex n).hom ≫
        HomologicalComplex.homologyMap
          ((A.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) n := by
  have hpsii : (HomotopyCategory.Plus.ι C₃).map (A.mapHomotopyCategoryPlus.map
        (resolutionExtendPlusHom T I J φ)) =
      (HomotopyCategory.quotient C₃ (ComplexShape.up ℤ)).map
        ((A.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (resolutionExtendComparison T I J φ)) :=
    congrArg ((A.mapHomotopyCategory (ComplexShape.up ℤ)).map)
      (map_resolutionExtendPlusHom T I J φ)
  have hlhs : (DerivedCategory.Plus.homologyFunctor C₃ (n : ℤ)).map
        (DerivedCategory.Plus.Qh.map (A.mapHomotopyCategoryPlus.map
          (resolutionExtendPlusHom T I J φ))) =
      (DerivedCategory.homologyFunctor C₃ (n : ℤ)).map (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient C₃ (ComplexShape.up ℤ)).map
          ((A.mapHomologicalComplex (ComplexShape.up ℤ)).map
            (resolutionExtendComparison T I J φ)))) :=
    congrArg (fun z ↦ (DerivedCategory.homologyFunctor C₃ (n : ℤ)).map
      (DerivedCategory.Qh.map z)) hpsii
  rw [hlhs, extendedHomologyIso_comp T A I.cocomplex n]
  dsimp only [resolutionExtendComparison]
  simp only [Functor.map_comp]
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun z ↦ (DerivedCategory.homologyFunctor C₃ (n : ℤ)).map
      (DerivedCategory.Qh.map ((HomotopyCategory.quotient C₃ (ComplexShape.up ℤ)).map
        ((A.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (derivedMapExtendIso T ComplexShape.embeddingUpNat I.cocomplex).hom))) ≫ z)
    (extendedHomologyIso_naturality A φ n)) ?_
  exact (Category.assoc _ _ _).symm

/-- Bundling four applications of a functor, the outer two to composites. -/
private theorem map_bundle {Ca Cb : Type*} [Category* Ca] [Category* Cb] (F : Ca ⥤ Cb)
    {X₀ X₁ X₂ X₃ X₄ X₅ X₆ : Ca} (a₁ : X₀ ⟶ X₁) (a₂ : X₁ ⟶ X₂) (b : X₂ ⟶ X₃)
    (c : X₃ ⟶ X₄) (d₁ : X₄ ⟶ X₅) (d₂ : X₅ ⟶ X₆) (m : X₀ ⟶ X₆)
    (h : a₁ ≫ a₂ ≫ b ≫ c ≫ d₁ ≫ d₂ = m) :
    F.map (a₁ ≫ a₂) ≫ F.map b ≫ F.map c ≫ F.map (d₁ ≫ d₂) = F.map m := by
  rw [← h]; simp

/-- Cancelling an isomorphism against a four-factor composite whose value is known. -/
private theorem glue_mid {E' : Type*} [Category* E'] {p q r s t u v : E'}
    (eI : q ≅ p) (a : q ⟶ r) (b : r ⟶ s) (c : s ⟶ t) (d : t ⟶ u) (ej : u ⟶ v)
    (z : q ⟶ u) (hz : a ≫ b ≫ c ≫ d = z) (m : p ⟶ v) (hm : z ≫ ej = eI.hom ≫ m) :
    eI.inv ≫ a ≫ b ≫ c ≫ d ≫ ej = m := by
  have e : a ≫ b ≫ c ≫ d ≫ ej = z ≫ ej := by rw [← hz]; simp
  rw [e, hm, Iso.inv_hom_id_assoc]

/-- Conjugating a composite of two `derivedPlusToStandardObjOfResolution`s by their
`CategoryTheory.InjectiveResolution.isoRightDerivedObj` factors. -/
private theorem glue_dpts {E' : Type*} [Category* E'] {a b c d e f g h k : E'}
    (pI : a ≅ b) (eI : b ≅ c) (rI : d ≅ c) (x : a ⟶ e) (y : e ⟶ f)
    (pJ : f ≅ g) (eJ : g ≅ h) (rJ : k ≅ h) (m : c ⟶ h)
    (hm : eI.inv ≫ pI.inv ≫ x ≫ y ≫ pJ.hom ≫ eJ.hom = m) :
    (pI ≪≫ eI ≪≫ rI.symm).inv ≫ x ≫ y ≫ (pJ ≪≫ eJ ≪≫ rJ.symm).hom
      = rI.hom ≫ m ≫ rJ.inv := by
  rw [← hm]; simp

/-- **The resolution-level formula for a two-step comparison.**  Let `T` be exact and let
`dc : R(A ∘ T) ⟶ RA ∘ RT` be an invertible comparison whose composite with the unit of
`R(A ∘ T)` is `derivedCompositionUnitOf`.  Then the
comparison `(A ∘ T).rightDerived n ≅ T ⋙ A.rightDerived n` that `dc` assembles is computed at
`M` on the pair `(I, J)` by `φ`. -/
theorem derivedPlusToStandard_trans_hom_app_eq [IsIso T.rightDerivedFunctorPlusUnith]
    (dc : (T ⋙ A).rightDerivedFunctorPlus ⟶
      T.rightDerivedFunctorPlus ⋙ A.rightDerivedFunctorPlus) [IsIso dc]
    (hdc : (T ⋙ A).rightDerivedFunctorPlusUnith ≫
      Functor.whiskerLeft DerivedCategory.Plus.Qh dc = derivedCompositionUnitOf T A)
    (n : ℕ) {M : C₁} (I : InjectiveResolution M) (J : InjectiveResolution (T.obj M))
    (φ : (T.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex ⟶ J.cocomplex)
    (hφ : T.map (I.ι.f 0) ≫ φ.f 0 = J.ι.f 0) :
    ((derivedPlusToStandard (T ⋙ A) n).symm ≪≫
        Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor C₁ 0)
          (Functor.isoWhiskerRight (asIso dc)
            (DerivedCategory.Plus.homologyFunctor C₃ (n : ℤ))) ≪≫
        Functor.isoWhiskerRight (singleFunctorPlusRightDerivedIso T)
          (A.rightDerivedFunctorPlus ⋙
            DerivedCategory.Plus.homologyFunctor C₃ (n : ℤ)) ≪≫
        Functor.isoWhiskerLeft T (derivedPlusToStandard A n)).hom.app M =
      (I.isoRightDerivedObj (T ⋙ A) n).hom ≫
        (A.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
          HomologicalComplex.homologyFunctor C₃ (ComplexShape.up ℕ) n).map φ ≫
          (J.isoRightDerivedObj A n).inv := by
  have hL : ((derivedPlusToStandard (T ⋙ A) n).symm ≪≫
        Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor C₁ 0)
          (Functor.isoWhiskerRight (asIso dc)
            (DerivedCategory.Plus.homologyFunctor C₃ (n : ℤ))) ≪≫
        Functor.isoWhiskerRight (singleFunctorPlusRightDerivedIso T)
          (A.rightDerivedFunctorPlus ⋙
            DerivedCategory.Plus.homologyFunctor C₃ (n : ℤ)) ≪≫
        Functor.isoWhiskerLeft T (derivedPlusToStandard A n)).hom.app M =
      (derivedPlusToStandardObjOfResolution (T ⋙ A) I n).inv ≫
        (DerivedCategory.Plus.homologyFunctor C₃ (n : ℤ)).map
            (dc.app ((DerivedCategory.Plus.singleFunctor C₁ 0).obj M)) ≫
          (A.rightDerivedFunctorPlus ⋙
              DerivedCategory.Plus.homologyFunctor C₃ (n : ℤ)).map
              ((singleFunctorPlusRightDerivedIso T).hom.app M) ≫
            (derivedPlusToStandardObjOfResolution A J n).hom := by
    show (derivedPlusToStandard (T ⋙ A) n).inv.app M ≫
        (DerivedCategory.Plus.homologyFunctor C₃ (n : ℤ)).map
            (dc.app ((DerivedCategory.Plus.singleFunctor C₁ 0).obj M)) ≫
          (A.rightDerivedFunctorPlus ⋙
              DerivedCategory.Plus.homologyFunctor C₃ (n : ℤ)).map
              ((singleFunctorPlusRightDerivedIso T).hom.app M) ≫
            (derivedPlusToStandard A n).hom.app (T.obj M) = _
    rw [show (derivedPlusToStandard (T ⋙ A) n).inv.app M =
        (derivedPlusToStandardObjOfResolution (T ⋙ A) I n).inv from
      congrArg Iso.inv (derivedPlusToStandard_app_eq (T ⋙ A) I n),
      show (derivedPlusToStandard A n).hom.app (T.obj M) =
        (derivedPlusToStandardObjOfResolution A J n).hom from
      congrArg Iso.hom (derivedPlusToStandard_app_eq A J n)]
  have hm := glue_mid (extendedHomologyIso (T ⋙ A) I.cocomplex n) _ _ _ _ _ _
    (map_bundle (DerivedCategory.Plus.homologyFunctor C₃ (n : ℤ)) _ _ _ _ _ _ _
      (derivedComposition_app_eq_qh_resolutionExtendPlusHom T A dc hdc I J φ hφ)) _
    (homologyFunctor_map_qh_resolutionExtendPlusHom T A I J φ n)
  rw [hL, derivedPlusToStandardObjOfResolution_eq_trans (T ⋙ A) I n,
    derivedPlusToStandardObjOfResolution_eq_trans A J n]
  exact glue_dpts _ _ _ _ _ _ _ _ _ hm

end TwoStepComparison

/-! ### Higher direct images of modules and of abelian sheaves -/

section PushforwardClause

open AlgebraicGeometry Opposite TopologicalSpace RingedSpaceModuleAdjunction

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

universe u

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The unit of the bounded below right derived functor of the forgetful functor to abelian
sheaves is invertible. -/
theorem isIso_toSheaf_rightDerivedFunctorPlusUnit (Z : RingedSpace.{u, u}) :
    IsIso (SheafOfModules.toSheaf (structureSheafRing Z)).rightDerivedFunctorPlusUnith :=
  Stacks.Cohomology.HigherDirectImage.isIso_rightDerivedFunctorPlusUnit _

attribute [local instance] isIso_toSheaf_rightDerivedFunctorPlusUnit

/-- The comparison `rightDerivedToSheafAbelianPushforwardIso` between the higher direct images
of a sheaf of modules and of its underlying abelian sheaf is computed on the pair `(I, J)` by
`φ`. -/
theorem rightDerivedToSheafAbelianPushforwardIso_hom_app_eq (n : ℕ)
    (M : SheafOfModules.{u} (structureSheafRing X)) (I : InjectiveResolution M)
    (J : InjectiveResolution ((SheafOfModules.toSheaf (structureSheafRing X)).obj M))
    (φ : ((SheafOfModules.toSheaf (structureSheafRing X)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj I.cocomplex ⟶ J.cocomplex)
    (hφ : (SheafOfModules.toSheaf (structureSheafRing X)).map (I.ι.f 0) ≫ φ.f 0 = J.ι.f 0) :
    (rightDerivedToSheafAbelianPushforwardIso f n).hom.app M =
      (I.isoRightDerivedObj (SheafOfModules.toSheaf (structureSheafRing X) ⋙
          abelianPushforward f) n).hom ≫
        ((abelianPushforward f).mapHomologicalComplex (ComplexShape.up ℕ) ⋙
          HomologicalComplex.homologyFunctor
            (Sheaf (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u})
            (ComplexShape.up ℕ) n).map φ ≫
        (J.isoRightDerivedObj (abelianPushforward f) n).inv :=
  derivedPlusToStandard_trans_hom_app_eq (SheafOfModules.toSheaf (structureSheafRing X))
    (abelianPushforward f) (derivedComposition f)
    (Functor.rightDerived_fac _ _ _ _ _) n I J φ hφ

/-- The higher-direct-image comparison is induced by a comparison from a module injective
resolution to an abelian injective resolution extending the identity of the underlying abelian
sheaf: in every degree its effect on cocycles is the one prescribed by any such comparison.  This
fixes the comparison independently of all choices of resolutions and comparison maps. -/
@[stacks 01F1 "part (2), canonical comparison in every degree"]
theorem rightDerived_modulePushforward_forget_iso_cocycles (n : ℕ)
    (M : SheafOfModules.{u} (structureSheafRing X)) (I : InjectiveResolution M)
    (J : InjectiveResolution ((SheafOfModules.toSheaf (structureSheafRing X)).obj M))
    (φ : ((SheafOfModules.toSheaf (structureSheafRing X)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj I.cocomplex ⟶ J.cocomplex)
    (hφ : (SheafOfModules.toSheaf (structureSheafRing X)).map (I.ι.f 0) ≫ φ.f 0 = J.ι.f 0) :
    let E := modulePushforward f
    let G := SheafOfModules.toSheaf (structureSheafRing Y)
    let A := (opensMap f).sheafPushforwardContinuous AddCommGrpCat.{u}
      (Opens.grothendieckTopology Y.carrier) (Opens.grothendieckTopology X.carrier)
    let K := (E.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    let L := (A.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex
    ∀ (c : G.obj (K.cycles n) ⟶ L.cycles n)
      (_ : c ≫ L.iCycles n = G.map (K.iCycles n) ≫ A.map (φ.f n)),
      G.map (K.homologyπ n ≫ (I.isoRightDerivedObj E n).inv) ≫
          (rightDerived_modulePushforward_forget_iso f n).hom.app M ≫
          (J.isoRightDerivedObj A n).hom =
        c ≫ L.homologyπ n := by
  cases n with
  | zero => exact rightDerived_modulePushforward_forget_iso_cocycles_zero f M I J φ hφ
  | succ m =>
      exact rightDerived_modulePushforward_forget_iso_cocycles_succ f m M I J φ
        (rightDerivedToSheafAbelianPushforwardIso_hom_app_eq f (m + 1) M I J φ hφ)

end PushforwardClause

end Stacks.Cohomology.ModulePushforwardComparison

end
