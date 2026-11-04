module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedCoheratorInclusionAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisPushforwardTag
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPushforwardEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSharpBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackUnitComp
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModuleExtensionByZeroExact
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjectiveLocalization
public import Mathlib.CategoryTheory.Monad.Adjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackId

/-!
# Restriction to an open subspace, on derived categories

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`. Restriction of
modules along étale morphisms, and along the inclusion of an open subspace, on derived categories,
as in the proof of [Stacks, Tag 09TG]:

* For a monomorphism `k : Y ⟶ X` which is étale — the inclusion of an open subspace — the counit
  `(k_* F)|_Y ⟶ F` of `(-)|_Y ⊣ k_*` is an isomorphism, by the base change isomorphism of
  Stacks 03LX for the cartesian square `Y = Y ×_X Y`.
* Hence the derived unit `E ⟶ Rk_*(E|_Y)` becomes invertible after restriction to `Y`.
* For an étale `g : T ⟶ Y`, the derived functor `R(g_* g^*)` vanishes at an object whose
  restriction to `T` vanishes: on a K-injective representative `I`, the restriction `I|_T` is
  K-injective and acyclic, hence zero in the homotopy category.

All names are in the namespace `AlgebraicGeometry.Space`.

## Main definitions

* `restrictThenPushUnit`: the comparison exhibiting `D(h^*) ⋙ Rh_*` as a right derived functor of
  `h_* ∘ h^*`, for an étale `h`.
* `pushThenPushUnit`: the comparison exhibiting `Rf_* ⋙ Rg_*` as a right derived functor of
  `f_* ⋙ g_*`.

## Main results

* `isIso_etaleModulePullbackAdjunction_counit_of_mono`: along an étale monomorphism `k : Y ⟶ X` the
  counit `(k_* F)|_Y ⟶ F` is an isomorphism.
* `isIso_mapDerivedCategory_map_derivedUnitOfNatTrans_of_mono`: the derived unit `E ⟶ Rk_*(E|_Y)`
  is invertible after restriction to `Y`.
* `isZero_derivedRestrictPush_of_isZero`: `R(g_* g^*)` vanishes at an object whose restriction
  vanishes, for an étale `g`.
* `isRightDerivedFunctor_restrictThenPushUnit`, `isRightDerivedFunctor_pushThenPushUnit`: the two
  comparisons exhibit right derived functors.

## References

* [Stacks Project, Tag 09TG](https://stacks.math.columbia.edu/tag/09TG)
* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
* [Stacks Project, Tag 08FI](https://stacks.math.columbia.edu/tag/08FI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.PushforwardMayerVietoris

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The counit along a monomorphism -/

section Mono

variable {X Y : AlgebraicSpaces B S hS} (k : Y ⟶ X) (hk : IsEtale B S hS k.hom)

include hk in
/-- **Along an étale monomorphism the counit `(k_* F)|_Y ⟶ F` is an isomorphism**, by the base
change isomorphism of Stacks 03LX for the cartesian square `Y = Y ×_X Y`. -/
theorem isIso_etaleModulePullbackAdjunction_counit_of_mono [Mono k] :
    IsIso (etaleModulePullbackAdjunction B S hS k hk).counit := by
  have sq : IsPullback (𝟙 Y) (𝟙 Y) k k := IsKernelPair.id_of_mono k
  exact Adjunction.isIso_counit_of_iso _
    ((modulePushforwardEtaleBaseChangeIso B S hS (𝟙 Y) (𝟙 Y) k k sq hk).symm ≪≫
      Functor.isoWhiskerLeft _ (modulePushforwardIdIso B S hS Y) ≪≫ Functor.rightUnitor _ ≪≫
      etaleModulePullbackIdIso B S hS _)

include hk in
/-- Along an étale monomorphism, restriction carries the unit `F ⟶ k_*(F|_Y)` to an isomorphism, by
the triangle identity. -/
theorem isIso_etaleModulePullback_map_unit_of_mono [Mono k]
    (F : Modules.{u, u} B S hS X.1 X.2) :
    IsIso ((etaleModulePullback.{u, u} B S hS k hk).map
      ((etaleModulePullbackAdjunction B S hS k hk).unit.app F)) := by
  have := isIso_etaleModulePullbackAdjunction_counit_of_mono B S hS k hk
  have h := (etaleModulePullbackAdjunction B S hS k hk).left_triangle_components F
  have : IsIso ((etaleModulePullback.{u, u} B S hS k hk).map
      ((etaleModulePullbackAdjunction B S hS k hk).unit.app F) ≫
      (etaleModulePullbackAdjunction B S hS k hk).counit.app
        ((etaleModulePullback.{u, u} B S hS k hk).obj F)) := by
    rw [h]; exact IsIso.id _
  exact IsIso.of_isIso_comp_right _
    ((etaleModulePullbackAdjunction B S hS k hk).counit.app
      ((etaleModulePullback.{u, u} B S hS k hk).obj F))

include hk in
/-- Along an étale monomorphism, restriction carries the degreewise unit of a complex to an
isomorphism of complexes. -/
theorem isIso_mapHomologicalComplex_map_unitCochainMap_of_mono [Mono k]
    (K : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ) :
    IsIso (((etaleModulePullback.{u, u} B S hS k hk).mapHomologicalComplex
      (ComplexShape.up ℤ)).map
        (unitCochainMap (etaleModulePullbackAdjunction B S hS k hk).unit K)) := by
  have : ∀ n, IsIso ((((etaleModulePullback.{u, u} B S hS k hk).mapHomologicalComplex
      (ComplexShape.up ℤ)).map
        (unitCochainMap (etaleModulePullbackAdjunction B S hS k hk).unit K)).f n) := fun n => by
    have e : (((etaleModulePullback.{u, u} B S hS k hk).mapHomologicalComplex
        (ComplexShape.up ℤ)).map
          (unitCochainMap (etaleModulePullbackAdjunction B S hS k hk).unit K)).f n =
        (etaleModulePullback.{u, u} B S hS k hk).map
          ((etaleModulePullbackAdjunction B S hS k hk).unit.app (K.X n)) := by
      simp only [Functor.mapHomologicalComplex_map_f, unitCochainMap_f]
    rw [e]
    exact isIso_etaleModulePullback_map_unit_of_mono B S hS k hk (K.X n)
  exact HomologicalComplex.Hom.isIso_of_components _

end Mono

/-! ### Derived statements -/

section Derived

variable {X Y : AlgebraicSpaces B S hS}

/-- Every object of `D(𝒪_X)` is the image of a K-injective complex. -/
lemma exists_isKInjective_iso (M : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) :
    ∃ (I : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ) (_ : I.IsKInjective),
      Nonempty (DerivedCategory.Q.obj I ≅ M) := by
  obtain ⟨I, s, hI, hs⟩ := exists_quasiIso_isKInjective_modules B S hS X.1 X.2
    (DerivedCategory.Q.objPreimage M)
  have : IsIso (DerivedCategory.Q.map s) :=
    Localization.inverts DerivedCategory.Q (HomologicalComplex.quasiIso _ _) s hs
  exact ⟨I, hI, ⟨(asIso (DerivedCategory.Q.map s)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso M⟩⟩

variable (k : Y ⟶ X) (hk : IsEtale B S hS k.hom)
  (R : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
    DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
  (α : (etaleModulePullback.{u, u} B S hS k hk ⋙ modulePushforward B S hS k).mapHomotopyCategory
    (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ R)
  [R.IsRightDerivedFunctor α
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))]

/-- **Along an étale monomorphism `k : Y ⟶ X`, the derived unit `E ⟶ Rk_*(E|_Y)` becomes invertible
after restriction to `Y`.** -/
theorem isIso_mapDerivedCategory_map_derivedUnitOfNatTrans_of_mono [Mono k]
    (M : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) :
    IsIso ((etaleModulePullback.{u, u} B S hS k hk).mapDerivedCategory.map
      ((derivedUnitOfNatTrans (etaleModulePullbackAdjunction B S hS k hk).unit R α).app M)) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := exists_isKInjective_iso B S hS M
  have h := derivedUnitOfNatTrans_app_eq (etaleModulePullbackAdjunction B S hS k hk).unit R α e
  have hα := isIso_rightDerivedComparison_app_of_isKInjective
    (exists_quasiIso_isKInjective_modules B S hS X.1 X.2) _ R α inferInstance I hI
  have hcmp : IsIso ((rightDerivedCochainComparison _ R α).app I) := by
    rw [← rightDerivedCochainComparisonIso_hom _ R α I hα]; infer_instance
  have hφ := isIso_mapHomologicalComplex_map_unitCochainMap_of_mono B S hS k hk I
  have hQ : IsIso ((etaleModulePullback.{u, u} B S hS k hk).mapDerivedCategory.map
      (DerivedCategory.Q.map
        (unitCochainMap (etaleModulePullbackAdjunction B S hS k hk).unit I))) := by
    have := (NatIso.isIso_map_iff
      (etaleModulePullback.{u, u} B S hS k hk).mapDerivedCategoryFactors
      (unitCochainMap (etaleModulePullbackAdjunction B S hS k hk).unit I)).2
      (by simp only [Functor.comp_map]; infer_instance)
    simpa only [Functor.comp_map] using this
  have hu : (derivedUnitOfNatTrans (etaleModulePullbackAdjunction B S hS k hk).unit R α).app M =
      e.inv ≫ DerivedCategory.Q.map
        (unitCochainMap (etaleModulePullbackAdjunction B S hS k hk).unit I) ≫
        (rightDerivedCochainComparison _ R α).app I ≫ R.map e.hom := by
    rw [← h, Iso.inv_hom_id_assoc]
  rw [hu]
  simp only [Functor.map_comp]
  infer_instance

omit [R.IsRightDerivedFunctor α
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))] in
include hk in
/-- **`R(g_* g^*)` vanishes at an object whose restriction vanishes**, for an étale `g`; the
restriction of a K-injective complex is K-injective (Stacks 08FI). -/
theorem isZero_derivedRestrictPush_of_isZero
    (R' : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (α' : (etaleModulePullback.{u, u} B S hS k hk ⋙ modulePushforward B S hS k).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ R')
    (hR' : R'.IsRightDerivedFunctor α'
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)))
    (N : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hN : IsZero ((etaleModulePullback.{u, u} B S hS k hk).mapDerivedCategory.obj N)) :
    IsZero (R'.obj N) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := exists_isKInjective_iso B S hS N
  have hα := isIso_rightDerivedComparison_app_of_isKInjective
    (exists_quasiIso_isKInjective_modules B S hS X.1 X.2) _ R' α' hR' I hI
  let J := ((etaleModulePullback.{u, u} B S hS k hk).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj I
  have hJ : CochainComplex.IsKInjective J :=
    isKInjective_etaleModulePullback B S hS k hk (etaleModuleLowerShriekAdjunction B S hS k hk) I hI
  have hQJ : IsZero (DerivedCategory.Q.obj J) :=
    hN.of_iso ((etaleModulePullback.{u, u} B S hS k hk).mapDerivedCategoryFactors.symm.app I ≪≫
      (etaleModulePullback.{u, u} B S hS k hk).mapDerivedCategory.mapIso e)
  have hKJ : IsZero ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj J) := by
    rw [IsZero.iff_id_eq_zero]
    apply (CochainComplex.IsKInjective.Qh_map_bijective _ J).1
    have hQh : IsZero (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj J)) :=
      hQJ.of_iso ((DerivedCategory.quotientCompQhIso _).app J)
    exact hQh.eq_of_src _ _
  have hK : IsZero ((modulePushforward B S hS k).mapHomotopyCategory (ComplexShape.up ℤ) |>.obj
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj J)) :=
    Functor.map_isZero _ hKJ
  have hR : IsZero (R'.obj (DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) :=
    (Functor.map_isZero DerivedCategory.Qh hK).of_iso
      (asIso (α'.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))).symm
  exact hR.of_iso (R'.mapIso ((DerivedCategory.quotientCompQhIso _).app I ≪≫ e)).symm

end Derived

/-! ### Identifying derived direct images -/

section Identify

variable {X Y Z : AlgebraicSpaces B S hS}

/-- The comparison exhibiting `D(h^*) ⋙ Rh_*` as a right derived functor of `h_* ∘ h^*`. -/
def restrictThenPushUnit (h : Y ⟶ X) (hh : IsEtale B S hS h.hom)
    (Rh : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (βh : (modulePushforward B S hS h).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rh) :
    (etaleModulePullback.{u, u} B S hS h hh ⋙ modulePushforward B S hS h).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ (etaleModulePullback.{u, u} B S hS h hh).mapDerivedCategory ⋙ Rh :=
  (Functor.isoWhiskerRight (Functor.mapHomotopyCategoryCompIso (Iso.refl _)
      (ComplexShape.up ℤ)).symm DerivedCategory.Qh ≪≫ Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ βh ≫
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (etaleModulePullback.{u, u} B S hS h hh).mapDerivedCategoryFactorsh.symm
        Rh ≪≫ Functor.associator _ _ _).hom

/-- The component of `restrictThenPushUnit` at `K`: `βh` at the restriction of `K`, between the two
identifications of functors. -/
lemma restrictThenPushUnit_app (h : Y ⟶ X) (hh : IsEtale B S hS h.hom)
    (Rh : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (βh : (modulePushforward B S hS h).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rh)
    (K : HomotopyCategory (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)) :
    (restrictThenPushUnit B S hS h hh Rh βh).app K =
      (Functor.isoWhiskerRight (Functor.mapHomotopyCategoryCompIso (Iso.refl _)
        (ComplexShape.up ℤ)).symm DerivedCategory.Qh ≪≫ Functor.associator _ _ _).hom.app K ≫
        βh.app ((etaleModulePullback.{u, u} B S hS h hh).mapHomotopyCategory
          (ComplexShape.up ℤ) |>.obj K) ≫
        ((Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight
            (etaleModulePullback.{u, u} B S hS h hh).mapDerivedCategoryFactorsh.symm Rh ≪≫
          Functor.associator _ _ _).hom.app K := by
  simp [restrictThenPushUnit]

/-- `D(h^*) ⋙ Rh_*` is a right derived functor of `h_* ∘ h^*`: restriction preserves K-injective
complexes (Stacks 08FI). -/
lemma isRightDerivedFunctor_restrictThenPushUnit (h : Y ⟶ X) (hh : IsEtale B S hS h.hom)
    (Rh : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (βh : (modulePushforward B S hS h).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rh)
    [Rh.IsRightDerivedFunctor βh
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ))] :
    ((etaleModulePullback.{u, u} B S hS h hh).mapDerivedCategory ⋙ Rh).IsRightDerivedFunctor
      (restrictThenPushUnit B S hS h hh Rh βh)
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)) :=
  Stacks.Cohomology.Localization.rightDerived_of_kInjectives _ _ _ fun I hI => by
    have hJ : CochainComplex.IsKInjective
        (((etaleModulePullback.{u, u} B S hS h hh).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I) :=
      isKInjective_etaleModulePullback B S hS h hh
        (etaleModuleLowerShriekAdjunction B S hS h hh) I hI
    have := Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective _ Rh βh
      (((etaleModulePullback.{u, u} B S hS h hh).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
    rw [restrictThenPushUnit_app]
    exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' this inferInstance)

/-- The comparison exhibiting `Rf_* ⋙ Rg_*` as a right derived functor of `f_* ⋙ g_*`. -/
def pushThenPushUnit (f : Z ⟶ Y) (g : Y ⟶ X)
    (Rf : DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (βf : (modulePushforward B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rf)
    (Rg : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (βg : (modulePushforward B S hS g).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rg) :
    (modulePushforward B S hS f ⋙ modulePushforward B S hS g).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rf ⋙ Rg :=
  (Functor.isoWhiskerRight (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (modulePushforward B S hS f ⋙ modulePushforward B S hS g))
      (ComplexShape.up ℤ)).symm DerivedCategory.Qh ≪≫
    Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ βg ≫ (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight βf Rg ≫ (Functor.associator _ _ _).hom

/-- The component of `pushThenPushUnit` at `K`: `βg` at `f_* K` followed by `Rg_*` applied to `βf`
at `K`, after the identification of functors. -/
lemma pushThenPushUnit_app (f : Z ⟶ Y) (g : Y ⟶ X)
    (Rf : DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (βf : (modulePushforward B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rf)
    (Rg : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (βg : (modulePushforward B S hS g).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rg)
    (K : HomotopyCategory (Modules.{u, u} B S hS Z.1 Z.2) (ComplexShape.up ℤ)) :
    (pushThenPushUnit B S hS f g Rf βf Rg βg).app K =
      (Functor.isoWhiskerRight (Functor.mapHomotopyCategoryCompIso
        (Iso.refl (modulePushforward B S hS f ⋙ modulePushforward B S hS g))
        (ComplexShape.up ℤ)).symm DerivedCategory.Qh ≪≫
        Functor.associator _ _ _).hom.app K ≫
        βg.app ((modulePushforward B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) |>.obj K) ≫
        Rg.map (βf.app K) := by
  simp [pushThenPushUnit]

/-- `Rf_* ⋙ Rg_*` is a right derived functor of `f_* ⋙ g_*`: the direct image preserves K-injective
complexes, being right adjoint to an exact functor. -/
lemma isRightDerivedFunctor_pushThenPushUnit (f : Z ⟶ Y) (hf : IsEtale B S hS f.hom) (g : Y ⟶ X)
    (Rf : DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (βf : (modulePushforward B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rf)
    [Rf.IsRightDerivedFunctor βf
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Z.1 Z.2) (ComplexShape.up ℤ))]
    (Rg : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (βg : (modulePushforward B S hS g).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rg)
    [Rg.IsRightDerivedFunctor βg
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ))] :
    (Rf ⋙ Rg).IsRightDerivedFunctor (pushThenPushUnit B S hS f g Rf βf Rg βg)
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Z.1 Z.2) (ComplexShape.up ℤ)) :=
  Stacks.Cohomology.Localization.rightDerived_of_kInjectives _ _ _ fun I hI => by
    have hJ : CochainComplex.IsKInjective
        (((modulePushforward B S hS f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
      CochainComplex.isKInjective_mapHomologicalComplex_of_exact _ _
        (etaleModulePullbackAdjunction B S hS f hf) I
    have h₁ := Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective _ Rg βg
      (((modulePushforward B S hS f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
    have h₂ := Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective _ Rf βf I
    rw [pushThenPushUnit_app]
    exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' h₁ inferInstance)

end Identify

end AlgebraicGeometry.Space

end
