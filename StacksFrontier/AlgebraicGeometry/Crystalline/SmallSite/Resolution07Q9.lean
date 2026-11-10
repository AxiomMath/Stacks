module

public import StacksFrontier.Algebra.Homology.DerivedCategory.InjectiveResolutionDerived
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Comparison07Q9
public import StacksFrontier.Homology.DerivedIndexing.SingleDegreeUnit
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.DerivedGlobalSectionsMap

/-!
# The comparison map of [Stacks, Tag 07Q9] on injective resolutions

The first arrow `Ru_{X/S, *}ℱ ⟶ Rf_{Zar, *}Ru_{X'/S, *}ℱ'` of the triangle of [Stacks, Tag 07Q9]
is `...SmallSite.moduleComparison07Q9`.  The proof of [Stacks, Tag 07Q9] computes it on injective
resolutions: for `J^•` an injective resolution of `ℱ`, `J'^•` one of `ℱ' = f_cris^*ℱ` and
`ψ : J^• ⟶ f_{cris, *}J'^•` a lift of the unit `ℱ ⟶ f_{cris, *}ℱ'`, the arrow is
`u_{X/S, *}ψ : u_{X/S, *}J^• ⟶ u_{X/S, *}f_{cris, *}J'^•` up to isomorphism.

* `Stacks.Cohomology.singleRightDerivedUnit_app_eq`: the canonical map `Φ(N)[0] ⟶ RΦ(N[0])` is the
  class of `Φ` of the augmentation of any injective resolution of `N`.
* `CategoryTheory.InjectiveResolution.liftToComplex`: a lift of a morphism into the degree-zero
  term of a complex of injectives to a chain map out of an injective resolution.
* `Stacks.Cohomology.singleUnitArrowIso` and `Stacks.Cohomology.rightDerivedQArrowIso`: the two
  generic steps, for an arbitrary additive functor.
* `...SmallSite.derivedModuleCrisUnit`, `...SmallSite.moduleComparison07Q9_eq`,
  `...SmallSite.derivedModuleCrisUnit_eq`: the first arrow of [Stacks, Tag 07Q9] is
  `Ru_{X/S, *}` of the derived unit `ℱ[0] ⟶ Rf_{cris, *}ℱ'[0]`, followed by the derived square.
* `...SmallSite.moduleCrisUnitArrowIso`: `Ru_{X/S, *}` of the derived unit is isomorphic, as an
  arrow of `D(Ab(X_Zar))`, to the class of `u_{X/S, *}ψ`; `...SmallSite.crisResolutionMap` is a
  choice of `ψ`.

## References

* [Stacks Project, Lemma 60.26.3, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
* [Stacks Project, Tag 05TN](https://stacks.math.columbia.edu/tag/05TN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w w' u

noncomputable section

namespace Stacks.Cohomology

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]
  (Φ : A ⥤ B) [Φ.Additive]

/-- The canonical map `Φ(N)[0] ⟶ Φ(J'^•)` in `D⁺(ℬ)` attached to an injective resolution `J'` of
`N`: the class of `Φ` applied to the augmentation `N[0] ⟶ J'^•`, precomposed with the
identification `(ΦN)[0] ≅ Φ(N[0])` of `HomologicalComplex.singleMapHomologicalComplex`. -/
def singleToMapResolution {N : A} (J' : InjectiveResolution N) :
    (DerivedCategory.Plus.singleFunctor B 0).obj (Φ.obj N) ⟶
      DerivedCategory.Plus.Q.obj (Φ.mapCochainComplexPlus.obj J'.plusObj) :=
  ObjectProperty.homMk (DerivedCategory.Q.map
    ((HomologicalComplex.singleMapHomologicalComplex Φ (ComplexShape.up ℤ) 0).inv.app N ≫
      (Φ.mapHomologicalComplex _).map J'.ι'))

variable [EnoughInjectives A]

/-- The identification `Φ(J'^•) ≅ RΦ(N[0])` in `D⁺(ℬ)` for an injective resolution `J'` of `N`: the
two descriptions of the class of a bounded below complex (`DerivedCategory.Plus.qhQIso`), followed
by the comparison `CategoryTheory.InjectiveResolution.toRightDerivedPlus`. -/
def mapResolutionIsoRightDerived {N : A} (J' : InjectiveResolution N) :
    DerivedCategory.Plus.Q.obj (Φ.mapCochainComplexPlus.obj J'.plusObj) ≅
      Φ.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj N) :=
  (DerivedCategory.Plus.qhQIso _).symm ≪≫
    @asIso _ _ _ _ (J'.toRightDerivedPlus Φ) (InjectiveResolution.isIso_toRightDerivedPlus Φ J')

/-- **The canonical map `Φ(N)[0] ⟶ RΦ(N[0])` computed on an injective resolution.**  For any
injective resolution `J'` of `N`, the component of `Stacks.Cohomology.singleRightDerivedUnit` at
`N` is the class `Φ(N)[0] ⟶ Φ(J'^•)` of `Φ` of the augmentation, followed by the identification
`Φ(J'^•) ≅ RΦ(N[0])`.  This is the naturality of the unit of `RΦ` along the augmentation
`N[0] ⟶ J'^•`. -/
theorem singleRightDerivedUnit_app_eq {N : A} (J' : InjectiveResolution N) :
    (singleRightDerivedUnit Φ).app N =
      singleToMapResolution Φ J' ≫ (mapResolutionIsoRightDerived Φ J').hom := by
  let a : (HomotopyCategory.Plus.singleFunctor A 0).obj N ⟶
      (HomotopyCategory.Plus.quotient A).obj J'.plusObj :=
    ObjectProperty.homMk ((HomotopyCategory.quotient _ _).map J'.ι')
  have hn := Φ.rightDerivedFunctorPlusUnith.naturality a
  have h₁ : (Functor.mapSingleFunctorCompQhIso Φ).inv.app N ≫
      DerivedCategory.Plus.Qh.map (Φ.mapHomotopyCategoryPlus.map a) =
      singleToMapResolution Φ J' ≫ (DerivedCategory.Plus.qhQIso _).inv := by
    have e₁ : ((Functor.mapSingleFunctorCompQhIso Φ).inv.app N).hom = _ :=
      Stacks.DerivedIndexing.ι_map_mapSingleFunctorCompQhIso_inv_app Φ N
    apply ObjectProperty.hom_ext
    rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom, e₁,
      Stacks.DerivedIndexing.singleFunctorIsoCompQh_hom_app]
    have e₂ : (DerivedCategory.Plus.Qh.map (Φ.mapHomotopyCategoryPlus.map a)).hom =
        DerivedCategory.Qh.map ((HomotopyCategory.quotient B _).map
          ((Φ.mapHomologicalComplex _).map J'.ι')) :=
      congrArg DerivedCategory.Qh.map (Φ.mapHomotopyCategory_map J'.ι')
    have e₃ : (DerivedCategory.Plus.qhQIso (Φ.mapCochainComplexPlus.obj J'.plusObj)).inv.hom =
        (DerivedCategory.quotientCompQhIso B).inv.app _ := rfl
    rw [e₂, e₃]
    refine Eq.trans ?_ (DerivedCategory.quotientCompQhIso_inv_naturality
      ((HomologicalComplex.singleMapHomologicalComplex Φ (ComplexShape.up ℤ) 0).inv.app N ≫
        (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).map J'.ι')).symm
    rw [Functor.map_comp, Functor.map_comp]
    exact Category.assoc _ _ _
  have h₂ : (Functor.singleFunctorPlusIsoCompQh (A := A) 0).inv.app N ≫ J'.plusQIso.hom =
      DerivedCategory.Plus.Qh.map a ≫ (DerivedCategory.Plus.qhQIso J'.plusObj).hom := by
    have e₁ : ((Functor.singleFunctorPlusIsoCompQh (A := A) 0).inv.app N).hom = _ :=
      Stacks.DerivedIndexing.ι_map_singleFunctorPlusIsoCompQh_inv_app N
    apply ObjectProperty.hom_ext
    rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom, e₁]
    have e₀ : (DerivedCategory.singleFunctorIsoCompQh A 0).inv.app N =
        (DerivedCategory.quotientCompQhIso A).hom.app _ :=
      Iso.inv_ext (f := (DerivedCategory.singleFunctorIsoCompQh A 0).app N) (by
        change (DerivedCategory.singleFunctorIsoCompQh A 0).hom.app N ≫ _ = _
        rw [Stacks.DerivedIndexing.singleFunctorIsoCompQh_hom_app]
        exact Iso.inv_hom_id_app _ _)
    rw [e₀]
    exact (DerivedCategory.quotientCompQhIso_hom_naturality J'.ι').symm
  have hn' : DerivedCategory.Plus.Qh.map (Φ.mapHomotopyCategoryPlus.map a) ≫
      Φ.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient A).obj J'.plusObj) =
    Φ.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.singleFunctor A 0).obj N) ≫
      Φ.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map a) := hn
  have h₂' : (Functor.singleFunctorPlusIsoCompQh (A := A) 0).inv.app N =
      DerivedCategory.Plus.Qh.map a ≫ (DerivedCategory.Plus.qhQIso J'.plusObj).hom ≫
        J'.plusQIso.inv := by
    rw [← Category.assoc, ← h₂, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [singleRightDerivedUnit_app, Iso.app_inv]
  calc _ = (Functor.mapSingleFunctorCompQhIso Φ).inv.app N ≫
        (Φ.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.singleFunctor A 0).obj N) ≫
          Φ.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map a)) ≫
        Φ.rightDerivedFunctorPlus.map (DerivedCategory.Plus.qhQIso J'.plusObj).hom ≫
        Φ.rightDerivedFunctorPlus.map J'.plusQIso.inv := by
        rw [h₂', Functor.map_comp, Functor.map_comp]
        simp only [Category.assoc]
    _ = ((Functor.mapSingleFunctorCompQhIso Φ).inv.app N ≫
        DerivedCategory.Plus.Qh.map (Φ.mapHomotopyCategoryPlus.map a)) ≫
        Φ.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient A).obj J'.plusObj) ≫
        Φ.rightDerivedFunctorPlus.map (DerivedCategory.Plus.qhQIso J'.plusObj).hom ≫
        Φ.rightDerivedFunctorPlus.map J'.plusQIso.inv := by
        rw [← hn']
        simp only [Category.assoc]
    _ = _ := by
        rw [h₁]
        exact Category.assoc _ _ _

/-- A cochain complex indexed by `ℕ`, extended by zero to `ℤ`, as a bounded below complex. -/
abbrev extendPlusObj (K : CochainComplex B ℕ) : CochainComplex.Plus B :=
  ⟨K.extend ComplexShape.embeddingUpNat, 0, inferInstance⟩

omit [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A] in
/-- The extension by zero to `ℤ` of a complex of injective objects indexed by `ℕ` has injective
terms. -/
lemma injective_extend_X (K : CochainComplex B ℕ) [∀ n, Injective (K.X n)] (n : ℤ) :
    Injective ((K.extend ComplexShape.embeddingUpNat).X n) := by
  by_cases hn : 0 ≤ n
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    exact Injective.of_iso (K.extendXIso ComplexShape.embeddingUpNat rfl).symm inferInstance
  · exact IsZero.injective (K.isZero_extend_X _ _ (fun i hi => hn (by
      rw [← hi]
      exact Int.natCast_nonneg i)))

/-- The extension by zero to `ℤ` of a chain map out of an injective resolution, with source the
`ℤ`-indexed complex `CategoryTheory.InjectiveResolution.cochainComplex` of the resolution. -/
def extendResolutionMap {M : B} (J : InjectiveResolution M) {K : CochainComplex B ℕ}
    (ψ : J.cocomplex ⟶ K) : J.cochainComplex ⟶ K.extend ComplexShape.embeddingUpNat :=
  HomologicalComplex.extendMap ψ ComplexShape.embeddingUpNat

omit [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A] in
/-- The degree-zero component of `extendResolutionMap`. -/
lemma extendResolutionMap_f_zero {M : B} (J : InjectiveResolution M) {K : CochainComplex B ℕ}
    (ψ : J.cocomplex ⟶ K) :
    (extendResolutionMap J ψ).f 0 = (J.cochainComplexXIso 0 0 rfl).hom ≫ ψ.f 0 ≫
      (K.extendXIso ComplexShape.embeddingUpNat
        (show ComplexShape.embeddingUpNat.f 0 = (0 : ℤ) from rfl)).inv :=
  HomologicalComplex.extendMap_f _ _ rfl

/-- Applying `Φ` termwise commutes with extension by zero from `ℕ` to `ℤ`, at an injective
resolution. -/
def mapCochainComplexIso {N : A} (J' : InjectiveResolution N) :
    (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj J'.cochainComplex ≅
      ((Φ.mapHomologicalComplex _).obj J'.cocomplex).extend ComplexShape.embeddingUpNat :=
  (Stacks.DerivedIndexing.mapExtendIso Φ ComplexShape.embeddingUpNat J'.cocomplex).symm

omit [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A] in
/-- The degree-zero component of `mapCochainComplexIso`. -/
lemma mapCochainComplexIso_hom_f_zero {N : A} (J' : InjectiveResolution N) :
    (mapCochainComplexIso Φ J').hom.f 0 = Φ.map (J'.cochainComplexXIso 0 0 rfl).hom ≫
      (((Φ.mapHomologicalComplex _).obj J'.cocomplex).extendXIso
        ComplexShape.embeddingUpNat
        (show ComplexShape.embeddingUpNat.f 0 = (0 : ℤ) from rfl)).inv :=
  Stacks.DerivedIndexing.mapExtendIso_inv_f_eq _ _ _ rfl

omit [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A] in
/-- A chain map `ψ : J^• ⟶ Φ(J'^•)` which in degree zero is compatible with `u : M ⟶ Φ(N)` and the
augmentations composes with the augmentation `M[0] ⟶ J^•` to `u[0]` followed by `Φ` of the
augmentation `N[0] ⟶ J'^•`, as maps of `ℤ`-indexed complexes. -/
lemma ι'_comp_extendMap {M : B} {N : A} (u : M ⟶ Φ.obj N) (J : InjectiveResolution M)
    (J' : InjectiveResolution N)
    (ψ : J.cocomplex ⟶ (Φ.mapHomologicalComplex _).obj J'.cocomplex)
    (hψ : J.ι.f 0 ≫ ψ.f 0 = (HomologicalComplex.singleObjXSelf _ 0 M).hom ≫ u ≫
      Φ.map ((HomologicalComplex.singleObjXSelf _ 0 N).inv ≫ J'.ι.f 0)) :
    J.ι' ≫ extendResolutionMap J ψ =
      (CochainComplex.singleFunctor B 0).map u ≫
        (HomologicalComplex.singleMapHomologicalComplex Φ (ComplexShape.up ℤ) 0).inv.app N ≫
        (Φ.mapHomologicalComplex _).map J'.ι' ≫
        (mapCochainComplexIso Φ J').hom := by
  have kM : J.ι'.f 0 = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).hom ≫
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 M).inv ≫ J.ι.f 0) ≫
        (J.cochainComplexXIso 0 0 rfl).inv := by
    rw [show (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 M).inv ≫ J.ι.f 0 =
      J.ι.f 0 from Category.id_comp _]
    exact J.ι'_f_zero
  have kN : J'.ι'.f 0 = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 N).hom ≫
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 N).inv ≫ J'.ι.f 0) ≫
        (J'.cochainComplexXIso 0 0 rfl).inv := by
    rw [show (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 N).inv ≫ J'.ι.f 0 =
      J'.ι.f 0 from Category.id_comp _]
    exact J'.ι'_f_zero
  have hψ' : ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 M).inv ≫ J.ι.f 0) ≫
      ψ.f 0 = u ≫ Φ.map ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 N).inv ≫
        J'.ι.f 0) := by
    rw [Category.assoc, hψ, Iso.inv_hom_id_assoc]
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f, extendResolutionMap_f_zero,
    kM, mapCochainComplexIso_hom_f_zero, kN,
    show ((CochainComplex.singleFunctor B 0).map u).f 0 = _ from
      HomologicalComplex.single_map_f_self (ComplexShape.up ℤ) 0 u,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc _ (ψ.f 0), hψ']
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id_map_assoc]

/-- A chain map `ψ : J^• ⟶ Φ(J'^•)`, extended by zero to `ℤ`, as a morphism of bounded below
complexes. -/
def resolutionHomPlus {M : B} {N : A} (J : InjectiveResolution M) (J' : InjectiveResolution N)
    (ψ : J.cocomplex ⟶ (Φ.mapHomologicalComplex _).obj J'.cocomplex) :
    J.plusObj ⟶ extendPlusObj ((Φ.mapHomologicalComplex _).obj J'.cocomplex) :=
  ObjectProperty.homMk (extendResolutionMap J ψ)

/-- **The arrow `M[0] ⟶ RΦ(N[0])` induced by `u : M ⟶ Φ(N)` is the class of a lift of `u` to
injective resolutions.**  Given injective resolutions `J` of `M` and `J'` of `N` and a chain map
`ψ : J^• ⟶ Φ(J'^•)` lifting `u` in degree zero (`hψ`), the composite of `u[0]` with the canonical
map `Φ(N)[0] ⟶ RΦ(N[0])` is isomorphic, as an arrow of `D⁺(ℬ)`, to the class of `ψ`.  The
vertical isomorphisms are `CategoryTheory.InjectiveResolution.plusQIso` and
`mapResolutionIsoRightDerived`. -/
def singleUnitArrowIso {M : B} {N : A} (u : M ⟶ Φ.obj N) (J : InjectiveResolution M)
    (J' : InjectiveResolution N)
    (ψ : J.cocomplex ⟶ (Φ.mapHomologicalComplex _).obj J'.cocomplex)
    (hψ : J.ι.f 0 ≫ ψ.f 0 = (HomologicalComplex.singleObjXSelf _ 0 M).hom ≫ u ≫
      Φ.map ((HomologicalComplex.singleObjXSelf _ 0 N).inv ≫ J'.ι.f 0)) :
    Arrow.mk ((DerivedCategory.Plus.singleFunctor B 0).map u ≫
        (singleRightDerivedUnit Φ).app N) ≅
      Arrow.mk (DerivedCategory.Plus.Q.map (resolutionHomPlus Φ J J' ψ)) :=
  Arrow.isoMk J.plusQIso ((mapResolutionIsoRightDerived Φ J').symm ≪≫
    DerivedCategory.Plus.Q.mapIso (ObjectProperty.isoMk _ (mapCochainComplexIso Φ J'))) (by
      dsimp
      rw [singleRightDerivedUnit_app_eq Φ J', Category.assoc, Category.assoc,
        Iso.hom_inv_id_assoc]
      have key : DerivedCategory.Q.map J.ι' ≫ DerivedCategory.Q.map (extendResolutionMap J ψ) =
          DerivedCategory.Q.map ((CochainComplex.singleFunctor B 0).map u) ≫
            DerivedCategory.Q.map
              ((HomologicalComplex.singleMapHomologicalComplex Φ (ComplexShape.up ℤ) 0).inv.app N ≫
                (Φ.mapHomologicalComplex _).map J'.ι') ≫
            DerivedCategory.Q.map (mapCochainComplexIso Φ J').hom := by
        rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
          ι'_comp_extendMap Φ u J J' ψ hψ, Category.assoc]
      exact ObjectProperty.hom_ext _ key)

section Injective

variable {Z : Type*} [Category* Z] [Abelian Z] [HasDerivedCategory Z]
  (U : B ⥤ Z) [U.Additive] [EnoughInjectives B]

/-- The class of `U(K)` for a bounded below complex `K`, computed either through the bounded below
homotopy category or directly. -/
def mapQhQIso (K : CochainComplex.Plus B) :
    DerivedCategory.Plus.Qh.obj (U.mapHomotopyCategoryPlus.obj
        ((HomotopyCategory.Plus.quotient B).obj K)) ≅
      DerivedCategory.Plus.Q.obj (U.mapCochainComplexPlus.obj K) :=
  DerivedCategory.Plus.qhQIso (U.mapCochainComplexPlus.obj K)

omit [EnoughInjectives B] [HasDerivedCategory B] in
/-- `mapQhQIso` is natural in the complex. -/
lemma mapQhQIso_naturality {K L : CochainComplex.Plus B} (f : K ⟶ L) :
    DerivedCategory.Plus.Qh.map (U.mapHomotopyCategoryPlus.map
        ((HomotopyCategory.Plus.quotient B).map f)) ≫ (mapQhQIso U L).hom =
      (mapQhQIso U K).hom ≫ DerivedCategory.Plus.Q.map (U.mapCochainComplexPlus.map f) := by
  have e : U.mapHomotopyCategoryPlus.map ((HomotopyCategory.Plus.quotient B).map f) =
      (HomotopyCategory.Plus.quotient Z).map (U.mapCochainComplexPlus.map f) :=
    ObjectProperty.hom_ext _ (U.mapHomotopyCategory_map f.hom)
  rw [e]
  exact DerivedCategory.Plus.qhQIso_naturality (U.mapCochainComplexPlus.map f)

/-- **`RU` computed on a bounded below complex of injectives**: `RU(K) ≅ U(K)` in `D⁺`, through the
unit of `RU`, which is invertible at a complex of injective objects. -/
def rightDerivedQIso (K : CochainComplex.Plus B) [∀ n, Injective (K.obj.X n)] :
    U.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K) ≅
      DerivedCategory.Plus.Q.obj (U.mapCochainComplexPlus.obj K) :=
  U.rightDerivedFunctorPlus.mapIso (DerivedCategory.Plus.qhQIso K).symm ≪≫
    (asIso (U.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient B).obj K))).symm ≪≫
    mapQhQIso U K

/-- The components of `rightDerivedQIso`, written out. -/
lemma rightDerivedQIso_hom (K : CochainComplex.Plus B) [∀ n, Injective (K.obj.X n)] :
    (rightDerivedQIso U K).hom =
      U.rightDerivedFunctorPlus.map (DerivedCategory.Plus.qhQIso K).inv ≫
        CategoryTheory.inv (U.rightDerivedFunctorPlusUnith.app
          ((HomotopyCategory.Plus.quotient B).obj K)) ≫ (mapQhQIso U K).hom :=
  rfl

/-- `rightDerivedQIso` is natural in morphisms between bounded below complexes of injectives. -/
lemma rightDerivedQIso_naturality {K L : CochainComplex.Plus B} [∀ n, Injective (K.obj.X n)]
    [∀ n, Injective (L.obj.X n)] (f : K ⟶ L) :
    U.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f) ≫
        (rightDerivedQIso U L).hom =
      (rightDerivedQIso U K).hom ≫ DerivedCategory.Plus.Q.map (U.mapCochainComplexPlus.map f) := by
  have h₁ := DerivedCategory.Plus.qhQIso_naturality f
  have hn := U.rightDerivedFunctorPlusUnith.naturality ((HomotopyCategory.Plus.quotient B).map f)
  have hn' : DerivedCategory.Plus.Qh.map (U.mapHomotopyCategoryPlus.map
        ((HomotopyCategory.Plus.quotient B).map f)) ≫
        U.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient B).obj L) =
      U.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient B).obj K) ≫
        U.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map
          ((HomotopyCategory.Plus.quotient B).map f)) := hn
  have hn'' : CategoryTheory.inv (U.rightDerivedFunctorPlusUnith.app
        ((HomotopyCategory.Plus.quotient B).obj K)) ≫
      DerivedCategory.Plus.Qh.map (U.mapHomotopyCategoryPlus.map
        ((HomotopyCategory.Plus.quotient B).map f)) =
      U.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map
          ((HomotopyCategory.Plus.quotient B).map f)) ≫
        CategoryTheory.inv (U.rightDerivedFunctorPlusUnith.app
          ((HomotopyCategory.Plus.quotient B).obj L)) :=
    (IsIso.inv_comp_eq (U.rightDerivedFunctorPlusUnith.app
        ((HomotopyCategory.Plus.quotient B).obj K))).2
      (((IsIso.eq_comp_inv (U.rightDerivedFunctorPlusUnith.app
        ((HomotopyCategory.Plus.quotient B).obj L))).2 hn').trans (Category.assoc _ _ _))
  have h₁' : U.rightDerivedFunctorPlus.map (DerivedCategory.Plus.qhQIso K).inv ≫
      U.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map
          ((HomotopyCategory.Plus.quotient B).map f)) =
      U.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f) ≫
        U.rightDerivedFunctorPlus.map (DerivedCategory.Plus.qhQIso L).inv := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg U.rightDerivedFunctorPlus.map
      ((Iso.inv_comp_eq _).2 (((Iso.eq_comp_inv _).2 h₁).trans (Category.assoc _ _ _)))
  rw [rightDerivedQIso_hom, rightDerivedQIso_hom, ← reassoc_of% h₁', ← reassoc_of% hn'',
    mapQhQIso_naturality]
  simp only [Category.assoc]

/-- **`RU` of the class of a map of bounded below complexes of injectives is the class of `U` of
it**, as an isomorphism of arrows. -/
def rightDerivedQArrowIso {K L : CochainComplex.Plus B} [∀ n, Injective (K.obj.X n)]
    [∀ n, Injective (L.obj.X n)] (f : K ⟶ L) :
    Arrow.mk (U.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f)) ≅
      Arrow.mk (DerivedCategory.Plus.Q.map (U.mapCochainComplexPlus.map f)) :=
  Arrow.isoMk (rightDerivedQIso U K) (rightDerivedQIso U L)
    (rightDerivedQIso_naturality U f).symm

end Injective

section Extend

variable {Z : Type*} [Category* Z] [Abelian Z] [HasDerivedCategory Z] (U : B ⥤ Z) [U.Additive]

omit [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory Z] in
/-- Extension by zero from `ℕ` to `ℤ` commutes with applying `U` termwise, naturally in the
chain map. -/
lemma map_extendMap_comp_mapExtendIso_inv {K L : CochainComplex B ℕ} (ψ : K ⟶ L) :
    (U.mapHomologicalComplex _).map (HomologicalComplex.extendMap ψ ComplexShape.embeddingUpNat) ≫
        (Stacks.DerivedIndexing.mapExtendIso U ComplexShape.embeddingUpNat L).inv =
      (Stacks.DerivedIndexing.mapExtendIso U ComplexShape.embeddingUpNat K).inv ≫
        HomologicalComplex.extendMap ((U.mapHomologicalComplex _).map ψ)
          ComplexShape.embeddingUpNat :=
  (Stacks.DerivedIndexing.mapExtendNatIso U ComplexShape.embeddingUpNat).inv.naturality ψ

omit [HasDerivedCategory A] [HasDerivedCategory B] in
/-- The class of `U` applied to the extension of a chain map is isomorphic, as an arrow, to the
class of the extension of `U` applied to it. -/
def mapExtendArrowIso {K L : CochainComplex B ℕ} (ψ : K ⟶ L) :
    Arrow.mk (DerivedCategory.Q.map ((U.mapHomologicalComplex _).map
        (HomologicalComplex.extendMap ψ ComplexShape.embeddingUpNat))) ≅
      Arrow.mk (DerivedCategory.Q.map (HomologicalComplex.extendMap
        ((U.mapHomologicalComplex _).map ψ) ComplexShape.embeddingUpNat)) :=
  Arrow.isoMk
    (DerivedCategory.Q.mapIso
      (Stacks.DerivedIndexing.mapExtendIso U ComplexShape.embeddingUpNat K).symm)
    (DerivedCategory.Q.mapIso
      (Stacks.DerivedIndexing.mapExtendIso U ComplexShape.embeddingUpNat L).symm) (by
      dsimp
      rw [← Functor.map_comp, ← Functor.map_comp, map_extendMap_comp_mapExtendIso_inv])

end Extend

end Stacks.Cohomology

namespace CategoryTheory.InjectiveResolution

variable {C : Type*} [Category* C] [Abelian C]

/-- Auxiliary construction for `CategoryTheory.InjectiveResolution.liftToComplex`. -/
def liftToComplexZero {G : C} (J : InjectiveResolution G) (K : CochainComplex C ℕ)
    [∀ n, Injective (K.X n)] (g : G ⟶ K.X 0) : J.cocomplex.X 0 ⟶ K.X 0 :=
  Injective.factorThru ((HomologicalComplex.singleObjXSelf _ 0 G).hom ≫ g) (J.ι.f 0)

/-- Auxiliary construction for `CategoryTheory.InjectiveResolution.liftToComplex`. -/
def liftToComplexOne {G : C} (J : InjectiveResolution G) (K : CochainComplex C ℕ)
    [∀ n, Injective (K.X n)] (g : G ⟶ K.X 0) (hg : g ≫ K.d 0 1 = 0) :
    J.cocomplex.X 1 ⟶ K.X 1 :=
  J.exact₀.descToInjective (J.liftToComplexZero K g ≫ K.d 0 1)
    (by
      change J.ι.f 0 ≫ J.liftToComplexZero K g ≫ K.d 0 1 = 0
      rw [liftToComplexZero, Injective.comp_factorThru_assoc, Category.assoc, hg, comp_zero])

/-- The first square of `CategoryTheory.InjectiveResolution.liftToComplex` commutes. -/
lemma d_comp_liftToComplexOne {G : C} (J : InjectiveResolution G) (K : CochainComplex C ℕ)
    [∀ n, Injective (K.X n)] (g : G ⟶ K.X 0) (hg : g ≫ K.d 0 1 = 0) :
    J.cocomplex.d 0 1 ≫ J.liftToComplexOne K g hg = J.liftToComplexZero K g ≫ K.d 0 1 :=
  J.exact₀.comp_descToInjective _ _

/-- **A morphism into the degree-zero term of a complex of injectives lifts to a chain map out of
an injective resolution.**  For `J` an injective resolution of `G`, `K` a complex indexed by `ℕ`
with injective terms and `g : G ⟶ K⁰` killed by the differential, this is a chain map `J^• ⟶ K`
extending `g`.  It is the construction of `CategoryTheory.InjectiveResolution.desc`, which uses
only the exactness of `J^•` and the injectivity of the terms of the target. -/
def liftToComplex {G : C} (J : InjectiveResolution G) (K : CochainComplex C ℕ)
    [∀ n, Injective (K.X n)] (g : G ⟶ K.X 0) (hg : g ≫ K.d 0 1 = 0) :
    J.cocomplex ⟶ K :=
  CochainComplex.mkHom _ _ (J.liftToComplexZero K g) (J.liftToComplexOne K g hg)
    (J.d_comp_liftToComplexOne K g hg).symm
    fun n ⟨f, f', w⟩ => ⟨(J.exact_succ n).descToInjective (f' ≫ K.d (n + 1) (n + 2))
      (by dsimp; rw [reassoc_of% w.symm, K.d_comp_d, comp_zero]),
      ((J.exact_succ n).comp_descToInjective _ _).symm⟩

/-- `CategoryTheory.InjectiveResolution.liftToComplex` extends `g` in degree zero. -/
@[reassoc]
lemma ι_f_zero_comp_liftToComplex_f_zero {G : C} (J : InjectiveResolution G)
    (K : CochainComplex C ℕ) [∀ n, Injective (K.X n)] (g : G ⟶ K.X 0)
    (hg : g ≫ K.d 0 1 = 0) :
    J.ι.f 0 ≫ (J.liftToComplex K g hg).f 0 =
      (HomologicalComplex.singleObjXSelf _ 0 G).hom ≫ g :=
  Injective.comp_factorThru ((HomologicalComplex.singleObjXSelf _ 0 G).hom ≫ g) (J.ι.f 0)

end CategoryTheory.InjectiveResolution

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Stacks.Cohomology

variable (S S' : GlobalCrystallineSituation.{u}) (fS : S.S ⟶ S'.S) (fX : S.X ⟶ S'.X)
  (hf : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap fS = fX ≫ S'.toClosedFiber)

/-- `f_{cris, *}` applied to an injective resolution has injective terms, by
`...SmallSite.preservesInjectiveObjects_crisDirectImage`. -/
instance injective_crisDirectImage_cocomplex_X {N : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}}
    (J' : InjectiveResolution N) (n : ℕ) :
    Injective ((((crisDirectImage S S' fS fX hf).mapHomologicalComplex _).obj J'.cocomplex).X n) :=
  Functor.PreservesInjectiveObjects.injective_obj (F := crisDirectImage S S' fS fX hf)
    (J'.injective n)

/-- **A lift `ψ : J^• ⟶ f_{cris, *}J'^•` of the unit `ℱ ⟶ f_{cris, *}f_cris^*ℱ`** to injective
resolutions `J` of `ℱ` and `J'` of `ℱ' = f_cris^*ℱ`, built by
`CategoryTheory.InjectiveResolution.liftToComplex`. -/
def crisResolutionMap (F : ModuleSheaf S')
    (J : InjectiveResolution ((toAbelianSheaf S').obj F))
    (J' : InjectiveResolution ((toAbelianSheaf S).obj ((crisModuleInverseImage fS fX hf).obj F))) :
    J.cocomplex ⟶ ((crisDirectImage S S' fS fX hf).mapHomologicalComplex _).obj J'.cocomplex :=
  J.liftToComplex _ (crisModuleUnit S S' fS fX hf F ≫ (crisDirectImage S S' fS fX hf).map
      ((HomologicalComplex.singleObjXSelf _ 0 _).inv ≫ J'.ι.f 0)) (by
    change _ ≫ (crisDirectImage S S' fS fX hf).map (J'.cocomplex.d 0 1) = 0
    rw [Category.assoc, ← Functor.map_comp, Category.assoc, J'.ι_f_zero_comp_complex_d,
      comp_zero, Functor.map_zero, comp_zero])

/-- `crisResolutionMap` lifts `crisModuleUnit` in degree zero, in the form
`moduleCrisUnitArrowIso` takes as its hypothesis. -/
lemma ι_f_zero_comp_crisResolutionMap_f_zero (F : ModuleSheaf S')
    (J : InjectiveResolution ((toAbelianSheaf S').obj F))
    (J' : InjectiveResolution ((toAbelianSheaf S).obj ((crisModuleInverseImage fS fX hf).obj F))) :
    J.ι.f 0 ≫ (crisResolutionMap S S' fS fX hf F J J').f 0 =
      (HomologicalComplex.singleObjXSelf _ 0 _).hom ≫ crisModuleUnit S S' fS fX hf F ≫
        (crisDirectImage S S' fS fX hf).map
          ((HomologicalComplex.singleObjXSelf _ 0 _).inv ≫ J'.ι.f 0) :=
  J.ι_f_zero_comp_liftToComplex_f_zero _ _ _

section Derived

variable [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w} (Sheaf (smallTopology S') AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S') AddCommGrpCat.{u + 1})]

/-- **The derived unit `ℱ[0] ⟶ Rf_{cris, *}(f_cris^*ℱ)[0]`** in `D⁺(Ab(Cris(X/S)))`: the
derived unit `...SmallSite.derivedCrisUnit` of the underlying abelian sheaf followed by
`Rf_{cris, *}` of the comparison `f_cris^{-1}ℱ ⟶ f_cris^*ℱ`. -/
def derivedModuleCrisUnit (F : ModuleSheaf S') :
    (DerivedCategory.Plus.singleFunctor (Sheaf (smallTopology S') AddCommGrpCat.{u + 1}) 0).obj
        ((toAbelianSheaf S').obj F) ⟶
      (derivedCrisDirectImageFunctor S S' fS fX hf).obj
        ((DerivedCategory.Plus.singleFunctor (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) 0).obj
          ((toAbelianSheaf S).obj ((crisModuleInverseImage fS fX hf).obj F))) :=
  derivedCrisUnit S S' fS fX hf ((toAbelianSheaf S').obj F) ≫
    (derivedCrisDirectImageFunctor S S' fS fX hf).map
      ((DerivedCategory.Plus.singleFunctor _ 0).map (crisModuleComparison S S' fS fX hf F))

/-- **The first arrow of [Stacks, Tag 07Q9] is `Ru_{X/S, *}` of the derived unit**, followed by the
derived square `...SmallSite.derivedZariskiSquare`. -/
theorem moduleComparison07Q9_eq (F : ModuleSheaf S') :
    moduleComparison07Q9 S S' fS fX hf F =
      (derivedZariskiDirectImageFunctor S').map (derivedModuleCrisUnit S S' fS fX hf F) ≫
        (derivedZariskiSquare S S' fS fX hf (crisZariskiSquare S S' fS fX hf)).hom.app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((toAbelianSheaf S).obj ((crisModuleInverseImage fS fX hf).obj F))) := by
  have h := (derivedZariskiSquare S S' fS fX hf (crisZariskiSquare S S' fS fX hf)).hom.naturality
    ((DerivedCategory.Plus.singleFunctor _ 0).map (crisModuleComparison S S' fS fX hf F))
  simp only [Functor.comp_map] at h
  simp only [moduleComparison07Q9, derivedZariskiComparison, derivedModuleCrisUnit,
    Functor.map_comp, Category.assoc, h]
  exact Category.assoc _ _ _

omit [HasDerivedCategory.{w'} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S') AddCommGrpCat.{u + 1})] in
/-- **The derived unit is the module unit followed by the canonical map**
`f_{cris, *}ℱ'[0] ⟶ Rf_{cris, *}ℱ'[0]`. -/
theorem derivedModuleCrisUnit_eq (F : ModuleSheaf S') :
    derivedModuleCrisUnit S S' fS fX hf F =
      (DerivedCategory.Plus.singleFunctor _ 0).map (crisModuleUnit S S' fS fX hf F) ≫
        (singleRightDerivedUnit (crisDirectImage S S' fS fX hf)).app
          ((toAbelianSheaf S).obj ((crisModuleInverseImage fS fX hf).obj F)) := by
  have h := (singleRightDerivedUnit (crisDirectImage S S' fS fX hf)).naturality
    (crisModuleComparison S S' fS fX hf F)
  simp only [Functor.comp_map] at h
  rw [← crisUnit_comp_crisModuleComparison, Functor.map_comp, Category.assoc, h,
    derivedModuleCrisUnit, derivedCrisUnit]
  exact Category.assoc _ _ _

/-- **`Ru_{X/S, *}` of the derived unit is the class of `u_{X/S, *}ψ`**, as an isomorphism of
arrows of `D(Ab(X_Zar))`, for any chain map `ψ : J^• ⟶ f_{cris, *}J'^•` between injective
resolutions of `ℱ` and of `ℱ' = f_cris^*ℱ` which lifts `crisModuleUnit` in degree zero (`hψ`, as
supplied by `ι_f_zero_comp_crisResolutionMap_f_zero` for `crisResolutionMap`).  The complexes are
extended by zero to `ℤ` before `u_{X/S, *}` is applied. -/
def moduleCrisUnitArrowIso (F : ModuleSheaf S')
    (J : InjectiveResolution ((toAbelianSheaf S').obj F))
    (J' : InjectiveResolution ((toAbelianSheaf S).obj ((crisModuleInverseImage fS fX hf).obj F)))
    (ψ : J.cocomplex ⟶ ((crisDirectImage S S' fS fX hf).mapHomologicalComplex _).obj J'.cocomplex)
    (hψ : J.ι.f 0 ≫ ψ.f 0 = (HomologicalComplex.singleObjXSelf _ 0 _).hom ≫
      crisModuleUnit S S' fS fX hf F ≫ (crisDirectImage S S' fS fX hf).map
        ((HomologicalComplex.singleObjXSelf _ 0 _).inv ≫ J'.ι.f 0)) :
    Arrow.mk (DerivedCategory.Plus.ι.map
        ((derivedZariskiDirectImageFunctor S').map (derivedModuleCrisUnit S S' fS fX hf F))) ≅
      Arrow.mk (DerivedCategory.Q.map (((zariskiDirectImage S').mapHomologicalComplex _).map
        (HomologicalComplex.extendMap ψ ComplexShape.embeddingUpNat))) :=
  haveI : ∀ n, Injective ((extendPlusObj (((crisDirectImage S S' fS fX hf).mapHomologicalComplex
      _).obj J'.cocomplex)).obj.X n) := injective_extend_X _
  DerivedCategory.Plus.ι.mapArrow.mapIso
    ((derivedZariskiDirectImageFunctor S').mapArrow.mapIso
      (eqToIso (congrArg Arrow.mk (derivedModuleCrisUnit_eq S S' fS fX hf F)) ≪≫
        singleUnitArrowIso (crisDirectImage S S' fS fX hf) (crisModuleUnit S S' fS fX hf F)
          J J' ψ hψ) ≪≫
      rightDerivedQArrowIso (zariskiDirectImage S')
        (resolutionHomPlus (crisDirectImage S S' fS fX hf) J J' ψ))

/-- `moduleCrisUnitArrowIso` with `u_{X/S, *}` applied before the complexes are extended by zero to
`ℤ`. -/
def moduleCrisUnitArrowIsoExtend (F : ModuleSheaf S')
    (J : InjectiveResolution ((toAbelianSheaf S').obj F))
    (J' : InjectiveResolution ((toAbelianSheaf S).obj ((crisModuleInverseImage fS fX hf).obj F)))
    (ψ : J.cocomplex ⟶ ((crisDirectImage S S' fS fX hf).mapHomologicalComplex _).obj J'.cocomplex)
    (hψ : J.ι.f 0 ≫ ψ.f 0 = (HomologicalComplex.singleObjXSelf _ 0 _).hom ≫
      crisModuleUnit S S' fS fX hf F ≫ (crisDirectImage S S' fS fX hf).map
        ((HomologicalComplex.singleObjXSelf _ 0 _).inv ≫ J'.ι.f 0)) :
    Arrow.mk (DerivedCategory.Plus.ι.map
        ((derivedZariskiDirectImageFunctor S').map (derivedModuleCrisUnit S S' fS fX hf F))) ≅
      Arrow.mk (DerivedCategory.Q.map (HomologicalComplex.extendMap
        (((zariskiDirectImage S').mapHomologicalComplex _).map ψ) ComplexShape.embeddingUpNat)) :=
  moduleCrisUnitArrowIso S S' fS fX hf F J J' ψ hψ ≪≫
    mapExtendArrowIso (zariskiDirectImage S') ψ

end Derived

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
