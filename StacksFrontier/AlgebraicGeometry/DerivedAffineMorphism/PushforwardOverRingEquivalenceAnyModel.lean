module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GrothendieckAbelian
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreNatTransDevissage
public import StacksFrontier.AlgebraicGeometry.AffineQcohEquivalence.PullbackModulesExact
public import StacksFrontier.AlgebraicGeometry.AffineQcohUnit.Equivalence
public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.QuasicoherentEquivalenceOverPushforwardRing
public import StacksFrontier.AlgebraicGeometry.Duality.AffineVanishing.UpperBounds
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.DerivedAdjunction
public import StacksFrontier.Homology.Injectives.DerivedCategory.DerivedLimit

/-!
# `Φ` is an equivalence `D_QCoh(𝒪_X) ⥤ D_QCoh(f_* 𝒪_X)` at every model

Let `f : X ⟶ S` be an affine morphism of schemes, `g : (X, 𝒪_X) ⟶ (S, f_* 𝒪_X)` and
`Φ = Rg_* : D(𝒪_X) ⥤ D(f_* 𝒪_X)` as in [Stacks, Tag 0AVW]. The equivalence clause of that tag is
`isEquivalence_derivedQuasicoherentPushforwardOverRing` at the standard model of the derived
categories. This file proves it at an arbitrary chosen model. That name and those listed under Main
results are in the namespace `Stacks.AlgebraicGeometry.DerivedAffinePushforward`.

The counit of `Lg^* ⊣ Φ` is invertible on `D_QCoh(𝒪_X)` by dévissage
(`DerivedCategory.isIso_app_of_derivedCategoryB`): `Φ` and `Lg^*` are triangulated, both preserve
the vanishing of each cohomology sheaf on `D_QCoh`, and on a quasi-coherent module placed in a
single degree the counit is that of [Stacks, Tag 01SB]. The unit then follows from the triangle
identity, as at the standard model.

## Main results

* `isIso_mapDerivedCategoryPullbackModulesAdjunction_counit_app`: the counit of `Lg^* ⊣ Φ` is an
  isomorphism on `D_QCoh(𝒪_X)`.
* `isIso_mapDerivedCategoryPullbackModulesAdjunction_unit_app`: the unit of `Lg^* ⊣ Φ` is an
  isomorphism on `D_QCoh(f_* 𝒪_X)`.
* `isEquivalence_derivedQuasicoherentPushforwardOverRing_anyModel`: the equivalence clause of
  [Stacks, Tag 0AVW], at any model.

## References

* [Stacks Project, Tag 0AVW](https://stacks.math.columbia.edu/tag/0AVW)
* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.AffineQcohPushforward
open Stacks.AlgebraicGeometry.AffineQcohEquivalence
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe w u

namespace Stacks.AlgebraicGeometry.DerivedAffinePushforward

variable {X S : Scheme.{u}} (f : X ⟶ S)
  [HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf)]
  [HasDerivedCategory.{w} (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf))]
  [HasDerivedCategory.{w} (SheafOfModules.{u} S.ringCatSheaf)]

/-- The quasi-inverse `𝒢 ↦ f^*𝒢 ⊗_{f^*f_*𝒪_X} 𝒪_X` of [Stacks, Tag 01SB] is additive, being a
left adjoint. -/
instance pullbackModules_additive : (pullbackModules f).Additive :=
  (AffineQcohEquivalence.pullbackPushforwardAdjunction f).left_adjoint_additive

variable [IsAffineHom f]

/-- **The derived adjunction `Lg^* ⊣ Φ`** of the proof of [Stacks, Tag 0AVW], derived from the
abelian adjunction `g^* ⊣ f_*` with `g^*` exact. -/
def mapDerivedCategoryPullbackModulesAdjunction :
    (pullbackModules f).mapDerivedCategory ⊣ derivedPushforwardOverRing.{w} f :=
  Stacks.DerivedFunctor.derivedAdjunction (AffineQcohEquivalence.pullbackPushforwardAdjunction f)
    (derivedPushforwardOverRing.{w} f) (derivedPushforwardOverRingUnit.{w} f)
    (exists_quasiIso_isKInjective_ringCatSheaf X)

/-- A morphism of complexes which is termwise invertible becomes invertible in the homotopy
category. -/
private theorem isIso_quotient_map_of_isIso_f {C : Type*} [Category C] [Preadditive C]
    {K L : CochainComplex C ℤ} (φ : K ⟶ L) (h : ∀ n, IsIso (φ.f n)) :
    IsIso ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map φ) :=
  have := HomologicalComplex.Hom.isIso_of_components φ
  inferInstance

/-- `Lg^*` carries `D_QCoh(f_* 𝒪_X)` into `D_QCoh(𝒪_X)`: `g^*` is exact and preserves
quasi-coherence. -/
private theorem derivedCategoryB_mapDerivedCategory_pullbackModules {X S : Scheme.{u}}
    (f : X ⟶ S) [IsAffineHom f] [HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf)]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf))]
    (E : DerivedCategory (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)))
    (hE : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent (pushforwardRing f.base X.ringCatSheaf)) E) :
    DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent X.ringCatSheaf)
      ((pullbackModules f).mapDerivedCategory.obj E) := fun n =>
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (((pullbackModules f).mapDerivedCategoryCompHomologyFunctorIso n).app E).symm
    (RestrictEquivalence.isQuasicoherent_pullbackModules f _ (hE n))

/-- The unit of `Lg^* ⊣ Φ` is invertible at a complex of quasi-coherent `f_* 𝒪_X`-modules: there it
is the termwise unit of [Stacks, Tag 01SB], `Φ` being computed termwise on the complex of
quasi-coherent modules `g^*K`. -/
theorem isIso_mapDerivedCategoryPullbackModulesAdjunction_unit_app_of_isQuasicoherent
    (K : CochainComplex (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)) ℤ)
    (hqc : ∀ n : ℤ, (K.X n).IsQuasicoherent) :
    IsIso ((mapDerivedCategoryPullbackModulesAdjunction.{w} f).unit.app (DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))) := by
  have h : (mapDerivedCategoryPullbackModulesAdjunction.{w} f).unit.app (DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) ≫
        (derivedPushforwardOverRing.{w} f).map
          ((pullbackModules f).mapDerivedCategoryFactorsh.hom.app
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) =
      DerivedCategory.Qh.map ((Adjunction.mapHomotopyCategoryAdjunction
          (AffineQcohEquivalence.pullbackPushforwardAdjunction f) (ComplexShape.up ℤ)).unit.app
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) ≫
        (derivedPushforwardOverRingUnit.{w} f).app
          (((pullbackModules f).mapHomotopyCategory (ComplexShape.up ℤ)).obj
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) :=
    Stacks.DerivedFunctor.derivedAdjunction_unit_app
      (AffineQcohEquivalence.pullbackPushforwardAdjunction f)
      (derivedPushforwardOverRing.{w} f) (derivedPushforwardOverRingUnit.{w} f)
      (exists_quasiIso_isKInjective_ringCatSheaf X)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)
  have hβ : IsIso ((derivedPushforwardOverRingUnit.{w} f).app
      (((pullbackModules f).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))) :=
    isIso_derivedPushforwardOverRingUnit_app_of_isAffineHom.{w} f
      (((pullbackModules f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) fun n =>
        RestrictEquivalence.isQuasicoherent_pullbackModules f _ (hqc n)
  have : IsIso ((Adjunction.mapHomotopyCategoryAdjunction
      (AffineQcohEquivalence.pullbackPushforwardAdjunction f)
      (ComplexShape.up ℤ)).unit.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) :=
    isIso_quotient_map_of_isIso_f ((Adjunction.mapHomologicalComplexAdjunction
      (AffineQcohEquivalence.pullbackPushforwardAdjunction f)
      (ComplexShape.up ℤ)).unit.app K) fun n =>
      AffineQcohUnit.isIso_unit_app_of_isQuasicoherent f _ (hqc n)
  have : IsIso ((mapDerivedCategoryPullbackModulesAdjunction.{w} f).unit.app (DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) ≫
        (derivedPushforwardOverRing.{w} f).map
          ((pullbackModules f).mapDerivedCategoryFactorsh.hom.app
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((derivedPushforwardOverRing.{w} f).map ((pullbackModules f).mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)))

/-- The counit of `Lg^* ⊣ Φ` is invertible at a complex of quasi-coherent `𝒪_X`-modules: there it
is the termwise counit of [Stacks, Tag 01SB], `Φ` being computed termwise on such a complex. -/
theorem isIso_mapDerivedCategoryPullbackModulesAdjunction_counit_app_of_isQuasicoherent
    (K : CochainComplex (SheafOfModules.{u} X.ringCatSheaf) ℤ)
    (hqc : ∀ n : ℤ, (K.X n).IsQuasicoherent) :
    IsIso ((mapDerivedCategoryPullbackModulesAdjunction.{w} f).counit.app (DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))) := by
  have h : (pullbackModules f).mapDerivedCategory.map ((derivedPushforwardOverRingUnit.{w} f).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) ≫
        (mapDerivedCategoryPullbackModulesAdjunction.{w} f).counit.app (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) =
      (pullbackModules f).mapDerivedCategoryFactorsh.hom.app
          (((pushforwardModules.{u} f.base X.ringCatSheaf).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) ≫
        DerivedCategory.Qh.map ((Adjunction.mapHomotopyCategoryAdjunction
          (AffineQcohEquivalence.pullbackPushforwardAdjunction f) (ComplexShape.up ℤ)).counit.app
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) :=
    Stacks.DerivedFunctor.derivedAdjunction_counit_app
      (AffineQcohEquivalence.pullbackPushforwardAdjunction f)
      (derivedPushforwardOverRing.{w} f) (derivedPushforwardOverRingUnit.{w} f)
      (exists_quasiIso_isKInjective_ringCatSheaf X)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)
  have := isIso_derivedPushforwardOverRingUnit_app_of_isAffineHom.{w} f K hqc
  have : IsIso ((Adjunction.mapHomotopyCategoryAdjunction
      (AffineQcohEquivalence.pullbackPushforwardAdjunction f)
      (ComplexShape.up ℤ)).counit.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) :=
    isIso_quotient_map_of_isIso_f ((Adjunction.mapHomologicalComplexAdjunction
      (AffineQcohEquivalence.pullbackPushforwardAdjunction f)
      (ComplexShape.up ℤ)).counit.app K) fun n =>
      PushforwardColimits.isIso_counit_app_of_isQuasicoherent f _ (hqc n)
  have : IsIso ((pullbackModules f).mapDerivedCategory.map
      ((derivedPushforwardOverRingUnit.{w} f).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) ≫
      (mapDerivedCategoryPullbackModulesAdjunction.{w} f).counit.app (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_left ((pullbackModules f).mapDerivedCategory.map
    ((derivedPushforwardOverRingUnit.{w} f).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))) _

/-! ### Invertibility of the unit and counit on `D_QCoh` -/

/-- Every term of a complex concentrated in one degree lies in a property containing the zero
objects as soon as the nonzero term does. -/
theorem prop_single_obj_X {C : Type*} [Category C] [Abelian C] (P : ObjectProperty C)
    [P.IsClosedUnderIsomorphisms] [P.ContainsZero] (M : C) (hM : P M) (i n : ℤ) :
    P (((CochainComplex.singleFunctor C i).obj M).X n) := by
  by_cases h : n = i
  · subst h
    exact P.prop_of_iso (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n M).symm hM
  · exact P.prop_of_iso
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) i M n h).isoZero.symm
      (ObjectProperty.prop_zero _)

/-- The identification of `M[-i]` in a derived category with the object represented by the
complex concentrated in degree `i`, read through the homotopy category. -/
def singleFunctorObjIsoQh {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (M : C) (i : ℤ) :
    (DerivedCategory.singleFunctor C i).obj M ≅ DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor C i).obj M)) :=
  (DerivedCategory.singleFunctorIsoCompQ C i).app M ≪≫
    ((DerivedCategory.quotientCompQhIso C).app _).symm

/-- Sheaves of `𝒪_X`-modules form a Grothendieck abelian category. -/
local instance isGrothendieckAbelian_ringCatSheaf :
    IsGrothendieckAbelian.{u} (SheafOfModules.{u} X.ringCatSheaf) :=
  SheafOfModules.isGrothendieckAbelianU.{u, u, u} X.ringCatSheaf

/-- `Φ` commutes with the shift, as a right derived functor. -/
local instance derivedPushforwardOverRing_commShift :
    (derivedPushforwardOverRing.{w} f).CommShift ℤ :=
  Functor.IsRightDerivedFunctor.commShift (derivedPushforwardOverRing.{w} f)
    (derivedPushforwardOverRingUnit.{w} f)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ)) ℤ

/-- `Φ` is triangulated, as a right derived functor of an additive functor out of a Grothendieck
abelian category. -/
local instance derivedPushforwardOverRing_isTriangulated :
    (derivedPushforwardOverRing.{w} f).IsTriangulated :=
  Stacks.Injectives.rightDerivedFunctor_isTriangulated
    (pushforwardModules.{u} f.base X.ringCatSheaf) (derivedPushforwardOverRing.{w} f)
    (derivedPushforwardOverRingUnit.{w} f)

/-- **The counit `Lg^* Φ K ⟶ K` is invertible on `D_QCoh(𝒪_X)`**, for `f` affine. -/
theorem isIso_mapDerivedCategoryPullbackModulesAdjunction_counit_app
    (E : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf))
    (hE : DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent X.ringCatSheaf) E) :
    IsIso ((mapDerivedCategoryPullbackModulesAdjunction.{w} f).counit.app E) := by
  have := containsZero_isQuasicoherent X
  refine DerivedCategory.isIso_app_of_derivedCategoryB
    (SheafOfModules.isQuasicoherent X.ringCatSheaf) _ (fun E hE j hj => ?_)
    (fun E _ j hj => hj) (fun M i hM => ?_) E hE
  · exact ((pullbackModules f).map_isZero
      ((isZero_homologyFunctor_derivedPushforwardOverRing_iff_of_isAffineHom.{w} f E hE j).2
        hj)).of_iso
      (((pullbackModules f).mapDerivedCategoryCompHomologyFunctorIso j).app _)
  · rw [NatTrans.isIso_app_iff_of_iso _ (singleFunctorObjIsoQh M i)]
    exact isIso_mapDerivedCategoryPullbackModulesAdjunction_counit_app_of_isQuasicoherent.{w} f _
      (prop_single_obj_X (SheafOfModules.isQuasicoherent X.ringCatSheaf) M hM i)

/-- **The unit `M ⟶ Φ Lg^* M` is invertible on `D_QCoh(f_* 𝒪_X)`**, for `f` affine. -/
theorem isIso_mapDerivedCategoryPullbackModulesAdjunction_unit_app
    (E : DerivedCategory (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)))
    (hE : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent (pushforwardRing f.base X.ringCatSheaf)) E) :
    IsIso ((mapDerivedCategoryPullbackModulesAdjunction.{w} f).unit.app E) := by
  have := containsZero_isQuasicoherent X
  have := containsZero_isQuasicoherent_pushforwardRing f
  refine DerivedCategory.isIso_app_of_derivedCategoryB
    (SheafOfModules.isQuasicoherent (pushforwardRing f.base X.ringCatSheaf)) _
    (fun E _ j hj => hj) (fun E hE j hj => ?_) (fun M i hM => ?_) E hE
  · exact (isZero_homologyFunctor_derivedPushforwardOverRing_iff_of_isAffineHom.{w} f _
      (derivedCategoryB_mapDerivedCategory_pullbackModules f E hE) j).2
      (((pullbackModules f).map_isZero hj).of_iso
        (((pullbackModules f).mapDerivedCategoryCompHomologyFunctorIso j).app _))
  · rw [NatTrans.isIso_app_iff_of_iso _ (singleFunctorObjIsoQh M i)]
    exact isIso_mapDerivedCategoryPullbackModulesAdjunction_unit_app_of_isQuasicoherent.{w} f _
      (prop_single_obj_X (SheafOfModules.isQuasicoherent (pushforwardRing f.base X.ringCatSheaf))
        M hM i)

/-! ### The equivalence -/

omit [HasDerivedCategory (SheafOfModules S.ringCatSheaf)] in
/-- `Lg^*` carries `D_QCoh(f_* 𝒪_X)` into `D_QCoh(𝒪_X)`: `g^*` is exact and preserves
quasi-coherence. -/
theorem derivedCategoryB_derivedPullbackOverRing_obj
    (E : DerivedCategory (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)))
    (hE : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent (pushforwardRing f.base X.ringCatSheaf)) E) :
    DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent X.ringCatSheaf)
      ((pullbackModules f).mapDerivedCategory.obj E) :=
  derivedCategoryB_mapDerivedCategory_pullbackModules f E hE

/-- `Lg^*` as a functor `D_QCoh(f_* 𝒪_X) ⥤ D_QCoh(𝒪_X)`. -/
def derivedQuasicoherentPullbackOverRing :
    (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent
        (pushforwardRing f.base X.ringCatSheaf))).FullSubcategory ⥤
      (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)).FullSubcategory :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ (pullbackModules f).mapDerivedCategory)
    (fun E => derivedCategoryB_derivedPullbackOverRing_obj f E.obj E.property)

/-- **[Stacks, Tag 0AVW], the equivalence.** For an affine morphism `f : X ⟶ S`, the functor
`Φ : D_QCoh(𝒪_X) ⥤ D_QCoh(f_* 𝒪_X)` induced by direct image is an equivalence of categories, with
quasi-inverse `Lg^*` for `g : (X, 𝒪_X) ⟶ (S, f_* 𝒪_X)`. Together with
`derivedPushforwardOverRingCompRestrictScalarsIso`, which says that `Φ` followed by restriction of
scalars is `Rf_*`, this is the whole of the tag. -/
theorem isEquivalence_derivedQuasicoherentPushforwardOverRing_anyModel :
    (derivedQuasicoherentPushforwardOverRing.{w} f).IsEquivalence :=
  (CategoryTheory.Equivalence.mk (derivedQuasicoherentPushforwardOverRing.{w} f)
    (derivedQuasicoherentPullbackOverRing f)
    (NatIso.ofComponents (fun E =>
      ObjectProperty.isoMk _ (@asIso _ _ _ _
        ((mapDerivedCategoryPullbackModulesAdjunction.{w} f).counit.app E.obj)
        (isIso_mapDerivedCategoryPullbackModulesAdjunction_counit_app.{w} f E.obj E.property)))
      fun {E₁ E₂ : (DerivedCategoryB.derivedCategoryB
          (SheafOfModules.isQuasicoherent X.ringCatSheaf)).FullSubcategory} (φ : E₁ ⟶ E₂) =>
        by
          apply ObjectProperty.hom_ext
          exact (mapDerivedCategoryPullbackModulesAdjunction.{w} f).counit.naturality φ.hom).symm
    (NatIso.ofComponents (fun E =>
      ObjectProperty.isoMk _ (@asIso _ _ _ _
        ((mapDerivedCategoryPullbackModulesAdjunction.{w} f).unit.app E.obj)
        (isIso_mapDerivedCategoryPullbackModulesAdjunction_unit_app.{w} f E.obj E.property)))
      fun {E₁ E₂ : (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent
          (pushforwardRing f.base X.ringCatSheaf))).FullSubcategory} (φ : E₁ ⟶ E₂) =>
        by
          apply ObjectProperty.hom_ext
          exact (mapDerivedCategoryPullbackModulesAdjunction.{w} f).unit.naturality
            φ.hom).symm).isEquivalence_functor

end Stacks.AlgebraicGeometry.DerivedAffinePushforward

end
