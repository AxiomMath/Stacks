module

public import StacksFrontier.AlgebraicGeometry.Spaces.DescentLocus.DegreeZeroBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SingleDegreeRankOpenSubspaceExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SingleDegreeFreeGeometricPointVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SingleDegreeFreeLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceImage
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedPushforwardSingleSections
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedModulePushforwardTotalRightDerived
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ApproximationQcqsRestrict
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeEnoughFields
public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.PushforwardOverRingEquivalenceAnyModel
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedPushforwardQuasicoherentCohomology

/-!
# Cohomology and base change in degree zero over a one-point space

Let `f : X ⟶ Y` be a proper morphism of finite presentation of algebraic spaces, `𝒢` an
`𝒪_X`-module of finite presentation, flat over `Y`, and `X' ⟶ Y'` the base change of `f` along a
morphism `g : Y' ⟶ Y` from an algebraic space with at most one point (for instance the spectrum of
a field). If the higher direct images `R^q f'_*((g')^*𝒢)`, `q ≥ 1`, vanish, then the base change
map `g^*f_*𝒢 ⟶ f'_*(g')^*𝒢` of `AlgebraicGeometry.Space.moduleBaseChangeMap` is an isomorphism.

## Main results

* `AlgebraicGeometry.C1764Prereq.isIso_moduleBaseChangeMap_app_of_isZero_rightDerived`: cohomology
  and base change in degree zero over a one-point space.
* `AlgebraicGeometry.C1764Prereq.isIso_smallEtaleDerivedModulePullback_map_of_geometricFibres`: a
  morphism into a perfect object with geometric fibres in degree `0` becomes invertible after
  derived pullback to a one-point space.
* `C1764Prereq.nonempty_smallEtaleDerivedModulePullback_derivedModulePushforward_iso`: the
  isomorphism `Lg^*Rf_*𝒢 ≅ Rf'_*((g')^*𝒢)` of Stacks 0CTM (2).

## References

* [Stacks Project, Tag 0CTM](https://stacks.math.columbia.edu/tag/0CTM)
* [Stacks Project, Tag 0D20](https://stacks.math.columbia.edu/tag/0D20)
* [Stacks Project, Tag 0E6Y](https://stacks.math.columbia.edu/tag/0E6Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPushforward (derivedPushforward pushforwardOnHomotopy sourceQuasiIso)

universe u

namespace AlgebraicGeometry.C1764Prereq

open AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [-instance] AlgebraicGeometry.RingedSpace.hasDerivedCategoryOXMod
  Stacks.ModulesOnACategory.QuasiCoherentEquivalence.derivedPresheafCategory
  AlgebraicGeometry.SmallEtale.hasDerivedCategory_smallEtaleRingedSite
  Stacks.DerivedQCoh.hasDerivedCategoryQuasicoherent
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] spaceModulesHasDerivedCategory

section Unit

universe w₀ v₀ u₀ v₉ u₉

/-- **`R⁰w = w` for a left exact functor out of a Grothendieck abelian category**: the unit of a
right derived functor of `w` on the unbounded derived category is an isomorphism on degree-zero
cohomology at every object placed in degree zero. -/
theorem isIso_homology_zero_unit_app_single {A : Type u₀} [Category.{v₀} A] [Abelian A]
    [IsGrothendieckAbelian.{w₀} A] {B : Type u₉} [Category.{v₉} B] [Abelian B]
    (w : A ⥤ B) [w.Additive] [PreservesFiniteLimits w]
    (Rw : DerivedCategory A ⥤ DerivedCategory B)
    (α : w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rw)
    [Rw.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))] (M : A) :
    IsIso ((DerivedCategory.homologyFunctor B 0).map
      (α.app ((HomotopyCategory.singleFunctor A 0).obj M))) := by
  let := Functor.IsRightDerivedFunctor.commShift Rw α
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ℤ
  have : Rw.IsTriangulated :=
    Stacks.Perfect.CechAugmentation.isTriangulated_of_isRightDerivedFunctor w Rw α
  have : EnoughInjectives A := IsGrothendieckAbelian.enoughInjectives.{w₀}
  have hK : ∀ I : CochainComplex A ℤ, I.IsKInjective →
      IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)) := fun I hI =>
    Stacks.Cohomology.UnboundedComplexes.isIso_app_of_isKInjective _ DerivedCategory.Qh Rw α I hI
  exact Stacks.DerivedFunctor.isIso_singleUnitHomology_app w Rw α
    (fun X => Stacks.SmallDerivedCategory.isGE_obj_of_isGE w Rw α hK _ 0 inferInstance)
    (fun J hJ => Stacks.DerivedFunctor.isIso_unit_app_single_of_injective w Rw α
      Stacks.Injectives.exists_kInjective_resolution_of_grothendieck J hJ) M

end Unit

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A functor `L` of derived categories isomorphic to the functor `F.mapDerivedCategory` of an
exact functor `F` inverts a morphism `φ : A ⟶ E` with invertible `H⁰` as soon as `A` and `L(E)`
have no cohomology outside degree `0`. -/
theorem isIso_map_of_isIso_homology_zero_of_iso_mapDerivedCategory {C D : Type*} [Category C]
    [Category D]
    {_ : Abelian C} {_ : Abelian D} {_ : HasDerivedCategory C} {_ : HasDerivedCategory D}
    (F : C ⥤ D) (_ : F.Additive) (_ : PreservesFiniteLimits F) (_ : PreservesFiniteColimits F)
    (L : DerivedCategory C ⥤ DerivedCategory D) (e : L ≅ F.mapDerivedCategory)
    {A E : DerivedCategory C} (φ : A ⟶ E)
    (h0 : IsIso ((DerivedCategory.homologyFunctor C 0).map φ))
    (hA : ∀ n : ℤ, n ≠ 0 → IsZero ((DerivedCategory.homologyFunctor C n).obj A))
    (hE : ∀ n : ℤ, n ≠ 0 → IsZero ((DerivedCategory.homologyFunctor D n).obj (L.obj E))) :
    IsIso (L.map φ) := by
  suffices hF : IsIso (F.mapDerivedCategory.map φ) by
    have : L.map φ = e.hom.app A ≫ F.mapDerivedCategory.map φ ≫ e.inv.app E := by
      rw [← reassoc_of% (e.hom.naturality φ), Iso.hom_inv_id_app, Category.comp_id]
    rw [this]
    infer_instance
  rw [DerivedCategory.isIso_iff]
  intro n
  let i := F.mapDerivedCategoryHomologyIso n
  have nat : (DerivedCategory.homologyFunctor D n).map (F.mapDerivedCategory.map φ) =
      i.hom.app A ≫ F.map ((DerivedCategory.homologyFunctor C n).map φ) ≫ i.inv.app E := by
    have := i.hom.naturality φ
    simp only [Functor.comp_map] at this
    rw [← reassoc_of% this]
    simp
  by_cases hn : n = 0
  · subst hn
    rw [nat]
    infer_instance
  · refine isIso_of_source_target_iso_zero _ ?_ ?_
    · exact ((F.map_isZero (hA n hn)).of_iso (i.app A)).isoZero
    · exact ((hE n hn).of_iso ((DerivedCategory.homologyFunctor D n).mapIso
        (e.app E).symm)).isoZero

/-- An object of the derived category with cohomology bounded in degrees `≥ 0` and `≤ 0` has no
cohomology outside degree `0`. -/
private theorem isZero_homology_of_isGE_zero_of_isLE_zero {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (X : DerivedCategory C) [X.IsGE 0] [X.IsLE 0] {n : ℤ} (hn : n ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor C n).obj X) := by
  rcases lt_or_gt_of_ne hn with hn | hn
  · exact DerivedCategory.isZero_of_isGE _ 0 n hn
  · exact DerivedCategory.isZero_of_isLE _ 0 n hn

/-- Along an étale morphism `ι`, a morphism `φ : A ⟶ E` of `D(𝒪_Y)` with invertible `H⁰`, whose
source has no cohomology outside degree `0`, has invertible derived pullback `Lι^*φ` as soon as
`Lι^*E` has no cohomology outside degree `0`. -/
theorem isIso_smallEtaleDerivedModulePullback_map_of_isEtale {Y Z : AlgebraicSpaces B S hS}
    (ι : Z ⟶ Y) (hι : Space.IsEtale B S hS ι.hom)
    {A E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))}
    (φ : A ⟶ E) (h0 : IsIso ((DerivedCategory.homologyFunctor _ 0).map φ))
    (hA : ∀ n : ℤ, n ≠ 0 → IsZero ((DerivedCategory.homologyFunctor _ n).obj A))
    (hE : ∀ n : ℤ, n ≠ 0 → IsZero ((DerivedCategory.homologyFunctor _ n).obj
      ((smallEtaleDerivedModulePullback B S hS ι).obj E))) :
    IsIso ((smallEtaleDerivedModulePullback B S hS ι).map φ) :=
  isIso_map_of_isIso_homology_zero_of_iso_mapDerivedCategory
    (etaleModulePullback.{u, u} B S hS ι hι)
    (etaleModulePullback_additive B S hS ι hι)
    (preservesFiniteLimits_etaleModulePullback B S hS ι hι)
    (preservesFiniteColimits_etaleModulePullback B S hS ι hι) _
    (smallEtaleDerivedModulePullbackIsoEtale B S hS ι hι) φ h0 hA hE

/-- The morphism of algebraic spaces from the spectrum of the field of a geometric point `p` of
`Y'` to `Y'` defined by `p`. -/
abbrev geometricPointMap {Y' : AlgebraicSpaces B S hS} (p : Space.GeometricPoint B S hS Y'.1) :
    (schemeSpace p.val.siteObject :
      AlgebraicSpaces B S hS) ⟶ Y' :=
  ObjectProperty.homMk (yonedaEquiv.symm p.val.value)

/-- **Spreading out a fibre in degree `0` (Stacks 0D20).** Let `φ : A ⟶ E` be a morphism of
`D(𝒪_Y)` with `E` perfect, `H⁰(φ)` invertible and `A` without cohomology outside degree `0`, and
let `g : Y' ⟶ Y` be a morphism from an algebraic space with at most one point such that the derived
fibres of `E` at the geometric points of `Y'` have no cohomology outside degree `0`. Then `Lg^*φ`
is invertible. -/
theorem isIso_smallEtaleDerivedModulePullback_map_of_geometricFibres
    {Y Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y) (hpts : Subsingleton (points B S hS Y'.1))
    {A E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))}
    (φ : A ⟶ E) (hE : RingedSite.IsPerfect (Space.smallEtaleRingedSite B S hS Y.1 Y.2) E)
    (h0 : IsIso ((DerivedCategory.homologyFunctor _ 0).map φ))
    (hA : ∀ n : ℤ, n ≠ 0 → IsZero ((DerivedCategory.homologyFunctor _ n).obj A))
    (hgeom : ∀ (p : Space.GeometricPoint B S hS Y'.1) (j : ℤ), j ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor _ j).obj
        ((smallEtaleDerivedModulePullback B S hS (geometricPointMap p ≫ g)).obj E))) :
    IsIso ((smallEtaleDerivedModulePullback B S hS g).map φ) := by
  classical
  obtain ⟨r, hr⟩ : ∃ r : ℤ, ∀ y : points B S hS Y'.1,
      pointsMap B S hS Y'.1 g.hom y ∈ singleDegreeFreePoints B S hS E 0 r := by
    by_cases hne : Nonempty (points B S hS Y'.1)
    · obtain ⟨y₀⟩ := hne
      obtain ⟨p, -⟩ := (geometricPoints_large_enough B S hS Y'.1 Y'.1 Y'.2 Y'.2).1 y₀
      obtain ⟨n, hn⟩ := exists_mem_singleDegreeFreePoints_of_isZero_homModule_homology B S hS E
        hE 0 p (geometricPointMap p ≫ g) (fun j hj => Functor.map_isZero _ (hgeom p j hj))
      refine ⟨n, fun y => ?_⟩
      rw [Subsingleton.elim y p.image, ← pointsMap_yonedaEquiv_symm_comp_tautological p g.hom]
      exact hn
    · exact ⟨0, fun y => (hne ⟨y⟩).elim⟩
  obtain ⟨U, hU, hUloc, -⟩ := exists_isSingleDegreeRankLocus B S hS Y E 0 r hE
  have hLg : IsFiniteLocallyFreeOfIntRankInDegree B S hS Y'
      ((smallEtaleDerivedModulePullback B S hS g).obj E) 0 r :=
    (isFiniteLocallyFreeOfIntRankInDegree_iff B S hS Y' _ 0 r).2 fun y =>
      exists_isFreeOfRankInDegree_chart_of_mem_singleDegreeFreePoints B S hS Y g E 0 r y (hr y)
  obtain ⟨h, hh⟩ :=
    (@hUloc Y' g (hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS g)).2 hLg
  let ι := openSubspaceImmersion B S hS U
  have hι : IsIso ((smallEtaleDerivedModulePullback B S hS ι).map φ) := by
    refine isIso_smallEtaleDerivedModulePullback_map_of_isEtale ι
      (isEtale_ι_of_isOpenSubspace U.2) φ h0 hA fun n hn => ?_
    obtain ⟨M, -, ⟨e⟩⟩ := hU
    exact (isZero_homology_of_isGE_zero_of_isLE_zero _ hn).of_iso
      ((DerivedCategory.homologyFunctor _ n).mapIso e)
  let e := smallEtaleDerivedModulePullbackCompIso B S hS h ι ≪≫
    smallEtaleDerivedModulePullbackCongr B S hS hh
  have : (smallEtaleDerivedModulePullback B S hS g).map φ = e.inv.app A ≫
      (smallEtaleDerivedModulePullback B S hS h).map
        ((smallEtaleDerivedModulePullback B S hS ι).map φ) ≫ e.hom.app E := by
    have := e.hom.naturality φ
    simp only [Functor.comp_map] at this
    rw [this, Iso.inv_hom_id_app_assoc]
  rw [this]
  infer_instance

section Square

variable {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
  (g' : X' ⟶ X)

/-- **Stacks 0CTM (2) as an isomorphism of objects**: for a cartesian square with `f` proper and of
finite presentation and `𝒢` of finite presentation, flat over `Y`, `Lg^*Rf_*𝒢 ≅ Rf'_*((g')^*𝒢)`. -/
theorem nonempty_smallEtaleDerivedModulePullback_derivedModulePushforward_iso
    (hf : Space.IsProper B S hS f.hom) (hfp : Space.IsFinitePresentation B S hS f.hom)
    (G : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
    (hGfp : G.IsFinitePresentation) (hGflat : Space.IsFlatOver B S hS X.2 f.hom G)
    (sq : IsPullback g' f' f g) :
    Nonempty ((smallEtaleDerivedModulePullback B S hS g).obj
        ((derivedModulePushforward B S hS f).obj ((DerivedCategory.singleFunctor _ 0).obj G)) ≅
      (derivedModulePushforward B S hS f').obj
        ((DerivedCategory.singleFunctor _ 0).obj ((modulePullback B S hS g').obj G))) := by
  have := modulePullback_additive g'
  have h := (isPerfect_derivedModulePushforward_single_and_isIso_baseChange f hf hfp G hGfp
    hGflat).2 g f' g' sq
  exact ⟨(smallEtaleDerivedModulePullback B S hS g).mapIso ((derivedModulePushforward B S hS
      f).mapIso ((DerivedCategory.singleFunctorIsoCompQ _ 0).app G)) ≪≫ @asIso _ _ _ _ _ h ≪≫
    (derivedModulePushforward B S hS f').mapIso (DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex (modulePullback B S hS g')
        (ComplexShape.up ℤ) 0).app G) ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ _ 0).app _).symm)⟩

/-- **The derived fibres of `Rf_*𝒢` live in degrees `≥ 0`**: for `f` proper and of finite
presentation, `𝒢` of finite presentation and flat over `Y`, and any `c : Z ⟶ Y`, the derived
pullback `Lc^*Rf_*𝒢 ≅ Rf_{Z,*}𝒢_Z` (Stacks 0CTM (2)) has no cohomology in negative degrees. -/
theorem isGE_smallEtaleDerivedModulePullback_derivedModulePushforward
    (hf : Space.IsProper B S hS f.hom) (hfp : Space.IsFinitePresentation B S hS f.hom)
    (G : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
    (hGfp : G.IsFinitePresentation) (hGflat : Space.IsFlatOver B S hS X.2 f.hom G)
    {Z : AlgebraicSpaces B S hS} (c : Z ⟶ Y) :
    ((smallEtaleDerivedModulePullback B S hS c).obj
        ((derivedModulePushforward B S hS f).obj
          ((DerivedCategory.singleFunctor _ 0).obj G))).IsGE 0 := by
  obtain ⟨e⟩ := nonempty_smallEtaleDerivedModulePullback_derivedModulePushforward_iso f c
    (pullback.snd f c) (pullback.fst f c) hf hfp G hGfp hGflat (IsPullback.of_hasPullback f c)
  have := isGE_rightDerived_modulePushforward_obj_singleFunctor B S hS (pullback.snd f c)
    (derivedModulePushforward B S hS (pullback.snd f c))
    (derivedModulePushforwardUnit B S hS (pullback.snd f c))
    ((modulePullback B S hS (pullback.fst f c)).obj G)
  exact DerivedCategory.TStructure.t.isGE_of_iso e.symm 0

/-- **The derived fibre of `Rf_*𝒢` along `g` lives in degrees `≤ 0`** when the higher direct images
of the base change `(g')^*𝒢` vanish, for a cartesian square with `f` proper and of finite
presentation and `𝒢` of finite presentation, flat over `Y` (Stacks 0CTM (2)). -/
theorem isLE_smallEtaleDerivedModulePullback_derivedModulePushforward
    (hf : Space.IsProper B S hS f.hom) (hfp : Space.IsFinitePresentation B S hS f.hom)
    (G : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
    (hGfp : G.IsFinitePresentation) (hGflat : Space.IsFlatOver B S hS X.2 f.hom G)
    (sq : IsPullback g' f' f g)
    (hvan : ∀ q : ℕ, 0 < q →
      have := hasInjectiveResolutions_modules B S hS X'.1 X'.2
      IsZero (((modulePushforward B S hS f').rightDerived q).obj
        ((modulePullback B S hS g').obj G))) :
    ((smallEtaleDerivedModulePullback B S hS g).obj
        ((derivedModulePushforward B S hS f).obj
          ((DerivedCategory.singleFunctor _ 0).obj G))).IsLE 0 := by
  obtain ⟨e⟩ := nonempty_smallEtaleDerivedModulePullback_derivedModulePushforward_iso f g f' g'
    hf hfp G hGfp hGflat sq
  rw [DerivedCategory.isLE_iff]
  intro i hi
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, i = q := ⟨i.toNat, by omega⟩
  have := hasInjectiveResolutions_modules B S hS X'.1 X'.2
  exact (hvan q (by omega)).of_iso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y')) q).mapIso
    (e ≪≫ (totalRightDerivedModulePushforwardIso B S hS f').symm.app _) ≪≫
    homologyDerivedModulePushforwardSingleZeroIso B S hS f' _ q)

/-- **`R⁰f_* = f_*`**: the unit `f_*𝒢[0] ⟶ Rf_*𝒢[0]` of the derived direct image of a morphism of
algebraic spaces is an isomorphism on degree-zero cohomology. -/
theorem isIso_homology_zero_totalRightDerivedUnit_app_single
    (G : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) :
    IsIso ((DerivedCategory.homologyFunctor _ 0).map
      (((pushforwardOnHomotopy (X := Space.smallEtaleRingedTopos B S hS X)
        (Y := Space.smallEtaleRingedTopos B S hS Y)
        (Space.smallEtaleRingedToposHom B S hS f)).totalRightDerivedUnit
          DerivedCategory.Qh (sourceQuasiIso (Space.smallEtaleRingedTopos B S hS X))).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G)))) := by
  have := (RingedToposHom.pullbackAdjPushforwardModules
    (X := Space.smallEtaleRingedTopos B S hS X) (Y := Space.smallEtaleRingedTopos B S hS Y)
    (Space.smallEtaleRingedToposHom B S hS f)).isRightAdjoint
  have : PreservesFiniteLimits (RingedToposHom.pushforwardModules
      (X := Space.smallEtaleRingedTopos B S hS X) (Y := Space.smallEtaleRingedTopos B S hS Y)
      (Space.smallEtaleRingedToposHom B S hS f)) :=
    PreservesLimitsOfSize.preservesFiniteLimits.{0, 0} _
  exact isIso_homology_zero_unit_app_single _ _ _ G

/-- The degreewise direct image of a module placed in degree `0`, read in the derived category, has
no cohomology outside degree `0`. -/
theorem isZero_homology_pushforwardOnHomotopy_single
    (G : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) (n : ℤ) (hn : n ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor _ n).obj
      ((pushforwardOnHomotopy (X := Space.smallEtaleRingedTopos B S hS X)
        (Y := Space.smallEtaleRingedTopos B S hS Y) (Space.smallEtaleRingedToposHom B S hS f)).obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G)))) := by
  let Gf := RingedToposHom.pushforwardModules (X := Space.smallEtaleRingedTopos B S hS X)
    (Y := Space.smallEtaleRingedTopos B S hS Y) (Space.smallEtaleRingedToposHom B S hS f)
  let e : DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        ((Gf.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G))) ≅
      (DerivedCategory.singleFunctor _ 0).obj (Gf.obj G) :=
    DerivedCategory.Qh.mapIso ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex Gf (ComplexShape.up ℤ) 0).app G)) ≪≫
      (Stacks.AlgebraicGeometry.DerivedAffinePushforward.singleFunctorObjIsoQh (Gf.obj G) 0).symm
  exact (isZero_homology_of_isGE_zero_of_isLE_zero _ hn).of_iso
    ((DerivedCategory.homologyFunctor _ n).mapIso e)

/-- **The derived fibres of `Rf_*𝒢` at the geometric points of `Y'` live in degree `0`** when the
higher direct images of `(g')^*𝒢` vanish, for a cartesian square with `f` proper and of finite
presentation and `𝒢` of finite presentation, flat over `Y` (Stacks 0CTM (2)). -/
theorem isZero_homology_geometricFibre_derivedModulePushforward
    (hf : Space.IsProper B S hS f.hom) (hfp : Space.IsFinitePresentation B S hS f.hom)
    (G : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
    (hGfp : G.IsFinitePresentation) (hGflat : Space.IsFlatOver B S hS X.2 f.hom G)
    (sq : IsPullback g' f' f g)
    (hvan : ∀ q : ℕ, 0 < q →
      have := hasInjectiveResolutions_modules B S hS X'.1 X'.2
      IsZero (((modulePushforward B S hS f').rightDerived q).obj
        ((modulePullback B S hS g').obj G)))
    (p : Space.GeometricPoint B S hS Y'.1) (j : ℤ) (hj : j ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor _ j).obj
      ((smallEtaleDerivedModulePullback B S hS (geometricPointMap p ≫ g)).obj
        ((derivedModulePushforward B S hS f).obj
          ((DerivedCategory.singleFunctor _ 0).obj G)))) := by
  rcases lt_or_gt_of_ne hj with hj | hj
  · have := isGE_smallEtaleDerivedModulePullback_derivedModulePushforward f hf hfp G hGfp
      hGflat (geometricPointMap p ≫ g)
    exact DerivedCategory.isZero_of_isGE _ 0 j hj
  · have := isLE_smallEtaleDerivedModulePullback_obj (geometricPointMap p) _ 0
      (isLE_smallEtaleDerivedModulePullback_derivedModulePushforward f g f' g' hf hfp G
        hGfp hGflat sq hvan)
    exact (DerivedCategory.isZero_of_isLE ((smallEtaleDerivedModulePullback B S hS
      (geometricPointMap p)).obj ((smallEtaleDerivedModulePullback B S hS g).obj
        ((derivedModulePushforward B S hS f).obj
          ((DerivedCategory.singleFunctor _ 0).obj G)))) 0 j hj).of_iso
      ((DerivedCategory.homologyFunctor _ j).mapIso
        ((smallEtaleDerivedModulePullbackCompIso B S hS (geometricPointMap p) g).app _).symm)

/-- **`g^*` commutes with `H⁰` on `Rf_*𝒢`** over a one-point space with no higher cohomology on the
fibre: under the hypotheses of `isIso_moduleBaseChangeMap_app_of_isZero_rightDerived`, `Lg^*` of
the unit `f_*𝒢[0] ⟶ Rf_*𝒢[0]` is an isomorphism on degree-zero cohomology. -/
theorem isIso_homology_smallEtaleDerivedModulePullback_map_unit_of_isZero_rightDerived
    (hf : Space.IsProper B S hS f.hom) (hfp : Space.IsFinitePresentation B S hS f.hom)
    (G : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
    (hGfp : G.IsFinitePresentation) (hGflat : Space.IsFlatOver B S hS X.2 f.hom G)
    (sq : IsPullback g' f' f g) (hpts : Subsingleton (points B S hS Y'.1))
    (hvan : ∀ q : ℕ, 0 < q →
      have := hasInjectiveResolutions_modules B S hS X'.1 X'.2
      IsZero (((modulePushforward B S hS f').rightDerived q).obj
        ((modulePullback B S hS g').obj G))) :
    IsIso ((DerivedCategory.homologyFunctor _ 0).map
      ((smallEtaleDerivedModulePullback B S hS g).map
        (((pushforwardOnHomotopy (X := Space.smallEtaleRingedTopos B S hS X)
          (Y := Space.smallEtaleRingedTopos B S hS Y)
          (Space.smallEtaleRingedToposHom B S hS f)).totalRightDerivedUnit DerivedCategory.Qh
            (sourceQuasiIso (Space.smallEtaleRingedTopos B S hS X))).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
            ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G))))) := by
  have h0CTM := isPerfect_derivedModulePushforward_single_and_isIso_baseChange f hf hfp G hGfp
    hGflat
  let eE := (derivedModulePushforward B S hS f).mapIso
    (Stacks.AlgebraicGeometry.DerivedAffinePushforward.singleFunctorObjIsoQh G 0)
  have := isIso_smallEtaleDerivedModulePullback_map_of_geometricFibres g hpts _
    (isPerfect_of_iso B S hS h0CTM.1 eE)
    (isIso_homology_zero_totalRightDerivedUnit_app_single f G)
    (isZero_homology_pushforwardOnHomotopy_single f G)
    (fun p j hj => (isZero_homology_geometricFibre_derivedModulePushforward f g f' g' hf hfp G
      hGfp hGflat sq hvan p j hj).of_iso ((DerivedCategory.homologyFunctor _ j).mapIso
        ((smallEtaleDerivedModulePullback B S hS (geometricPointMap p ≫ g)).mapIso eE.symm)))
  exact Functor.map_isIso _ _

/-- **Cohomology and base change in degree zero over a one-point space.** Let `f : X ⟶ Y` be proper
and of finite presentation, `𝒢` an `𝒪_X`-module of finite presentation, flat over `Y`, and
`X' ⟶ Y'` the base change of `f` along `g : Y' ⟶ Y`, where `Y'` has at most one point (for instance
the spectrum of a field). If the higher direct images `R^q f'_*((g')^*𝒢)`, `q ≥ 1`, vanish, then
the base change map `g^*f_*𝒢 ⟶ f'_*(g')^*𝒢` is an isomorphism. -/
theorem isIso_moduleBaseChangeMap_app_of_isZero_rightDerived
    (hf : Space.IsProper B S hS f.hom) (hfp : Space.IsFinitePresentation B S hS f.hom)
    (G : Space.Modules.{u, u} B S hS X.1 X.2)
    (hGfp : G.IsFinitePresentation) (hGflat : Space.IsFlatOver B S hS X.2 f.hom G)
    (sq : IsPullback g' f' f g) (hpts : Subsingleton (points B S hS Y'.1))
    (hvan : ∀ q : ℕ, 0 < q →
      have := hasInjectiveResolutions_modules B S hS X'.1 X'.2
      IsZero (((modulePushforward B S hS f').rightDerived q).obj
        ((modulePullback B S hS g').obj G)))
    (w : g' ≫ f = f' ≫ g) :
    IsIso ((moduleBaseChangeMap f g f' g' w).app G) :=
  DescentStratum.isIso_moduleBaseChangeMap_app_of_isIso_homology_map_unit f g f' g' w G
    (isIso_homology_smallEtaleDerivedModulePullback_map_unit_of_isZero_rightDerived f g f' g' hf
      hfp G hGfp hGflat sq hpts hvan)
    ((isPerfect_derivedModulePushforward_single_and_isIso_baseChange f hf hfp G hGfp
      hGflat).2 g f' g' sq)

end Square

end AlgebraicGeometry.C1764Prereq

end
