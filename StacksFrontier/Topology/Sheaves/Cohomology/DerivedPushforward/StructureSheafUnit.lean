module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangeMap
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.DegreeZeroPushforward
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.UnitComparison
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorDegreeZero
public import StacksFrontier.AlgebraicGeometry.TotalDirectImage.QuasiCoherentDirectImage
public import StacksFrontier.Homology.Injectives.DerivedCategory.DerivedLimit
public import StacksFrontier.CategoryTheory.Localization.MapHomotopyCategoryAdjunctionCounit

/-!
# The derived unit `𝒪_Y[0] ⟶ Rf_*(𝒪_X[0])`

Let `f : X ⟶ Y` be a morphism of ringed spaces. The unit of the derived adjunction
`Lf^* ⊣ Rf_*` at `𝒪_Y[0]`, followed by `Rf_*` of the identification `Lf^*(𝒪_Y[0]) ≅ 𝒪_X[0]`, is
a morphism `𝒪_Y[0] ⟶ Rf_*(𝒪_X[0])`. This file names it and records its compatibility with the
derived base change map of [Stacks, Tag 08HY].

## Main definitions

* `Stacks.Cohomology.DerivedStructureUnit.structureUnit`: the morphism `𝒪_Y[0] ⟶ Rf_*(𝒪_X[0])`.

## Main results

* `Stacks.Cohomology.DerivedStructureUnit.derivedBaseChangeMap_unit`: for a commutative square,
  the derived pullback of the unit of `Lf^* ⊣ Rf_*` followed by the base change map is the unit of
  `Lf'^* ⊣ Rf'_*` followed by `Rf'_*` of the comparison of the two iterated derived pullbacks.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces Stacks.Cohomology.DerivedPullbackUnit

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.Cohomology.DerivedStructureUnit

/-- For adjunctions `Lf ⊣ Rf` and `Lf' ⊣ Rf'` and isomorphisms `Lg ⋙ Lf' ≅ Lc ≅ Lf ⋙ Lg'`, the
image under `Lg` of the unit of `Lf ⊣ Rf` at `A`, followed by the base change map at `Lf A`, is the
unit of `Lf' ⊣ Rf'` at `Lg A` followed by `Rf'` of the comparison `Lf' (Lg A) ⟶ Lg' (Lf A)`. -/
theorem _root_.Stacks.Cohomology.DerivedBaseChange.Mate.derivedBaseChangeMap_unit
    {X' X S' S : RingedSpace.{u, u}}
    {Lf : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    {Lg : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing S'))}
    {Lf' : DerivedCategory (SheafOfModules.{u} (structureSheafRing S')) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))}
    {Lg' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))}
    {Lc : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))}
    {Rf : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing S))}
    {Rf' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X')) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing S'))}
    (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf') (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)
    (A : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))) :
    Lg.map (adjf.unit.app A) ≫ DerivedBaseChange.Mate.derivedBaseChangeMap adjf adjf' eg ef
        (Lf.obj A) =
      adjf'.unit.app (Lg.obj A) ≫ Rf'.map (eg.hom.app A ≫ ef.inv.app A) :=
  unit_mateEquiv adjf adjf' (DerivedBaseChange.Mate.derivedPullbackSquare eg ef) A

/-- **The derived base change map is compatible with the units.** For a commutative square of
ringed spaces, the derived pullback along `g` of the unit of `Lf^* ⊣ Rf_*` at `A`, followed by the
derived base change map at `Lf^* A`, is the unit of `Lf'^* ⊣ Rf'_*` at `Lg^* A` followed by `Rf'_*`
of the comparison `Lf'^* Lg^* A ⟶ Lg'^* Lf^* A` of the two iterated derived pullbacks. -/
theorem derivedBaseChangeMap_unit {X' X S' S : RingedSpace.{u, u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S) (sq : g' ≫ f = f' ≫ g)
    (A : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))) :
    (derivedPullback g).map ((derivedAdjunction f).unit.app A) ≫
        DerivedBaseChange.derivedBaseChangeMap g' f' f g sq ((derivedPullback f).obj A) =
      (derivedAdjunction f').unit.app ((derivedPullback g).obj A) ≫
        (derivedPushforward f').map
          ((DerivedBaseChange.derivedPullbackCompIsoLeft g' f' f g sq).hom.app A ≫
            (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical g' f).inv.app A) :=
  DerivedBaseChange.Mate.derivedBaseChangeMap_unit (derivedAdjunction f) (derivedAdjunction f')
    (DerivedBaseChange.derivedPullbackCompIsoLeft g' f' f g sq)
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical g' f) A

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **The derived unit `𝒪_Y[0] ⟶ Rf_*(𝒪_X[0])`**: the unit of `Lf^* ⊣ Rf_*` at `𝒪_Y[0]`, followed
by `Rf_*` of the identification `Lf^*(𝒪_Y[0]) ≅ 𝒪_X[0]`. -/
def structureUnit :
    (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).obj
        (SheafOfModules.unit (structureSheafRing Y)) ⟶
      (derivedPushforward f).obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj
          (SheafOfModules.unit (structureSheafRing X))) :=
  (derivedAdjunction f).unit.app _ ≫ (derivedPushforward f).map (derivedPullbackUnitIso f).hom

/-- The complex `𝒪_Y[0]` of the homotopy category. -/
abbrev unitComplex (Y : RingedSpace.{u, u}) :
    HomotopyCategory (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ) :=
  (HomotopyCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).obj
    (SheafOfModules.unit (structureSheafRing Y))

/-- **The derived unit through the degreewise unit.** `structureUnit f` is, up to isomorphisms at
both ends, the degreewise unit of `K(f^*) ⊣ K(f_*)` at `𝒪_Y[0]` followed by the comparison
`f_* ⟶ Rf_*` at `f^*(𝒪_Y[0])`. -/
theorem exists_structureUnit_eq :
    ∃ ρ : DerivedCategory.Qh.obj (((modulePullback f).mapHomotopyCategory
        (ComplexShape.up ℤ)).obj (unitComplex Y)) ≅
        (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj
          (SheafOfModules.unit (structureSheafRing X)),
      structureUnit f =
        ((DerivedCategory.singleFunctorIsoCompQh _ 0).app
            (SheafOfModules.unit (structureSheafRing Y))).hom ≫
          DerivedCategory.Qh.map ((homotopyPullbackPushforwardAdjunction f).unit.app
            (unitComplex Y)) ≫
          (derivedPushforwardUnit f).app (((modulePullback f).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj (unitComplex Y)) ≫
          (derivedPushforward f).map ρ.hom := by
  have : IsIso ((derivedPullbackComparison f).app (unitComplex Y)) :=
    Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat f _
      (Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat Y.sheaf _ (isFlat_unit Y) 0)
  refine ⟨(asIso ((derivedPullbackComparison f).app (unitComplex Y))).symm ≪≫
      ((derivedPullback f).mapIso ((DerivedCategory.singleFunctorIsoCompQh
        (SheafOfModules.{u} (structureSheafRing Y)) 0).app
          (SheafOfModules.unit (structureSheafRing Y)))).symm ≪≫ derivedPullbackUnitIso f, ?_⟩
  refine ((derivedAdjunction f).unit_app_comp_map_eq_of_iso
    ((DerivedCategory.singleFunctorIsoCompQh (SheafOfModules.{u} (structureSheafRing Y)) 0).app
      (SheafOfModules.unit (structureSheafRing Y)))
    ((derivedPullbackComparison f).app (unitComplex Y))
    (derivedAdjunction_unit_fac f (unitComplex Y)) (derivedPullbackUnitIso f).hom).trans ?_
  simp only [Category.assoc]
  rfl

/-- **`H⁰` of the derived unit `𝒪_Y[0] ⟶ Rf_*(𝒪_X[0])` is invertible exactly when the unit
`𝒪_Y ⟶ f_* f^* 𝒪_Y` of `f^* ⊣ f_*` is.** -/
theorem isIso_homology_structureUnit_iff_isIso_unit_app :
    IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).map
        (structureUnit f)) ↔
      IsIso ((modulePullbackPushforwardAdjunction f).unit.app
        (SheafOfModules.unit (structureSheafRing Y))) := by
  obtain ⟨ρ, h⟩ := exists_structureUnit_eq f
  have hB :
      IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).map
        ((derivedPushforwardUnit f).app (((modulePullback f).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj (unitComplex Y)))) :=
    (NatTrans.isIso_app_iff_of_iso (Functor.whiskerRight (derivedPushforwardUnit f)
        (DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0))
      (((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso
          ((HomologicalComplex.singleMapHomologicalComplex (modulePullback f)
            (ComplexShape.up ℤ) 0).app (SheafOfModules.unit (structureSheafRing Y)))).symm ≪≫
        (((modulePullback f).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app
          ((CochainComplex.singleFunctor _ 0).obj
            (SheafOfModules.unit (structureSheafRing Y)))).symm)).1
      (isIso_homology_derivedPushforwardUnit_app_single f _)
  rw [h, Functor.map_comp, Functor.map_comp, Functor.map_comp, isIso_comp_left_iff,
    isIso_comp_right_iff]
  exact isIso_homology_Qh_map_unit_app_single_iff f (SheafOfModules.unit (structureSheafRing Y))

/-- **`H⁰` of the derived unit `𝒪_Y[0] ⟶ Rf_*(𝒪_X[0])` is invertible exactly when the comparison
`𝒪_Y ⟶ f_* 𝒪_X` is.** -/
theorem isIso_homology_structureUnit_iff :
    IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).map
        (structureUnit f)) ↔
      IsIso (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f)) := by
  rw [isIso_homology_structureUnit_iff_isIso_unit_app]
  have e : SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f) =
      (modulePullbackPushforwardAdjunction f).unit.app
          (SheafOfModules.unit (structureSheafRing Y)) ≫
        (modulePushforward f).map (modulePullbackObjUnitIso f).hom :=
    (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _).symm.trans
      ((modulePullbackPushforwardAdjunction f).homEquiv_unit _ _ _)
  have hm := ((modulePushforward f).mapIso (modulePullbackObjUnitIso f)).isIso_hom
  rw [e]
  exact ⟨fun h => @IsIso.comp_isIso _ _ _ _ _ _ _ h hm,
    fun h => @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ hm h⟩

/-- **Units transported along an invertible base change map**, for abstract adjunctions. Let
`bc_K : Lg(Rf K) ⟶ Rf'(Lg' K)` be natural in `K`, compatible with the units through an invertible
comparison `cmp : Lf'(Lg A) ⟶ Lg'(Lf A)`, and invertible at `B`. Then for identifications
`ψ : Lg A ≅ A'`, `ν : Lf A ≅ B`, `ν' : Lf' A' ≅ B'` the image under `Lg` of
`η_A ≫ Rf(ν) : A ⟶ Rf B` is, up to an isomorphism `Lg(Rf B) ≅ Rf' B'`, the morphism
`ψ ≫ η'_{A'} ≫ Rf'(ν')`. -/
theorem _root_.CategoryTheory.Adjunction.exists_map_unit_comp_map_eq_of_baseChange
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {Lf : C ⥤ D} {Rf : D ⥤ C} (adjf : Lf ⊣ Rf) {Lf' : C' ⥤ D'} {Rf' : D' ⥤ C'}
    (adjf' : Lf' ⊣ Rf') (Lg : C ⥤ C') (Lg' : D ⥤ D')
    (bc : ∀ K : D, Lg.obj (Rf.obj K) ⟶ Rf'.obj (Lg'.obj K))
    (hnat : ∀ {K L : D} (u : K ⟶ L), Lg.map (Rf.map u) ≫ bc L = bc K ≫ Rf'.map (Lg'.map u))
    {A : C} {A' : C'} (ψ : Lg.obj A ≅ A') {B : D} (ν : Lf.obj A ≅ B) {B' : D'}
    (ν' : Lf'.obj A' ≅ B') (cmp : Lf'.obj (Lg.obj A) ⟶ Lg'.obj (Lf.obj A)) [IsIso cmp]
    (hunit : Lg.map (adjf.unit.app A) ≫ bc (Lf.obj A) = adjf'.unit.app (Lg.obj A) ≫ Rf'.map cmp)
    [IsIso (bc B)] :
    ∃ β : Lg.obj (Rf.obj B) ≅ Rf'.obj B',
      Lg.map (adjf.unit.app A ≫ Rf.map ν.hom) ≫ β.hom =
        ψ.hom ≫ adjf'.unit.app A' ≫ Rf'.map ν'.hom := by
  let χ : Lg'.obj B ≅ B' := (Lg'.mapIso ν).symm ≪≫ (asIso cmp).symm ≪≫ Lf'.mapIso ψ ≪≫ ν'
  refine ⟨asIso (bc B) ≪≫ Rf'.mapIso χ, ?_⟩
  have hχ : cmp ≫ Lg'.map ν.hom ≫ χ.hom = Lf'.map ψ.hom ≫ ν'.hom := by
    simp [χ]
  simp only [Functor.map_comp, Category.assoc, Iso.trans_hom, asIso_hom, Functor.mapIso_hom]
  rw [reassoc_of% (hnat ν.hom), reassoc_of% hunit, ← adjf'.unit_naturality_assoc, ← Rf'.map_comp,
    ← Rf'.map_comp, ← Rf'.map_comp, hχ]

/-- **The derived unit commutes with an invertible base change map.** For a commutative square of
ringed spaces whose derived base change map is invertible at `𝒪_X[0]`, the derived pullback along
`g` of `structureUnit f` is `structureUnit f'`, up to the identification
`Lg^*(𝒪_S[0]) ≅ 𝒪_{S'}[0]` and an isomorphism `Lg^* Rf_*(𝒪_X[0]) ≅ Rf'_*(𝒪_{X'}[0])`. -/
theorem exists_derivedPullback_map_structureUnit_eq {X' X S' S : RingedSpace.{u, u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S) (sq : g' ≫ f = f' ≫ g)
    [IsIso (DerivedBaseChange.derivedBaseChangeMap g' f' f g sq
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj
        (SheafOfModules.unit (structureSheafRing X))))] :
    ∃ β : (derivedPullback g).obj ((derivedPushforward f).obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj
          (SheafOfModules.unit (structureSheafRing X)))) ≅
        (derivedPushforward f').obj
          ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X')) 0).obj
            (SheafOfModules.unit (structureSheafRing X'))),
      (derivedPullback g).map (structureUnit f) ≫ β.hom =
        (derivedPullbackUnitIso g).hom ≫ structureUnit f' :=
  (derivedAdjunction f).exists_map_unit_comp_map_eq_of_baseChange (derivedAdjunction f')
    (derivedPullback g) (derivedPullback g') (DerivedBaseChange.derivedBaseChangeMap g' f' f g sq)
    (fun u => DerivedBaseChange.derivedBaseChangeMap_naturality g' f' f g sq u)
    (derivedPullbackUnitIso g) (derivedPullbackUnitIso f) (derivedPullbackUnitIso f')
    ((DerivedBaseChange.derivedPullbackCompIsoLeft g' f' f g sq).hom.app _ ≫
      (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical g' f).inv.app _)
    (derivedBaseChangeMap_unit g' f' f g sq _)

end Stacks.Cohomology.DerivedStructureUnit

end
