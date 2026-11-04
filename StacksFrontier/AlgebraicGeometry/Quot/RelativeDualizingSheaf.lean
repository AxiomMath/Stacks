module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyDualizingFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.FibrewiseConcentrated
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.TorIndependentDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperFlatSingleDegreeRankLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.DerivedPullbackTriangulated
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDualizingComplexAffinePerfect
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.ShiftAndVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.ExtensionByZeroUnderivedBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.FibrewiseInvertible
public import StacksFrontier.Homology.PseudoCoherent.Homology
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.GorensteinDualizingInvertible
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.EtaleLocalList
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackInvertible.RingedTopos
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Gorenstein.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Gorenstein.CohenMacaulay
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesGorensteinDimOne
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleEtaleChartTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ElementaryEtaleNeighborhood
import StacksCore.Tactic.StacksAttribute

/-!
# The relative dualizing sheaf of a family of curves (Stacks 0E6P, 0E6Q, 0E6R)

Let `f : X ⟶ S` be a family of curves with Cohen–Macaulay fibres equidimensional of dimension
one, and `(ω^•_{X/S}, τ)` a relative dualizing complex (Stacks 0E5X). Then
`ω^•_{X/S} = ω_{X/S}[1]` for a pseudo-coherent `𝒪_X`-module `ω_{X/S}` flat over `S` whose
formation commutes with base change (Stacks 0E6P), and `ω_{X/S} = H^{-1}(ω^•_{X/S})` is the
*relative dualizing sheaf* of `f` (Stacks 0E6Q).

The derived fibres of `ω^•_{X/S}` live in degree `-1`
(`AlgebraicGeometry.CurveFamily.isZero_homology_smallEtaleDerivedModulePullback_residueFibreι`), so
`ω^•_{X/S}` does and its cohomology sheaf there is flat over `S`
(`AlgebraicGeometry.Space.isZero_homology_and_isFlatOver_of_isZero_homology_residueFibre`).
Formation commutes with base change because relative dualizing complexes are unique (Stacks
0E5Z) and their base changes are relative dualizing complexes (Stacks 0E6C), while the derived
pullback of a module flat over the base is its pullback (Stacks 0DKD).

If moreover the fibres are Gorenstein, then `ω_{X/S}` is invertible and its formation commutes with
arbitrary base change (Stacks 0E6R). Base change is 0E6P read in degree `-1`. Invertibility is
checked on the fibres
(`AlgebraicGeometry.Space.isInvertibleModule_of_isInvertibleModule_residueFibre`): `ω_{X/S}` is
flat over `S` and of finite presentation, and its pullback to the fibre `X_s` is the relative
dualizing sheaf of `X_s` over `κ(s)`, which is the dualizing sheaf of the Gorenstein curve `X_s`,
invertible by Stacks 0BS6.

## Main definitions

* `AlgebraicGeometry.CurveFamily.relativeDualizingSheaf`: the relative dualizing sheaf
  `ω_{X/S} = H^{-1}(ω^•_{X/S})` of a family of curves.

## Main results

* `AlgebraicGeometry.CurveFamily.exists_iso_shift_relativeDualizingComplex`: for a Cohen–Macaulay
  family of relative dimension one, `ω^•_{X/S} = ω_{X/S}[1]` with `ω_{X/S}` flat over `S`.
* `AlgebraicGeometry.CurveFamily.nonempty_relativeDualizingSheaf_iso_modulePullback`: the
  formation of the relative dualizing sheaf commutes with base change.
* `AlgebraicGeometry.CurveFamily.isInvertibleModule_relativeDualizingSheaf_of_base_eq`: the
  relative dualizing sheaf of a Gorenstein curve over a field is invertible.
* `AlgebraicGeometry.CurveFamily.isInvertibleModule_relativeDualizingSheaf`: for a Gorenstein
  family of relative dimension one, `ω_{X/S}` is invertible and commutes with base change.

## Implementation notes

A relative dualizing complex is taken as an argument rather than chosen: relative dualizing
complexes of a proper, flat morphism of finite presentation are unique up to unique isomorphism
(Stacks 0E5Z), so every statement about `ω^•_{X/S}` is a statement about each of them.

Base change is stated along a morphism of families of curves `X' ⟶ X`, a cartesian square over a
morphism of base schemes `S' ⟶ S`: every relative dualizing complex of `X'/S'` is
`L(g')^*(ω_{X/S}[1])`, and `L(g')^*(ω_{X/S}[0]) = (g')^*ω_{X/S}[0]`. The second isomorphism is
stated in the spelling of the module category of the small étale ringed topos in which the
derived pullback is constructed.

## References

* [Stacks Project, Tag 0E6P](https://stacks.math.columbia.edu/tag/0E6P)
* [Stacks Project, Tag 0E6Q](https://stacks.math.columbia.edu/tag/0E6Q)
* [Stacks Project, Tag 0E6R](https://stacks.math.columbia.edu/tag/0E6R)
* [Stacks Project, Tag 0BS6](https://stacks.math.columbia.edu/tag/0BS6)
* [Stacks Project, Tag 0E5Z](https://stacks.math.columbia.edu/tag/0E5Z)
* [Stacks Project, Tag 0E6C](https://stacks.math.columbia.edu/tag/0E6C)
* [Stacks Project, Tag 0DKD](https://stacks.math.columbia.edu/tag/0DKD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry

open Space

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
  RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- The cohomology sheaves of a relative dualizing complex of a Cohen–Macaulay family of curves
vanish outside degree `-1`, and the one in degree `-1` is flat over the base. -/
theorem CurveFamily.isZero_homology_and_isFlatOver_relativeDualizingComplex
    (X : CurveFamily B hZ) (hX : IsCohenMacaulayDimOneFamily B hZ X)
    (D : RelativeDualizingComplex B.contains_terminal X.toBase X.proper X.flat
      X.finitePresentation) :
    (∀ i, i ≠ -1 → IsZero ((DerivedCategory.homologyFunctor _ i).obj D.ω)) ∧
      Space.IsFlatOver B integerBase hZ X.total.2 X.toBase.hom
        ((DerivedCategory.homologyFunctor _ (-1)).obj D.ω) :=
  isZero_homology_and_isFlatOver_of_isZero_homology_residueFibre
    (X.toBase : X.total ⟶ representedSpace X.base) X.flat
    X.finitePresentation.1 D.ω D.isPerfectRelativeTo.1 (-1)
    (CurveFamily.isZero_homology_smallEtaleDerivedModulePullback_residueFibreι X hX D)

/-- Let `f : X ⟶ S` be a family of curves and `(ω^•_{X/S}, τ)` its relative dualizing complex
(Stacks 0E5X). The *relative dualizing sheaf* of `f` is the `𝒪_X`-module
`ω_{X/S} = H^{-1}(ω^•_{X/S})`. For a Cohen–Macaulay family of relative dimension one it is the
pseudo-coherent module flat over `S` of Stacks 0E6P, with `ω^•_{X/S} = ω_{X/S}[1]`
(`AlgebraicGeometry.CurveFamily.exists_iso_shift_relativeDualizingComplex`). -/
@[stacks 0E6Q]
def CurveFamily.relativeDualizingSheaf (X : CurveFamily B hZ)
    (D : RelativeDualizingComplex B.contains_terminal X.toBase X.proper X.flat
      X.finitePresentation) :
    Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2 :=
  (DerivedCategory.homologyFunctor _ (-1)).obj D.ω

/-- A relative dualizing complex has quasi-coherent cohomology sheaves. -/
private theorem qcohDerived_relativeDualizingComplex (X : CurveFamily B hZ)
    (D : RelativeDualizingComplex B.contains_terminal X.toBase X.proper X.flat
      X.finitePresentation) :
    QcohDerived B integerBase hZ X.total D.ω :=
  derivedCategoryB_of_isPseudoCoherent_unconditional B integerBase hZ X.total.1 X.total.2 D.ω
    D.isPerfectRelativeTo.1

/-- Let `f : X ⟶ S` be a family of curves with Cohen–Macaulay fibres equidimensional of
dimension one (Stacks 0E1F: `f` is Cohen–Macaulay in the sense of Stacks 0E0V and has relative
dimension one in the sense of part (2) of Stacks 06LR), and let `(ω^•_{X/S}, τ)` be a relative
dualizing complex of `f` (Stacks 0E5X). Then `ω^•_{X/S} = ω_{X/S}[1]` for a pseudo-coherent
`𝒪_X`-module `ω_{X/S}` flat over `S` whose formation commutes with arbitrary base change: for
every morphism of families of curves `X' ⟶ X` over `S' ⟶ S` (a cartesian square), every relative
dualizing complex of `X'/S'` is `(g'^*ω_{X/S})[1]`, `g' : X' ⟶ X` the projection. -/
@[stacks 0E6P]
theorem CurveFamily.exists_iso_shift_relativeDualizingComplex (X : CurveFamily B hZ)
    (hcm : Space.IsCohenMacaulay B integerBase hZ X.toBase.hom)
    (hdim : Space.HasRelativeDimension 1 B integerBase hZ X.toBase.hom)
    (D : RelativeDualizingComplex B.contains_terminal X.toBase X.proper X.flat
      X.finitePresentation) :
    ∃ F : Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2,
      Nonempty (D.ω ≅ ((DerivedCategory.singleFunctor _ 0).obj F)⟦(1 : ℤ)⟧) ∧
      (Space.smallEtaleRingedSite B integerBase hZ X.total.1 X.total.2).IsPseudoCoherent
        ((DerivedCategory.singleFunctor _ 0).obj F) ∧
      Space.IsFlatOver B integerBase hZ X.total.2 X.toBase.hom F ∧
      ∀ {X' : CurveFamily B hZ} (φ : X' ⟶ X)
        (D' : RelativeDualizingComplex B.contains_terminal X'.toBase X'.proper X'.flat
          X'.finitePresentation),
        Nonempty (D'.ω ≅ (smallEtaleDerivedModulePullback B integerBase hZ φ.totalMap).obj
          (((DerivedCategory.singleFunctor _ 0).obj F)⟦(1 : ℤ)⟧)) ∧
        Nonempty ((smallEtaleDerivedModulePullback B integerBase hZ φ.totalMap).obj
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (ringedToposStructureRingSheaf B integerBase hZ X.total))
                0).obj F) ≅
          (DerivedCategory.singleFunctor
            (SheafOfModules.{u} (ringedToposStructureRingSheaf B integerBase hZ X'.total)) 0).obj
            ((modulePullback B integerBase hZ φ.totalMap).obj F)) := by
  obtain ⟨hvan, hflat⟩ := X.isZero_homology_and_isFlatOver_relativeDualizingComplex ⟨hcm, hdim⟩ D
  have : D.ω.IsGE (-1) := (DerivedCategory.isGE_iff _ _).2 fun i hi => hvan i (by omega)
  have : D.ω.IsLE (-1) := (DerivedCategory.isLE_iff _ _).2 fun i hi => hvan i (by omega)
  obtain ⟨M, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE D.ω (-1)
  let F := (DerivedCategory.homologyFunctor _ (-1)).obj D.ω
  let hM : F ≅ M := (DerivedCategory.homologyFunctor _ (-1)).mapIso e ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso _ (-1)).app M
  let eF : D.ω ≅ ((DerivedCategory.singleFunctor _ 0).obj F)⟦(1 : ℤ)⟧ :=
    e ≪≫ (DerivedCategory.singleFunctor _ (-1)).mapIso hM.symm ≪≫
      (((DerivedCategory.singleFunctors _).shiftIso 1 (-1) 0 (by norm_num)).app F).symm
  have hEq := qcohDerived_relativeDualizingComplex X D
  refine ⟨F, ⟨eF⟩, ?_, hflat, ?_⟩
  · refine (RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom _ _).2 fun m => ?_
    have hω := (RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom _ _).1
      D.isPerfectRelativeTo.1 (m - 1)
    exact (RingedSite.isPseudoCoherentFrom_shift_iff _ m 1 _).1
      (RingedSite.isPseudoCoherentFrom_of_iso _ (m - 1) hω eF.symm)
  · intro X' φ D'
    obtain ⟨e₁, -⟩ := (RelativeDualizingComplex.existsUnique_iso_of_relativeDualizingComplex D'
      (D.baseChange φ.cartesian)).exists
    have : F.IsQuasicoherentOnSite := hEq (-1)
    let pb :=
      (Space.smallEtaleRingedToposHom B integerBase hZ φ.totalMap).toModulesHom.pullbackModules
    have hadd : pb.Additive := RingedToposHom.pullbackModules_additive
      (Space.smallEtaleRingedToposHom B integerBase hZ φ.totalMap)
    have : pb.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive pb
    let K₀ := (CochainComplex.singleFunctor
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B integerBase hZ X.total)) 0).obj F
    have hiso : IsIso ((smallEtaleDerivedModulePullbackComparison B integerBase hZ φ.totalMap).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K₀)) :=
      isIso_smallEtaleDerivedModulePullbackComparison_of_isFlatOver φ.totalMap
        X'.toBase X.toBase (schemeSpaceMap φ.baseMap) φ.cartesian
        (torIndependent_of_isFlat_left X.toBase (schemeSpaceMap φ.baseMap) X.flat) F hflat
    let e₄ : (smallEtaleDerivedModulePullback B integerBase hZ φ.totalMap).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (ringedToposStructureRingSheaf B integerBase hZ X.total)) 0).obj F) ≅
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (ringedToposStructureRingSheaf B integerBase hZ X'.total)) 0).obj
          (pb.obj F) :=
      (smallEtaleDerivedModulePullback B integerBase hZ φ.totalMap).mapIso
          ((DerivedCategory.singleFunctorIsoCompQ _ 0).app F) ≪≫
        (smallEtaleDerivedModulePullback B integerBase hZ φ.totalMap).mapIso
          ((DerivedCategory.quotientCompQhIso _).app K₀).symm ≪≫
        asIso ((smallEtaleDerivedModulePullbackComparison B integerBase hZ φ.totalMap).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K₀)) ≪≫
        (DerivedCategory.quotientCompQhIso _).app _ ≪≫
        (DerivedCategory.Q).mapIso
          ((HomologicalComplex.singleMapHomologicalComplex pb (ComplexShape.up ℤ) 0).app F) ≪≫
        ((DerivedCategory.singleFunctorIsoCompQ _ 0).app _).symm
    have hpb : pb.obj F = (modulePullback B integerBase hZ φ.totalMap).obj F :=
      congrArg (fun h => h.pullbackModules.obj F)
        (smallEtaleRingedToposHom_toModulesHom_eq φ.totalMap)
    exact ⟨⟨e₁ ≪≫ (smallEtaleDerivedModulePullback B integerBase hZ φ.totalMap).mapIso eF⟩,
      ⟨e₄ ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso (eqToIso hpb)⟩⟩

/-- The cohomology sheaf in degree `-1` of `𝒢[0]⟦1⟧` is `𝒢`. -/
def homologyNegOneSingleShiftIso {Z : AlgebraicSpaces B integerBase hZ}
    (G : Space.Modules.{u, u} B integerBase hZ Z.1 Z.2) :
    (DerivedCategory.homologyFunctor _ (-1)).obj
        (((DerivedCategory.singleFunctor _ 0).obj G)⟦(1 : ℤ)⟧) ≅ G :=
  (DerivedCategory.homologyFunctor _ (-1)).mapIso
      (((DerivedCategory.singleFunctors _).shiftIso 1 (-1) 0 (by norm_num)).app G) ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso _ (-1)).app G

/-- **The relative dualizing sheaf commutes with base change.** For a family of curves `X ⟶ S`
with Cohen–Macaulay fibres equidimensional of dimension one and a morphism of families of curves
`X' ⟶ X` over `S' ⟶ S`, the relative dualizing sheaf of `X'/S'` is the pullback of that of
`X/S` along the projection `g' : X' ⟶ X`. This is the base change clause of Stacks 0E6P read in
degree `-1`. -/
theorem CurveFamily.nonempty_relativeDualizingSheaf_iso_modulePullback (X : CurveFamily B hZ)
    (hcm : Space.IsCohenMacaulay B integerBase hZ X.toBase.hom)
    (hdim : Space.HasRelativeDimension 1 B integerBase hZ X.toBase.hom)
    (D : RelativeDualizingComplex B.contains_terminal X.toBase X.proper X.flat
      X.finitePresentation) {X' : CurveFamily B hZ} (φ : X' ⟶ X)
    (D' : RelativeDualizingComplex B.contains_terminal X'.toBase X'.proper X'.flat
      X'.finitePresentation) :
    Nonempty (X'.relativeDualizingSheaf D' ≅
      (modulePullback B integerBase hZ φ.totalMap).obj (X.relativeDualizingSheaf D)) := by
  obtain ⟨F, ⟨eF⟩, -, -, hbc⟩ := X.exists_iso_shift_relativeDualizingComplex hcm hdim D
  obtain ⟨⟨e₁⟩, ⟨e₂⟩⟩ := hbc φ D'
  let L := smallEtaleDerivedModulePullback B integerBase hZ φ.totalMap
  let eF' : X.relativeDualizingSheaf D ≅ F :=
    (DerivedCategory.homologyFunctor _ (-1)).mapIso eF ≪≫ homologyNegOneSingleShiftIso F
  exact ⟨(DerivedCategory.homologyFunctor _ (-1)).mapIso
      (e₁ ≪≫ (L.commShiftIso (1 : ℤ)).app _ ≪≫ (shiftFunctor _ (1 : ℤ)).mapIso e₂) ≪≫
    homologyNegOneSingleShiftIso _ ≪≫
    (modulePullback B integerBase hZ φ.totalMap).mapIso eF'.symm⟩

/-- The cohomology sheaves of an étale derived pullback are the module pullbacks of the cohomology
sheaves. -/
private def homologySmallEtaleDerivedModulePullbackIso {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : AlgebraicSpaces B S hS} (a : X ⟶ Y) (ha : IsEtale B S hS a.hom)
    (E : DerivedCategory (Space.Modules.{u, u} B S hS Y.1 Y.2)) (i : ℤ) :
    (DerivedCategory.homologyFunctor _ i).obj ((smallEtaleDerivedModulePullback B S hS a).obj E) ≅
      (modulePullback B S hS a).obj ((DerivedCategory.homologyFunctor _ i).obj E) :=
  haveI := etaleModulePullback_additive B S hS a ha
  haveI := preservesFiniteLimits_etaleModulePullback B S hS a ha
  haveI := preservesFiniteColimits_etaleModulePullback B S hS a ha
  (DerivedCategory.homologyFunctor _ i).mapIso
      ((smallEtaleDerivedModulePullbackIsoEtale B S hS a ha).app E) ≪≫
    ((etaleModulePullback.{u, u} B S hS a ha).mapDerivedCategoryHomologyIso i).app E ≪≫
    ((modulePullbackIsoEtaleModulePullback B S hS a ha).app _).symm

/-- **A pseudo-coherent module has finitely presented sections over affine charts.** If `𝓕[0]` is
pseudo-coherent, then for an affine étale chart `U` of `X` over an affine open of the base, the
`Γ(U)`-module `Γ(U, 𝓕)` is finitely presented: `RΓ(U, 𝓕[0])` is `(-1)`-pseudo-coherent with
cohomology only in degree `0` (Stacks 08E7), so its cohomology in degree `0` is finitely
presented (Stacks 064S). -/
theorem Space.OpenAffineChartSquare.finitePresentation_chartSections_of_isPseudoCoherent
    {S : Scheme.{u}} {hS : B.Contains S} {T : BigFppfOver B S hS} {X : AlgebraicSpaces B S hS}
    {f : X ⟶ representedSpace T} (c : Space.OpenAffineChartSquare f)
    (F : Space.Modules.{u, u} B S hS X.1 X.2)
    (hpc : (Space.smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent
      ((DerivedCategory.singleFunctor _ 0).obj F)) :
    Module.FinitePresentation Γ(chartScheme c.toChartDiagram.U, ⊤) (c.chartSections F) := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj c.U)) :=
    c.isAffine_U
  let E := (DerivedCategory.singleFunctor (Space.Modules.{u, u} B S hS X.1 X.2) 0).obj F
  have hEq : QcohDerived B S hS X E :=
    derivedCategoryB_of_isPseudoCoherent_unconditional B S hS X.1 X.2 E hpc
  let a := chartToSpace B S hS X c.U
  have ha : IsEtale B S hS a.hom := isEtale_chartToSpace B S hS X c.U
  let E' := (smallEtaleDerivedModulePullback B S hS a).obj E
  have hE' : QcohDerived B S hS (chartSpace B S hS X c.U) E' :=
    derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ a E hEq
  let K := (representedAffineDerivedSections B S hS ((SmallEtale.toOver B S hS X.1).obj c.U)).obj E'
  have hK : StacksDraft.PseudoCoherence.IsPseudoCoherentFrom K (-1) :=
    (isPseudoCoherentFrom_iff_forall_isAffineChart X E hEq (-1)).1
      ((RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom _ E).1 hpc (-1))
      c.U c.isAffine_U
  let eE := homologySmallEtaleDerivedModulePullbackIso a ha E
  have hvan : ∀ i : ℤ, -1 + 1 < i →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj K) := fun i hi => by
    refine (isZero_homology_iff_representedAffineDerivedSections _ E' hE' i).1 ?_
    have h0 : IsZero ((DerivedCategory.homologyFunctor _ i).obj E) :=
      (DerivedCategory.isLE_iff E 0).1 inferInstance i (by omega)
    exact (Functor.map_isZero (modulePullback B S hS a) h0).of_iso (eE i)
  have hfp :=
    PseudoCoherence.finitePresentation_homology_succ_of_isPseudoCoherentFrom K (-1) hK hvan
  show Module.FinitePresentation
    Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj c.U), ⊤)
    ((representedAffineSections B S hS ((SmallEtale.toOver B S hS X.1).obj c.U)).obj
      ((modulePullback B S hS a).obj F))
  let e : (DerivedCategory.homologyFunctor _ (-1 + 1)).obj K ≅
      (representedAffineSections B S hS ((SmallEtale.toOver B S hS X.1).obj c.U)).obj
        ((modulePullback B S hS a).obj F) :=
    representedAffineDerivedSectionsHomologyIso B S hS _ E' hE' 0 ≪≫
      (representedAffineSections B S hS ((SmallEtale.toOver B S hS X.1).obj c.U)).mapIso
        (eE 0 ≪≫ (modulePullback B S hS a).mapIso
          ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app F))
  exact Module.FinitePresentation.of_equiv e.toLinearEquiv

/-- On an algebraic space with no points every module is invertible: all modules vanish. -/
theorem Space.isInvertibleModule_of_isEmpty_points {S : Scheme.{u}} {hS : B.Contains S}
    (Z : AlgebraicSpaces B S hS) [IsEmpty (Space.points B S hS Z.1)]
    (L : Space.Modules.{u, u} B S hS Z.1 Z.2) : Space.IsInvertibleModule Z L := by
  have h0 : ∀ M : Space.Modules.{u, u} B S hS Z.1 Z.2, IsZero M := fun M =>
    isZero_of_supportOfSheaf_eq_empty B S hS Z M (Set.eq_empty_of_isEmpty _)
  exact (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit _).2
    ⟨L, ⟨(h0 _).iso (h0 _)⟩⟩

/-- **The relative dualizing sheaf of a Gorenstein curve over a field is invertible.** Let
`Y ⟶ Spec k` be a family of curves over a field whose total space is Gorenstein and which has
relative dimension one. Then for every relative dualizing complex `ω^•` of `Y` over `Spec k`,
`H^{-1}(ω^•)` is invertible: the total space is a scheme `X` (Stacks 0ADD), on which `ω^•` is the
twisted inverse image `f^×(𝒪_{Spec k})` (Stacks 0E5X, 0E6E and 071Q), the dualizing complex of
Stacks 0BS2, and `ω_X = H^{-1}` of it is invertible for a Gorenstein curve (Stacks 0BS6). -/
theorem CurveFamily.isInvertibleModule_relativeDualizingSheaf_of_base_eq (Y : CurveFamily B hZ)
    (k : Type u) [Field k] (hK : (BigFppfOver.toScheme B integerBase hZ).obj Y.base = Spec (.of k))
    (hG : Space.HasEtaleLocalProperty B integerBase hZ Y.total.obj
      (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsGorenstein T))
    (hY : Space.HasRelativeDimension 1 B integerBase hZ Y.toBase.hom)
    (D : RelativeDualizingComplex B.contains_terminal Y.toBase Y.proper Y.flat
      Y.finitePresentation) :
    Space.IsInvertibleModule Y.total (Y.relativeDualizingSheaf D) := by
  obtain ⟨⟨⟨T₀, hT₀⟩, ⟨⟨⟩⟩, t⟩, total, toBase, hflat, hproper, hfp, hdim⟩ := Y
  change T₀ = Spec (.of k) at hK
  subst hK
  let T : BigFppfOver B integerBase hZ := ⟨⟨Spec (.of k), hT₀⟩, ⟨⟨⟩⟩, t⟩
  have hrep : total.obj.IsRepresentable :=
    CurveFamily.isRepresentable_total_of_base_eq
      ⟨T, total, toBase, hflat, hproper, hfp, hdim⟩ rfl
  let X₀ := total.obj.reprX
  let e : yoneda.obj X₀ ≅ total.obj := total.obj.reprW
  let e' : schemeSpace X₀ ≅ total := (ObjectProperty.fullyFaithfulι _).preimageIso e
  let g₀ : X₀ ⟶ T := Yoneda.fullyFaithful.preimage (e.hom ≫ toBase.hom)
  have hg₀ : yoneda.map g₀ = e.hom ≫ toBase.hom := Yoneda.fullyFaithful.map_preimage _
  have hcomm : e'.hom ≫ toBase = representedSpaceMap B integerBase hZ g₀ ≫ 𝟙 _ := by
    refine ObjectProperty.hom_ext _ ?_
    show e.hom ≫ toBase.hom = yoneda.map g₀ ≫ 𝟙 _
    rw [hg₀]
    exact (Category.comp_id _).symm
  have sq : IsPullback e'.hom (representedSpaceMap B integerBase hZ g₀) toBase (𝟙 _) :=
    @IsPullback.of_horiz_isIso _ _ _ _ _ _ _ _ _ _ inferInstance (IsIso.id _) ⟨hcomm⟩
  have : IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj T) :=
    (inferInstance : IsAffine (Spec (.of k)))
  have hY' : IsAffineSpace B integerBase hZ (schemeSpace T).1 :=
    isAffineSpace_yoneda B integerBase hZ T inferInstance
  have hpr' : Space.IsProper B integerBase hZ (representedSpaceMap B integerBase hZ g₀).hom :=
    (isProper_isStableUnderBaseChange B integerBase hZ).of_isPullback sq hproper
  have hfl' : Space.IsFlat B integerBase hZ (representedSpaceMap B integerBase hZ g₀).hom :=
    (isFlat_isStableUnderBaseChange B integerBase hZ).of_isPullback sq hflat
  have : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g₀) :=
    (isProper_yoneda_map_iff B integerBase hZ g₀).1 hpr'
  have : Flat ((BigFppfOver.toScheme B integerBase hZ).map g₀) :=
    (AlgebraicGeometry.Stack.isFlat_yoneda_map_iff B integerBase hZ g₀).1 hfl'
  have hrdS : Space.HasRelativeDimension 1 B integerBase hZ (schemeSpaceMap g₀).hom := fun x =>
    (holdsOnEveryEtaleChartAtPoint_iso_iff B integerBase hZ (@HasFiberDimensionAt.{u} (1 : ℕ∞))
      e (Iso.refl _) (yoneda.map g₀) toBase.hom
      (by rw [hg₀]; exact (Category.comp_id _).symm) x).2 (hY _)
  have hGX₀ :
      _root_.AlgebraicGeometry.IsGorenstein ((BigFppfOver.toScheme B integerBase hZ).obj X₀) :=
    (Space.exists_atlas_iff_of_representable B integerBase hZ total.obj _ X₀ e.symm).1 hG
  obtain ⟨eω, -⟩ := D.isAffineBaseChangePair (representedSpaceMap B integerBase hZ g₀) (𝟙 _)
    e'.hom sq hY'
  let H₀ := (@DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) (-1)).obj
    ((smallEtaleDerivedModulePullback B integerBase hZ e'.hom).obj D.ω)
  have hpull : Space.IsInvertibleModule (schemeSpace X₀) H₀ := by
    by_cases hne : Nonempty ((BigFppfOver.toScheme B integerBase hZ).obj X₀)
    · obtain ⟨hequi, hdim'⟩ := (hasRelativeDimension_schemeSpaceMap_iff_equidimensional B hZ 1 g₀ k
        rfl inferInstance hne).1 hrdS
      have hXqc := isQuasiCompactSpace_of_isQuasiCompact_hom_of_isAffineSpace B integerBase hZ
        (representedSpaceMap B integerBase hZ g₀)
        (isQuasiCompact_of_isPullback_of_isFinitePresentation sq hfp) hY'
      have hXqs := isAbsolutelyQuasiSeparated_of_isQuasiSeparated_hom_of_isAffineSpace B integerBase
        hZ B.contains_terminal (representedSpaceMap B integerBase hZ g₀)
        (isQuasiSeparated_of_isPullback_of_isFinitePresentation sq hfp) hY'
      have hYqs :=
        isAbsolutelyQuasiSeparated_of_isAffineSpace B integerBase hZ B.contains_terminal hY'
      have hYqc := isQuasiCompactSpace_yoneda_of_isAffine B integerBase hZ T inferInstance
      have hω₀ := (Stacks.Duality.isInvertible_dualizingSheafOverField_of_isGorenstein
        ((BigFppfOver.toScheme B integerBase hZ).map g₀) hGX₀ hequi (by exact_mod_cast hdim')).1
      have hinv : Space.IsInvertibleModule (schemeSpace X₀)
          ((representedZariskiModulePullbackRepresentedZariskiPullbackExact B integerBase hZ X₀).obj
            (Stacks.Duality.dualizingSheafOverField
              ((BigFppfOver.toScheme B integerBase hZ).map g₀))) := by
        have : Stacks.SheafOfModules.IsInvertible
            (representedSchemeRepresentedZariskiRingedToposHom B integerBase hZ
              X₀).zariskiRingedTopos.O.obj
            (Stacks.SheafOfModules.Tensor.ringSheaf
              (representedSchemeRepresentedZariskiRingedToposHom B integerBase hZ
                X₀).zariskiRingedTopos.O).property
            (Stacks.Duality.dualizingSheafOverField
              ((BigFppfOver.toScheme B integerBase hZ).map g₀)) :=
          Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hω₀
        exact Stacks.SheafOfModules.isInvertible_pullbackModules_obj
          (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B integerBase hZ
            X₀).toModulesHom _
      exact isInvertibleModule_of_iso
        ((homologyQuasicoherentDerivedRightAdjointRepresentedSpaceMapIso B.contains_terminal g₀
          hXqc hXqs hYqc hYqs (-1)).symm ≪≫
          (@DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) (-1)).mapIso
            eω.symm) hinv
    · have : IsEmpty ((BigFppfOver.toScheme B integerBase hZ).obj X₀) := not_nonempty_iff.1 hne
      have : IsEmpty (points B integerBase hZ (schemeSpace X₀).1) :=
        (pointsEquivScheme B integerBase hZ X₀).isEmpty
      exact Space.isInvertibleModule_of_isEmpty_points _ _
  have hω : D.ω ≅ (smallEtaleDerivedModulePullback B integerBase hZ e'.inv).obj
      ((smallEtaleDerivedModulePullback B integerBase hZ e'.hom).obj D.ω) :=
    ((smallEtaleDerivedModulePullbackIdIso B integerBase hZ total).app D.ω).symm ≪≫
      (smallEtaleDerivedModulePullbackCongr B integerBase hZ e'.inv_hom_id).symm.app D.ω ≪≫
      ((smallEtaleDerivedModulePullbackCompIso B integerBase hZ e'.inv e'.hom).app D.ω).symm
  have ha : IsEtale B integerBase hZ e'.inv.hom := isEtale_hom_of_isIso B integerBase hZ e'.inv
  let eH : (DerivedCategory.homologyFunctor _ (-1)).obj D.ω ≅
      (modulePullback B integerBase hZ e'.inv).obj H₀ :=
    (DerivedCategory.homologyFunctor _ (-1)).mapIso hω ≪≫
      homologySmallEtaleDerivedModulePullbackIso e'.inv ha _ (-1)
  exact isInvertibleModule_of_iso eH.symm (modulePullbackInvertible e'.inv _ hpull)

/-- **The fibres of a Gorenstein family of curves are Gorenstein.** If the structure morphism of a
family of curves `X ⟶ S` is Gorenstein (Stacks 0E14), then for every point `s ∈ S` the fibre
`X_s` is a Gorenstein algebraic space: on a surjective étale atlas of `X_s` presented by a chart
`U ⟶ S` of `X ⟶ S` it is the scheme theoretic fibre of `U ⟶ S` at `s` (Stacks 0E15). -/
theorem CurveFamily.hasEtaleLocalProperty_isGorenstein_residueFibre (X : CurveFamily B hZ)
    (hG : Space.IsGorenstein B integerBase hZ X.toBase.hom)
    (s : (BigFppfOver.toScheme B integerBase hZ).obj X.base) :
    Space.HasEtaleLocalProperty B integerBase hZ (residueFibre X.toBase s).1
      (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsGorenstein T) := by
  let V := X.base
  let f : X.total.obj ⟶ yoneda.obj V := X.toBase.hom
  let g : yoneda.obj V ⟶ yoneda.obj V := 𝟙 (yoneda.obj V)
  have : IsIso g := IsIso.id _
  have hv : B.Contains (Spec (.of (V.left.1.residueField s))) :=
    B.residueField_spec_contains V.left.property s
  have hYV := isAlgebraicSpace_yoneda B integerBase hZ V
  obtain ⟨U, a, h, comm, haS, haE⟩ :=
    exists_surjective_etale_atlas_over_chart B integerBase hZ X.total.2 hYV f V g
  let a' := a ≫ pullback.fst f g
  have ha' : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B integerBase hZ))) a' :=
    MorphismProperty.RespectsIso.postcomp _ (pullback.fst f g) a haE
  have hb : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B integerBase hZ))) g :=
    (isEtale_iff_presheaf_of_yoneda B integerBase hZ g).1
      (isEtale_hom_of_isIso B integerBase hZ (𝟙 (schemeSpace V)))
  have hcomm : a' ≫ f = yoneda.map h := by
    show (a ≫ pullback.fst f g) ≫ f = _
    rw [Category.assoc, pullback.condition, ← Category.assoc, comm, Category.comp_id]
  have hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map h) :=
    locallyOfFinitePresentation_chartDiagram_g X.toBase X.finitePresentation.1
      (etaleChartDiagramOfFactorization B integerBase hZ X.toBase a'
        ((isEtale_iff_presheaf_of_yoneda B integerBase hZ a').2 ha') h hcomm)
  have hc : ∀ y : (BigFppfOver.toScheme B integerBase hZ).obj V,
      IsLocallyNoetherian (((BigFppfOver.toScheme B integerBase hZ).map h).fiber y) := fun y => by
    have : LocallyOfFiniteType
        (((BigFppfOver.toScheme B integerBase hZ).map h).fiberToSpecResidueField y) := by
      show LocallyOfFiniteType (pullback.snd ((BigFppfOver.toScheme B integerBase hZ).map h)
        (((BigFppfOver.toScheme B integerBase hZ).obj V).fromSpecResidueField y))
      infer_instance
    exact LocallyOfFiniteType.isLocallyNoetherian
      (((BigFppfOver.toScheme B integerBase hZ).map h).fiberToSpecResidueField y)
  have hGh : Space.IsGorenstein B integerBase hZ (yoneda.map h) := fun z =>
    Quot.inductionOn z fun p =>
      (isGorensteinAt_chart_iff B integerBase hZ f U V a' g h ha' hb
        (hcomm.trans (Category.comp_id _).symm) hc p (IsLocalRing.closedPoint _)).2 (hG _)
  have hfib := ((isGorenstein_yoneda_map_iff B integerBase hZ U V h hc).1 hGh).2 s
  have key := (hasEtaleLocalProperty_fiberAt_iff B integerBase hZ X.total.2 hYV f V g U a h comm
    haS haE (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsGorenstein T) s hv).2 hfib
  have hval : yonedaEquiv.symm (chartResidueFieldPoint B integerBase hZ V g s hv).value =
      yonedaEquiv.symm (residueFieldValuedPoint B integerBase hZ V s).value := by
    rw [yonedaEquiv_symm_value_chartResidueFieldPoint, Category.comp_id,
      yonedaEquiv_symm_residueFieldValuedPoint_value]
    exact congrArg yoneda.map ((BigFppfOver.toScheme B integerBase hZ).map_injective
      ((toScheme_map_residueFieldValuedPoint_value s).trans rfl)).symm
  let e := pullback.congrHom (f₁ := f) (f₂ := f) rfl hval
  exact Space.hasEtaleLocalProperty_of_iso B integerBase hZ _ e key

/-- **The relative dualizing sheaf of a Gorenstein family of curves is invertible on the fibres
over fields.** Let `X ⟶ S` be a family of curves which is Gorenstein of relative dimension one
and `r : R ⟶ S` a morphism from the spectrum of a field over which the fibre `X ×_S R` is
Gorenstein. Then the pullback of `ω_{X/S}` to `X ×_S R` is invertible: it is the relative
dualizing sheaf of the base change (Stacks 0E6P), a Gorenstein curve over a field. -/
theorem CurveFamily.isInvertibleModule_modulePullback_pullbackFst_relativeDualizingSheaf
    (X : CurveFamily B hZ) (hX : IsGorensteinDimOneFamily B hZ X)
    (D : RelativeDualizingComplex B.contains_terminal X.toBase X.proper X.flat
      X.finitePresentation)
    {R : BigFppfOver B integerBase hZ} (r : R ⟶ X.base) (k : Type u) [Field k]
    (hR : (BigFppfOver.toScheme B integerBase hZ).obj R = Spec (.of k))
    (hP : IsAlgebraicSpace B integerBase hZ (pullback X.toBase.hom (yoneda.map r)))
    (hGP : Space.HasEtaleLocalProperty B integerBase hZ (pullback X.toBase.hom (yoneda.map r))
      (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsGorenstein T)) :
    Space.IsInvertibleModule (⟨_, hP⟩ : AlgebraicSpaces B integerBase hZ)
      ((modulePullback B integerBase hZ
        (ObjectProperty.homMk (pullback.fst X.toBase.hom (yoneda.map r)) :
          (⟨_, hP⟩ : AlgebraicSpaces B integerBase hZ) ⟶ X.total)).obj
        (X.relativeDualizingSheaf D)) := by
  have hcm := Space.isCohenMacaulay_of_isGorenstein B integerBase hZ hX.1
  obtain ⟨Y, hYR, φ, hφ⟩ :=
    Functor.IsFiberedInGroupoids.exists_lift_eqToHom (curvesFiberedCategory B hZ).2 X r
  change Y.base = R at hYR
  subst hYR
  have hr : r = φ.baseMap := by
    have h : eqToHom (rfl : Y.base = Y.base) ≫ r = φ.baseMap := hφ.symm
    rw [eqToHom_refl, Category.id_comp] at h
    exact h
  subst hr
  have hYdim : Space.HasRelativeDimension 1 B integerBase hZ Y.toBase.hom := fun x =>
    (CurveFamily.hasRelativeDimensionAt_iff_hom B hZ φ _ x).mpr (hX.2 _)
  have hpb := AlgebraicSpaces.isPullback_hom B integerBase hZ φ.cartesian
  let j := hpb.isoPullback
  let P : AlgebraicSpaces B integerBase hZ := ⟨_, hP⟩
  let j' : Y.total ≅ P := (ObjectProperty.fullyFaithfulι _).preimageIso j
  have hj : j'.inv ≫ φ.totalMap = ObjectProperty.homMk (pullback.fst X.toBase.hom
      (yoneda.map φ.baseMap)) := by
    refine ObjectProperty.hom_ext _ ?_
    show j.inv ≫ φ.totalMap.hom = pullback.fst _ _
    exact hpb.isoPullback_inv_fst
  have hinv := Y.isInvertibleModule_relativeDualizingSheaf_of_base_eq k hR
    (Space.hasEtaleLocalProperty_of_iso B integerBase hZ _ j.symm hGP) hYdim
    (D.baseChange φ.cartesian)
  obtain ⟨eY⟩ := X.nonempty_relativeDualizingSheaf_iso_modulePullback hcm hX.2 D φ
    (D.baseChange φ.cartesian)
  let e : (modulePullback B integerBase hZ
        (ObjectProperty.homMk (pullback.fst X.toBase.hom (yoneda.map φ.baseMap)) :
          P ⟶ X.total)).obj (X.relativeDualizingSheaf D) ≅
      (modulePullback B integerBase hZ j'.inv).obj
        (Y.relativeDualizingSheaf (D.baseChange φ.cartesian)) :=
    eqToIso (congrArg (fun ψ => (modulePullback B integerBase hZ ψ).obj
        (X.relativeDualizingSheaf D)) hj.symm) ≪≫
      ((modulePullbackCompIso B integerBase hZ j'.inv φ.totalMap).app _).symm ≪≫
      (modulePullback B integerBase hZ j'.inv).mapIso eY.symm
  exact isInvertibleModule_of_iso e.symm (modulePullbackInvertible j'.inv _ hinv)

/-- **The relative dualizing sheaf of a Gorenstein family of curves is invertible on the
fibres.** For every point `s` of the base, the pullback of `ω_{X/S}` to the fibre `X_s` is
invertible. -/
theorem CurveFamily.isInvertibleModule_modulePullback_residueFibre_relativeDualizingSheaf
    (X : CurveFamily B hZ) (hX : IsGorensteinDimOneFamily B hZ X)
    (D : RelativeDualizingComplex B.contains_terminal X.toBase X.proper X.flat
      X.finitePresentation)
    (s : (BigFppfOver.toScheme B integerBase hZ).obj X.base) :
    Space.IsInvertibleModule (residueFibre X.toBase s)
      ((modulePullback B integerBase hZ (residueFibreι X.toBase s)).obj
        (X.relativeDualizingSheaf D)) :=
  X.isInvertibleModule_modulePullback_pullbackFst_relativeDualizingSheaf hX D
    (residueFieldValuedPoint B integerBase hZ X.base s).value _ rfl _
    (X.hasEtaleLocalProperty_isGorenstein_residueFibre hX.1 s)

/-- Let `f : X ⟶ S` be a family of curves with Gorenstein fibres equidimensional of dimension
one (`Curves^{Gorenstein, 1}` of Stacks 0E6M: `f` is Gorenstein in the sense of Stacks 0E14 and
has relative dimension one in the sense of part (2) of Stacks 06LR), and let `(ω^•_{X/S}, τ)` be
a relative dualizing complex (Stacks 0E5X). Then the relative dualizing sheaf
`ω_{X/S} = H^{-1}(ω^•_{X/S})` (Stacks 0E6Q) is an invertible `𝒪_X`-module, and its formation
commutes with arbitrary base change: for every morphism of families of curves `X' ⟶ X` over
`S' ⟶ S` (a cartesian square) and every relative dualizing complex of `X'/S'`, the relative
dualizing sheaf of `X'/S'` is the pullback of `ω_{X/S}` along the projection `g' : X' ⟶ X`. -/
@[stacks 0E6R]
theorem CurveFamily.isInvertibleModule_relativeDualizingSheaf (X : CurveFamily B hZ)
    (hX : IsGorensteinDimOneFamily B hZ X)
    (D : RelativeDualizingComplex B.contains_terminal X.toBase X.proper X.flat
      X.finitePresentation) :
    Space.IsInvertibleModule X.total (X.relativeDualizingSheaf D) ∧
      ∀ {X' : CurveFamily B hZ} (φ : X' ⟶ X)
        (D' : RelativeDualizingComplex B.contains_terminal X'.toBase X'.proper X'.flat
          X'.finitePresentation),
        Nonempty (X'.relativeDualizingSheaf D' ≅
          (modulePullback B integerBase hZ φ.totalMap).obj (X.relativeDualizingSheaf D)) := by
  have hcm := Space.isCohenMacaulay_of_isGorenstein B integerBase hZ hX.1
  refine ⟨?_, fun φ D' => X.nonempty_relativeDualizingSheaf_iso_modulePullback hcm hX.2 D φ D'⟩
  obtain ⟨F, ⟨eF⟩, hpc, hflat, -⟩ := X.exists_iso_shift_relativeDualizingComplex hcm hX.2 D
  let eF' : X.relativeDualizingSheaf D ≅ F :=
    (DerivedCategory.homologyFunctor _ (-1)).mapIso eF ≪≫ homologyNegOneSingleShiftIso F
  have hFq : F.IsQuasicoherentOnSite :=
    SheafOfModules.IsQuasicoherentOnSite.of_iso eF' (qcohDerived_relativeDualizingComplex X D (-1))
  exact isInvertibleModule_of_iso eF'.symm
    (Space.isInvertibleModule_of_isInvertibleModule_residueFibre F hFq hflat
      (fun c => c.finitePresentation_chartSections_of_isPseudoCoherent F hpc) fun s =>
        isInvertibleModule_of_iso ((modulePullback B integerBase hZ _).mapIso eF')
          (X.isInvertibleModule_modulePullback_residueFibre_relativeDualizingSheaf hX D s))

end AlgebraicGeometry

end
