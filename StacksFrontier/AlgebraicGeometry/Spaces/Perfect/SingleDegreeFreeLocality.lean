module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegree
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SingleDegreeFreeCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRepresentableBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.IteratedSliceFiniteFreeSummands
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.IntervalDescent

/-!
# Being a locally free module placed in one degree is étale local

Let `Y` be an algebraic space and `K` an object of `D(𝒪_Y)`. Then `K` is a finite locally free
module of rank `r` placed in degree `i` if and only if every point of `Y` lies in the image of an
étale chart `V` such that the derived restriction of `K` to `V` is `𝒪_V^{⊕r}[-i]`.

## Main results

* `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackSingleIsoOfIsEtale`: for `f` étale,
  `Lf^*(M[-i]) = (f^*M)[-i]`.
* `AlgebraicGeometry.Space.chartModuleSliceReindexFreeIso`: reading a free module on the slice at
  a chart as a module on the chart gives the free module.
* `AlgebraicGeometry.Space.isFiniteLocallyFreeOfIntRankInDegree_iff`: the locality statement.
* `AlgebraicGeometry.Space.exists_isFreeOfRankInDegree_chart_of_mem_singleDegreeFreePoints`:
  free charts of `E` pull back to free charts of `Lf^*E`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- For `f` étale, the derived pullback of a module placed in degree `i` is its pullback placed
in degree `i`. -/
def smallEtaleDerivedModulePullbackSingleIsoOfIsEtale {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsEtale B S hS f.hom)
    (M : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (i : ℤ) :
    (smallEtaleDerivedModulePullback B S hS f).obj
        ((DerivedCategory.singleFunctor _ i).obj M) ≅
      (DerivedCategory.singleFunctor _ i).obj ((modulePullback B S hS f).obj M) :=
  have := modulePullback_additive f
  (smallEtaleDerivedModulePullback B S hS f).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ _ i).app M) ≪≫
    smallEtaleDerivedModulePullbackObjQIsoOfIsEtale f hf _ ≪≫
    (DerivedCategory.Q).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex (modulePullback B S hS f)
        (ComplexShape.up ℤ) i).app M) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ _ i).app _).symm

variable (B S hS) (X : AlgebraicSpaces B S hS)

/-- Reading the unit module of the slice at a chart as a module on the chart gives the unit
module. -/
def chartModuleSliceReindexUnitIsoModulePullback (V : SmallEtale B S hS X.1) :
    (chartModuleSliceReindex B S hS X V).obj
        (SheafOfModules.unit ((structureRingSheaf B S hS X).over V)) ≅
      SheafOfModules.unit (structureRingSheaf B S hS (chartSpace B S hS X V)) :=
  (chartModuleRestrictionSliceIso B S hS X V).symm.app
      (SheafOfModules.unit (structureRingSheaf B S hS X)) ≪≫
    modulePullbackUnitIso B S hS (chartToSpace B S hS X V)

/-- Reading a free module on the slice at a chart as a module on the chart gives the free
module on the same type. -/
def chartModuleSliceReindexFreeIso (V : SmallEtale B S hS X.1) (I : Type u) :
    (chartModuleSliceReindex B S hS X V).obj
        (SheafOfModules.free (R := (structureRingSheaf B S hS X).over V) I) ≅
      SheafOfModules.free (R := structureRingSheaf B S hS (chartSpace B S hS X V)) I :=
  Stacks.SheafOfModules.inverseFreeIso (chartModuleSliceEquiv B S hS X V).symm
    (chartModuleSliceReindexUnitIsoModulePullback B S hS X V) I

/-- The restriction of a module to the slice at a chart, recovered from its restriction to the
chart through the inverse of the comparison equivalence. -/
def overIsoChartModuleSliceEquivInverse (V : SmallEtale B S hS X.1)
    (N : SheafOfModules.{u} (structureRingSheaf B S hS X)) :
    N.over V ≅ (chartModuleSliceEquiv B S hS X V).inverse.obj
      ((modulePullback B S hS (chartToSpace B S hS X V)).obj N) :=
  (chartModuleSliceEquiv B S hS X V).unitIso.app (N.over V) ≪≫
    (chartModuleSliceEquiv B S hS X V).inverse.mapIso
      ((chartModuleRestrictionSliceIso B S hS X V).app N).symm

/-- A module whose restriction to a chart vanishes vanishes on the slice at that chart. -/
theorem isZero_over_of_isZero_modulePullback (V : SmallEtale B S hS X.1)
    (N : SheafOfModules.{u} (structureRingSheaf B S hS X))
    (h : IsZero ((modulePullback B S hS (chartToSpace B S hS X V)).obj N)) :
    IsZero (N.over V) :=
  ((chartModuleSliceEquiv B S hS X V).inverse.map_isZero h).of_iso
    (overIsoChartModuleSliceEquivInverse B S hS X V N)

/-- A module whose restriction to a chart is free is free on the slice at that chart. -/
def overFreeIsoOfModulePullback (V : SmallEtale B S hS X.1)
    (N : SheafOfModules.{u} (structureRingSheaf B S hS X)) (I : Type u)
    (e : (modulePullback B S hS (chartToSpace B S hS X V)).obj N ≅
      SheafOfModules.free (R := structureRingSheaf B S hS (chartSpace B S hS X V)) I) :
    SheafOfModules.free (R := (structureRingSheaf B S hS X).over V) I ≅ N.over V :=
  (chartModuleSliceEquiv B S hS X V).unitIso.app _ ≪≫
    (chartModuleSliceEquiv B S hS X V).inverse.mapIso
      (chartModuleSliceReindexFreeIso B S hS X V I ≪≫ e.symm) ≪≫
    (overIsoChartModuleSliceEquivInverse B S hS X V N).symm

/-- **Being a finite locally free module of rank `r` placed in degree `i` is étale local.** An
object `K` of `D(𝒪_Y)` has this shape exactly when every point of `Y` lies in the image of an
étale chart `V` on which the derived restriction of `K` is `𝒪_V^{⊕r}[-i]`. -/
theorem isFiniteLocallyFreeOfIntRankInDegree_iff
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (i r : ℤ) :
    IsFiniteLocallyFreeOfIntRankInDegree B S hS X K i r ↔
      ∀ y : points B S hS X.1, ∃ V : SmallEtale B S hS X.1,
        y ∈ Set.range (pointsMap B S hS (yoneda.obj V.1.left) V.1.hom) ∧
          IsFreeOfRankInDegree
            ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X V)).obj K) i r := by
  constructor
  · rintro ⟨M, ⟨q, hq, hrk⟩, ⟨e⟩⟩ y
    obtain ⟨k, hk⟩ := SmallEtale.exists_mem_range_of_coversTop B S hS X.2 q.coversTop y
    obtain ⟨n, hn, ⟨σ⟩⟩ := hrk k
    let V := q.X k
    let ψ := chartToSpace B S hS X V
    let Fr := chartModuleSliceReindex B S hS X V
    let eM : (modulePullback B S hS ψ).obj M ≅
        SheafOfModules.free (R := structureRingSheaf B S hS (chartSpace B S hS X V))
          (ULift.{u} (Fin n)) :=
      (chartModuleRestrictionSliceIso B S hS X V).app M ≪≫
        Fr.mapIso ((asIso (q.generators k).π).symm ≪≫
          (SheafOfModules.freeFunctor (R := (structureRingSheaf B S hS X).over V)).mapIso
            (σ.trans Equiv.ulift.symm).toIso) ≪≫
        chartModuleSliceReindexFreeIso B S hS X V _
    exact ⟨V, hk, n, hn, ⟨(smallEtaleDerivedModulePullback B S hS ψ).mapIso e ≪≫
      smallEtaleDerivedModulePullbackSingleIsoOfIsEtale ψ (isEtale_chartToSpace B S hS X V) M i ≪≫
      (DerivedCategory.singleFunctor _ i).mapIso eM⟩⟩
  · intro h
    choose V hV hfree using h
    have hcov : (SmallEtale.topology B S hS X.1).CoversTop V :=
      SmallEtale.coversTop_of_forall_mem_range B S hS fun y => ⟨y, hV y⟩
    let H : ℤ → SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X) := fun j =>
      (DerivedCategory.homologyFunctor _ j).obj K
    -- the restriction of `H j` to the chart `V y` is the `j`-th cohomology of a free module
    -- placed in degree `i`
    have hloc : ∀ (y : points B S hS X.1) (j : ℤ), ∃ n : ℕ, (n : ℤ) = r ∧
        Nonempty ((modulePullback B S hS (chartToSpace B S hS X (V y))).obj (H j) ≅
          (DerivedCategory.homologyFunctor (SheafOfModules.{u}
            (ringedToposStructureRingSheaf B S hS (chartSpace B S hS X (V y)))) j).obj
            ((DerivedCategory.singleFunctor (SheafOfModules.{u}
              (ringedToposStructureRingSheaf B S hS (chartSpace B S hS X (V y)))) i).obj
            (SheafOfModules.free
              (R := ringedToposStructureRingSheaf B S hS (chartSpace B S hS X (V y)))
              (ULift.{u} (Fin n))))) := by
      intro y j
      obtain ⟨n, hn, ⟨e⟩⟩ := hfree y
      exact ⟨n, hn, ⟨(smallEtaleDerivedModulePullbackHomologyIsoOfIsEtale _
        (isEtale_chartToSpace B S hS X (V y)) K j).symm ≪≫
          (DerivedCategory.homologyFunctor _ j).mapIso e⟩⟩
    have hzero : ∀ j, j ≠ i → IsZero (H j) := by
      intro j hj
      refine Stacks.SheafOfModules.isZero_of_coversTop hcov _ fun y => ?_
      refine isZero_over_of_isZero_modulePullback B S hS X (V y) _ ?_
      obtain ⟨n, -, ⟨e⟩⟩ := hloc y j
      refine IsZero.of_iso ?_ e
      rcases lt_or_gt_of_ne hj with hlt | hlt
      · exact DerivedCategory.isZero_of_isGE (C := SheafOfModules.{u}
          (ringedToposStructureRingSheaf B S hS (chartSpace B S hS X (V y)))) _ i j hlt
      · exact DerivedCategory.isZero_of_isLE (C := SheafOfModules.{u}
          (ringedToposStructureRingSheaf B S hS (chartSpace B S hS X (V y)))) _ i j hlt
    refine ⟨H i, AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfIntRank_of_coversTop hcov
      (H i) r fun y => ?_,
      DerivedCategory.nonempty_iso_singleFunctor_homologyFunctor_of_isZero K i hzero⟩
    obtain ⟨n, hn, ⟨e'⟩⟩ := hloc y i
    exact ⟨n, hn, ⟨overFreeIsoOfModulePullback B S hS X (V y) (H i) _
      (e' ≪≫ (DerivedCategory.singleFunctorCompHomologyFunctorIso _ i).app _)⟩⟩

/-- **Free charts pull back.** Let `f : Y ⟶ X` and let `y` be a point of `Y` whose image lies
in the image of an étale chart of `X` on which `E` is free of rank `r` in degree `i`. Then `y`
lies in the image of an étale chart of `Y` on which `Lf^*E` is free of rank `r` in degree `i`. -/
theorem exists_isFreeOfRankInDegree_chart_of_mem_singleDegreeFreePoints {Y : AlgebraicSpaces B S hS}
    (f : Y ⟶ X)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (i r : ℤ) (y : points B S hS Y.1)
    (hy : pointsMap B S hS Y.1 f.hom y ∈ singleDegreeFreePoints B S hS E i r) :
    ∃ T : SmallEtale B S hS Y.1,
      y ∈ Set.range (pointsMap B S hS (yoneda.obj T.1.left) T.1.hom) ∧
        IsFreeOfRankInDegree ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS Y T)).obj
          ((smallEtaleDerivedModulePullback B S hS f).obj E)) i r := by
  obtain ⟨V, hyV, hV⟩ := hy
  obtain ⟨T, h, hyT, hw⟩ := exists_smallEtale_chart_lift B S hS Y.2 f.hom V y hyV
  have hcomp : chartToSpace B S hS Y T ≫ f =
      representedSpaceMap B S hS h ≫ chartToSpace B S hS X V :=
    InducedCategory.hom_ext hw.symm
  exact ⟨T, hyT, (hV.derivedPullback (representedSpaceMap B S hS h)).of_iso
    ((smallEtaleDerivedModulePullbackCompIso B S hS (representedSpaceMap B S hS h)
      (chartToSpace B S hS X V)).app E ≪≫
    (smallEtaleDerivedModulePullbackCongr B S hS hcomp.symm).app E ≪≫
    ((smallEtaleDerivedModulePullbackCompIso B S hS (chartToSpace B S hS Y T) f).app E).symm)⟩

end AlgebraicGeometry.Space

end
