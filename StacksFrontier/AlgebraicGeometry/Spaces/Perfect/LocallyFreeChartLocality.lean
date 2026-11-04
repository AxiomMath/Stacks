module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SingleDegreeFreeLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePostcomp

/-!
# Finite local freeness of a module on an algebraic space is étale local

Let `Y` be an algebraic space and `M` an `𝒪_Y`-module on its small étale site. Then `M` is finite
locally free of rank `r` if and only if every point of `Y` lies in the image of an étale chart
`V` on which the restriction of `M` is free of rank `r`; and it suffices that the restriction of
`M` to the members of a family of étale charts covering `Y` be finite locally free of rank `r`.

## Main results

* `AlgebraicGeometry.Space.isFiniteLocallyFreeOfIntRank_iff_forall_chart`: the chart criterion.
* `AlgebraicGeometry.Space.isFiniteLocallyFreeOfIntRank_of_forall_chart`: local freeness on
  charts covering `Y` gives local freeness on `Y`.
* `AlgebraicGeometry.Space.isFiniteLocallyFreeOfIntRank_modulePullback_chartToSpace`: local
  freeness restricts to every chart.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {Y : AlgebraicSpaces B S hS}

/-- The structure morphism of a chart of a chart, read as a chart of the ambient space, is the
composite of the two structure morphisms. -/
theorem chartToSpace_smallEtalePostcomp (V : SmallEtale B S hS Y.1)
    (A : SmallEtale B S hS (chartSpace B S hS Y V).1) :
    chartToSpace B S hS Y ((smallEtalePostcomp B S hS (chartToSpace B S hS Y V)
        (isEtale_chartToSpace B S hS Y V)).obj A) =
      chartToSpace B S hS (chartSpace B S hS Y V) A ≫ chartToSpace B S hS Y V :=
  rfl

/-- Restricting a module to a chart of a chart is restricting it to the composite chart. -/
def modulePullbackChartChartIso (V : SmallEtale B S hS Y.1)
    (A : SmallEtale B S hS (chartSpace B S hS Y V).1)
    (M : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) :
    (modulePullback B S hS (chartToSpace B S hS Y ((smallEtalePostcomp B S hS
        (chartToSpace B S hS Y V) (isEtale_chartToSpace B S hS Y V)).obj A))).obj M ≅
      (modulePullback B S hS (chartToSpace B S hS (chartSpace B S hS Y V) A)).obj
        ((modulePullback B S hS (chartToSpace B S hS Y V)).obj M) :=
  ((modulePullbackCompIso B S hS (chartToSpace B S hS (chartSpace B S hS Y V) A)
    (chartToSpace B S hS Y V)).app M).symm

/-- A module whose restriction to the slice at a chart is free has free restriction to the
chart. -/
def modulePullbackFreeIsoOfOverIso (V : SmallEtale B S hS Y.1)
    (M : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (I : Type u)
    (e : SheafOfModules.free (R := (structureRingSheaf B S hS Y).over V) I ≅ M.over V) :
    (modulePullback B S hS (chartToSpace B S hS Y V)).obj M ≅
      SheafOfModules.free (R := structureRingSheaf B S hS (chartSpace B S hS Y V)) I :=
  (chartModuleRestrictionSliceIso B S hS Y V).app M ≪≫
    (chartModuleSliceReindex B S hS Y V).mapIso e.symm ≪≫
    chartModuleSliceReindexFreeIso B S hS Y V I

/-- **The chart criterion for finite local freeness.** A module `M` on an algebraic space `Y` is
finite locally free of rank `r` if and only if every point of `Y` lies in the image of an étale
chart on which `M` restricts to `𝒪^{⊕r}`. -/
theorem isFiniteLocallyFreeOfIntRank_iff_forall_chart
    (M : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (r : ℤ) :
    SheafOfModules.IsFiniteLocallyFreeOfIntRank M r ↔
      ∀ y : points B S hS Y.1, ∃ V : SmallEtale B S hS Y.1,
        y ∈ Set.range (pointsMap B S hS (yoneda.obj V.1.left) V.1.hom) ∧
          ∃ n : ℕ, (n : ℤ) = r ∧ Nonempty ((modulePullback B S hS (chartToSpace B S hS Y V)).obj M ≅
            SheafOfModules.free (R := structureRingSheaf B S hS (chartSpace B S hS Y V))
              (ULift.{u} (Fin n))) := by
  constructor
  · rintro ⟨q, hq, hrk⟩ y
    obtain ⟨k, hk⟩ := SmallEtale.exists_mem_range_of_coversTop B S hS Y.2 q.coversTop y
    obtain ⟨n, hn, ⟨σ⟩⟩ := hrk k
    refine ⟨q.X k, hk, n, hn, ⟨modulePullbackFreeIsoOfOverIso B S hS (q.X k) M _
      ((SheafOfModules.freeFunctor (R := (structureRingSheaf B S hS Y).over (q.X k))).mapIso
          (σ.trans Equiv.ulift.symm).toIso.symm ≪≫
        @asIso _ _ _ _ (q.generators k).π (hq.isIso k))⟩⟩
  · intro h
    choose V hV n hn e using h
    exact SheafOfModules.isFiniteLocallyFreeOfIntRank_of_coversTop
      (SmallEtale.coversTop_of_forall_mem_range B S hS fun y => ⟨y, hV y⟩) M r fun y =>
        ⟨n y, hn y, ⟨overFreeIsoOfModulePullback B S hS Y (V y) M _ (e y).some⟩⟩

/-- **Finite local freeness restricts to charts.** -/
theorem isFiniteLocallyFreeOfIntRank_modulePullback_chartToSpace
    (M : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (r : ℤ)
    (hM : SheafOfModules.IsFiniteLocallyFreeOfIntRank M r) (V : SmallEtale B S hS Y.1) :
    SheafOfModules.IsFiniteLocallyFreeOfIntRank
      ((modulePullback B S hS (chartToSpace B S hS Y V)).obj M) r := by
  refine (isFiniteLocallyFreeOfIntRank_iff_forall_chart B S hS
    (Y := chartSpace B S hS Y V) _ r).2 fun v => ?_
  obtain ⟨W, hW, n, hn, ⟨e⟩⟩ := (isFiniteLocallyFreeOfIntRank_iff_forall_chart B S hS M r).1 hM
    (pointsMap B S hS _ (chartToSpace B S hS Y V).hom v)
  obtain ⟨T, h, hvT, hw⟩ := exists_smallEtale_chart_lift B S hS (chartSpace B S hS Y V).2
    (chartToSpace B S hS Y V).hom W v hW
  have hcomp : chartToSpace B S hS (chartSpace B S hS Y V) T ≫ chartToSpace B S hS Y V =
      representedSpaceMap B S hS h ≫ chartToSpace B S hS Y W :=
    InducedCategory.hom_ext hw.symm
  refine ⟨T, hvT, n, hn, ⟨?_⟩⟩
  exact (modulePullbackCompIso B S hS _ _).app M ≪≫
    eqToIso (congrArg (fun g => (modulePullback B S hS g).obj M) hcomp) ≪≫
    ((modulePullbackCompIso B S hS _ _).app M).symm ≪≫
    (modulePullback B S hS (representedSpaceMap B S hS h)).mapIso e ≪≫
    ((pullbackModulesIsoModulePullback B S hS (representedSpaceMap B S hS h)).app _).symm ≪≫
    (RingedToposHom.pullbackModulesFreeIso
      (X := smallEtaleRingedTopos B S hS (chartSpace B S hS (chartSpace B S hS Y V) T))
      (Y := smallEtaleRingedTopos B S hS (chartSpace B S hS Y W))
      (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS h)) _).symm

/-- **Finite local freeness on charts covering the space gives finite local freeness.** -/
theorem isFiniteLocallyFreeOfIntRank_of_forall_chart
    (M : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (r : ℤ)
    (h : ∀ y : points B S hS Y.1, ∃ V : SmallEtale B S hS Y.1,
      y ∈ Set.range (pointsMap B S hS (yoneda.obj V.1.left) V.1.hom) ∧
        SheafOfModules.IsFiniteLocallyFreeOfIntRank
          ((modulePullback B S hS (chartToSpace B S hS Y V)).obj M) r) :
    SheafOfModules.IsFiniteLocallyFreeOfIntRank M r := by
  refine (isFiniteLocallyFreeOfIntRank_iff_forall_chart B S hS M r).2 fun y => ?_
  obtain ⟨V, ⟨v, rfl⟩, hV⟩ := h y
  obtain ⟨A, ⟨a, rfl⟩, n, hn, ⟨e⟩⟩ := (isFiniteLocallyFreeOfIntRank_iff_forall_chart B S hS
    (Y := chartSpace B S hS Y V) _ r).1 hV v
  refine ⟨(smallEtalePostcomp B S hS (chartToSpace B S hS Y V)
    (isEtale_chartToSpace B S hS Y V)).obj A, ⟨a, ?_⟩, n, hn,
    ⟨modulePullbackChartChartIso B S hS V A M ≪≫ e⟩⟩
  exact pointsMap_comp_apply B S hS A.1.hom V.1.hom a

/-- Finite local freeness of an integer rank is invariant under isomorphism. -/
theorem isFiniteLocallyFreeOfIntRank_of_iso
    {M M' : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)} (e : M ≅ M') {r : ℤ}
    (hM : SheafOfModules.IsFiniteLocallyFreeOfIntRank M r) :
    SheafOfModules.IsFiniteLocallyFreeOfIntRank M' r := by
  refine (isFiniteLocallyFreeOfIntRank_iff_forall_chart B S hS M' r).2 fun y => ?_
  obtain ⟨V, hV, n, hn, ⟨e'⟩⟩ := (isFiniteLocallyFreeOfIntRank_iff_forall_chart B S hS M r).1 hM y
  exact ⟨V, hV, n, hn, ⟨(modulePullback B S hS (chartToSpace B S hS Y V)).mapIso e.symm ≪≫ e'⟩⟩

attribute [local instance 10000] HasDerivedCategory.standard

/-- The cohomology of the derived pullback along a chart composed with `f` is the restriction to
the chart of the cohomology of the derived pullback along `f`. -/
def homologyDerivedPullbackChartIso {X : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) (a : ℤ)
    (V : SmallEtale B S hS Y.1) :
    (DerivedCategory.homologyFunctor (SheafOfModules.{u}
        (ringedToposStructureRingSheaf B S hS (chartSpace B S hS Y V))) a).obj
        ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS Y V ≫ f)).obj E) ≅
      (modulePullback B S hS (chartToSpace B S hS Y V)).obj
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) a).obj
          ((smallEtaleDerivedModulePullback B S hS f).obj E)) :=
  (DerivedCategory.homologyFunctor (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS (chartSpace B S hS Y V))) a).mapIso
      ((smallEtaleDerivedModulePullbackCompIso B S hS (chartToSpace B S hS Y V) f).app E).symm ≪≫
    smallEtaleDerivedModulePullbackHomologyIsoOfIsEtale _ (isEtale_chartToSpace B S hS Y V) _ a

/-- **Finite local freeness of `H^a(Lf^*E)` is étale local on the source.** -/
theorem isFiniteLocallyFreeOfIntRank_homology_iff_forall_chart {X : AlgebraicSpaces B S hS}
    (f : Y ⟶ X)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (a r : ℤ) :
    SheafOfModules.IsFiniteLocallyFreeOfIntRank ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) a).obj
        ((smallEtaleDerivedModulePullback B S hS f).obj E)) r ↔
      ∀ y : points B S hS Y.1, ∃ V : SmallEtale B S hS Y.1,
        y ∈ Set.range (pointsMap B S hS (yoneda.obj V.1.left) V.1.hom) ∧
          SheafOfModules.IsFiniteLocallyFreeOfIntRank ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u}
              (ringedToposStructureRingSheaf B S hS (chartSpace B S hS Y V))) a).obj
            ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS Y V ≫ f)).obj E)) r := by
  constructor
  · intro h y
    obtain ⟨V, hV, -⟩ := (isFiniteLocallyFreeOfIntRank_iff_forall_chart B S hS _ r).1 h y
    exact ⟨V, hV, isFiniteLocallyFreeOfIntRank_of_iso B S hS
      (homologyDerivedPullbackChartIso B S hS f E a V).symm
      (isFiniteLocallyFreeOfIntRank_modulePullback_chartToSpace B S hS _ r h V)⟩
  · intro h
    refine isFiniteLocallyFreeOfIntRank_of_forall_chart B S hS _ r fun y => ?_
    obtain ⟨V, hV, hfree⟩ := h y
    exact ⟨V, hV, isFiniteLocallyFreeOfIntRank_of_iso B S hS
      (homologyDerivedPullbackChartIso B S hS f E a V) hfree⟩

end AlgebraicGeometry.Space
