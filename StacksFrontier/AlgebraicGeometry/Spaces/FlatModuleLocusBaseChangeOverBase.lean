module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.FlatLocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionEtalePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartwiseConditionsFromSite
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleLocusOverBase
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteOfFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatLocusBaseChange

/-!
# Base change of the flat locus of a module in a triangle of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` whose source and target are given
over a third algebraic space `Z` by `f ≫ q : X ⟶ Z` and `q : Y ⟶ Z`, and let `𝓕` be a
quasi-coherent `𝒪_X`-module.  Assume `X` is locally of finite presentation over `Z`, that `𝓕`
is of finite presentation, that `𝓕` is flat over `Z`, and that `Y` is locally of finite type
over `Z`.  The locus `A ⊆ |X|` of points at which `𝓕` is flat over `Y` then commutes with an
arbitrary base change `Z' ⟶ Z`: writing `X' = X ×_Z Z'`, `Y' = Y ×_Z Z'` and `𝓕'` for the
inverse image of `𝓕`, the locus of points of `|X'|` at which `𝓕'` is flat over `Y'` is the
inverse image of `A` under `|X'| ⟶ |X|`.

## Main results

* `AlgebraicGeometry.Space.flatLocus_modulePullback_eq_preimage_of_isFlatOverBase` is the
  base-change assertion of **Stacks 05X2**.  The openness assertion of that lemma is
  `AlgebraicGeometry.Space.isOpen_flatLocus_of_isLocallyOfFinitePresentation_comp`.
* `AlgebraicGeometry.Space.nonempty_restrictToChart_iso_restrictToChartScheme` identifies the
  two parallel readings of the restriction of a quasi-coherent module to an étale scheme chart.

## Implementation notes

The proof is the one the source gives: reduce to schemes.  The scheme-level statement is
`AlgebraicGeometry.setOf_isFlatOverAt_modulePullback_of_isFlatOver`, Stacks 05VJ, and it asks
for a *stacked* pair of cartesian squares of schemes — a chart of `Y'` over a chart of `Y`, and
a chart of `X'` over a chart of `X` lying over that same pair.  Independently chosen charts of
`X'` and `Y'` do not stack, so the squares are produced by
`AlgebraicGeometry.Space.exists_baseChangeChartTower`: a chart `W` of `Z`, a chart `V` of `Y`
over it, a chart `U` of `X` over that and a chart `W'` of `Z'` over `W`, which make `V ×_W W'`
a chart of `Y'` and `U ×_V (V ×_W W')` one of `X'`.  That tower is the same one the base-change
assertion of Stacks 05X3 is read on.

Membership of the flat locus is tested at a geometric representative of the point, where
`AlgebraicGeometry.Space.isFlatOverAtOnChartDiagram_iff_isFlatOverAtGeometricPoint` — Stacks
05VU at one commuting square of charts — turns each side into flatness of a restricted module
at a point of a chart scheme, and the geometric point lifts to the chart of `X'` because that
chart is surjective.

What connects the two sides is that the chart restriction of the inverse image `𝓕'` is the
inverse image of the chart restriction of `𝓕`.  That comparison is available for
`AlgebraicGeometry.Space.restrictToChartScheme`, as
`AlgebraicGeometry.Space.nonempty_restrictToChartScheme_modulePullback_square`, whereas the
flat locus of an algebraic space is read through the parallel construction
`AlgebraicGeometry.Space.restrictToChart`.  The two agree:
`AlgebraicGeometry.Space.nonempty_restrictToChart_iso_restrictToChartScheme` below proves it,
both being `AlgebraicGeometry.SmallEtale.restrictModule` of the same module on the small étale
site of the chart scheme, up to the universe lift of the sections.  This is the reading of the
hypothesis `AlgebraicGeometry.Space.ChartRestrictionBaseChange` of
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/ModuleFiniteness.lean` which that file carries as
an assumption; it is not carried here.

## References

* [Stacks Project, Tag 05X2](https://stacks.math.columbia.edu/tag/05X2)
* [Stacks Project, Tag 05VJ](https://stacks.math.columbia.edu/tag/05VJ)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 05X3](https://stacks.math.columbia.edu/tag/05X3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The two readings of the chart restriction -/

/-- **The two parallel readings of the restriction of a quasi-coherent module to an étale scheme
chart agree.**  `AlgebraicGeometry.Space.restrictToChart` sheafifies the sections over the
Zariski opens of the chart, while `AlgebraicGeometry.Space.restrictToChartScheme` is the same
construction with the change of scalars spelled through the structure presheaf of the chart
scheme; the two are not definitionally equal.

Both are `AlgebraicGeometry.SmallEtale.restrictModule` applied to the restriction of the module
to the small étale site of the chart scheme, the first to the restriction of the universe lift
of the sections and the second to the restriction of the module itself, so the comparison is
the universe-lift isomorphism carried along the two functors. -/
theorem nonempty_restrictToChart_iso_restrictToChartScheme (X : AlgebraicSpaces B S hS)
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite)
    (A : SmallEtale B S hS X.1) :
    Nonempty (restrictToChart B S hS X.2 M A ≅
      restrictToChartScheme B S hS X.1 X.2 M A) := by
  have e : chartSmallEtaleRestriction B S hS X
        (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u} M) A ≅
      chartSmallEtaleRestriction B S hS X M A :=
    (@SheafOfModules.pushforward _ _ _ _
      (SmallEtale.topology B S hS (chartSpace B S hS X A).1)
      ((SmallEtale.topology B S hS X.1).over A)
      (SmallEtale.chartLocalizationEquivalence B S hS X.1 A).functor
      (chartStructureRingSheaf B S hS X A)
      ((structureRingSheaf B S hS X).over A)
      (isContinuous_chartLocalization_chartSpace B S hS X A)
      (𝟙 _)).mapIso
      ((SheafOfModules.overFunctor (structureRingSheaf B S hS X) A).mapIso
        (SheafOfModules.uliftForPresentationSelfIso.{u + 1, u, u, u} M))
  refine ⟨restrictToChartIsoChartRestrictionSheaf B S hS X M A ≪≫ ?_ ≪≫
    (restrictToChartSchemeIsoRestrictModule B S hS X M hM A).symm⟩
  exact (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      (chartScheme A) ((SmallEtale.toOver B S hS X.1).obj A).left.property).mapIso
    ((representedSmallEtaleModuleEquivalence B S hS
      ((SmallEtale.toOver B S hS X.1).obj A)).inverse.mapIso e)

/-! ### The base-change assertion of Stacks 05X2 -/

section BaseChange

variable {X Y Z X' Y' Z' : AlgebraicSpaces B S hS}

/-- **Stacks 05X2, the base-change assertion.** Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S` whose source and target are given over an algebraic space `Z` by `f ≫ q` and
`q : Y ⟶ Z`, and let `F` be a quasi-coherent `𝒪_X`-module.  Assume `X` is locally of finite
presentation over `Z`, that `F` is of finite presentation, that `F` is flat over `Z`, and that
`Y` is locally of finite type over `Z`.  Then for a base change along an arbitrary morphism
`h : Z' ⟶ Z`, presented by the cartesian squares `Y' = Y ×_Z Z'` and `X' = X ×_Y Y'`, the locus
of points of `|X'|` at which the inverse image of `F` is flat over `Y'` is the inverse image
under `|X'| ⟶ |X|` of the locus of points of `|X|` at which `F` is flat over `Y`. -/
@[stacks 05X2 "base change: the locus on the base change is the inverse image of the locus \
downstairs. Hypotheses (1)-(4) of the source are the finite presentation of `X` over `Z`, of \
the module on the small etale site, the flatness of the module over `Z`, and the finite type of \
`Y` over `Z`. The openness assertion is \
Space.isOpen_flatLocus_of_isLocallyOfFinitePresentation_comp."]
theorem flatLocus_modulePullback_eq_preimage_of_isFlatOverBase
    {f : X ⟶ Y} {q : Y ⟶ Z} {h : Z' ⟶ Z} {g : Y' ⟶ Y} {q' : Y' ⟶ Z'}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    (sqY : IsPullback g q' q h) (sqX : IsPullback g' f' f g)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite]
    (hFfp : F.IsFinitePresentation)
    (hp : IsLocallyOfFinitePresentation B S hS (f ≫ q).hom)
    (hq : IsLocallyOfFiniteType B S hS q.hom)
    (hFZ : IsFlatOver B S hS X.2 (f ≫ q).hom F) :
    flatLocus B S hS X'.2 f'.hom ((modulePullback B S hS g').obj F) =
      pointsMap B S hS X'.1 g'.hom ⁻¹' flatLocus B S hS X.2 f.hom F := by
  -- the chartwise readings of the two hypotheses on the module, from their readings on the site
  have hqc : IsQuasicoherentOnCharts B S hS X.2 F :=
    isQuasicoherentOnCharts_of_isQuasicoherentOnSite B S hS X F inferInstance
  have hfp : IsFinitePresentationOnCharts B S hS X.2 F :=
    isFinitePresentationOnCharts_of_isFinitePresentationOnSite B S hS X F inferInstance
      (SheafOfModules.isFinitePresentationOnSite_of_isFinitePresentation F (h := hFfp))
  let T := BigFppfOver.toScheme B S hS
  have := isQuasicoherentOnSite_modulePullback_of_isFinitePresentation B S hS g' F hFfp
  obtain ⟨C⟩ := exists_baseChangeChartTower B S hS X.2 Y.2 Z.2 Z'.2
    (AlgebraicSpaces.isPullback_hom B S hS sqY) (AlgebraicSpaces.isPullback_hom B S hS sqX)
  let AX : SmallEtale B S hS X.1 := ⟨CostructuredArrow.mk C.u, C.uEtale⟩
  let AY : SmallEtale B S hS Y.1 := ⟨CostructuredArrow.mk C.v, C.vEtale⟩
  let AZ : SmallEtale B S hS Z.1 := ⟨CostructuredArrow.mk C.w, C.wEtale⟩
  let AX' : SmallEtale B S hS X'.1 := ⟨CostructuredArrow.mk C.cU, C.cUEtale⟩
  let AY' : SmallEtale B S hS Y'.1 := ⟨CostructuredArrow.mk C.cV, C.cVEtale⟩
  -- the finiteness hypotheses, read on the charts
  have : LocallyOfFinitePresentation (T.map C.α ≫ T.map C.β) := by
    rw [← Functor.map_comp]
    exact hp C.U C.W C.u C.w (C.α ≫ C.β) C.uEtale C.wEtale C.commP
  have : LocallyOfFiniteType (T.map C.β) :=
    hq C.V C.W C.v C.w C.β C.vEtale C.wEtale C.commQ
  -- flatness over the base, read on the charts
  have hFlat' : AlgebraicGeometry.IsFlatOver
      (T.map C.α ≫ T.map C.β).toLRSHom.toShHom (restrictToChart B S hS X.2 F AX) := by
    rw [← Functor.map_comp]
    exact hFZ { U := AX, V := AZ, g := C.α ≫ C.β, comm := C.commP.symm }
  -- the scheme-level statement, Stacks 05VJ, at the two cartesian squares of the tower
  have hbc := @_root_.AlgebraicGeometry.setOf_isFlatOverAt_modulePullback_of_isFlatOver
    _ _ _ _ _ _ _ _ _ _ _ _ _ C.isPullbackY C.isPullbackX
    (restrictToChart B S hS X.2 F AX) (hqc AX) (hfp AX) inferInstance inferInstance hFlat'
  -- the chart restriction of the pullback is the pullback of the chart restriction
  obtain ⟨e₁⟩ := nonempty_restrictToChart_iso_restrictToChartScheme B S hS X'
    ((modulePullback B S hS g').obj F) inferInstance AX'
  obtain ⟨e₂⟩ := nonempty_restrictToChartScheme_modulePullback_square B S hS g' F
    inferInstance AX' AX C.qU C.cUfst
  obtain ⟨e₃⟩ := nonempty_restrictToChart_iso_restrictToChartScheme B S hS X F
    inferInstance AX
  have eF : restrictToChart B S hS X'.2 ((modulePullback B S hS g').obj F) AX' ≅
      (AlgebraicGeometry.Scheme.Modules.pullback (T.map C.qU)).obj
        (restrictToChart B S hS X.2 F AX) :=
    e₁ ≪≫ e₂ ≪≫ (AlgebraicGeometry.Scheme.Modules.pullback (T.map C.qU)).mapIso e₃.symm
  -- pointwise, at a geometric representative
  refine Set.ext fun x' => ?_
  obtain ⟨xbar, rfl⟩ := exists_geometricRepresentative B S hS X'.1 x'
  rw [Set.mem_preimage,
    mem_flatLocus_iff_isFlatOverAtGeometricPoint B S hS f'
      ((modulePullback B S hS g').obj F) xbar,
    ← geometricPointMap_image g'.hom xbar,
    mem_flatLocus_iff_isFlatOverAtGeometricPoint B S hS f F (geometricPointMap g'.hom xbar)]
  -- lift the geometric point to the chart of `X'`, and push it to the chart of `X`
  obtain ⟨l, hl⟩ := exists_chartLift_of_isSurjective B S hS X'.1 X'.2 AX'
    (isSurjective_of_presheafSurjective B S hS C.cU C.cUSurjective) xbar
  have hl₀ : C.cU.app (Opposite.op xbar.val.siteObject) l = xbar.val.value := hl
  have hlU : C.u.app (Opposite.op xbar.val.siteObject)
      (l ≫ pullback.fst C.α (pullback.fst C.β C.γ)) =
      (geometricPointMap g'.hom xbar).val.value := by
    simpa [hl₀, geometricPointMap, FieldValuedPoint.map] using (ConcreteCategory.congr_hom
      (NatTrans.congr_app C.cUfst (Opposite.op xbar.val.siteObject)) l).symm
  let N' : SmallEtaleNeighborhood xbar := ⟨AX', l, hl⟩
  let N : SmallEtaleNeighborhood (geometricPointMap g'.hom xbar) := ⟨AX, l ≫ C.qU, hlU⟩
  rw [← isFlatOverAtOnChartDiagram_iff_isFlatOverAtGeometricPoint B S hS f'
      ((modulePullback B S hS g').obj F) N' AY' C.fU C.cUsnd,
    ← isFlatOverAtOnChartDiagram_iff_isFlatOverAtGeometricPoint B S hS f F N AY C.α
      C.commF.symm]
  have hcp : chartPoint B S hS X.1 N = T.map C.qU (chartPoint B S hS X'.1 N') := by
    show T.map (l ≫ C.qU) (IsLocalRing.closedPoint xbar.val.carrier) =
      T.map C.qU ((T.map l) (IsLocalRing.closedPoint xbar.val.carrier))
    rw [Functor.map_comp]
    exact Scheme.Hom.comp_apply _ _ _
  rw [hcp]
  exact (AlgebraicGeometry.isFlatOverAt_iff_of_moduleIso _ eF _).trans
    (Set.ext_iff.mp hbc (chartPoint B S hS X'.1 N'))

end BaseChange

end AlgebraicGeometry.Space

end
