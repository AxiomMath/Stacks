module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Modules.RestrictFree
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartOpenNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartPullbackRestrictionIdentification
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionReadingsFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleFreeLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeChartScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricFibreStalkFiniteFree

/-!
# The Zariski-chart reading of clause (4) of Stacks 0CZS is the étale-site locus of Stacks 0CZT

Clause (4) of Stacks 0CZS says that `F` is *finite free in an étale neighbourhood of `x`*.  This
condition has two readings:

* `AlgebraicGeometry.Space.IsFiniteFreeNearGeometricPoint`, the **Zariski-chart** reading, which is
  the source's own: an étale *scheme* chart `U ⟶ X` carrying a lift of the geometric point `x̄`,
  and a Zariski open `W` of `U` containing the point `u` under that lift, on which the chart
  restriction `F|_U` becomes a free sheaf of finite rank;
* `AlgebraicGeometry.Space.etaleFiniteFreeLocus`, the **small-étale-site** reading, in which the
  locus of Stacks 0CZT is defined: an étale morphism `a : V ⟶ X` of algebraic *spaces* whose image
  on points contains `x` and along which the inverse image of `F` is finite free in the sense of
  Stacks 03DE (2) on the small étale site of `V`.

This file passes from the first to the second.  Doing so needs the chart restriction to be
compatible with shrinking a chart along a Zariski open — the restriction of `F|_U` to `W` is the
chart restriction at the chart `W` cuts out of `U` — and then the comparison of the Zariski site of
a chart scheme with the small étale site of the chart space, in its finite-free form.

## Main results

* `nonempty_restrictToChart_chartOpens`: **the chart restriction shrinks along a Zariski open of
  the chart.**  For a quasi-coherent `𝒪_X`-module `M`, an étale scheme chart `U` of `X` and a
  Zariski open `W` of its scheme, the chart restriction of `M` at the étale chart `W` cuts out of
  `U` is the Zariski restriction to `W` of the chart restriction of `M` at `U`.
* `Stacks.SheafOfModules.isFiniteFree_representedSmallEtaleModule_iff`: finite freeness, Stacks
  03DE (2), is invariant under the comparison equivalence of Stacks 03DX (2) at a representable
  algebraic space.
* `isFiniteFree_chartSmallEtaleRestriction_of_isFiniteFree_chartSchemeModule`: if the Zariski
  chart module of Stacks 03DX (2) is finite free, so is the inverse image of the module to the
  chart space.
* `isFiniteFree_chartSchemeModule_of_isFiniteFree_chartSmallEtaleRestriction`: the converse of
  the previous statement.
* `isFiniteFree_restrictToChart_chartOpens`: a trivialization of the chart restriction on a
  Zariski open of the chart makes the chart restriction at the chart that open cuts out finite
  free.
* `mem_etaleFiniteFreeLocus_of_isFiniteFreeNearGeometricPoint`: **clause (4) of Stacks 0CZS in
  the small-étale-site reading** — the Zariski-chart reading at a geometric point `x̄` puts the
  image point of `x̄` in the finite-free étale locus of Stacks 0CZT.
* `mem_etaleFiniteFreeLocus_of_flat_geometricFibreModuleStalk`: **Stacks 0CZS, (1) implies (4)
  in the small-étale-site reading** — under the source's own hypotheses, flatness of the
  geometric fibre stalk puts the point in that locus.

## References

* [Stacks Project, Tag 0CZS](https://stacks.math.columbia.edu/tag/0CZS)
* [Stacks Project, Tag 0CZT](https://stacks.math.columbia.edu/tag/0CZT)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 05VG](https://stacks.math.columbia.edu/tag/05VG)
* [Stacks Project, Tag 0B8J](https://stacks.math.columbia.edu/tag/0B8J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.SheafOfModules

/-- **Finite freeness, Stacks 03DE (2), is invariant under the comparison equivalence of
Stacks 03DX (2) at a representable algebraic space.** -/
theorem isFiniteFree_representedSmallEtaleModule_iff
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : AlgebraicGeometry.Scheme.{u})
    (hS : B.Contains S) (U : AlgebraicGeometry.BigFppfOver B S hS)
    (M : _root_.SheafOfModules.{u}
      (AlgebraicGeometry.Space.representedSchemeStructureSheaf B S hS U)) :
    _root_.SheafOfModules.IsFiniteFree
        (AlgebraicGeometry.Space.representedStructureRingSheaf B S hS U)
        (AlgebraicGeometry.Space.representedSmallEtaleModule B S hS U M) ↔
      _root_.SheafOfModules.IsFiniteFree
        (AlgebraicGeometry.Space.representedSchemeStructureSheaf B S hS U) M :=
  isFiniteFree_reindex_iff
    (AlgebraicGeometry.Space.representedSmallEtaleEquivalence B S hS U)
    (AlgebraicGeometry.Space.representedSchemeStructureSheaf B S hS U) M

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Shrinking a chart along a Zariski open -/

/-- **The chart restriction of a module shrinks along a Zariski open of the chart.**  Let `M` be a
quasi-coherent `𝒪_X`-module, let `U` be an étale scheme chart of `X` and let `W` be a Zariski open
of its scheme.  Then the chart restriction of `M` at the étale chart `W` cuts out of `U` is the
Zariski restriction to `W` of the chart restriction of `M` at `U`. -/
theorem nonempty_restrictToChart_chartOpens (X : AlgebraicSpaces B S hS)
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite)
    (U : SmallEtale B S hS X.1) (W : (chartScheme U).Opens) :
    Nonempty ((show (W : Scheme.{u}).Modules from
        restrictToChart B S hS X.2 M ((chartOpens B S hS U).obj W)) ≅
      Scheme.Modules.restrict
        (show (chartScheme U).Modules from restrictToChart B S hS X.2 M U) W.ι) := by
  obtain ⟨e⟩ := nonempty_pullback_restrictToChartScheme B S hS X M hM
    (show (chartOpens B S hS U).obj W ⟶ U from
      ObjectProperty.homMk (CostructuredArrow.homMk (chartOpenOverι B S hS U W) rfl))
  rw [show chartSchemeMap
      (show (chartOpens B S hS U).obj W ⟶ U from
        ObjectProperty.homMk (CostructuredArrow.homMk (chartOpenOverι B S hS U W) rfl)) = W.ι from
    rfl] at e
  exact ⟨restrictToChartIsoRestrictToChartScheme B S hS X.2 M _ ≪≫ e.symm ≪≫
    ((Scheme.Modules.restrictFunctorIsoPullback W.ι).app
        (restrictToChartScheme B S hS X.1 X.2 M U)).symm ≪≫
    (Scheme.Modules.restrictFunctor W.ι).mapIso
      (restrictToChartIsoRestrictToChartScheme B S hS X.2 M U).symm⟩

/-! ### Finite freeness across the two site comparisons -/

/-- Finite freeness is invariant under isomorphism, as an equivalence. -/
private theorem isFiniteFree_iff_of_iso {C : Type (u + 1)} [Category.{u} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    {M N : _root_.SheafOfModules.{u} R} (e : M ≅ N) :
    SheafOfModules.IsFiniteFree R M ↔ SheafOfModules.IsFiniteFree R N :=
  ⟨Stacks.SheafOfModules.isFiniteFree_of_iso e,
    Stacks.SheafOfModules.isFiniteFree_of_iso e.symm⟩

/-- Finite freeness of the Zariski chart module and of the 04M0 reading of the restriction to the
chart are equivalent. -/
private theorem isFiniteFree_chartSmallEtaleRestriction_iff
    (X : AlgebraicSpaces B S hS) (M : SheafOfModules.{u} (structureRingSheaf B S hS X))
    (hM : M.IsQuasicoherentOnSite) (A : SmallEtale B S hS X.1) :
    SheafOfModules.IsFiniteFree (chartStructureRingSheaf B S hS X A)
        (chartSmallEtaleRestriction B S hS X M A) ↔
      SheafOfModules.IsFiniteFree (chartScheme A).ringCatSheaf
        (chartSchemeModule B S hS X M hM A) := by
  have : (chartSchemeModule B S hS X M hM A).IsQuasicoherent :=
    isQuasicoherent_chartSchemeModule B S hS X M hM A
  refine (isFiniteFree_iff_of_iso
    (representedSmallEtaleChartSchemeEtaleModuleIso B S hS X M hM A)).symm.trans ?_
  refine (Stacks.SheafOfModules.isFiniteFree_representedSmallEtaleModule_iff B S hS _ _).trans ?_
  refine (isFiniteFree_iff_of_iso
    (associatedModuleChartSchemeModuleIso B S hS X M hM A)).symm.trans ?_
  exact _root_.AlgebraicGeometry.SmallEtale.isFiniteFree_associatedModule_iff
    (associatedBigEtaleSite B) (chartScheme A)
    ((SmallEtale.toOver B S hS X.1).obj A).left.property (chartSchemeModule B S hS X M hM A)

/-- **If the Zariski chart module of Stacks 03DX (2) is finite free, so is the 04M0 reading of the
restriction of the module to the chart.** -/
theorem isFiniteFree_chartSmallEtaleRestriction_of_isFiniteFree_chartSchemeModule
    (X : AlgebraicSpaces B S hS) (M : SheafOfModules.{u} (structureRingSheaf B S hS X))
    (hM : M.IsQuasicoherentOnSite) (A : SmallEtale B S hS X.1)
    (h : SheafOfModules.IsFiniteFree (chartScheme A).ringCatSheaf
      (chartSchemeModule B S hS X M hM A)) :
    SheafOfModules.IsFiniteFree (chartStructureRingSheaf B S hS X A)
      (chartSmallEtaleRestriction B S hS X M A) :=
  (isFiniteFree_chartSmallEtaleRestriction_iff B S hS X M hM A).2 h

/-- **The converse: if the 04M0 reading of the restriction of the module to the chart is finite
free, so is the Zariski chart module of Stacks 03DX (2).** -/
theorem isFiniteFree_chartSchemeModule_of_isFiniteFree_chartSmallEtaleRestriction
    (X : AlgebraicSpaces B S hS) (M : SheafOfModules.{u} (structureRingSheaf B S hS X))
    (hM : M.IsQuasicoherentOnSite) (A : SmallEtale B S hS X.1)
    (h : SheafOfModules.IsFiniteFree (chartStructureRingSheaf B S hS X A)
      (chartSmallEtaleRestriction B S hS X M A)) :
    SheafOfModules.IsFiniteFree (chartScheme A).ringCatSheaf
      (chartSchemeModule B S hS X M hM A) :=
  (isFiniteFree_chartSmallEtaleRestriction_iff B S hS X M hM A).1 h

/-- **A trivialization of the chart restriction on a Zariski open of the chart makes the chart
restriction at the chart that open cuts out finite free.** -/
theorem isFiniteFree_restrictToChart_chartOpens (X : AlgebraicSpaces B S hS)
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite)
    (U : SmallEtale B S hS X.1) (W : (chartScheme U).Opens) (r : ℕ)
    (e : (restrictToChart B S hS X.2 M U).over W ≅
      SheafOfModules.free (ULift.{u} (Fin r))) :
    SheafOfModules.IsFiniteFree (chartScheme ((chartOpens B S hS U).obj W)).ringCatSheaf
      (restrictToChart B S hS X.2 M ((chartOpens B S hS U).obj W)) := by
  obtain ⟨c⟩ := nonempty_restrictToChart_chartOpens B S hS X M hM U W
  have e2 : Scheme.Modules.restrict
        (show (chartScheme U).Modules from restrictToChart B S hS X.2 M U) W.ι ≅
      SheafOfModules.free (R := (W : Scheme.{u}).ringCatSheaf) (ULift.{u} (Fin r)) :=
    ((Scheme.Modules.overFunctorEquiv W).app (restrictToChart B S hS X.2 M U)).symm ≪≫
      (Scheme.Modules.overEquiv W).functor.mapIso e ≪≫
      Scheme.Modules.overEquivFunctorObjFree W (ULift.{u} (Fin r))
  exact Stacks.SheafOfModules.isFiniteFree_of_iso (c ≪≫ e2).symm
    (Stacks.SheafOfModules.isFiniteFree_freeULift _ r)

/-! ### Clause (4) of Stacks 0CZS in the small-étale-site reading -/

/-- **Clause (4) of Stacks 0CZS in the small-étale-site reading of Stacks 0CZT.**  If a
quasi-coherent `𝒪_X`-module `M` is finite free in an étale neighbourhood of a geometric point `x̄`
of `X` in the Zariski-chart sense of `AlgebraicGeometry.Space.IsFiniteFreeNearGeometricPoint` —
the source's own reading — then the image point of `x̄` lies in the finite-free étale locus
`AlgebraicGeometry.Space.etaleFiniteFreeLocus`, the locus of Stacks 0CZT. -/
@[stacks 0CZS "clause (4) in the SMALL-ETALE-SITE reading: the source's Zariski-chart reading of \
clause (4) at a geometric point xbar implies that the image point of xbar lies in the locus of \
points of |X| admitting an etale morphism of algebraic spaces a : V -> X through them along which \
the inverse image of F is finite free in the sense of 03DE(2), which is the locus of Stacks 0CZT"]
theorem mem_etaleFiniteFreeLocus_of_isFiniteFreeNearGeometricPoint
    {X : AlgebraicSpaces B S hS} (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (xbar : GeometricPoint B S hS X.1)
    (h : IsFiniteFreeNearGeometricPoint B S hS xbar M) :
    xbar.image ∈ etaleFiniteFreeLocus B S hS M := by
  obtain ⟨N, r, W, hW, ⟨e⟩⟩ := h
  refine ⟨chartSpace B S hS X ((chartOpens B S hS N.chart).obj W),
    chartToSpace B S hS X ((chartOpens B S hS N.chart).obj W),
    isEtale_chartToSpace B S hS X ((chartOpens B S hS N.chart).obj W), ?_, ?_⟩
  · exact ⟨(chartFieldValuedPoint (chartOpenNeighborhood B S hS N W hW)).class B S hS _,
      chartFieldValuedPoint_pointsMap (chartOpenNeighborhood B S hS N W hW)⟩
  · have h2 : SheafOfModules.IsFiniteFree
        (chartScheme ((chartOpens B S hS N.chart).obj W)).ringCatSheaf
        (chartSchemeModule B S hS X M hM ((chartOpens B S hS N.chart).obj W)) :=
      Stacks.SheafOfModules.isFiniteFree_of_iso
        (restrictToChartIsoChartSchemeModule B S hS X M hM
          ((chartOpens B S hS N.chart).obj W))
        (isFiniteFree_restrictToChart_chartOpens B S hS X M hM N.chart W r e)
    have ei : chartSmallEtaleRestriction B S hS X M ((chartOpens B S hS N.chart).obj W) ≅
        (modulePullback B S hS
          (chartToSpace B S hS X ((chartOpens B S hS N.chart).obj W))).obj M :=
      ((modulePullbackIsoEtaleModulePullback B S hS
            (chartToSpace B S hS X ((chartOpens B S hS N.chart).obj W))
            (isEtale_chartToSpace B S hS X ((chartOpens B S hS N.chart).obj W))).app M ≪≫
          etaleModulePullbackChartToSpaceIso B S hS X M
            ((chartOpens B S hS N.chart).obj W)).symm
    exact Stacks.SheafOfModules.isFiniteFree_of_iso ei
      (isFiniteFree_chartSmallEtaleRestriction_of_isFiniteFree_chartSchemeModule B S hS X M hM
        ((chartOpens B S hS N.chart).obj W) h2)

/-- **Clause (1) implies clause (4), in the small-étale-site reading of Stacks 0CZT.**  Let
`f : X ⟶ Y` be locally of finite presentation, let `M` be a quasi-coherent `𝒪_X`-module of finite
presentation on charts and let `x̄` be a geometric point of `X`.  If `M` is flat at `x` over `Y`
and the geometric fibre stalk `(M_{ȳ})_{x̄}` is a flat `𝒪_{X_{ȳ}, x̄}`-module, then the image point
of `x̄` lies in the finite-free étale locus of Stacks 0CZT.  The fibre stalk and its base ring are
in the quotient form `M_{x̄} / 𝔪_{ȳ} M_{x̄}` over `𝒪_{X, x̄} / 𝔪_{ȳ} 𝒪_{X, x̄}`. -/
@[stacks 0CZS "(1) implies (4) with clause (4) in the SMALL-ETALE-SITE reading, i.e. membership in \
the locus of Stacks 0CZT; the fibre stalk and its base ring are in the QUOTIENT FORM \
M_xbar / m_ybar M_xbar over O_{X, xbar} / m_ybar O_{X, xbar}, whose identification with the stalk \
on the geometric fibre X_ybar is condition (2) of Stacks 05WY and is not available"]
theorem mem_etaleFiniteFreeLocus_of_flat_geometricFibreModuleStalk
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (M : Modules.{u, u} B S hS X.1 X.2)
    [M.IsQuasicoherentOnSite] (hf : IsLocallyOfFinitePresentation B S hS f.hom)
    (hfp : IsFinitePresentationOnCharts B S hS X.2 M)
    (xbar : GeometricPoint B S hS X.1)
    (hflat : IsFlatOverAtGeometricPoint B S hS f M xbar)
    (hfibre : Module.Flat (geometricFibreLocalRing B S hS f xbar)
      (geometricFibreModuleStalk B S hS f M xbar)) :
    xbar.image ∈ etaleFiniteFreeLocus B S hS M :=
  mem_etaleFiniteFreeLocus_of_isFiniteFreeNearGeometricPoint B S hS M inferInstance xbar
    (isFiniteFreeNearGeometricPoint_of_flat_geometricFibreModuleStalk B S hS f M hf hfp xbar
      hflat hfibre)

end AlgebraicGeometry.Space

end
