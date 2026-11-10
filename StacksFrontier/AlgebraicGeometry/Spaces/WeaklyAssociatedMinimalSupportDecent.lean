module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.MinimalSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionSections
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Specializations
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportChartZariski
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportGeometricStalkCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedTFAE

/-!
# Minimal points of the support of a module on a decent algebraic space

Let `X` be an algebraic space over `S` and `F` a quasi-coherent `𝒪_X`-module. A point of `|X|`
which lies in `Supp(F)` and is not a specialization of another point of `Supp(F)` is weakly
associated to `F`, provided the chart fibres of `X` are finite above every point — in
particular on a decent `X`.

## Main results

* `AlgebraicGeometry.Space.isWeaklyAssociatedPoint_of_mem_supportOfSheaf_of_specializes` is
  **Stacks 0CUM**, under the source's own hypotheses.
* `isWeaklyAssociatedPoint_of_mem_supportOfSheaf_of_specializes_of_isQuasicoherent_restrictToChart`
  is the same statement with quasi-coherence of the chart restrictions taken as a hypothesis
  rather than proved.

## Implementation notes

The argument is the source's: a point of an étale scheme chart above `x` is minimal in the
support of the chart restriction, so the scheme-level
`AlgebraicGeometry.mem_weaklyAssociatedPoints_of_mem_supp_of_specializes` of Stacks 05AQ
applies there, and `(1) ⟹ (3)` of Stacks 0CTW,
`AlgebraicGeometry.Space.isWeaklyAssociatedPoint_of_isWeaklyAssociatedPoint_restrictToChart`,
carries the conclusion back to `X`. Minimality on the chart uses the support comparison
`Supp(φ^*F) = |φ|^{-1}(Supp(F))` of Stacks 07TY in both directions together with Stacks 03K5,
`AlgebraicGeometry.Space.eq_of_specializes_of_pointsMap_eq_of_hasFiniteChartFibers`, which
collapses a specialization inside a chart fibre.

Decency enters only through Stacks 03K5, which the library states under condition `(α)` of
Stacks 03JX, `AlgebraicGeometry.Space.HasFiniteChartFibersAtEveryPoint`; that is weaker than
`AlgebraicGeometry.Space.IsDecentSpace`, the equivalence of the readings of Stacks 03I8 being
the unproved Stacks 03JV, so the hypothesis is carried in the weaker form. The two asides of
the source, that a quasi-separated and that a locally separated algebraic space is decent, are
Stacks 03I7 and Stacks 088J and are not part of the statement.

The remaining input of the source proof is proved. `hqc` is quasi-coherence of the restriction of
`F` to the *Zariski* site of an
étale scheme chart, which Stacks 05AQ needs. It was never an extra assumption of the source:
Stacks 03M0 reads quasi-coherence on an algebraic space off exactly that restriction, so the
source has it for free. What is needed is its comparison with
`AlgebraicGeometry.Space.restrictToChart`, the restriction the statements used here are phrased
with, and that comparison is supplied by
`StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionSections`: the sheafification
`restrictToChart` performs does nothing, because the presheaf it sheafifies is already the
restriction, along the inclusion of the small Zariski site, of the module `F` induces on the
small étale site of the chart's scheme
(`AlgebraicGeometry.Space.restrictToChartIsoChartRestrictionSheaf`, with no hypothesis on the
module). Quasi-coherence of that restriction is Descent, Proposition 03DX (2) at `τ = étale`
for a scheme, proved unconditionally as
`AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule`. The two together are
`AlgebraicGeometry.Space.isQuasicoherent_restrictToChart`, which assumes nothing beyond
quasi-coherence of `F` on the small étale site, and that is what discharges `hqc` here. So the
blanket remark that 03DX is unavailable, which several modules of this tree carry, is too
broad: what 03DX is missing is essential surjectivity on a *big* site, not the small étale site
of a scheme.

The form of the result that carries `hqc` as a hypothesis is kept, as
`isWeaklyAssociatedPoint_of_mem_supportOfSheaf_of_specializes_of_isQuasicoherent_restrictToChart`;
it is what the tagged version calls. Quasi-coherence of `F` on the small étale site is assumed
in both, since `(1) ⟹ (3)` of Stacks 0CTW asks for it. The same `hqc`-shaped hypothesis is
still carried undischarged by several other modules of this tree, which
`AlgebraicGeometry.Space.isQuasicoherent_restrictToChart` should now let them drop.

The parallel restriction `AlgebraicGeometry.Space.restrictToChartScheme` is a different reading
of the chart restriction. For a quasi-coherent module the two agree, by
`AlgebraicGeometry.Space.restrictToChartIsoChartSchemeModule`
(`StacksDraft.AlgebraicGeometry.Spaces.ChartRestrictionIsoChartSchemeModule`) composed with
`AlgebraicGeometry.Space.restrictToChartSchemeIsoRestrictModule` and
`AlgebraicGeometry.Space.chartSchemeModuleIsoRestrictModule`. An *equality* of the two is still
owed: `StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionReadings` has the object half — the
two readings of a Zariski open of the chart as an object of the big fppf category agree,
`AlgebraicGeometry.Space.chartOpenOver_eq_openSub`, and the two change-of-scalars maps are
equal by `rfl`, `AlgebraicGeometry.Space.chartRestrictionRingHom_eq` — but not the morphism
half, the two inclusions being comparable only after transport along that object equality.

The other input the source proof needs, the comparison `(φ^*F)_u ⊗_{𝒪_{U, u}} 𝒪_{X, x̄} ≅
F_{x̄}` of Stacks 05VP that Stacks 07TY rests on, *is* available for a quasi-coherent module:
`StacksFrontier.AlgebraicGeometry.Spaces.SupportGeometricStalkCriterion` proves Stacks 07TY
unconditionally in that case
(`AlgebraicGeometry.Space.supp_restrictToChart_eq_preimage_supportOfSheaf_of_isQuasicoherent`),
discharging the comparison internally through
`AlgebraicGeometry.Space.isIso_chartStalkTensorComparison`. So no `h05VP`-style hypothesis is
carried here.

The other input the source proof needs, the comparison `(φ^*F)_u ⊗_{𝒪_{U, u}} 𝒪_{X, x̄} ≅
F_{x̄}` of Stacks 05VP that Stacks 07TY rests on, *is* available for a quasi-coherent module:
`StacksFrontier.AlgebraicGeometry.Spaces.SupportGeometricStalkCriterion` proves Stacks 07TY
unconditionally in that case
(`AlgebraicGeometry.Space.supp_restrictToChart_eq_preimage_supportOfSheaf_of_isQuasicoherent`),
discharging the comparison internally through
`AlgebraicGeometry.Space.isIso_chartStalkTensorComparison`. So no `h05VP`-style hypothesis is
carried here.

The other input the source proof needs, the comparison `(φ^*F)_u ⊗_{𝒪_{U, u}} 𝒪_{X, x̄} ≅
F_{x̄}` of Stacks 05VP that Stacks 07TY rests on, *is* available for a quasi-coherent module:
`StacksFrontier.AlgebraicGeometry.Spaces.SupportGeometricStalkCriterion` proves Stacks 07TY
unconditionally in that case
(`AlgebraicGeometry.Space.supp_restrictToChart_eq_preimage_supportOfSheaf_of_isQuasicoherent`),
discharging the comparison internally through
`AlgebraicGeometry.Space.isIso_chartStalkTensorComparison`. So no `h05VP`-style hypothesis is
carried here.

## References

* [Stacks Project, Lemma 71.2.7 (Tag 0CUM)](https://stacks.math.columbia.edu/tag/0CUM)
* [Stacks Project, Tag 05AQ](https://stacks.math.columbia.edu/tag/05AQ)
* [Stacks Project, Tag 07TY](https://stacks.math.columbia.edu/tag/07TY)
* [Stacks Project, Tag 03K5](https://stacks.math.columbia.edu/tag/03K5)
* [Stacks Project, Tag 0CTW](https://stacks.math.columbia.edu/tag/0CTW)
* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS)

/-- Let `X` be an algebraic space over `S` all of whose chart fibres are finite — in
particular a decent one — and let `F` be a quasi-coherent `𝒪_X`-module whose restriction to
the Zariski site of every étale scheme chart is quasi-coherent. A point of `|X|` which lies in
the support of `F` and is not a specialization of another point of that support is weakly
associated to `F`.

This is the form of Stacks 0CUM that carries the chartwise quasi-coherence `hqc` as a
hypothesis. That hypothesis holds for every quasi-coherent `F`, by
`AlgebraicGeometry.Space.isQuasicoherent_restrictToChart`, so Stacks 0CUM itself is the
version below,
`AlgebraicGeometry.Space.isWeaklyAssociatedPoint_of_mem_supportOfSheaf_of_specializes`,
which assumes only the source's hypotheses. -/
theorem
    isWeaklyAssociatedPoint_of_mem_supportOfSheaf_of_specializes_of_isQuasicoherent_restrictToChart
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite]
    (hdecent : HasFiniteChartFibersAtEveryPoint B S hS X.1)
    (hqc : ∀ U : SmallEtale B S hS X.1, (restrictToChart B S hS X.2 F U).IsQuasicoherent)
    (x : points B S hS X.1)
    (hx : x ∈ supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F))
    (hmin : ∀ y, y ∈ supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F) →
      y ⤳ x → y = x) :
    IsWeaklyAssociatedPoint B S hS X F x := by
  obtain ⟨xbar, hxbar⟩ := exists_geometricRepresentative B S hS X.1 x
  obtain ⟨V⟩ := nonempty_smallEtaleNeighborhood X.2 xbar
  set A : BigFppfOver B S hS := (SmallEtale.toOver B S hS X.1).obj V.chart with hA
  set e := pointsEquivScheme B S hS A with he
  -- The point of the chart underlying `V` is the image of the geometric point `V` carries.
  have hpt : e.symm (chartPoint B S hS X.1 V) = (neighborhoodPoint B S hS X.1 V).image := by
    rw [show chartPoint B S hS X.1 V = e ((neighborhoodPoint B S hS X.1 V).image) from rfl]
    exact e.symm_apply_apply _
  have himg : pointsMap B S hS (yoneda.obj A) V.chart.obj.hom
      (e.symm (chartPoint B S hS X.1 V)) = x :=
    hpt ▸ (neighborhoodPoint_image B S hS X.1 V).trans hxbar
  -- Stacks 07TY: the support on the chart is the inverse image of the support on `X`.
  have hsupp := supp_restrictToChart_eq_preimage_supportOfSheaf_of_isQuasicoherent
    B S hS X V.chart F
  have hu : chartPoint B S hS X.1 V ∈
      SheafOfModules.supp (restrictToChart B S hS X.2 F V.chart) := by
    rw [hsupp, Set.mem_preimage]
    exact himg ▸ hx
  -- Minimality transfers to the chart: Stacks 03K5 collapses a specialization in a fibre.
  have hminU : ∀ w : chartScheme V.chart,
      w ∈ SheafOfModules.supp (restrictToChart B S hS X.2 F V.chart) →
      w ⤳ chartPoint B S hS X.1 V → w = chartPoint B S hS X.1 V := by
    intro w hw hspec
    have hspec' : e.symm w ⤳ e.symm (chartPoint B S hS X.1 V) :=
      hspec.map (schemePointsHomeomorph B S hS A).symm.continuous
    have hwsupp : pointsMap B S hS (yoneda.obj A) V.chart.obj.hom (e.symm w) ∈
        supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F) := by
      rw [hsupp, Set.mem_preimage] at hw
      exact hw
    have hwspec := hspec'.map
      (continuous_pointsMap B S hS (F := yoneda.obj A) (G := X.1) V.chart.obj.hom)
    rw [himg] at hwspec
    refine (e.symm.injective (eq_of_specializes_of_pointsMap_eq_of_hasFiniteChartFibers
      B S hS X.2 hdecent A V.chart.obj.hom V.chart.property _ _ ?_ hspec')).symm
    rw [himg, hmin _ hwsupp hwspec]
  -- Stacks 05AQ on the chart, then (1) ⟹ (3) of Stacks 0CTW back to `X`.
  have _ : (restrictToChart B S hS X.2 F V.chart).IsQuasicoherent := hqc V.chart
  exact isWeaklyAssociatedPoint_of_isWeaklyAssociatedPoint_restrictToChart B S hS X F x hxbar V
    (mem_weaklyAssociatedPoints_of_mem_supp_of_specializes (chartScheme V.chart)
      (restrictToChart B S hS X.2 F V.chart) (chartPoint B S hS X.1 V) hu hminU)

/-- **Stacks 0CUM.** Let `X` be an algebraic space over `S` all of whose chart fibres are
finite — in particular a decent one — and let `F` be a quasi-coherent `𝒪_X`-module. A point of
`|X|` which lies in the support of `F` and is not a specialization of another point of that
support is weakly associated to `F`. -/
@[stacks 0CUM "with decency read as condition (α) of Stacks 03JX, which is all Stacks 03K5 \
needs, and with no assumed inputs"]
theorem isWeaklyAssociatedPoint_of_mem_supportOfSheaf_of_specializes
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite]
    (hdecent : HasFiniteChartFibersAtEveryPoint B S hS X.1)
    (x : points B S hS X.1)
    (hx : x ∈ supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F))
    (hmin : ∀ y, y ∈ supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F) →
      y ⤳ x → y = x) :
    IsWeaklyAssociatedPoint B S hS X F x :=
  isWeaklyAssociatedPoint_of_mem_supportOfSheaf_of_specializes_of_isQuasicoherent_restrictToChart
    B S hS X F hdecent
    (fun U => isQuasicoherent_restrictToChart B S hS X F inferInstance U) x hx hmin

end AlgebraicGeometry.Space

end
