module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Modules.RestrictFree
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartOpenRestrictionOver
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartPullbackRestrictionIdentification
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleFreeLocusPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeChartScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleGeometricPointCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricFibreStalkEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkFree
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricRepresentative

/-!
# The base-change clause of Stacks 0CZT

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site which is
locally of finite presentation and let `F` be a quasi-coherent `𝒪_X`-module of finite
presentation which is flat over `Y`.  Stacks 0CZT says that the locus

```
W(F) = {x ∈ |X| : F is free in an étale neighbourhood of x}
```

is open and that *its formation commutes with arbitrary base change*.  Openness is proved in
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleFreeLocus.lean`; this file proves the base-change
clause, in the form of the equality

```
W((g')^* F) = |g'|⁻¹(W(F))
```

at an arbitrary cartesian square of algebraic spaces.

## Main results

* `AlgebraicGeometry.Space.etaleFreeLocus_modulePullback_eq`: **Stacks 0CZT, the base-change
  clause.**
* `exists_geometricPoint_flat_geometricFibreModuleStalk_of_mem_etaleFreeLocus`:
  step (A), membership in the locus produces a geometric point above the given point at which
  clause (1) of Stacks 0CZS holds.  No hypothesis on `f` or on `F`.
* `AlgebraicGeometry.Space.mem_etaleFreeLocus_of_flat_geometricFibreModuleStalk`: step (B), clause
  (1) of Stacks 0CZS at a geometric point puts its image point in the locus.  This carries the
  source's hypotheses, through clause (4) of Stacks 0CZS.
* `AlgebraicGeometry.Space.isFreeModule_chartOpenNeighborhood` and
  `AlgebraicGeometry.Space.isFiniteFree_modulePullback_chartToSpace`: the passage from the
  trivialization on a Zariski open of an étale scheme chart which clause (4) of Stacks 0CZS
  produces to freeness of the inverse image on the chart space, which is the reading the locus
  asks for.

## Implementation notes

The two inclusions are proved by different arguments, and only one of them costs anything.

The easy inclusion `|g'|⁻¹(W(F)) ⊆ W((g')^* F)` holds for an *arbitrary* morphism and with no
hypothesis at all; it is
`AlgebraicGeometry.Space.preimage_etaleFreeLocus_subset` of
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleFreeLocusPullback.lean`.  Nothing about a base change
is used: a trivializing étale neighbourhood pulls back to one of the same index type, because
the inverse image of Stacks 03LU preserves coproducts.

The hard inclusion `W((g')^* F) ⊆ |g'|⁻¹(W(F))` is the source's own argument, and it runs
through clause (1) of Stacks 0CZS — flatness of the geometric fibre stalk — at a geometric point
`x̄'` above the given point `x'` of `|X'|`:

```
x' ∈ W((g')^* F)  ==(A)==>  clause (1) at x̄'  ==(invariance)==>  clause (1) at |g'|(x̄')
                  ==(B)==>  |g'|(x') ∈ W(F)
```

The middle step is `AlgebraicGeometry.Space.flat_geometricFibreModuleStalk_modulePullback_iff`,
which needs nothing but the cartesian square — in particular no flatness of `g`, and no
hypothesis of Stacks 0CZT.  The two ends are (A) and (B) above.

**Where the hypotheses are used, and where they are not.**  Step (A) uses none of them: freeness
of the module on the étale neighbourhood gives freeness of its geometric stalk at an arbitrary
index type (`AlgebraicGeometry.Space.free_geometricModuleStalk_of_isFreeModule`), that gives
clause (1) for the composite
(`AlgebraicGeometry.Space.flat_geometricFibreModuleStalk_of_free_geometricModuleStalk`), and
clause (1) is étale-local on the source
(`AlgebraicGeometry.Space.flat_geometricFibreModuleStalk_comp_modulePullback_iff`).  Step (B) is
where the source's hypotheses enter, through clause (4) of Stacks 0CZS
(`AlgebraicGeometry.Space.exists_chartOpen_over_iso_free_of_flat_geometricFibreModuleStalk`),
which is stated under them.  They are therefore needed **downstairs only**: the statement below
asks nothing of `(g')^* F` or of `f'`, so no stability of the hypotheses under base change is
required, and none is used.

`AlgebraicGeometry.Space.IsFinitePresentationOnSite` and
`AlgebraicGeometry.Space.IsFinitePresentationOnCharts` are two different predicates; the
statement below takes the first, which is what Stacks 0CZT's own hypothesis is and what the
consumers in `StacksFrontier/AlgebraicGeometry/Quot/PicardStackOpenInCoherentStack.lean` carry,
and `AlgebraicGeometry.Space.isFinitePresentationOnCharts_of_isFinitePresentationOnSite`
converts it to the second, which is what clause (4) takes.

**The last hop of (B) does not use the site identification that clause (4) disclaims.**  Clause
(4) hands back an étale scheme chart `(U, u)`, a Zariski open `W ∋ u` and a trivialization of
`(φ^* F)|_W` on the slice of the Zariski site of `U` at `W`.  That `W` is itself a small étale
neighbourhood of `x̄` in `X`
(`AlgebraicGeometry.Space.chartOpenNeighborhood`), and
`AlgebraicGeometry.Space.nonempty_over_restrictToChart_chartOpenNeighborhood` reads the
trivialization as one of the chart restriction of `F` at that neighbourhood.  From there the
route is the *outright freeness* analogue of the chain which
`AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_over_of_isFiniteLocallyFree_chartSchemeModule`
runs for finite local freeness, and it goes directly to the inverse image on the chart space
rather than to the restriction to the slice of the small étale site of `X`: Stacks 03DX (2)
carries a free Zariski module to a free module on the small étale site of the chart scheme
(`AlgebraicGeometry.SmallEtale.isFiniteFree_associatedModule_iff`, whose content is that the
associated module of a free module is free), the comparison of a representable algebraic space
with its scheme carries that across
(`AlgebraicGeometry.Space.isFiniteFree_representedSmallEtaleModule_iff`), and the result *is* the
inverse image along the structure morphism of the chart, by Stacks 04M0 and Equation 03LW
(`AlgebraicGeometry.Space.etaleModulePullback_chartToSpace_eq_chartSmallEtaleRestriction`, an
equality, and `AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback`).  So the
identification of an arbitrary small étale neighbourhood of algebraic spaces with a Zariski open
of a scheme chart, which the attribute on clause (4) records as not claimed, is never needed:
the neighbourhood produced here *is* a chart.

## References

* [Stacks Project, Tag 0CZT](https://stacks.math.columbia.edu/tag/0CZT)
* [Stacks Project, Tag 0CZS](https://stacks.math.columbia.edu/tag/0CZS)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 05VQ](https://stacks.math.columbia.edu/tag/05VQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### From a free Zariski chart module to freeness on the chart space -/

/-- **If the Zariski chart module of Stacks 03DX (2) is finite free, so is the inverse image of
the module on the chart space.**  This is the outright-freeness analogue of
`AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_over_of_isFiniteLocallyFree_chartSchemeModule`,
and it lands on the inverse image along the structure morphism of the chart rather than on the
restriction to the slice of the small étale site.

The chain is Stacks 03DX (2) for finite freeness
(`AlgebraicGeometry.SmallEtale.isFiniteFree_associatedModule_iff`), its counit at the chart
scheme, the comparison of a representable algebraic space with its scheme
(`AlgebraicGeometry.Space.isFiniteFree_representedSmallEtaleModule_iff`), and the identification
of the result with the inverse image of Stacks 03LU. -/
theorem isFiniteFree_modulePullback_chartToSpace (X : AlgebraicSpaces B S hS)
    (F : Modules.{u, u} B S hS X.1 X.2) (hqc : F.IsQuasicoherentOnSite)
    (A : SmallEtale B S hS X.1)
    (h : SheafOfModules.IsFiniteFree (chartScheme A).ringCatSheaf
      (chartSchemeModule B S hS X F hqc A)) :
    SheafOfModules.IsFiniteFree
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (chartSpace B S hS X A).1
        (chartSpace B S hS X A).2).O)
      ((modulePullback B S hS (chartToSpace B S hS X A)).obj F) := by
  have := isQuasicoherent_chartSchemeModule B S hS X F hqc A
  have h3 := (_root_.AlgebraicGeometry.SmallEtale.isFiniteFree_associatedModule_iff
    (associatedBigEtaleSite B) (chartScheme A)
    ((SmallEtale.toOver B S hS X.1).obj A).left.property
    (chartSchemeModule B S hS X F hqc A)).2 h
  have h4 := Stacks.SheafOfModules.isFiniteFree_of_iso
    (associatedModuleChartSchemeModuleIso B S hS X F hqc A) h3
  have h5 := (isFiniteFree_representedSmallEtaleModule_iff B S hS
    ((SmallEtale.toOver B S hS X.1).obj A) (chartSchemeEtaleModule B S hS X F hqc A)).2 h4
  have h6 := Stacks.SheafOfModules.isFiniteFree_of_iso
    (representedSmallEtaleChartSchemeEtaleModuleIso B S hS X F hqc A) h5
  have h7 : SheafOfModules.IsFiniteFree _ (chartSmallEtaleRestriction B S hS X F A) := h6
  have h8 : SheafOfModules.IsFiniteFree _
      ((etaleModulePullback B S hS (chartToSpace B S hS X A)
        (isEtale_chartToSpace B S hS X A)).obj F) := by
    rw [etaleModulePullback_chartToSpace_eq_chartSmallEtaleRestriction B S hS X F A]
    exact h7
  exact Stacks.SheafOfModules.isFiniteFree_of_iso
    (((modulePullbackIsoEtaleModulePullback B S hS (chartToSpace B S hS X A)
      (isEtale_chartToSpace B S hS X A)).app F)).symm h8

/-- **The trivialization clause (4) of Stacks 0CZS produces makes the module free on an étale
neighbourhood of algebraic spaces.**  Given an étale scheme chart `(U, u)` over `(X, x̄)`, a
Zariski open `W ∋ u` of `U` and an isomorphism of `(φ^* F)|_W` with a finite free module, the
inverse image of `F` on the chart space of the étale chart `W` cuts out is free in the sense of
`AlgebraicGeometry.Space.IsFreeModule`.

`AlgebraicGeometry.Space.nonempty_over_restrictToChart_chartOpenNeighborhood` reads the
trivialization as one of the chart restriction of `F` at
`AlgebraicGeometry.Space.chartOpenNeighborhood`, the free module on the slice being the free
module on the open subscheme by
`AlgebraicGeometry.Scheme.Modules.overEquivFunctorObjFree`, and
`AlgebraicGeometry.Space.isFiniteFree_modulePullback_chartToSpace` carries it to the chart
space. -/
theorem isFreeModule_chartOpenNeighborhood (X : AlgebraicSpaces B S hS)
    (F : Modules.{u, u} B S hS X.1 X.2) (hqc : F.IsQuasicoherentOnSite)
    {xbar : GeometricPoint B S hS X.1} (N : SmallEtaleNeighborhood xbar)
    (W : (chartScheme N.chart).Opens) (hw : chartPoint B S hS X.1 N ∈ W) {r : ℕ}
    (e : (restrictToChart B S hS X.2 F N.chart).over W ≅
      SheafOfModules.free (ULift.{u} (Fin r))) :
    IsFreeModule B S hS (chartSpace B S hS X (chartOpenNeighborhood B S hS N W hw).chart)
      ((modulePullback B S hS
        (chartToSpace B S hS X (chartOpenNeighborhood B S hS N W hw).chart)).obj F) := by
  have iso : restrictToChart B S hS X.2 F (chartOpenNeighborhood B S hS N W hw).chart ≅
      SheafOfModules.free (ULift.{u} (Fin r)) :=
    (nonempty_over_restrictToChart_chartOpenNeighborhood B S hS X F hqc N W hw).some.symm ≪≫
      (Scheme.Modules.overEquiv W).functor.mapIso e ≪≫
      Scheme.Modules.overEquivFunctorObjFree W (ULift.{u} (Fin r))
  have hff : SheafOfModules.IsFiniteFree
      (chartScheme (chartOpenNeighborhood B S hS N W hw).chart).ringCatSheaf
      (chartSchemeModule B S hS X F hqc (chartOpenNeighborhood B S hS N W hw).chart) :=
    Stacks.SheafOfModules.isFiniteFree_of_iso
      (restrictToChartIsoChartSchemeModule B S hS X F hqc
        (chartOpenNeighborhood B S hS N W hw).chart)
      (Stacks.SheafOfModules.isFiniteFree_of_iso iso.symm
        (Stacks.SheafOfModules.isFiniteFree_freeULift _ r))
  exact IsFreeModule.of_isFiniteFree B S hS
    (chartSpace B S hS X (chartOpenNeighborhood B S hS N W hw).chart) _
    (isFiniteFree_modulePullback_chartToSpace B S hS X F hqc
      (chartOpenNeighborhood B S hS N W hw).chart hff)

/-! ### The two ends of the transport -/

/-- **Step (A): membership in the étale free locus gives clause (1) of Stacks 0CZS at a geometric
point above the point.**  If `F` is free on an étale neighbourhood of `x`, then there is a
geometric point `x̄` above `x` at which the geometric fibre stalk of `F` over `f` is flat.

No hypothesis on `f` or on `F` is used.  The three steps are: the geometric stalk of a module
free on the small étale site is free over the étale local ring, at an arbitrary index type
(`AlgebraicGeometry.Space.free_geometricModuleStalk_of_isFreeModule`); a free geometric stalk
gives clause (1)
(`AlgebraicGeometry.Space.flat_geometricFibreModuleStalk_of_free_geometricModuleStalk`), for the
composite `a ≫ f`; and clause (1) is étale-local on the source
(`AlgebraicGeometry.Space.flat_geometricFibreModuleStalk_comp_modulePullback_iff`), which moves
it from the neighbourhood down to `X`. -/
theorem exists_geometricPoint_flat_geometricFibreModuleStalk_of_mem_etaleFreeLocus
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    {x : points B S hS X.1} (hx : x ∈ etaleFreeLocus B S hS F) :
    ∃ xbar : GeometricPoint B S hS X.1, xbar.LiesOver x ∧
      Module.Flat (geometricFibreLocalRing B S hS f xbar)
        (geometricFibreModuleStalk B S hS f F xbar) := by
  obtain ⟨V, a, hae, ⟨v, hv⟩, hfree⟩ := hx
  obtain ⟨vbar, hvbar⟩ := exists_geometricRepresentative B S hS V.1 v
  refine ⟨geometricPointMap a.hom vbar, ?_, ?_⟩
  · change (geometricPointMap a.hom vbar).image = x
    rw [geometricPointMap_image, hvbar]
    exact hv
  · exact (flat_geometricFibreModuleStalk_comp_modulePullback_iff B S hS hae f F vbar).2
      (flat_geometricFibreModuleStalk_of_free_geometricModuleStalk B S hS (a ≫ f) _ vbar
        (free_geometricModuleStalk_of_isFreeModule B S hS V vbar _ hfree))

/-- **Step (B): clause (1) of Stacks 0CZS at a geometric point puts its image point in the étale
free locus.**  Under the source's own hypotheses — `f` locally of finite presentation, `F`
quasi-coherent and of finite presentation on charts, `F` flat over `Y` at `x̄` — flatness of the
geometric fibre stalk at `x̄` makes `x̄`'s image point a point at which `F` is free in an étale
neighbourhood.

Clause (4) of Stacks 0CZS
(`AlgebraicGeometry.Space.exists_chartOpen_over_iso_free_of_flat_geometricFibreModuleStalk`)
produces a trivialization on a Zariski open of an étale scheme chart of `x̄`, and
`AlgebraicGeometry.Space.isFreeModule_chartOpenNeighborhood` turns it into freeness on the chart
space of that open, which is an étale neighbourhood of algebraic spaces containing the image
point by `AlgebraicGeometry.Space.chartFieldValuedPoint_pointsMap`. -/
theorem mem_etaleFreeLocus_of_flat_geometricFibreModuleStalk
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    (hqc : F.IsQuasicoherentOnSite) (hf : IsLocallyOfFinitePresentation B S hS f.hom)
    (hfp : IsFinitePresentationOnCharts B S hS X.2 F)
    (xbar : GeometricPoint B S hS X.1)
    (hflat : IsFlatOverAtGeometricPoint B S hS f F xbar)
    (hfibre : Module.Flat (geometricFibreLocalRing B S hS f xbar)
      (geometricFibreModuleStalk B S hS f F xbar)) :
    xbar.image ∈ etaleFreeLocus B S hS F := by
  have := hqc
  obtain ⟨N, W, hw, r, ⟨e⟩⟩ :=
    exists_chartOpen_over_iso_free_of_flat_geometricFibreModuleStalk B S hS f F hf hfp xbar
      hflat hfibre
  exact ⟨chartSpace B S hS X (chartOpenNeighborhood B S hS N W hw).chart,
    chartToSpace B S hS X (chartOpenNeighborhood B S hS N W hw).chart,
    isEtale_chartToSpace B S hS X _,
    ⟨(chartFieldValuedPoint (chartOpenNeighborhood B S hS N W hw)).class B S hS _,
      chartFieldValuedPoint_pointsMap (chartOpenNeighborhood B S hS N W hw)⟩,
    isFreeModule_chartOpenNeighborhood B S hS X F hqc N W hw e⟩

/-! ### The base-change clause -/

/-- **Stacks 0CZT, the base-change clause.**  Let

```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```

be a cartesian square of algebraic spaces over `S`, let `f` be locally of finite presentation and
let `F` be a quasi-coherent `𝒪_X`-module of finite presentation on the small étale site which is
flat over `Y`.  Then the étale free locus of the inverse image of `F` on `X'` is the inverse
image of the étale free locus of `F`:

```
W((g')^* F) = |g'|⁻¹(W(F)).
```

The hypotheses are asked of `f` and `F` only, which is what the source asks; nothing is required
of `f'` or of `(g')^* F`, so no stability of the hypotheses under base change is used.

The inclusion `⊇` is `AlgebraicGeometry.Space.preimage_etaleFreeLocus_subset` and holds for an
arbitrary morphism with no hypothesis.  The inclusion `⊆` is the source's argument, transporting
clause (1) of Stacks 0CZS across the square by
`AlgebraicGeometry.Space.flat_geometricFibreModuleStalk_modulePullback_iff`, between the two ends
`exists_geometricPoint_flat_geometricFibreModuleStalk_of_mem_etaleFreeLocus` and
`AlgebraicGeometry.Space.mem_etaleFreeLocus_of_flat_geometricFibreModuleStalk`. -/
@[stacks 0CZT "the base-change clause: the formation of the locus W commutes with arbitrary base \
change, as the EQUALITY W((g')^* F) = |g'|^(-1)(W(F)) of subsets of |X'|, at an arbitrary \
cartesian square of algebraic spaces over S. The openness clause is isOpen_etaleFreeLocus of \
Spaces/EtaleFreeLocus.lean; the two together are the whole tag. Hypotheses are the source's own \
and are asked DOWNSTAIRS only, of f and F: f locally of finite presentation, F quasi-coherent, \
F of finite presentation on the small etale site, and F flat over Y. Nothing is asked of f' or \
of the inverse image of F, so no stability of the hypotheses under base change is used. The \
test scheme T of the source is not named: the statement is at a cartesian square, of which the \
square of a morphism of test schemes is an instance by isPullback_baseChangeMap. Freeness is \
IsFreeModule, the universal-property reading on the small etale site, at an arbitrary index \
type."]
theorem etaleFreeLocus_modulePullback_eq
    {X Y X' Y' : AlgebraicSpaces B S hS} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (hpb : IsPullback g' f' f g) (F : Modules.{u, u} B S hS X.1 X.2)
    (hqc : F.IsQuasicoherentOnSite) (hf : IsLocallyOfFinitePresentation B S hS f.hom)
    (hfp : SheafOfModules.IsFinitePresentationOnSite F)
    (hflat : IsFlatOver B S hS X.2 f.hom F) :
    etaleFreeLocus B S hS ((modulePullback B S hS g').obj F) =
      pointsMap B S hS X'.1 g'.hom ⁻¹' etaleFreeLocus B S hS F := by
  have := hqc
  refine Set.Subset.antisymm (fun x' hx' => ?_) (preimage_etaleFreeLocus_subset B S hS g' F)
  obtain ⟨xbar', hxbar', hfibre'⟩ :=
    exists_geometricPoint_flat_geometricFibreModuleStalk_of_mem_etaleFreeLocus B S hS f'
      ((modulePullback B S hS g').obj F) hx'
  have hfibre := (flat_geometricFibreModuleStalk_modulePullback_iff B S hS hpb F xbar').2 hfibre'
  have key := mem_etaleFreeLocus_of_flat_geometricFibreModuleStalk B S hS f F hqc hf
    (isFinitePresentationOnCharts_of_isFinitePresentationOnSite B S hS X F hqc hfp)
    (geometricPointMap g'.hom xbar')
    ((isFlatOver_iff_forall_isFlatOverAtGeometricPoint B S hS f F).1 hflat _) hfibre
  rw [geometricPointMap_image, hxbar'] at key
  exact key

end AlgebraicGeometry.Space

end
