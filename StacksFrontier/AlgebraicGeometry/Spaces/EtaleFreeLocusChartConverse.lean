module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleFreeLocusBaseChangeReverse
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSourceChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricRepresentative
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatEtaleLocalRing

/-!
# The small-étale-site locus of Stacks 0CZT is the Zariski-chart reading of clause (4) of 0CZS

Clause (4) of Stacks 0CZS — `F` is finite free in an étale neighbourhood of `x` — has two readings:
`AlgebraicGeometry.Space.IsFiniteFreeNearGeometricPoint`, the source's own Zariski-chart reading at
a geometric point, and `AlgebraicGeometry.Space.etaleFiniteFreeLocus`, the small-étale-site locus
in which Stacks 0CZT is stated.  This file passes from the second to the first, at a geometric
point chosen over the given point of the locus, and then proves the base-change equality of Stacks
0CZT at the finite-free reading of the locus.

## Main definitions

* `SmallEtaleNeighborhood.ofEtaleSource`: a small étale neighbourhood of a geometric point `v̄` of
  `V`, read as one of the image geometric point along an étale morphism `a : V ⟶ X` of algebraic
  spaces.

## Main results

* `Stacks.SheafOfModules.exists_nonempty_iso_freeULift_of_isFiniteFree`: a finite free sheaf of
  modules, Stacks 03DE (2), is isomorphic to `SheafOfModules.free (ULift (Fin r))` for some `r`.
* `exists_isFiniteFreeNearGeometricPoint_of_mem_etaleFiniteFreeLocus`: **the converse comparison of
  the two readings of clause (4) of Stacks 0CZS** — a point of the small-étale-site locus of Stacks
  0CZT is the image of a geometric point at which the module is finite free in the source's
  Zariski-chart sense.
* `etaleFiniteFreeLocus_modulePullback_eq_preimage_of_isPullback`: **the base-change clause of
  Stacks 0CZT at the finite-free reading of the locus.**

## References

* [Stacks Project, Tag 0CZS](https://stacks.math.columbia.edu/tag/0CZS)
* [Stacks Project, Tag 0CZT](https://stacks.math.columbia.edu/tag/0CZT)
* [Stacks Project, Tag 0488](https://stacks.math.columbia.edu/tag/0488)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 03DF](https://stacks.math.columbia.edu/tag/03DF)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 04JY](https://stacks.math.columbia.edu/tag/04JY)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u₁ v u

namespace Stacks.SheafOfModules

/-- **A finite free sheaf of modules is isomorphic to a free sheaf on a finite index type.** -/
theorem exists_nonempty_iso_freeULift_of_isFiniteFree {C : Type u₁} [Category.{v} C]
    {J : GrothendieckTopology C} [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] (R : Sheaf J RingCat.{u})
    (M : _root_.SheafOfModules.{u} R) (h : _root_.SheafOfModules.IsFiniteFree R M) :
    ∃ r : ℕ, Nonempty (M ≅ _root_.SheafOfModules.free.{u} (R := R) (ULift.{u} (Fin r))) := by
  obtain ⟨n, ι, ⟨hc⟩⟩ := (_root_.SheafOfModules.isFiniteFree_iff_exists_isColimit R M).1 h
  exact ⟨n, ⟨(((Cofan.mk M ι).isColimitEquivOfEquiv Equiv.ulift) hc).coconePointUniqueUpToIso
    (_root_.SheafOfModules.isColimitFreeCofan (ULift.{u} (Fin n)))⟩⟩

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### An étale neighbourhood of a geometric point, read along an étale morphism -/

/-- **A small étale neighbourhood read along an étale morphism.**  For an étale morphism
`a : V ⟶ X` of algebraic spaces and a geometric point `v̄` of `V`, a small étale neighbourhood of
`v̄` is a small étale neighbourhood of the image geometric point of `X`: the chart is the same
scheme, read as a chart of `X` by `AlgebraicGeometry.Space.chartOfEtaleSource`, and the chosen
lift of the geometric point is unchanged, because the image geometric point has the same field
spectrum and its section is the image of the section of `v̄`. -/
def SmallEtaleNeighborhood.ofEtaleSource {X V : AlgebraicSpaces B S hS} {a : V ⟶ X}
    (ha : IsEtale B S hS a.hom) {vbar : GeometricPoint B S hS V.1}
    (N : SmallEtaleNeighborhood vbar) :
    SmallEtaleNeighborhood (geometricPointMap a.hom vbar) where
  chart := chartOfEtaleSource B S hS ha N.chart
  point := N.point
  point_comp := by
    change (N.chart.obj.hom ≫ a.hom).app (Opposite.op vbar.val.siteObject) N.point =
      a.hom.app (Opposite.op vbar.val.siteObject) vbar.val.value
    rw [FunctorToTypes.comp, N.point_comp]

/-- The chart of a small étale neighbourhood read along an étale morphism is the chart read along
that morphism. -/
theorem SmallEtaleNeighborhood.ofEtaleSource_chart {X V : AlgebraicSpaces B S hS} {a : V ⟶ X}
    (ha : IsEtale B S hS a.hom) {vbar : GeometricPoint B S hS V.1}
    (N : SmallEtaleNeighborhood vbar) :
    (SmallEtaleNeighborhood.ofEtaleSource B S hS ha N).chart =
      chartOfEtaleSource B S hS ha N.chart :=
  rfl

/-! ### The converse comparison of the two readings of clause (4) of Stacks 0CZS -/

/-- **The converse comparison of the two readings of clause (4) of Stacks 0CZS.**  Let `M` be a
quasi-coherent `𝒪_X`-module and let `x` be a point of `|X|` lying in the finite-free étale locus
`AlgebraicGeometry.Space.etaleFiniteFreeLocus` of Stacks 0CZT — there is an étale morphism
`a : V ⟶ X` of algebraic spaces whose image on points contains `x` and along which the inverse
image of `M` is finite free in the sense of Stacks 03DE (2).  Then there is a geometric point `x̄`
of `X` above `x` at which `M` is finite free in an étale neighbourhood in the source's own
Zariski-chart sense, `AlgebraicGeometry.Space.IsFiniteFreeNearGeometricPoint`. -/
theorem exists_isFiniteFreeNearGeometricPoint_of_mem_etaleFiniteFreeLocus
    {X : AlgebraicSpaces B S hS} (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) {x : points B S hS X.1}
    (hx : x ∈ etaleFiniteFreeLocus B S hS M) :
    ∃ xbar : GeometricPoint B S hS X.1, xbar.image = x ∧
      IsFiniteFreeNearGeometricPoint B S hS xbar M := by
  obtain ⟨V, a, hae, ⟨v, hv⟩, hff⟩ := hx
  obtain ⟨vbar, hvbar⟩ := exists_geometricRepresentative B S hS V.1 v
  obtain ⟨N⟩ := nonempty_smallEtaleNeighborhood V.2 vbar
  have hGqc : ((modulePullback B S hS a).obj M).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS a M hM
  have hpull := isFiniteFreeModule_modulePullback B S hS (chartToSpace B S hS V N.chart)
    ((modulePullback B S hS a).obj M) hff
  have ei : chartSmallEtaleRestriction B S hS V ((modulePullback B S hS a).obj M) N.chart ≅
      (modulePullback B S hS (chartToSpace B S hS V N.chart)).obj
        ((modulePullback B S hS a).obj M) :=
    ((modulePullbackIsoEtaleModulePullback B S hS (chartToSpace B S hS V N.chart)
          (isEtale_chartToSpace B S hS V N.chart)).app ((modulePullback B S hS a).obj M) ≪≫
        etaleModulePullbackChartToSpaceIso B S hS V ((modulePullback B S hS a).obj M)
          N.chart).symm
  have hsch := isFiniteFree_chartSchemeModule_of_isFiniteFree_chartSmallEtaleRestriction B S hS V
    ((modulePullback B S hS a).obj M) hGqc N.chart
    (Stacks.SheafOfModules.isFiniteFree_of_iso ei.symm hpull)
  have hX : SheafOfModules.IsFiniteFree
      (chartScheme (chartOfEtaleSource B S hS hae N.chart)).ringCatSheaf
      (restrictToChart B S hS X.2 M (chartOfEtaleSource B S hS hae N.chart)) :=
    Stacks.SheafOfModules.isFiniteFree_of_iso
      (restrictToChartEtaleSourceIso B S hS hae M hM N.chart).symm
      (Stacks.SheafOfModules.isFiniteFree_of_iso
        (restrictToChartIsoChartSchemeModule B S hS V ((modulePullback B S hS a).obj M) hGqc
          N.chart).symm hsch)
  obtain ⟨r, ⟨e⟩⟩ := Stacks.SheafOfModules.exists_nonempty_iso_freeULift_of_isFiniteFree _ _
    (Stacks.SheafOfModules.isFiniteFree_over
      (restrictToChart B S hS X.2 M (chartOfEtaleSource B S hS hae N.chart)) ⊤ hX)
  exact ⟨geometricPointMap a.hom vbar, by rw [geometricPointMap_image, hvbar, hv],
    SmallEtaleNeighborhood.ofEtaleSource B S hS hae N, r, ⊤, trivial, ⟨e⟩⟩

/-! ### The base-change clause of Stacks 0CZT at the finite-free reading of the locus -/

/-- **The base-change clause of Stacks 0CZT at the finite-free reading of the locus.**  Let
`f : X ⟶ Y` be a morphism of algebraic spaces over `S` which is locally of finite presentation,
let `F` be a quasi-coherent `𝒪_X`-module of finite presentation on charts which is flat over `Y`,
and let

```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```

be a cartesian square.  Then the finite-free étale locus of the inverse image `(g')^*F` on `|X'|`
is the inverse image under `|g'|` of the finite-free étale locus of `F` on `|X|`.

The locus here is the finite-free reading of Stacks 03DE (2), not the plain freeness by which
Stacks 0CZT defines its locus. -/
theorem etaleFiniteFreeLocus_modulePullback_eq_preimage_of_isPullback
    {X Y X' Y' : AlgebraicSpaces B S hS} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (hpb : IsPullback g' f' f g) (F : Modules.{u, u} B S hS X.1 X.2)
    [F.IsQuasicoherentOnSite] (hf : IsLocallyOfFinitePresentation B S hS f.hom)
    (hfp : IsFinitePresentationOnCharts B S hS X.2 F)
    (hF : IsFlatOver B S hS X.2 f.hom F) :
    etaleFiniteFreeLocus B S hS ((modulePullback B S hS g').obj F) =
      pointsMap B S hS X'.1 g'.hom ⁻¹' etaleFiniteFreeLocus B S hS F := by
  refine Set.Subset.antisymm (fun x' hx' => ?_)
    (preimage_etaleFiniteFreeLocus_subset_etaleFiniteFreeLocus_modulePullback B S hS g' F)
  obtain ⟨xbar', hxbar', hnear⟩ :=
    exists_isFiniteFreeNearGeometricPoint_of_mem_etaleFiniteFreeLocus B S hS
      ((modulePullback B S hS g').obj F)
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS g' F inferInstance)
      hx'
  have := mem_etaleFiniteFreeLocus_of_isFiniteFreeNearGeometricPoint_modulePullback B S hS hpb F
    hf hfp hF xbar' hnear
  rwa [hxbar'] at this

end AlgebraicGeometry.Space

end
