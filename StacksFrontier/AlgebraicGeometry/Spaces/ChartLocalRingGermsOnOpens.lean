module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartOpenNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkBaseChange

/-!
# The comparison map to the étale local ring on germs over opens of the chart

Let `X` be an algebraic space over a scheme `S`, let `x̄` be a geometric point of `X` and let
`V` be a small étale neighbourhood of `x̄` whose chart is a scheme `U`.  The canonical map
`AlgebraicGeometry.Space.chartLocalRingToEtaleLocalRing` of Stacks 05VP sends the ordinary germ
at `u` of a *global* function on `U` to the germ of the same function at `x̄`
(`AlgebraicGeometry.Space.chartLocalRingToEtaleLocalRing_germ`).  This file upgrades that to
the germ of a function on an arbitrary Zariski open `W` of `U` containing `u`: it is sent to the
germ of the restricted function on the small étale neighbourhood
`AlgebraicGeometry.Space.chartOpenNeighborhood` given by `W`.

## Main results

* `AlgebraicGeometry.Space.chartLocalRingToEtaleLocalRing_germ_open` and
  `AlgebraicGeometry.Space.chartLocalRingToEtaleLocalRing_germ_open'`: the canonical map
  `𝒪_{U, u} → 𝒪_{X, x̄}` sends the ordinary germ at `u` of a regular function on a Zariski open
  `W ∋ u` of the chart to the germ at `x̄` of the same function, read on the small étale
  neighbourhood `W`.  The two forms differ only in how the restricted function is written: by
  `TopologicalSpace.Opens.topIso` on the chart, or by
  `AlgebraicGeometry.Space.chartRestrictionRingHom`, which agree on the nose.
* `AlgebraicGeometry.Space.germ_stalkMap_openTop`: the stalk map of the inclusion of a Zariski
  open of a scheme carries an ordinary germ over that open to the germ of the restricted
  function over the whole open subscheme.

## Implementation notes

The global case is not enough to deduce the general one: the canonical map is built from
`AlgebraicGeometry.Space.strictHenselizationEquivEtaleLocalRing`, which is chosen from an
existence statement, so it is pinned down only by what
`AlgebraicGeometry.Space.etaleLocalRingEquivChart` asserts about it.  The relevant assertion is
the second one, which matches germs at every *pointed étale refinement* of the chart inside a
big étale site; a Zariski open `W ∋ u` of the chart, with the lift of the geometric point
supplied by `AlgebraicGeometry.Space.chartOpenLift`, is such a refinement.  The proof therefore
compares both sides inside
`_root_.AlgebraicGeometry.etaleLocalRing`: the left side through
`AlgebraicGeometry.etaleLocalRing_strictHenselization_canonical` and
`AlgebraicGeometry.structureSheafStalkFromLocalRing_germ`, the right side through that second
assertion, and both land on the same component of the colimit presenting the scheme-side étale
local ring.

The scheme-level input to `AlgebraicGeometry.structureSheafStalkFromLocalRing_germ` is
`AlgebraicGeometry.Space.germ_stalkMap_openTop`, which is read off
`AlgebraicGeometry.Scheme.Opens.germ_stalkIso_inv` and
`AlgebraicGeometry.Scheme.Opens.stalkIso_inv` together with the fact that
`TopologicalSpace.Opens.topIso` is the restriction map of the presheaf along the equality
`W.ι ''ᵁ ⊤ = W`, which holds by `rfl`.

## References

* [Stacks Project, Tag 05VP](https://stacks.math.columbia.edu/tag/05VP)
* [Stacks Project, Tag 04KF](https://stacks.math.columbia.edu/tag/04KF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits IsLocalRing Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

/-- **The stalk map of an open immersion of a Zariski open on ordinary germs.**  The germ at a
point of the open of a function defined on the open, transported along the stalk map of the
inclusion, is the germ of the same function read as a global function on the open subscheme. -/
theorem germ_stalkMap_openTop (Z : Scheme.{u}) (W : Z.Opens) (p : W.toScheme)
    (a : Γ(Z, W)) :
    (W.ι.stalkMap p).hom (Z.presheaf.germ W p.1 p.2 a) =
      W.toScheme.presheaf.germ ⊤ p trivial (W.topIso.inv a) := by
  have hmap : (W.topIso.inv : Γ(Z, W) ⟶ Γ(W.toScheme, ⊤)) =
      Z.presheaf.map (homOfLE (le_of_eq W.ι_image_top)).op := rfl
  have h1 := Scheme.Opens.germ_stalkIso_inv W ⊤ p trivial
  rw [Scheme.Opens.stalkIso_inv W p] at h1
  have h3 := (ConcreteCategory.comp_apply
      (Z.presheaf.germ (W.ι ''ᵁ (⊤ : W.toScheme.Opens)) p.1 ⟨p, trivial, rfl⟩)
      (W.ι.stalkMap p) (W.topIso.inv a)).symm.trans
    (ConcreteCategory.congr_hom h1 (W.topIso.inv a))
  refine Eq.trans (congrArg _ ?_) h3
  rw [hmap]
  exact (ConcreteCategory.congr_hom
    (Z.presheaf.germ_res (homOfLE (le_of_eq W.ι_image_top)) p.1 ⟨p, trivial, rfl⟩) a).symm

/-- `AlgebraicGeometry.Space.germ_stalkMap_openTop` with the point of the ambient scheme given
by an equation rather than as the image of the point of the open. -/
theorem germ_stalkMap_openTop_of_eq (Z : Scheme.{u}) (W : Z.Opens) (p : W.toScheme)
    (y : Z) (hy : W.ι p = y) (hyW : y ∈ W) (a : Γ(Z, W)) :
    (W.ι.stalkMap p).hom (hy.symm ▸ Z.presheaf.germ W y hyW a) =
      W.toScheme.presheaf.germ ⊤ p trivial (W.topIso.inv a) := by
  subst y
  exact germ_stalkMap_openTop Z W p a

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)

/-- **The comparison map `𝒪_{U, u} → 𝒪_{X, x̄}` on germs of functions on an open of the
chart.**  The ordinary germ at `u` of a regular function on a Zariski open `W ∋ u` of the chart
is sent to the germ at `x̄` of the same function, read on the small étale neighbourhood
`AlgebraicGeometry.Space.chartOpenNeighborhood` given by `W`.  This extends
`AlgebraicGeometry.Space.chartLocalRingToEtaleLocalRing_germ`, which is the case `W = ⊤`. -/
@[stacks 05VP "the comparison map on germs of functions on an open of the chart"]
theorem chartLocalRingToEtaleLocalRing_germ_open {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (W : (chartScheme V.chart).Opens)
    (hw : chartPoint B S hS X V ∈ W) (a : Γ(chartScheme V.chart, W)) :
    chartLocalRingToEtaleLocalRing B S hS X hX V
        ((chartScheme V.chart).presheaf.germ W (chartPoint B S hS X V) hw a) =
      etaleLocalRingGerm B S hS X x (op (chartOpenNeighborhood B S hS V W hw))
        (W.topIso.inv a) := by
  let E := bigEtaleSiteOfFppfSite B
  have hV : E.Contains (neighborhoodChartScheme V) := V.chart.obj.left.left.property
  let Y := chartScheme V.chart
  let g := chartGeometricPoint V
  let T := chartHenselizationTower B S hS X V
  let N := chartOpenNeighborhood B S hS V W hw
  let i : N ⟶ V := chartOpenNeighborhoodHom B S hS V W hw
  let pt : g.source ⟶ W.toScheme := (chartGeometricPoint N).hom
  have hpt : pt ≫ W.ι = g.hom := chartOpenLift_comp B S hS V W hw
  have hWsize : E.Contains W.toScheme := (Scheme.size_coe_opens_le _ W).trans_lt hV
  let W' : _root_.AlgebraicGeometry.SmallEtale E Y hV :=
    ⟨Over.mk (ObjectProperty.homMk W.ι : E.obj W.toScheme hWsize ⟶ E.obj Y hV), by
      show Etale W.ι
      infer_instance⟩
  let n : (geometricPointFiber E Y hV g).Elementsᵒᵖ := op ((geometricPointFiber E Y hV g).elementsMk W' ⟨pt, hpt⟩)
  let pW : W.toScheme := pt (closedPoint g.residueField)
  have hpW : W.ι pW = chartPoint B S hS X V :=
    (Scheme.Hom.comp_apply pt W.ι _).symm.trans
      (congrArg (fun f : g.source ⟶ Y => f (closedPoint g.residueField)) hpt)
  let a' := W.topIso.inv a
  let e := etaleLocalRingEquivChart hX V E hV
  let c := etaleLocalRing_strictHenselization_canonical E Y hV g T
  apply e.val.injective
  refine Eq.trans ?_ (e.property.2 N i n a' rfl HEq.rfl HEq.rfl).symm
  refine Eq.trans ?_ (structureSheafStalkFromLocalRing_germ E Y hV g n
    ((chartScheme V.chart).presheaf.germ W (chartPoint B S hS X V) hw a) a'
    (germ_stalkMap_openTop_of_eq Y W pW (chartPoint B S hS X V) hpW hw a))
  show e.val ((c.val.trans e.val.symm)
    (algebraMap _ T.strictHenselization
      ((chartScheme V.chart).presheaf.germ W (chartPoint B S hS X V) hw a))) = _
  rw [RingEquiv.trans_apply, e.val.apply_symm_apply]
  exact c.property.1 _

/-- The comparison of the structure sheaf of the chart with the restriction of the structure
sheaf of the algebraic space is, on sections over a Zariski open `W` of the chart, the
identification of `Γ(W)` with the global functions on `W` as a scheme. -/
theorem chartRestrictionRingHom_app_apply {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (W : (chartScheme V.chart).Opens)
    (a : Γ(chartScheme V.chart, W)) :
    ((chartRestrictionRingHom B S hS hX V.chart).app (op W)).hom a = W.topIso.inv a := rfl

/-- `AlgebraicGeometry.Space.chartLocalRingToEtaleLocalRing_germ_open` with the restricted
function written through `AlgebraicGeometry.Space.chartRestrictionRingHom`, the form in which
the sections of a module on the algebraic space carry their scalars over an open of the
chart. -/
@[stacks 05VP "the comparison map on germs, through the chart restriction of functions"]
theorem chartLocalRingToEtaleLocalRing_germ_open' {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (W : (chartScheme V.chart).Opens)
    (hw : chartPoint B S hS X V ∈ W) (a : Γ(chartScheme V.chart, W)) :
    chartLocalRingToEtaleLocalRing B S hS X hX V
        ((chartScheme V.chart).presheaf.germ W (chartPoint B S hS X V) hw a) =
      etaleLocalRingGerm B S hS X x (op (chartOpenNeighborhood B S hS V W hw))
        (((chartRestrictionRingHom B S hS hX V.chart).app (op W)).hom a) :=
  chartLocalRingToEtaleLocalRing_germ_open B S hS hX V W hw a

end AlgebraicGeometry.Space

end
