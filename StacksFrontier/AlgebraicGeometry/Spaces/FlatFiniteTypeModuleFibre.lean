module

public import StacksFrontier.AlgebraicGeometry.Etale.FlatFiniteTypeNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionSections
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.SingletonChartFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFiniteTypeModuleLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleAtGeometricPointEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.UniversallyClosedSeparation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointsConditions

/-!
# Openness in a fibre of the relative flat locus on an algebraic space

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site which is
locally of finite type, let `F` be a quasi-coherent `𝒪_X`-module of finite type and let `y` be a
point of `|Y|` which has a quasi-compact field-valued representative — condition (5) of
Stacks 03JV, which holds at every point of a decent algebraic space. Inside the set-theoretic
fibre `f^{-1}({y}) ⊆ |X|`, with its subspace topology, the points at which `F` is flat over `Y`
form an open subset. This is Stacks 0CWK. The source asks nothing of `y`, and without a
condition on `y` the statement is false:
`Stacks.Examples.NonOpenFlatLocusSpace.not_isOpen_flatLocus_setFibre_of_free_shift`
exhibits an algebraic space, a morphism to it locally of finite type, a quasi-coherent
module of finite type on its source and a point of its target at which the unrestricted
statement fails.

## Main definitions

* `AlgebraicGeometry.Space.HasUniquePointInSomeChart`: some étale scheme chart of the target has
  exactly one point above the given point.

## Main results

* `AlgebraicGeometry.Space.isFlatOverAtOnChartDiagram_iff_mem_flatLocus` is chart independence
  of flatness over the target at a point, read off Stacks 05VU: on every commuting square of
  étale scheme charts, flatness of the restricted module at a point of the source chart is
  membership of the image point in the relative flat locus of Stacks 05VV.
* `AlgebraicGeometry.Space.exists_etaleChart_covering_setFibre` chooses, for an étale scheme
  chart `(V, v)` of the target above `y`, an étale scheme chart of the source over `V` whose
  points cover the set-theoretic fibre over `y`.
* `AlgebraicGeometry.Space.HasQuasiCompactFieldRepresentative.hasUniquePointInSomeChart` is the
  shrinking step of the proof of Stacks 0AC8: a point with a quasi-compact field-valued
  representative has an étale scheme chart with exactly one point above it.
* `AlgebraicGeometry.Space.isOpen_flatLocus_setFibre` is **Stacks 0CWK** at a point with a
  quasi-compact field-valued representative, which is as far as the source's statement is true;
  `AlgebraicGeometry.Space.isOpen_flatLocus_setFibre_of_hasUniquePointInSomeChart` is the form
  of it for a target chart with a single point above `y`, and
  `AlgebraicGeometry.Space.isOpen_flatLocus_setFibre_of_isDecentSpace` the form for a decent
  target.

## Implementation notes

The pointwise flatness predicate is `AlgebraicGeometry.Space.flatLocus`, the some-chart form of
Stacks 05VV part (1); Stacks 05VU, in the form
`AlgebraicGeometry.Space.isFlatOverAt_exists_chartDiagram_iff_isFlatOverAtGeometricPoint`,
shows that it does not depend on the chart, and that independence is what the proof below needs.
Quasi-coherence and finite type of the module are assumed both on the small étale site, as
Stacks 05VU requires, and chartwise, as the scheme-level Stacks 05M9 requires; the implication
from the site-local predicates to the chartwise ones (Tag 060Q) is not formalized, so both
readings of the hypothesis are assumed.

The topological step of the source's proof is that `|U_v| → f^{-1}({y})` is an open map for a
scheme `U` surjective and étale over `V ×_Y X`, and that step does not hold for an arbitrary
point of an arbitrary algebraic space. What makes it correct is that the preimage of the fibre in
the chart of the source is the single scheme-theoretic fibre `U_v`, and that holds exactly when
`v` is the only point of `V` above `y`, which is the condition
`AlgebraicGeometry.Space.HasUniquePointInSomeChart` on the target.

The proof of Stacks 0AC8 produces such a chart by shrinking an affine one, using that `y` has a
quasi-compact field-valued representative; that shrinking step is
`AlgebraicGeometry.Space.exists_etale_chart_singleton_fibre_of_isQuasiCompact_fieldMorphism`.
The condition is not vacuous for this argument: for the non-decent space `𝔸^1_ℚ/ℤ` and the image
`y` of the origin, every nonempty étale scheme chart has infinitely many points above `y`, since
a `ℤ`-torsor over a connected scheme is trivial, so such a chart is covered by one whose
composite to `𝔸^1_ℚ` is étale, and the image of an étale morphism to `𝔸^1_ℚ` is a nonempty open,
hence omits only finitely many of the integral points whose orbit `y` is.

A condition at `y` cannot be dropped: the statement of Stacks 0CWK, and not only its proof, fails at
a point with no quasi-compact field-valued representative. That is
`Stacks.Examples.NonOpenFlatLocusSpace.not_isOpen_flatLocus_setFibre_of_free_shift`, which exhibits
a big fppf site, a morphism of algebraic spaces locally of finite type over `Spec ℚ`, a
quasi-coherent module of finite type on its source and a point of its target satisfying every
hypothesis of `AlgebraicGeometry.Space.isOpen_flatLocus_setFibre` except the one on `y`, and at
which the conclusion fails. The hypothesis-carrying form of it is
`Stacks.Examples.NonOpenFlatLocusSpace.not_isOpen_setOf_mem_flatLocus`.

In that counterexample `A = ℚ[t, u_i (i ∈ ℤ)]/((t - i) u_i : i ∈ ℤ)`, the integers act on
`Spec A` over `Spec ℚ` by `t ↦ t - n`, `u_i ↦ u_{i + n}`
(`Stacks.Examples.NonOpenFlatLocusSpace.shiftAction`), and `Y = Spec A / ℤ` with
`f : Spec A ⟶ Y` the quotient map (`…fmap`), locally of finite type by
`…isLocallyOfFiniteType_fmap`. The module is `F = A ⧸ I` with `I = (u_i : i ≥ 1)`
(`…Fm`), of finite type on charts by `…isFiniteTypeOnCharts_Fm`, and `y`
is the image of the `ℚ`-point `p_0 = (t) + (u_i : i ∈ ℤ)` (`…ybase`).

The argument has three inputs. The freeness of the action on residue fields —
condition (*) of Stacks 02Z2, which makes the graph relation an étale equivalence relation and
the quotient an algebraic space by Stacks 02WW — is
`Stacks.Examples.NonOpenFlatLocusSpace.shiftAction_residueFieldFaithful`: the
`n`-th shift translates the global section `t` by `n ∈ ℚ^×`, so it fixes no point of `Spec A`
at all. That the set-theoretic fibre over `y` is the single orbit `{p_m : m ∈ ℤ}` of the
maximal ideals `p_m = (t - m) + (u_i : i ∈ ℤ)` is
`Stacks.Examples.NonOpenFlatLocusSpace.fibre_eq_range_ptPoint`, which is Stacks
03BW for a group action in the form
`AlgebraicGeometry.Space.exists_smul_of_pointsMap_actionProjection_eq`. And the commutative
algebra is `Stacks.Examples.NonOpenFlatLocus.not_isOpen_flatLocus`, which says that `F` localizes
flatly at `p_m` exactly for `m ≤ 0`, while `p_0` lies in the closure of `{p_m : m ≥ 1}`, so that
locus is not open in the subspace `{p_m : m ∈ ℤ}` of `|Spec A|`. The transport between the two is
`Stacks.Examples.NonOpenFlatLocusSpace.mem_flatLocus_iff_isFlatAt`, which reads
Stacks 05VU at the square of étale scheme charts whose vertical map is the identity of
`Spec A`.

The hypothesis of Stacks 0CWK below is exactly what fails there:
`Stacks.Examples.NonOpenFlatLocusSpace.not_hasQuasiCompactFieldRepresentative_ybase`
derives from the counterexample, by the theorem below, that `y` has no quasi-compact
field-valued representative.

That counterexample needs `F` of finite type and not of finite presentation, which is the same
gap that makes Stacks 05M9 a statement about one fibre rather than about `X`: for a module of
finite presentation over a morphism locally of finite presentation the flat locus is open in all
of `|X|` by Stacks 05WV, available as
`AlgebraicGeometry.Space.isOpen_flatLocus_of_isFinitePresentationOnCharts`, and openness in
every set-theoretic fibre follows from it with no condition on `y`.

Once the chart is chosen the argument is the source's. The chart of the source is a surjective
étale atlas of `X` based changed along the chart of the target, which covers the fibre by Tag
03H4; the preimage of the fibre in it is the scheme-theoretic fibre over `v`, on which Stacks
05M9 gives openness; and an étale chart is open on points by Tag 03BX, which turns openness in
the preimage into openness in the fibre.

`AlgebraicGeometry.Space.pointTopology` of Tag 03BY is a plain definition rather than an
instance and is made a local instance here.

## References

* [Stacks Project, Tag 0CWK](https://stacks.math.columbia.edu/tag/0CWK)
* [Stacks Project, Tag 05M9](https://stacks.math.columbia.edu/tag/05M9)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 03JV](https://stacks.math.columbia.edu/tag/03JV)
* [Stacks Project, Tag 03I8](https://stacks.math.columbia.edu/tag/03I8)
* [Stacks Project, Tag 0AC8](https://stacks.math.columbia.edu/tag/0AC8)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
* [Stacks Project, Tag 05WV](https://stacks.math.columbia.edu/tag/05WV)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Points of a chart and the comparison map -/

/-- A point of an étale scheme chart lies above the point of the algebraic space it
determines. -/
theorem chartPoint_pointOfEtaleChart {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (U : SmallEtale B S hS X) (u : etaleChartScheme B S hS U) :
    ChartPoint B S hS U.obj.left U.obj.hom u (pointOfEtaleChart B S hS U u) := by
  have h := chartPoint_pointsToScheme B S hS U.obj.left U.obj.hom
    ((pointsEquivScheme B S hS U.obj.left).symm u)
  have hu : pointsToScheme B S hS U.obj.left
      ((pointsEquivScheme B S hS U.obj.left).symm u) = u :=
    (pointsEquivScheme B S hS U.obj.left).apply_symm_apply u
  rwa [hu] at h

/-- The map on points of a morphism of the site, read through the comparison bijection of
Tag 03BV, is the map on points of the underlying morphism of schemes. -/
theorem pointsMap_yoneda_map_symm {U V : BigFppfOver B S hS} (α : U ⟶ V)
    (u : (BigFppfOver.toScheme B S hS).obj U) :
    pointsMap B S hS (yoneda.obj U) (yoneda.map α) ((pointsEquivScheme B S hS U).symm u) =
      (pointsEquivScheme B S hS V).symm ((BigFppfOver.toScheme B S hS).map α u) := by
  refine injective_pointsToScheme B S hS V ?_
  have h1 : pointsToScheme B S hS V ((pointsEquivScheme B S hS V).symm
      ((BigFppfOver.toScheme B S hS).map α u)) = (BigFppfOver.toScheme B S hS).map α u :=
    (pointsEquivScheme B S hS V).apply_symm_apply _
  have h2 : pointsToScheme B S hS U ((pointsEquivScheme B S hS U).symm u) = u :=
    (pointsEquivScheme B S hS U).apply_symm_apply u
  rw [pointsToScheme_pointsMap_yoneda, h1, h2]

/-! ### Chart independence of flatness at a point -/

variable {X Y : AlgebraicSpaces B S hS}

/-- On a commuting square of étale scheme charts, flatness of the restricted module at a point
of the source chart above a geometric point is flatness of the geometric stalk over the étale
local ring of the target. This is Stacks 05VU read at an arbitrary point of an arbitrary square
rather than at the chosen lift of the geometric point. -/
private theorem isFlatOverAtOnChartDiagram_iff_of_chartPoint (f : X ⟶ Y)
    (Fm : Modules.{u, u} B S hS X.1 X.2) [Fm.IsQuasicoherentOnSite]
    (xbar : GeometricPoint B S hS X.1) (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (u : etaleChartScheme B S hS d.U)
    (hcp : ChartPoint B S hS d.U.obj.left d.U.obj.hom u xbar.image) :
    IsFlatOverAtOnChartDiagram B S hS X.2 Fm d u ↔
      IsFlatOverAtGeometricPoint B S hS f Fm xbar := by
  obtain ⟨q, hq, hqu⟩ := exists_chartLift_of_chartPoint B S hS X.2 xbar d.U u hcp
  subst hqu
  exact isFlatOverAtOnChartDiagram_iff_isFlatOverAtGeometricPoint B S hS f Fm
    ⟨d.U, q, hq⟩ d.V d.g d.comm

/-- The relative flat locus of a chart is the set of points of that chart at which the
restricted module is flat over the target chart. -/
theorem mem_chartFlatLocus_iff_isFlatOverAtOnChartDiagram {f : X ⟶ Y}
    (Fm : Modules.{u, u} B S hS X.1 X.2) (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (u : etaleChartScheme B S hS d.U) :
    u ∈ chartFlatLocus B S hS X.2 Fm d ↔ IsFlatOverAtOnChartDiagram B S hS X.2 Fm d u :=
  Iff.rfl

/-- **Chart independence of flatness over the target at a point.** On every commuting square of
étale scheme charts, flatness of the restriction of a quasi-coherent module at a point of the
source chart is membership of the image point in the relative flat locus of Stacks 05VV. This
is Stacks 05VU read on a chart: the some-chart condition defining
`AlgebraicGeometry.Space.flatLocus` is tested on any one square through the point.

Stacks 05VU itself — the equivalence of that some-chart condition with flatness of the geometric
stalk over the étale local ring of the target — is
`AlgebraicGeometry.Space.isFlatOverAt_exists_chartDiagram_iff_isFlatOverAtGeometricPoint`. -/
theorem isFlatOverAtOnChartDiagram_iff_mem_flatLocus (f : X ⟶ Y)
    (Fm : Modules.{u, u} B S hS X.1 X.2) [Fm.IsQuasicoherentOnSite]
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) (u : etaleChartScheme B S hS d.U) :
    IsFlatOverAtOnChartDiagram B S hS X.2 Fm d u ↔
      pointOfEtaleChart B S hS d.U u ∈ flatLocus B S hS X.2 f.hom Fm := by
  obtain ⟨xbar, hxbar⟩ :=
    exists_geometricRepresentative B S hS X.1 (pointOfEtaleChart B S hS d.U u)
  have hcp : ChartPoint B S hS d.U.obj.left d.U.obj.hom u xbar.image := by
    rw [hxbar]
    exact chartPoint_pointOfEtaleChart B S hS d.U u
  refine ⟨fun hu => ⟨d, u, rfl, hu⟩, ?_⟩
  rintro ⟨d', u', hd', hu'⟩
  have hcp' : ChartPoint B S hS d'.U.obj.left d'.U.obj.hom u' xbar.image := by
    rw [hxbar, ← hd']
    exact chartPoint_pointOfEtaleChart B S hS d'.U u'
  refine (isFlatOverAtOnChartDiagram_iff_of_chartPoint B S hS f Fm xbar d u hcp).2 ?_
  exact (isFlatOverAtOnChartDiagram_iff_of_chartPoint B S hS f Fm xbar d' u' hcp').1 hu'

/-! ### A chart of the source covering a set-theoretic fibre -/

/-- The scheme morphism of a commuting square of étale scheme charts of a morphism locally of
finite type is locally of finite type. -/
theorem locallyOfFiniteType_chartDiagram {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ G}
    (hf : IsLocallyOfFiniteType B S hS f) (d : ChartDiagram B S hS F G f) :
    LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map d.g) :=
  hf d.U.obj.left d.V.obj.left d.U.obj.hom d.V.obj.hom d.g d.U.property d.V.property
    d.comm.symm

/-- **A chart of the source over a chart of the target, covering a set-theoretic fibre.** Given
an étale scheme chart `V` of the target with a point `v`, there is an étale scheme chart of the
source lying over `V` whose points cover the set-theoretic fibre over the image of `v`.

The chart is a surjective étale atlas of the source based changed along `V`, and the covering
assertion is Tag 03H4. -/
theorem exists_etaleChart_covering_setFibre (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (v : etaleChartScheme B S hS V) :
    ∃ (U : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X.1)
      (_ : (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf p) (α : U ⟶ V.obj.left),
      p ≫ f.hom = yoneda.map α ≫ V.obj.hom ∧
        ∀ x : points B S hS X.1,
          pointsMap B S hS X.1 f.hom x = pointOfEtaleChart B S hS V v →
          ∃ w : points B S hS (yoneda.obj U), pointsMap B S hS (yoneda.obj U) p w = x := by
  obtain ⟨W, t, htSurj, htEtale⟩ := X.2.exists_atlas
  set g : yoneda.obj W ⟶ Y.1 := t ≫ f.hom with hg
  set hrep := V.property.rep with hrepdef
  have hsq : IsPullback (yoneda.map (hrep.fst' g)) (yoneda.map (hrep.snd g))
      V.obj.hom g := hrep.isPullback' g
  have hsnd : AlgebraicGeometry.Etale
      ((BigFppfOver.toScheme B S hS).map (hrep.snd g)) :=
    V.property.property g (yoneda.map (hrep.fst' g)) (hrep.snd g) hsq
  refine ⟨hrep.pullback g, yoneda.map (hrep.snd g) ≫ t,
    etale_comp_of_scheme B S hS (hrep.snd g) t hsnd htEtale, hrep.fst' g, ?_, ?_⟩
  · rw [Category.assoc, ← hg]
    exact hsq.w.symm
  · intro x hx
    obtain ⟨w₀, hw₀⟩ :=
      (surjective_iff_surjective_pointsMap B S hS X.1 X.2 W t).mp htSurj x
    have hmatch : pointsMap B S hS (yoneda.obj V.obj.left) V.obj.hom
        ((pointsEquivScheme B S hS V.obj.left).symm v) =
        pointsMap B S hS (yoneda.obj W) g w₀ := by
      rw [hg, pointsMap_comp_apply, hw₀, hx]
      rfl
    obtain ⟨wp, hwp₁, hwp₂⟩ := exists_points_of_isPullback B S hS hsq
      ((pointsEquivScheme B S hS V.obj.left).symm v) w₀ hmatch
    refine ⟨wp, ?_⟩
    rw [pointsMap_comp_apply, hwp₂, hw₀]

/-! ### Stacks 0CWK -/

/-- A point of a presheaf on the big fppf site of `S` *has a unique point in some chart* when
there is an étale scheme chart of the presheaf with exactly one point above it.

This is the condition the proof of Stacks 0AC8 arranges by shrinking a chart, using that the
point has a quasi-compact field-valued representative; that implication is
`AlgebraicGeometry.Space.HasQuasiCompactFieldRepresentative.hasUniquePointInSomeChart`. -/
abbrev HasUniquePointInSomeChart (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (y : points B S hS F) : Prop :=
  ∃ (V : SmallEtale B S hS F) (v : etaleChartScheme B S hS V),
    pointOfEtaleChart B S hS V v = y ∧
      ∀ v' : etaleChartScheme B S hS V, pointOfEtaleChart B S hS V v' = y → v' = v

/-- **The shrinking step of the proof of Stacks 0AC8.** A point of an algebraic space which has
a quasi-compact field-valued representative, condition (5) of Stacks 03JV, has an étale scheme
chart with exactly one point above it.

The chart is the one produced by
`AlgebraicGeometry.Space.exists_etale_chart_singleton_fibre_of_isQuasiCompact_fieldMorphism`,
whose fibre above the point is a singleton; here that fibre is read through the comparison
bijection of Tag 03BV between the points of a representable presheaf and the points of the
representing scheme. -/
theorem HasQuasiCompactFieldRepresentative.hasUniquePointInSomeChart
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    {y : points B S hS F} (hy : HasQuasiCompactFieldRepresentative B S hS F y) :
    HasUniquePointInSomeChart B S hS F y := by
  obtain ⟨p, hpy, hqc⟩ := hy
  obtain ⟨V, ψ, v, hψ, hfib⟩ :=
    exists_etale_chart_singleton_fibre_of_isQuasiCompact_fieldMorphism B S hS hF p hqc
  have key : ∀ w, pointsMap B S hS (yoneda.obj V) ψ w = y ↔ w = v := fun w => by
    have := Set.ext_iff.mp hfib w
    rw [← hpy]
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using this
  refine ⟨⟨CostructuredArrow.mk ψ, hψ⟩, pointsEquivScheme B S hS V v, ?_, fun v' hv' => ?_⟩
  · show pointsMap B S hS (yoneda.obj V) ψ
      ((pointsEquivScheme B S hS V).symm (pointsEquivScheme B S hS V v)) = y
    rw [(pointsEquivScheme B S hS V).symm_apply_apply]
    exact (key v).2 rfl
  · have hmem := (key ((pointsEquivScheme B S hS V).symm v')).1 hv'
    rw [← hmem, (pointsEquivScheme B S hS V).apply_symm_apply]

/-- **Stacks 0CWK for a chart of the target with a single point above `y`.** Let
`f : X ⟶ Y` be a morphism of algebraic spaces over `S` which is locally of finite type, let `F`
be a quasi-coherent `𝒪_X`-module of finite type and let `y` be a point of `|Y|` above which
some étale scheme chart of `Y` has exactly one point. In the set-theoretic fibre
`f^{-1}({y}) ⊆ |X|`, with its subspace topology, the points at which `F` is flat over `Y` form
an open subset.

Flatness at a point is `AlgebraicGeometry.Space.flatLocus`, the some-chart form of Stacks 05VV
part (1), which Stacks 05VU shows is independent of the chart. -/
theorem isOpen_flatLocus_setFibre_of_hasUniquePointInSomeChart (f : X ⟶ Y)
    (Fm : Modules.{u, u} B S hS X.1 X.2) [Fm.IsQuasicoherentOnSite]
    (hf : IsLocallyOfFiniteType B S hS f.hom)
    (hft : IsFiniteTypeOnCharts B S hS X.2 Fm)
    (y : points B S hS Y.1) (hy : HasUniquePointInSomeChart B S hS Y.1 y) :
    IsOpen {x : (pointsMap B S hS X.1 f.hom ⁻¹' {y} : Set (points B S hS X.1)) |
      (x : points B S hS X.1) ∈ flatLocus B S hS X.2 f.hom Fm} := by
  obtain ⟨V, v, hv, hvuniq⟩ := hy
  obtain ⟨U, p, hp, α, hcomm, hcov⟩ := exists_etaleChart_covering_setFibre B S hS f V v
  set d : ChartDiagram B S hS X.1 Y.1 f.hom :=
    { U := ⟨CostructuredArrow.mk p, hp⟩, V := V, g := α, comm := hcomm } with hd
  set τ := (BigFppfOver.toScheme B S hS).map α with hτ
  -- The square of charts is compatible with the maps on points.
  have hcompat : ∀ u : etaleChartScheme B S hS d.U,
      pointsMap B S hS X.1 f.hom (pointOfEtaleChart B S hS d.U u) =
        pointOfEtaleChart B S hS V (τ u) := by
    intro u
    show pointsMap B S hS X.1 f.hom (pointsMap B S hS (yoneda.obj U) p
      ((pointsEquivScheme B S hS U).symm u)) = _
    rw [← pointsMap_comp_apply, hcomm, pointsMap_comp_apply,
      pointsMap_yoneda_map_symm B S hS α u]
    rfl
  -- The preimage of the fibre in the chart is the scheme-theoretic fibre over `v`.
  have hpre : ∀ u : etaleChartScheme B S hS d.U,
      pointsMap B S hS X.1 f.hom (pointOfEtaleChart B S hS d.U u) = y ↔ τ u = v := by
    intro u
    rw [hcompat u]
    exact ⟨fun h => hvuniq _ h, fun h => by rw [h]; exact hv⟩
  -- Stacks 05M9 on the square of charts.
  have hqcU := isQuasicoherent_restrictToChart B S hS X Fm ‹_› d.U
  have hftU := hft d.U
  have hftτ : LocallyOfFiniteType τ := locallyOfFiniteType_chartDiagram B S hS hf d
  have h05M9 : IsOpen {w : τ.fiber v |
      IsFlatOverAt τ.toLRSHom.toShHom (chartModule B S hS X.2 Fm d.U) (τ.fiberι v w)} :=
    isOpen_isFlatOverAt_fiber_of_locallyOfFiniteType τ (chartModule B S hS X.2 Fm d.U) v
  -- Read it as openness in the subspace `τ ⁻¹' {v}`.
  have hsub : IsOpen (Subtype.val ⁻¹'
      chartFlatLocus B S hS X.2 Fm d : Set ↥(τ ⁻¹' {v})) := by
    refine (τ.fiberHomeo v).isOpen_preimage.mp ?_
    convert h05M9 using 1
    ext w
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    exact Iff.rfl
  obtain ⟨O, hO, hOeq⟩ := isOpen_induced_iff.mp hsub
  -- `O` cuts out the flat locus on the fibre of the chart.
  have hOfib : ∀ u : etaleChartScheme B S hS d.U, τ u = v →
      (u ∈ O ↔ u ∈ chartFlatLocus B S hS X.2 Fm d) := by
    intro u hu
    have := Set.ext_iff.mp hOeq ⟨u, hu⟩
    simpa only [Set.mem_preimage] using this
  -- The flat locus in the fibre is cut out by the image of `O`, which is open.
  have himg : IsOpen (pointOfEtaleChart B S hS d.U '' O) :=
    isOpen_image_pointOfEtaleChart B S hS d.U hO
  have hset : {x : (pointsMap B S hS X.1 f.hom ⁻¹' {y} : Set (points B S hS X.1)) |
      (x : points B S hS X.1) ∈ flatLocus B S hS X.2 f.hom Fm} =
      Subtype.val ⁻¹' (pointOfEtaleChart B S hS d.U '' O) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    constructor
    · intro hx
      obtain ⟨w, hw⟩ := hcov x.1 (by rw [hv]; exact x.2)
      have hux : pointOfEtaleChart B S hS d.U (pointsEquivScheme B S hS U w) = x.1 := by
        show pointsMap B S hS (yoneda.obj U) p
          ((pointsEquivScheme B S hS U).symm ((pointsEquivScheme B S hS U) w)) = x.1
        rw [(pointsEquivScheme B S hS U).symm_apply_apply, hw]
      refine ⟨pointsEquivScheme B S hS U w, (hOfib _ ((hpre _).1 (by rw [hux]; exact x.2))).2 ?_,
        hux⟩
      refine (mem_chartFlatLocus_iff_isFlatOverAtOnChartDiagram B S hS Fm d _).2 ?_
      refine (isFlatOverAtOnChartDiagram_iff_mem_flatLocus B S hS f Fm d _).2 ?_
      rw [hux]
      exact hx
    · rintro ⟨u, huO, hux⟩
      have hufib : τ u = v := (hpre u).1 (by rw [hux]; exact x.2)
      have hflat := (hOfib u hufib).1 huO
      have := (isFlatOverAtOnChartDiagram_iff_mem_flatLocus B S hS f Fm d u).1
        ((mem_chartFlatLocus_iff_isFlatOverAtOnChartDiagram B S hS Fm d u).1 hflat)
      rwa [hux] at this
  rw [hset]
  exact continuous_subtype_val.isOpen_preimage _ himg

/-- **Stacks 0CWK.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` which is
locally of finite type, let `F` be a quasi-coherent `𝒪_X`-module of finite type and let `y` be
a point of `|Y|` with a quasi-compact field-valued representative. In the set-theoretic fibre
`f^{-1}({y}) ⊆ |X|`, with its subspace topology, the points at which `F` is flat over `Y` form
an open subset.

The hypothesis on `y` is condition (5) of Stacks 03JV; by Stacks 0AC8 it provides an étale
scheme chart of `Y` with exactly one point above `y`, which is what makes the fibre of a chart
of `X` map openly onto the set-theoretic fibre. It holds at every point of a decent algebraic
space, which is `AlgebraicGeometry.Space.isOpen_flatLocus_setFibre_of_isDecentSpace`.

The hypothesis on `y` corrects Stacks 0CWK, which as published asks nothing of `y`; the corrected
statement adds condition (5) of Stacks 03JV at `y`. The published form is false:
`Stacks.Examples.NonOpenFlatLocusSpace.not_isOpen_flatLocus_setFibre_of_free_shift` takes no
hypotheses and produces a big fppf site, an algebraic space `Y = Spec A/ℤ` for
`A = ℚ[t, u_i]/((t - i)u_i)`, the étale quotient morphism `f : Spec A ⟶ Y`, the cyclic module
`A ⧸ (u_i : i ≥ 1)` on its source and a point `y` of `|Y|`, satisfying every hypothesis of this
theorem except the one on `y`, and for which the conclusion below is false. Its companion
`Stacks.Examples.NonOpenFlatLocusSpace.not_hasQuasiCompactFieldRepresentative_ybase` deduces from
that failure that the point it produces has no quasi-compact field-valued representative, so the
hypothesis on `y` is exactly what the source is missing.

Flatness at a point is `AlgebraicGeometry.Space.flatLocus`, the some-chart form of Stacks 05VV
part (1), which Stacks 05VU shows is independent of the chart. -/
@[stacks 0CWK "the statement in full, at the Stacks erratum: the point y of the target \
has a quasi-compact field-valued representative, condition (5) of Stacks 03JV, which holds at \
every point of a decent algebraic space. The tag as published asks nothing of y and is false \
that way, refuted by the theorem \
Stacks.Examples.NonOpenFlatLocusSpace.not_isOpen_flatLocus_setFibre_of_free_shift of \
StacksFrontier/Examples/Flatness/NonOpenFlatLocusSpace.lean"]
theorem isOpen_flatLocus_setFibre (f : X ⟶ Y)
    (Fm : Modules.{u, u} B S hS X.1 X.2) [Fm.IsQuasicoherentOnSite]
    (hf : IsLocallyOfFiniteType B S hS f.hom)
    (hft : IsFiniteTypeOnCharts B S hS X.2 Fm)
    (y : points B S hS Y.1) (hy : HasQuasiCompactFieldRepresentative B S hS Y.1 y) :
    IsOpen {x : (pointsMap B S hS X.1 f.hom ⁻¹' {y} : Set (points B S hS X.1)) |
      (x : points B S hS X.1) ∈ flatLocus B S hS X.2 f.hom Fm} :=
  isOpen_flatLocus_setFibre_of_hasUniquePointInSomeChart B S hS f Fm hf hft y
    (hy.hasUniquePointInSomeChart B S hS Y.2)

/-- **Stacks 0CWK for a decent target.** For a morphism of algebraic spaces locally of finite
type with decent target and a quasi-coherent module of finite type on the source, the flat
locus is open in every set-theoretic fibre.

Decency, Stacks 03I8, is condition (4) of Stacks 03JV at every point, which gives condition (5)
at the point in question. -/
theorem isOpen_flatLocus_setFibre_of_isDecentSpace (f : X ⟶ Y)
    (Fm : Modules.{u, u} B S hS X.1 X.2) [Fm.IsQuasicoherentOnSite]
    (hf : IsLocallyOfFiniteType B S hS f.hom)
    (hft : IsFiniteTypeOnCharts B S hS X.2 Fm)
    (hY : IsDecentSpace B S hS Y.1) (y : points B S hS Y.1) :
    IsOpen {x : (pointsMap B S hS X.1 f.hom ⁻¹' {y} : Set (points B S hS X.1)) |
      (x : points B S hS X.1) ∈ flatLocus B S hS X.2 f.hom Fm} :=
  isOpen_flatLocus_setFibre B S hS f Fm hf hft y
    ((hY y).hasQuasiCompactFieldRepresentative B S hS Y.1)

end AlgebraicGeometry.Space

end
