module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartDiagramCommonRefinement
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionTrivialChart
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackChartGeneration
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackInvertible

/-!
# The inverse image of a free generator is a free generator, locally

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site `B`, let
`M` be a sheaf of `𝒪_Y`-modules and let `d` be a commuting square of étale scheme charts over
`f`, with chart `d.U` of `X` above `d.V` of `Y`.  A section `e` of `M` over `d.V` has a canonical
inverse image `f^*e` in `(f^*M)(d.U)` — the chart component of the unit of the Stacks 03D7
adjunction.  Suppose `e` generates `M` *freely* over every chart over `d.V`.  Then **`f^*e`
generates `f^*M` freely over the charts of a covering sieve of `d.U`.**

Freeness of `f^*e` cannot be read off the construction of `f^*`: the inverse image is a
sheafification over the whole site of `X` and not a sectionwise base change, and the repository
records the same gap at
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleSourceModulePullbackComparison.lean`.  What is used
instead is that `f^*M` has free generators of its own when `M` is invertible — Stacks 0B8P
(`AlgebraicGeometry.Space.isInvertible_modulePullback_obj`) together with
`AlgebraicGeometry.Space.exists_generator_cover_smul_of_isInvertible` — and that the inverse
images of the chart sections generate `f^*M` locally
(`AlgebraicGeometry.Space.spanSieve_modulePullbackChart_mem`).  Comparing the two gives the
statement in three steps.

* Every inverse image `f^*s'` of a section of `M` over the chart of *another* square `d'` is, over
  a chart of `X` receiving both `d.U` and `d'.U`, an `𝒪_X`-multiple of `f^*e`.  The two squares
  are dominated by one (`AlgebraicGeometry.Space.exists_dominating_chartSection`) whose chart of
  `Y` lies over `d.V`, where `s'` restricts to a multiple of `e` by freeness, and the chart
  component of the unit is semilinear.
* Hence everything in the `𝒪_X`-span of the restricted chart sections over such a chart is an
  `𝒪_X`-multiple of `f^*e`.
* A free generator `ε` of `f^*M` lies, over a covering sieve, in that span, so `ε = u • f^*e`
  there; and `f^*e = v • ε` because `ε` is free.  Comparing coefficients against the free `ε`
  gives `u · v = 1`, so `v` is a unit and `f^*e` is free as well.

## Main definitions

* `AlgebraicGeometry.Space.modulePullbackChartSectionRestrict` is the inverse image of a chart
  section, restricted to a chart of `X` over the chart of the square.  It exists to give that
  element the type `(f^*M)(Z)` rather than the restriction-of-scalars spelling the presheaf map
  produces, which is the type the module instances over `AlgebraicGeometry.Space.chartRing` are
  registered at.

## Main results

* `AlgebraicGeometry.Space.exists_smul_modulePullbackChartSectionRestrict`: an inverse image of a
  chart section of another square is an `𝒪_X`-multiple of the inverse image of a free generator.
* `AlgebraicGeometry.Space.exists_smul_of_mem_spanSubmodule_modulePullbackChart`: so is anything
  in the span of the restricted chart sections.
* `AlgebraicGeometry.Space.exists_sieve_bijective_smul_modulePullbackChartSection`: **the inverse
  image of a free generator is a free generator of `f^*M` over the charts of a covering sieve.**

## Implementation notes

The generator of `M` is taken as the compatible *family* `e` that
`AlgebraicGeometry.Space.exists_generator_smul_of_isColimit` produces, and not as a single
section with a hypothesis about its restrictions: `r • (M.val.map p.op).hom e` has for its type
the restriction-of-scalars wrapper, at which the module instances are not registered, so such a
hypothesis cannot even be stated at face value.

The covering sieve is stated in the form that is stable under further restriction — freeness over
*every* chart below, not only over the chart itself — because freeness at one object does not
imply it below, while the consumer
(`AlgebraicGeometry.Space.injective_smul_eval_of_tmul_isUnit`) needs it below.

## References

* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 0B8P](https://stacks.math.columbia.edu/tag/0B8P)
* [Stacks Project, Tag 0ENC](https://stacks.math.columbia.edu/tag/0ENC)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace Stacks

/-- **Multiplying a free generator by a unit gives a free generator.**  If `x = v • y` with `v` a
unit of the base ring and `r ↦ r • y` a bijection onto the module, then `r ↦ r • x` is one too:
it is `r ↦ r • y` precomposed with multiplication by `v`. -/
theorem bijective_smul_of_isUnit_smul {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N]
    [Module R N] {x y : N} {v : R} (hv : IsUnit v) (hxy : x = v • y)
    (h : Function.Bijective fun r : R ↦ r • y) :
    Function.Bijective fun r : R ↦ r • x := by
  obtain ⟨w, rfl⟩ := hv
  have hmul : Function.Bijective fun r : R ↦ r * (w : R) := by
    refine ⟨fun a b hab ↦ ?_, fun z ↦ ⟨z * ((w⁻¹ : Rˣ) : R), ?_⟩⟩
    · have := congrArg (fun z : R ↦ z * ((w⁻¹ : Rˣ) : R)) hab
      simpa only [mul_assoc, Units.mul_inv, mul_one] using this
    · change z * ((w⁻¹ : Rˣ) : R) * (w : R) = z
      rw [mul_assoc, Units.inv_mul, mul_one]
  have hcomp : (fun r : R ↦ r • x) = (fun z : R ↦ z • y) ∘ fun r : R ↦ r * (w : R) := by
    funext r
    rw [hxy, Function.comp_apply, mul_smul]
  rw [hcomp]
  exact h.comp hmul

end Stacks

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (M : Modules.{u, u} B S hS Y.1 Y.2)

/-! ### The inverse image of a chart section, restricted -/

/-- The inverse image `f^*s` of a section of `M` over the chart of `Y` of a commuting square of
étale scheme charts, restricted along a morphism `ι` into the chart of `X` of that square.

Not an abbreviation: its stated type is the sections of `f^*M` over `Z`, whereas the presheaf
restriction map produces the restriction-of-scalars spelling of that type, and the module
structure over `AlgebraicGeometry.Space.chartRing` is registered only at the former. -/
noncomputable def modulePullbackChartSectionRestrict
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) (s : M.val.obj (op d.V))
    {Z : SmallEtale B S hS X.1} (ι : Z ⟶ d.U) :
    ((modulePullback B S hS f).obj M).val.obj (op Z) :=
  (((modulePullback B S hS f).obj M).val.map ι.op).hom
    ((modulePullbackChartFMap B S hS f M).app d s)

/-- The restricted inverse image of a chart section, read as a restriction. -/
theorem modulePullbackChartSectionRestrict_eq
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) (s : M.val.obj (op d.V))
    {Z : SmallEtale B S hS X.1} (ι : Z ⟶ d.U) :
    modulePullbackChartSectionRestrict B S hS f M d s ι =
      (((modulePullback B S hS f).obj M).val.map ι.op).hom
        ((modulePullbackChartFMap B S hS f M).app d s) :=
  rfl

/-- Restricting again composes the two morphisms of charts. -/
theorem modulePullbackChartSectionRestrict_map
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) (s : M.val.obj (op d.V))
    {Z Z' : SmallEtale B S hS X.1} (ι : Z ⟶ d.U) (h : Z' ⟶ Z) :
    (((modulePullback B S hS f).obj M).val.map h.op).hom
        (modulePullbackChartSectionRestrict B S hS f M d s ι) =
      modulePullbackChartSectionRestrict B S hS f M d s (h ≫ ι) :=
  (PresheafOfModules.map_comp_apply ((modulePullback B S hS f).obj M).val ι.op h.op
    ((modulePullbackChartFMap B S hS f M).app d s)).symm

/-! ### An inverse image of a chart section is a multiple of a free generator -/

/-- **An inverse image of a chart section of another square is an `𝒪_X`-multiple of the inverse
image of a free generator.**  Let `e` be a family of sections of `M` over the charts over `d.V`,
compatible with restriction, each generating `M` freely there; let `d''` be another commuting
square over `f` and `s'` a section of `M` over `d''.V`; and let `Z` be a chart of `X` with
morphisms into `d.U` and into `d''.U`.  Then `f^*s'` restricted to `Z` is an `𝒪_X(Z)`-multiple of
`f^*e` restricted to `Z`.

The two squares are dominated by a single one over `Z`
(`AlgebraicGeometry.Space.exists_dominating_chartSection`) whose chart `W` of `Y` lies over both
`d.V` and `d''.V`.  Over `W` the restriction of `s'` is a multiple of the restriction of `e`, by
freeness, and the chart component of the unit is semilinear over pullback of regular functions. -/
theorem exists_smul_modulePullbackChartSectionRestrict
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (e : (W : SmallEtale B S hS Y.1) → (W ⟶ d.V) → M.val.obj (op W))
    (hcompat : ∀ (W W' : SmallEtale B S hS Y.1) (k : W ⟶ d.V) (g : W' ⟶ W),
      (M.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hbij : ∀ (W : SmallEtale B S hS Y.1) (k : W ⟶ d.V),
      Function.Bijective fun r : chartRing B S hS Y.1 Y.2 W ↦ r • e W k)
    (d'' : ChartDiagram B S hS X.1 Y.1 f.hom) (s' : M.val.obj (op d''.V))
    {Z : SmallEtale B S hS X.1} (ι : Z ⟶ d.U) (i : Z ⟶ d''.U) :
    ∃ c : chartRing B S hS X.1 X.2 Z,
      modulePullbackChartSectionRestrict B S hS f M d'' s' i =
        c • modulePullbackChartSectionRestrict B S hS f M d (e d.V (𝟙 d.V)) ι := by
  obtain ⟨W, g, hcomm, p, q, h1, h2⟩ := exists_dominating_chartSection B S hS f
    (modulePullbackChartFMap B S hS f M) d d'' ι i (e d.V (𝟙 d.V)) s'
  obtain ⟨c₀, hc₀⟩ := (hbij W p).2 ((M.val.map q.op) s')
  have hep : (M.val.map p.op) (e d.V (𝟙 d.V)) = e W p :=
    (hcompat d.V W (𝟙 d.V) p).trans (congrArg (e W) (Category.comp_id p))
  refine ⟨chartDiagramRestrict B S hS f ⟨Z, W, g, hcomm⟩ c₀, ?_⟩
  refine Eq.trans h2.symm ?_
  refine Eq.trans (congrArg ((modulePullbackChartFMap B S hS f M).app ⟨Z, W, g, hcomm⟩)
    (show (M.val.map q.op) s' = c₀ • e W p from hc₀.symm)) ?_
  refine Eq.trans
    ((modulePullbackChartFMap B S hS f M).map_smul ⟨Z, W, g, hcomm⟩ c₀ (e W p)) ?_
  refine congrArg
    (fun z : ((modulePullback B S hS f).obj M).val.obj (op Z) ↦
      chartDiagramRestrict B S hS f ⟨Z, W, g, hcomm⟩ c₀ • z) ?_
  exact (congrArg ((modulePullbackChartFMap B S hS f M).app ⟨Z, W, g, hcomm⟩) hep.symm).trans h1

/-- **Everything in the span of the restricted chart sections is an `𝒪_X`-multiple of the inverse
image of a free generator.**  The span is generated by restrictions of inverse images of chart
sections, each of which is such a multiple by
`AlgebraicGeometry.Space.exists_smul_modulePullbackChartSectionRestrict`, and the multiples of a
single element form a submodule. -/
theorem exists_smul_of_mem_spanSubmodule_modulePullbackChart
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (e : (W : SmallEtale B S hS Y.1) → (W ⟶ d.V) → M.val.obj (op W))
    (hcompat : ∀ (W W' : SmallEtale B S hS Y.1) (k : W ⟶ d.V) (g : W' ⟶ W),
      (M.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hbij : ∀ (W : SmallEtale B S hS Y.1) (k : W ⟶ d.V),
      Function.Bijective fun r : chartRing B S hS Y.1 Y.2 W ↦ r • e W k)
    {Z : SmallEtale B S hS X.1} (ι : Z ⟶ d.U)
    (x : ((modulePullback B S hS f).obj M).val.obj (op Z))
    (hx : x ∈ (Stacks.SheafOfModules.spanSubmodule ((modulePullback B S hS f).obj M)
      (moduleFMapSpanningSet B S hS f M ((modulePullback B S hS f).obj M)
        (modulePullbackChartFMap B S hS f M))).obj (op Z)) :
    ∃ c : chartRing B S hS X.1 X.2 Z,
      x = c • modulePullbackChartSectionRestrict B S hS f M d (e d.V (𝟙 d.V)) ι := by
  have hmem : x ∈ Submodule.span (chartRing B S hS X.1 X.2 Z)
      {modulePullbackChartSectionRestrict B S hS f M d (e d.V (𝟙 d.V)) ι} := by
    refine Submodule.span_induction ?_ (zero_mem _) (fun _ _ _ _ ha hb ↦ add_mem ha hb)
      (fun r _ _ hz ↦ Submodule.smul_mem _ r hz) hx
    rintro z ⟨Z₁, g₁, z₁, ⟨d'', i₁, s', rfl⟩, rfl⟩
    obtain ⟨c, hc⟩ := exists_smul_modulePullbackChartSectionRestrict B S hS f M d e hcompat hbij
      d'' s' ι (g₁.unop ≫ i₁)
    exact Submodule.mem_span_singleton.2 ⟨c, hc.symm.trans
      (modulePullbackChartSectionRestrict_map B S hS f M d'' s' i₁ g₁.unop).symm⟩
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
  exact ⟨c, hc.symm⟩

/-! ### The inverse image of a free generator is locally free -/

/-- **The sieve of charts over which the inverse image of a chart section generates freely.**  A
morphism `ι : Z ⟶ d.U` of charts of `X` belongs to it when `r ↦ r • f^*s|_{Z'}` is a bijection of
`𝒪_X(Z')` onto `(f^*M)(Z')` for *every* chart `Z'` over `Z`.

Freeness over the chart alone is not stable under restriction, which is why the condition
quantifies over the charts below; with that quantifier the family of arrows is a sieve. -/
def freeGeneratorSieve (d : ChartDiagram B S hS X.1 Y.1 f.hom) (s : M.val.obj (op d.V)) :
    Sieve d.U where
  arrows Z ι := ∀ (Z' : SmallEtale B S hS X.1) (h : Z' ⟶ Z),
    Function.Bijective fun r : chartRing B S hS X.1 X.2 Z' ↦
      r • modulePullbackChartSectionRestrict B S hS f M d s (h ≫ ι)
  downward_closed := by
    intro Z Z' ι hι j Z'' h
    have hb := hι Z'' (h ≫ j)
    rwa [Category.assoc] at hb

/-- **The inverse image of a free generator is a free generator of `f^*M` over the charts of a
covering sieve.**  Let `M` be an invertible `𝒪_Y`-module, `d` a commuting square of étale scheme
charts over `f`, and `e` a compatible family of free generators of `M` over the charts over
`d.V`.  Then the charts `Z` over `d.U` such that `r ↦ r • f^*e|_{Z'}` is a bijection of `𝒪_X(Z')`
onto `(f^*M)(Z')` for *every* chart `Z'` over `Z` form a covering sieve of `d.U`.

Over a member `Z''` of the trivializing cover of `f^*M` refined by the generation sieve of
`AlgebraicGeometry.Space.spanSieve_modulePullbackChart_mem`, the free generator `ε` of `f^*M` is
an `𝒪_X`-multiple `u • f^*e` of the inverse image, by
`AlgebraicGeometry.Space.exists_smul_of_mem_spanSubmodule_modulePullbackChart`, while
`f^*e = v • ε` because `ε` is free.  Comparing coefficients against `ε` gives `u · v = 1`, so `v`
is a unit, and `Stacks.bijective_smul_of_isUnit_smul` transports freeness from `ε` to `f^*e` —
over `Z''` and, the generators and the unit all restricting, over every chart below it. -/
theorem exists_sieve_bijective_smul_modulePullbackChartSection
    (hM : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS Y)
      (structureRingSheaf B S hS Y).property M)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (e : (W : SmallEtale B S hS Y.1) → (W ⟶ d.V) → M.val.obj (op W))
    (hcompat : ∀ (W W' : SmallEtale B S hS Y.1) (k : W ⟶ d.V) (g : W' ⟶ W),
      (M.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hbij : ∀ (W : SmallEtale B S hS Y.1) (k : W ⟶ d.V),
      Function.Bijective fun r : chartRing B S hS Y.1 Y.2 W ↦ r • e W k) :
    ∃ T : Sieve d.U, T ∈ SmallEtale.topology B S hS X.1 d.U ∧
      ∀ ⦃Z : SmallEtale B S hS X.1⦄ (ι : Z ⟶ d.U), T ι →
        ∀ (Z' : SmallEtale B S hS X.1) (h : Z' ⟶ Z),
          Function.Bijective fun r : chartRing B S hS X.1 X.2 Z' ↦
            r • modulePullbackChartSectionRestrict B S hS f M d (e d.V (𝟙 d.V)) (h ≫ ι) := by
  refine ⟨freeGeneratorSieve B S hS f M d (e d.V (𝟙 d.V)), ?_, fun Z ι hι ↦ hι⟩
  obtain ⟨I, V₀, α, hcov, hgen⟩ := exists_generator_cover_smul_of_isInvertible B S hS X
    ((modulePullback B S hS f).obj M) (isInvertible_modulePullback_obj B S hS f M hM) d.U
  refine (SmallEtale.topology B S hS X.1).transitive hcov _ ?_
  rintro Q k ⟨Q', p, q, ⟨i⟩, rfl⟩
  obtain ⟨ε, hεcompat, hεbij⟩ := hgen i
  refine (SmallEtale.topology B S hS X.1).superset_covering ?_
    (spanSieve_modulePullbackChart_mem B S hS f M Q (ε Q p))
  intro Q'' h hh Z' h'
  obtain ⟨u, hu⟩ := exists_smul_of_mem_spanSubmodule_modulePullbackChart B S hS f M d e hcompat
    hbij (h ≫ p ≫ α i) (((modulePullback B S hS f).obj M).val.map h.op (ε Q p)) hh
  have hεQ : (((modulePullback B S hS f).obj M).val.map h.op) (ε Q p) = ε Q'' (h ≫ p) :=
    hεcompat Q Q'' p h
  obtain ⟨v, hv⟩ := (hεbij Q'' (h ≫ p)).2
    (modulePullbackChartSectionRestrict B S hS f M d (e d.V (𝟙 d.V)) (h ≫ p ≫ α i))
  have hvu : u * v = 1 := by
    refine (hεbij Q'' (h ≫ p)).1 ?_
    refine Eq.trans ?_ (one_smul (chartRing B S hS X.1 X.2 Q'') (ε Q'' (h ≫ p))).symm
    refine Eq.trans (mul_smul u v (ε Q'' (h ≫ p))) ?_
    refine Eq.trans (congrArg (fun z : ((modulePullback B S hS f).obj M).val.obj (op Q'') ↦
      u • z) hv) ?_
    exact (hεQ.symm.trans hu).symm
  have hvunit : IsUnit v := ⟨⟨v, u, (mul_comm v u).trans hvu, hvu⟩, rfl⟩
  have hrestrict : modulePullbackChartSectionRestrict B S hS f M d (e d.V (𝟙 d.V))
        (h' ≫ h ≫ p ≫ α i) =
      (chartRestrict (hF := X.2) h' v) • ε Z' (h' ≫ h ≫ p) := by
    refine Eq.trans (modulePullbackChartSectionRestrict_map B S hS f M d (e d.V (𝟙 d.V))
      (h ≫ p ≫ α i) h').symm ?_
    refine Eq.trans (congrArg (((modulePullback B S hS f).obj M).val.map h'.op) hv.symm) ?_
    refine Eq.trans (PresheafOfModules.map_smul ((modulePullback B S hS f).obj M).val h'.op v
      (ε Q'' (h ≫ p))) ?_
    exact congrArg (fun z : ((modulePullback B S hS f).obj M).val.obj (op Z') ↦
      (chartRestrict (hF := X.2) h' v) • z) (hεcompat Q'' Z' (h ≫ p) h')
  have hassoc : h' ≫ h ≫ p ≫ α i = h' ≫ (h ≫ p ≫ α i) := rfl
  rw [hassoc] at hrestrict
  exact Stacks.bijective_smul_of_isUnit_smul (hvunit.map (chartRestrict (hF := X.2) h'))
    hrestrict (hεbij Z' (h' ≫ h ≫ p))

end AlgebraicGeometry.Space

end
