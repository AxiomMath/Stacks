module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.FlatInDimensionsGE
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionFromSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.InverseImageDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionFunctionFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFiniteTypeModuleFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleBaseChangePoint
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleGeometricPointCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.TranscendenceDegreeChart
import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Flatness over the target in dimensions at least `n` for a module on an algebraic space

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site which is
locally of finite type, let `F` be a quasi-coherent `𝒪_X`-module of finite type and let `n` be a
natural number.  Stacks 0CWS says that the following are equivalent:

1. for some commuting square of étale scheme charts `U ⟶ V` of `f` with both charts surjective,
   the restriction of `F` to `U` is flat over `V` in dimensions `≥ n` (Stacks 0CWG);
2. the same for every commuting square of étale scheme charts, surjective or not;
3. at every point of `|X|` at which `F` is not flat over `Y`, the transcendence degree of the
   point over its image is `< n` (Stacks 04NM).

Condition (3) mentions no chart, which is what makes (1) and (2) agree.

## Main definitions

* `AlgebraicGeometry.Space.IsFlatOverInDimensionsGEOnChartDiagram` is the condition of
  Stacks 0CWG on one commuting square of étale scheme charts.
* `AlgebraicGeometry.Space.IsFlatOverInDimensionsGEOnSomeChartDiagram` and
  `AlgebraicGeometry.Space.IsFlatOverInDimensionsGEOnEveryChartDiagram` are conditions (1) and
  (2).
* `AlgebraicGeometry.Space.HasSmallTrdegAtNonflatPoints` is condition (3).

## Main results

* `AlgebraicGeometry.Space.isFlatOverInDimensionsGEOnChartDiagram_iff`: the chartwise condition
  is the condition of Stacks 0CWG for the restriction of the module to the source chart.
* `AlgebraicGeometry.Space.isFlatOverInDimensionsGEOnSomeChartDiagram_iff_hasSmallTrdeg`:
  **Stacks 0CWS**, the equivalence of (1) and (3).
* `AlgebraicGeometry.Space.isFlatOverInDimensionsGEOnEveryChartDiagram_iff_hasSmallTrdeg`:
  **Stacks 0CWS**, the equivalence of (2) and (3).
* `AlgebraicGeometry.Space.isFlatOverInDimensionsGEOnSomeChartDiagram_iff_onEveryChartDiagram`:
  **Stacks 0CWS**, the equivalence of (1) and (2).
* `AlgebraicGeometry.Space.isFlatOverInDimensionsGE_iff_of_moduleIso` and its chartwise forms:
  the condition of Stacks 0CWT depends on the module only through its isomorphism class.
* `AlgebraicGeometry.Space.hasTrdegLtAtNonflatPoints_modulePullback_of_isPullback` and
  `AlgebraicGeometry.Space.isFlatOverInDimensionsGE_modulePullback_of_hasTrdegLt`:
  **Stacks 0CWS**, the base-change clause, the second of them concluding the condition of
  Stacks 0CWT itself.  The same clause with the condition of Stacks 0CWT on both sides is
  `AlgebraicGeometry.Space.isFlatOverInDimensionsGE_modulePullback_of_isPullback`.

## The base-change clause

The source lemma has a fourth assertion after the equivalence: *if this is true, then it remains
true after any base change `Y' ⟶ Y`.*  It is
`AlgebraicGeometry.Space.isFlatOverInDimensionsGE_modulePullback_of_hasTrdegLt`, with the
inverse image taken to be `AlgebraicGeometry.Space.modulePullback` of Stacks 03LU; it takes the
bound of condition (3) written out, so the clause is registered at a statement whose
hypotheses name none of the abbreviations introduced in this file, and
`AlgebraicGeometry.Space.isFlatOverInDimensionsGE_modulePullback_of_isPullback` restates it with
the condition of Stacks 0CWT on both sides for a consumer holding that form.

It is proved through condition (3), which mentions no chart, so the chart comparison the clause
would otherwise need does not arise.  The two inputs condition (3) needs are: non-flatness of
the inverse image must descend to non-flatness of `F`, and base change must not increase the
transcendence degree of a point over its image.  The second is part (2) of Stacks 04NS,
`AlgebraicGeometry.Space.transcendenceDegreeAt_le_of_isPullback`.  The first is **Stacks 05VW at
a point**, `AlgebraicGeometry.Space.mem_flatLocus_modulePullback_of_mem_flatLocus` of
`StacksFrontier/AlgebraicGeometry/Spaces/FlatModuleBaseChangePoint.lean`, which reads part (1) of
Stacks 05VW — proved at a geometric point in
`StacksFrontier/AlgebraicGeometry/Spaces/FlatModuleBaseChange.lean` — at a point of the point space.
It is also the input the source's own proof of this clause appeals to.

The hypotheses of the clause are the source's, read on the small étale site: quasi-coherence and
finite type of `F` there.  The inverse image inherits both, by Stacks 03GA and by Stacks 03DO
for the clause 03DL (5); and the chartwise forms of the two, which the equivalence above
consumes, follow for either module by
`AlgebraicGeometry.Space.isQuasicoherentOnCharts_of_isQuasicoherentOnSite` and
`AlgebraicGeometry.Space.isFiniteTypeOnCharts_of_isFiniteTypeOnSite` of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartRestrictionFromSite.lean`.  So nothing about the
inverse image is assumed.

The chart route to the clause is still unavailable, and is not used: the base-changed morphism
has chart diagrams obtained from those of `f` by base change along a chart of `Y'`, and the
scheme-level base-change statement
`AlgebraicGeometry.IsFlatOverInDimensionsGE.of_isPullback` applies to them, but only once the two
modules on the base-changed source chart are identified, and the comparison that exists,
`AlgebraicGeometry.Space.restrictToChartSchemePullbackComparison`, is only a morphism and not an
isomorphism.

## Implementation notes

The commuting squares are `AlgebraicGeometry.Space.ChartDiagram`, as for
`AlgebraicGeometry.Space.IsFlatOver` of Stacks 05VV and for
`AlgebraicGeometry.Space.flatLocus` of Stacks 0DLR; the restriction of the module to the source
chart is `AlgebraicGeometry.Space.chartModule`, and non-flatness at a point of that chart is
`AlgebraicGeometry.Space.IsFlatOverAtOnChartDiagram`, condition (1) of Stacks 05VU.

The chartwise condition is written as the fibrewise dimension bound rather than as
`AlgebraicGeometry.IsFlatOverInDimensionsGE` itself, because the latter carries the hypotheses of
Stacks 0CWG as instance arguments, which on a chart are consequences of the hypotheses on `f` and
`F` rather than results of instance search;
`AlgebraicGeometry.Space.isFlatOverInDimensionsGEOnChartDiagram_iff` identifies the two once
those hypotheses are supplied.

Condition (3) is phrased with the flat locus `AlgebraicGeometry.Space.flatLocus` of Stacks 0DLR,
the some-chart form of flatness at a point of Stacks 05VV part (1), and with the transcendence
degree `AlgebraicGeometry.Space.HasTranscendenceDegreeAt` of Stacks 04NM, which specifies a
value in `ℕ∞` rather than producing one; the bound is therefore an existential over that value.
Both are chart-independent: the first by Stacks 05VU, available here as
`AlgebraicGeometry.Space.isFlatOverAtOnChartDiagram_iff_mem_flatLocus`, and the second by
Stacks 04NC, available as
`AlgebraicGeometry.Space.hasTranscendenceDegreeAt_pointsMap_iff`.  Those two chart comparisons
are the whole content of the passage between (1), (2) and the scheme-level dimension criterion
Stacks 0CWF, which is what the source's proof appeals to.

Quasi-coherence and finite type of the module are taken both on the small étale site, which is
what Stacks 05VU consumes, and chartwise, which is what Stacks 0CWF consumes, exactly as in
`StacksFrontier/AlgebraicGeometry/Spaces/FlatFiniteTypeModuleFibre.lean`.

Condition (1) asks both vertical arrows of the square to be surjective, as the source does;
surjectivity is `AlgebraicGeometry.Space.IsSurjective` of Stacks 03ME, surjectivity of the map
on points.  A square with both charts surjective exists by Tag 02X1.

## References

* [Stacks Project, Tag 0CWS](https://stacks.math.columbia.edu/tag/0CWS)
* [Stacks Project, Tag 0CWG](https://stacks.math.columbia.edu/tag/0CWG)
* [Stacks Project, Tag 0CWF](https://stacks.math.columbia.edu/tag/0CWF)
* [Stacks Project, Tag 04NM](https://stacks.math.columbia.edu/tag/04NM)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.Space

/-- Comparing an extended natural number with a natural number is the same in `ℕ∞` and in
`WithBot ℕ∞`. -/
private lemma coe_withBot_lt_natCast_iff {a : ℕ∞} {n : ℕ} :
    (a : WithBot ℕ∞) < (n : WithBot ℕ∞) ↔ a < (n : ℕ∞) := by
  exact_mod_cast Iff.rfl

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The condition on one commuting square of charts -/

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 0CWG on one commuting square of étale scheme charts.** The restriction of `F` to
the source chart is flat over the target chart in dimensions `≥ n`: in every fibre of the chart
morphism, the points at which the restricted module is not flat form a subset of dimension less
than `n`. -/
abbrev IsFlatOverInDimensionsGEOnChartDiagram (hX : IsAlgebraicSpace B S hS X) {f : X ⟶ Y}
    (F : Modules.{u, u} B S hS X hX) (d : ChartDiagram B S hS X Y f) (n : ℕ) : Prop :=
  ∀ s : etaleChartScheme B S hS d.V,
    topologicalKrullDim ↥{y : ((BigFppfOver.toScheme B S hS).map d.g).fiber s |
        ¬ IsFlatOverAtOnChartDiagram B S hS hX F d
          (((BigFppfOver.toScheme B S hS).map d.g).fiberι s y)} < (n : WithBot ℕ∞)

/-- The chartwise condition is the condition of Stacks 0CWG for the chart morphism and the
restriction of the module to the source chart. -/
theorem isFlatOverInDimensionsGEOnChartDiagram_iff (hX : IsAlgebraicSpace B S hS X) {f : X ⟶ Y}
    (F : Modules.{u, u} B S hS X hX) (hf : IsLocallyOfFiniteType B S hS f)
    (hqc : IsQuasicoherentOnCharts B S hS hX F) (hft : IsFiniteTypeOnCharts B S hS hX F)
    (d : ChartDiagram B S hS X Y f) (n : ℕ) :
    IsFlatOverInDimensionsGEOnChartDiagram B S hS hX F d n ↔
      letI := locallyOfFiniteType_chartDiagram B S hS hf d
      letI := hqc d.U
      letI := hft d.U
      IsFlatOverInDimensionsGE ((BigFppfOver.toScheme B S hS).map d.g)
        (chartModule B S hS hX F d.U) n :=
  Iff.rfl

/-- **The dimension criterion on one commuting square of charts, Stacks 0CWF.** The chartwise
condition holds exactly when the residue field extension of the chart morphism has transcendence
degree less than `n` at every point of the source chart at which the restricted module is not
flat over the target chart. -/
theorem isFlatOverInDimensionsGEOnChartDiagram_iff_forall_toENat_trdeg_lt
    (hX : IsAlgebraicSpace B S hS X) {f : X ⟶ Y} (F : Modules.{u, u} B S hS X hX)
    (hf : IsLocallyOfFiniteType B S hS f) (hqc : IsQuasicoherentOnCharts B S hS hX F)
    (hft : IsFiniteTypeOnCharts B S hS hX F) (d : ChartDiagram B S hS X Y f) (n : ℕ) :
    IsFlatOverInDimensionsGEOnChartDiagram B S hS hX F d n ↔
      ∀ u : etaleChartScheme B S hS d.U, ¬ IsFlatOverAtOnChartDiagram B S hS hX F d u →
        letI : Algebra
            ((etaleChartScheme B S hS d.V).residueField
              ((BigFppfOver.toScheme B S hS).map d.g u))
            ((etaleChartScheme B S hS d.U).residueField u) :=
          (((BigFppfOver.toScheme B S hS).map d.g).residueFieldMap u).hom.toAlgebra
        Cardinal.toENat (Algebra.trdeg
            ((etaleChartScheme B S hS d.V).residueField
              ((BigFppfOver.toScheme B S hS).map d.g u))
            ((etaleChartScheme B S hS d.U).residueField u)) < (n : ℕ∞) := by
  have := locallyOfFiniteType_chartDiagram B S hS hf d
  have := hqc d.U
  have := hft d.U
  refine Iff.trans (topologicalKrullDim_not_isFlatOverAt_fiber_lt_iff
    ((BigFppfOver.toScheme B S hS).map d.g) (chartModule B S hS hX F d.U) n) ?_
  refine forall_congr' fun u => imp_congr_right fun _ => ?_
  exact coe_withBot_lt_natCast_iff

/-! ### The three conditions -/

/-- **Condition (1) of Stacks 0CWS.** For some commuting square of étale scheme charts with
both charts surjective, the restriction of `F` to the source chart is flat over the target
chart in dimensions `≥ n`. -/
abbrev IsFlatOverInDimensionsGEOnSomeChartDiagram (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X hX) (n : ℕ) : Prop :=
  ∃ d : ChartDiagram B S hS X Y f, IsSurjective B S hS d.U.obj.hom ∧
    IsSurjective B S hS d.V.obj.hom ∧ IsFlatOverInDimensionsGEOnChartDiagram B S hS hX F d n

/-- **Condition (2) of Stacks 0CWS.** For every commuting square of étale scheme charts, the
restriction of `F` to the source chart is flat over the target chart in dimensions `≥ n`. -/
abbrev IsFlatOverInDimensionsGEOnEveryChartDiagram (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X hX) (n : ℕ) : Prop :=
  ∀ d : ChartDiagram B S hS X Y f, IsFlatOverInDimensionsGEOnChartDiagram B S hS hX F d n

/-- **Condition (3) of Stacks 0CWS.** At every point of `|X|` at which `F` is not flat over
`Y`, the transcendence degree of the point over its image is less than `n`. -/
abbrev HasTrdegLtAtNonflatPoints (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X hX) (n : ℕ) : Prop :=
  ∀ x : points B S hS X, x ∉ flatLocus B S hS hX f F →
    ∃ r : ℕ∞, HasTranscendenceDegreeAt B S hS f x r ∧ r < (n : ℕ∞)

/-! ### Reading the two chart-independent invariants on a chart -/

variable {Xs Ys : AlgebraicSpaces B S hS}

/-- **The chart equation for the transcendence degree of Stacks 04NM.** The transcendence degree
over its image of the point of `|X|` below a point `u` of the source chart of a commuting square
of étale scheme charts is `r` exactly when the residue field extension of the chart morphism at
`u` has transcendence degree `r`. -/
theorem hasTranscendenceDegreeAt_pointOfEtaleChart_iff (f : Xs ⟶ Ys)
    (d : ChartDiagram B S hS Xs.1 Ys.1 f.hom) (u : etaleChartScheme B S hS d.U) (r : ℕ∞) :
    HasTranscendenceDegreeAt B S hS f.hom (pointOfEtaleChart B S hS d.U u) r ↔
      letI : Algebra
          ((etaleChartScheme B S hS d.V).residueField
            ((BigFppfOver.toScheme B S hS).map d.g u))
          ((etaleChartScheme B S hS d.U).residueField u) :=
        (((BigFppfOver.toScheme B S hS).map d.g).residueFieldMap u).hom.toAlgebra
      Cardinal.toENat (Algebra.trdeg
          ((etaleChartScheme B S hS d.V).residueField
            ((BigFppfOver.toScheme B S hS).map d.g u))
          ((etaleChartScheme B S hS d.U).residueField u)) = r :=
  hasTranscendenceDegreeAt_pointsMap_iff B S hS r f.hom d.U.obj.left d.V.obj.left
    d.U.obj.hom d.V.obj.hom d.g d.U.property d.V.property d.comm.symm u

/-- A commuting square of étale scheme charts with both charts surjective exists, by Tag 02X1
applied to a surjective étale atlas of the target. -/
theorem exists_surjective_chartDiagram (f : Xs ⟶ Ys) :
    ∃ d : ChartDiagram B S hS Xs.1 Ys.1 f.hom,
      IsSurjective B S hS d.U.obj.hom ∧ IsSurjective B S hS d.V.obj.hom := by
  obtain ⟨V₀, b, hbSurjective, hbEtale⟩ := Ys.2.exists_atlas
  obtain ⟨U₀, a, g, hcomm, haSurjective, haEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS Xs.2 Ys.2 f.hom V₀ b hbSurjective hbEtale
  exact ⟨{ U := ⟨CostructuredArrow.mk a, haEtale⟩, V := ⟨CostructuredArrow.mk b, hbEtale⟩
           g := g, comm := hcomm },
    (surjective_iff_surjective_pointsMap B S hS Xs.1 Xs.2 U₀ a).mp haSurjective,
    (surjective_iff_surjective_pointsMap B S hS Ys.1 Ys.2 V₀ b).mp hbSurjective⟩

/-! ### The equivalence -/

variable (f : Xs ⟶ Ys) (F : Modules.{u, u} B S hS Xs.1 Xs.2) [F.IsQuasicoherentOnSite]
  (hf : IsLocallyOfFiniteType B S hS f.hom)
  (hqc : IsQuasicoherentOnCharts B S hS Xs.2 F) (hft : IsFiniteTypeOnCharts B S hS Xs.2 F)

include hf hqc hft in
/-- **(1) implies (3).** On a commuting square of étale scheme charts whose source chart is
surjective, the chartwise condition forces the transcendence degree bound at every point of
`|X|` at which `F` is not flat over `Y`. -/
theorem hasTrdegLtAtNonflatPoints_of_onChartDiagram {n : ℕ}
    {d : ChartDiagram B S hS Xs.1 Ys.1 f.hom} (hd : IsSurjective B S hS d.U.obj.hom)
    (h : IsFlatOverInDimensionsGEOnChartDiagram B S hS Xs.2 F d n) :
    HasTrdegLtAtNonflatPoints B S hS Xs.2 f.hom F n := by
  intro x hx
  obtain ⟨z, hz⟩ := hd x
  set u : etaleChartScheme B S hS d.U := pointsEquivScheme B S hS d.U.obj.left z with hudef
  have hu : pointOfEtaleChart B S hS d.U u = x := by
    have hzu : (pointsEquivScheme B S hS d.U.obj.left).symm u = z := by
      rw [hudef, Equiv.symm_apply_apply]
    change pointsMap B S hS (yoneda.obj d.U.obj.left) d.U.obj.hom
      ((pointsEquivScheme B S hS d.U.obj.left).symm u) = x
    rw [hzu]
    exact hz
  have hnf : ¬ IsFlatOverAtOnChartDiagram B S hS Xs.2 F d u := fun hflat =>
    hx (hu ▸ (isFlatOverAtOnChartDiagram_iff_mem_flatLocus B S hS f F d u).1 hflat)
  let : Algebra
      ((etaleChartScheme B S hS d.V).residueField ((BigFppfOver.toScheme B S hS).map d.g u))
      ((etaleChartScheme B S hS d.U).residueField u) :=
    (((BigFppfOver.toScheme B S hS).map d.g).residueFieldMap u).hom.toAlgebra
  refine ⟨Cardinal.toENat (Algebra.trdeg
      ((etaleChartScheme B S hS d.V).residueField ((BigFppfOver.toScheme B S hS).map d.g u))
      ((etaleChartScheme B S hS d.U).residueField u)), ?_, ?_⟩
  · rw [← hu]
    exact (hasTranscendenceDegreeAt_pointOfEtaleChart_iff B S hS f d u _).2 rfl
  · exact (isFlatOverInDimensionsGEOnChartDiagram_iff_forall_toENat_trdeg_lt B S hS Xs.2 F
      hf hqc hft d n).1 h u hnf

include hf hqc hft in
/-- **(3) implies (2).** The transcendence degree bound at the points of `|X|` at which `F` is
not flat over `Y` forces the chartwise condition on every commuting square of étale scheme
charts. -/
theorem isFlatOverInDimensionsGEOnChartDiagram_of_hasTrdegLt {n : ℕ}
    (h : HasTrdegLtAtNonflatPoints B S hS Xs.2 f.hom F n)
    (d : ChartDiagram B S hS Xs.1 Ys.1 f.hom) :
    IsFlatOverInDimensionsGEOnChartDiagram B S hS Xs.2 F d n := by
  refine (isFlatOverInDimensionsGEOnChartDiagram_iff_forall_toENat_trdeg_lt B S hS Xs.2 F
    hf hqc hft d n).2 fun u hu => ?_
  obtain ⟨r, hr, hrn⟩ := h (pointOfEtaleChart B S hS d.U u) fun hmem =>
    hu ((isFlatOverAtOnChartDiagram_iff_mem_flatLocus B S hS f F d u).2 hmem)
  rw [(hasTranscendenceDegreeAt_pointOfEtaleChart_iff B S hS f d u r).1 hr]
  exact hrn

include hf hqc hft in
/-- **Stacks 0CWS, conditions (1) and (3).** Flatness in dimensions `≥ n` on some commuting
square of surjective étale scheme charts is the bound `trdeg < n` at every point at which `F`
is not flat over `Y`. -/
@[stacks 0CWS "the equivalence of conditions (1) and (3)"]
theorem isFlatOverInDimensionsGEOnSomeChartDiagram_iff_hasTrdegLt (n : ℕ) :
    IsFlatOverInDimensionsGEOnSomeChartDiagram B S hS Xs.2 f.hom F n ↔
      HasTrdegLtAtNonflatPoints B S hS Xs.2 f.hom F n := by
  refine ⟨fun ⟨d, hdU, _, hd⟩ =>
    hasTrdegLtAtNonflatPoints_of_onChartDiagram B S hS f F hf hqc hft hdU hd, fun h => ?_⟩
  obtain ⟨d, hdU, hdV⟩ := exists_surjective_chartDiagram B S hS f
  exact ⟨d, hdU, hdV,
    isFlatOverInDimensionsGEOnChartDiagram_of_hasTrdegLt B S hS f F hf hqc hft h d⟩

include hf hqc hft in
/-- **Stacks 0CWS, conditions (2) and (3).** Flatness in dimensions `≥ n` on every commuting
square of étale scheme charts is the bound `trdeg < n` at every point at which `F` is not flat
over `Y`. -/
@[stacks 0CWS "the equivalence of conditions (2) and (3)"]
theorem isFlatOverInDimensionsGEOnEveryChartDiagram_iff_hasTrdegLt (n : ℕ) :
    IsFlatOverInDimensionsGEOnEveryChartDiagram B S hS Xs.2 f.hom F n ↔
      HasTrdegLtAtNonflatPoints B S hS Xs.2 f.hom F n := by
  refine ⟨fun h => ?_,
    fun h => isFlatOverInDimensionsGEOnChartDiagram_of_hasTrdegLt B S hS f F hf hqc hft h⟩
  obtain ⟨d, hdU, _⟩ := exists_surjective_chartDiagram B S hS f
  exact hasTrdegLtAtNonflatPoints_of_onChartDiagram B S hS f F hf hqc hft hdU (h d)

include hf hqc hft in
/-- **Stacks 0CWS, conditions (1) and (2).** Flatness in dimensions `≥ n` can be tested on one
commuting square of surjective étale scheme charts, and then holds on every commuting square of
étale scheme charts. -/
@[stacks 0CWS "the equivalence of conditions (1) and (2)"]
theorem isFlatOverInDimensionsGEOnSomeChartDiagram_iff_onEveryChartDiagram (n : ℕ) :
    IsFlatOverInDimensionsGEOnSomeChartDiagram B S hS Xs.2 f.hom F n ↔
      IsFlatOverInDimensionsGEOnEveryChartDiagram B S hS Xs.2 f.hom F n :=
  (isFlatOverInDimensionsGEOnSomeChartDiagram_iff_hasTrdegLt B S hS f F hf hqc hft n).trans
    (isFlatOverInDimensionsGEOnEveryChartDiagram_iff_hasTrdegLt B S hS f F hf hqc hft n).symm

/-- **Stacks 0CWT.** `F` is *flat over `Y` in dimensions `≥ n`*. The source defines this by the
equivalent conditions of Stacks 0CWS; condition (2) is taken as the definition, and the three
conditions are interchangeable by the theorems above. -/
@[stacks 0CWT "the definition, taken in the form of condition (2) of Stacks 0CWS; conditions \
(1) and (3) are interchangeable with it by \
`isFlatOverInDimensionsGEOnSomeChartDiagram_iff_onEveryChartDiagram` and \
`isFlatOverInDimensionsGEOnEveryChartDiagram_iff_hasTrdegLt`"]
abbrev IsFlatOverInDimensionsGE (n : ℕ) : Prop :=
  IsFlatOverInDimensionsGEOnEveryChartDiagram B S hS Xs.2 f.hom F n

include hf hqc hft in
/-- The definition of Stacks 0CWT may equally be tested on one commuting square of surjective
étale scheme charts, by condition (1) of Stacks 0CWS. -/
theorem isFlatOverInDimensionsGE_iff_onSomeChartDiagram (n : ℕ) :
    IsFlatOverInDimensionsGE B S hS f F n ↔
      IsFlatOverInDimensionsGEOnSomeChartDiagram B S hS Xs.2 f.hom F n :=
  (isFlatOverInDimensionsGEOnSomeChartDiagram_iff_onEveryChartDiagram B S hS f F hf hqc hft n).symm

include hf hqc hft in
/-- The definition of Stacks 0CWT is the bound `trdeg < n` at every point at which `F` is not
flat over `Y`, by condition (3) of Stacks 0CWS. -/
theorem isFlatOverInDimensionsGE_iff_hasTrdegLt (n : ℕ) :
    IsFlatOverInDimensionsGE B S hS f F n ↔
      HasTrdegLtAtNonflatPoints B S hS Xs.2 f.hom F n :=
  isFlatOverInDimensionsGEOnEveryChartDiagram_iff_hasTrdegLt B S hS f F hf hqc hft n

/-! ### Dependence on the isomorphism class of the module only -/

/-- Flatness over the target at a point of the source chart of a commuting square of étale
scheme charts depends on the module only through its isomorphism class: it is the ringed-space
statement of Stacks 08KT applied to the restriction of the isomorphism to the chart. -/
theorem isFlatOverAtOnChartDiagram_iff_of_moduleIso (hX : IsAlgebraicSpace B S hS X) {φ : X ⟶ Y}
    {M N : Modules.{u, u} B S hS X hX} (e : M ≅ N) (d : ChartDiagram B S hS X Y φ)
    (u : chartScheme d.U) :
    IsFlatOverAtOnChartDiagram B S hS hX M d u ↔ IsFlatOverAtOnChartDiagram B S hS hX N d u :=
  _root_.AlgebraicGeometry.isFlatOverAt_iff_of_moduleIso _ (restrictToChartIso B S hS hX e d.U) u

/-- The chartwise condition of Stacks 0CWG on one commuting square of étale scheme charts
depends on the module only through its isomorphism class: isomorphic modules have the same
non-flat locus in every fibre of the chart morphism. -/
theorem isFlatOverInDimensionsGEOnChartDiagram_iff_of_moduleIso
    (hX : IsAlgebraicSpace B S hS X) {φ : X ⟶ Y} {M N : Modules.{u, u} B S hS X hX} (e : M ≅ N)
    (d : ChartDiagram B S hS X Y φ) (n : ℕ) :
    IsFlatOverInDimensionsGEOnChartDiagram B S hS hX M d n ↔
      IsFlatOverInDimensionsGEOnChartDiagram B S hS hX N d n := by
  refine forall_congr' fun s => ?_
  have hset : {y : ((BigFppfOver.toScheme B S hS).map d.g).fiber s |
        ¬ IsFlatOverAtOnChartDiagram B S hS hX M d
          (((BigFppfOver.toScheme B S hS).map d.g).fiberι s y)} =
      {y : ((BigFppfOver.toScheme B S hS).map d.g).fiber s |
        ¬ IsFlatOverAtOnChartDiagram B S hS hX N d
          (((BigFppfOver.toScheme B S hS).map d.g).fiberι s y)} :=
    Set.ext fun y => not_congr (isFlatOverAtOnChartDiagram_iff_of_moduleIso B S hS hX e d _)
  rw [hset]

/-- **Stacks 0CWT depends on the module only through its isomorphism class.** Isomorphic
modules are flat over `Y` in dimensions `≥ n` together, in the form of condition (2). -/
theorem isFlatOverInDimensionsGEOnEveryChartDiagram_iff_of_moduleIso
    (hX : IsAlgebraicSpace B S hS X) (φ : X ⟶ Y) {M N : Modules.{u, u} B S hS X hX} (e : M ≅ N)
    (n : ℕ) :
    IsFlatOverInDimensionsGEOnEveryChartDiagram B S hS hX φ M n ↔
      IsFlatOverInDimensionsGEOnEveryChartDiagram B S hS hX φ N n :=
  forall_congr' fun d => isFlatOverInDimensionsGEOnChartDiagram_iff_of_moduleIso B S hS hX e d n

/-- **Stacks 0CWT depends on the module only through its isomorphism class**, at the definition
`AlgebraicGeometry.Space.IsFlatOverInDimensionsGE`. -/
theorem isFlatOverInDimensionsGE_iff_of_moduleIso (ψ : Xs ⟶ Ys)
    {M N : Modules.{u, u} B S hS Xs.1 Xs.2} (e : M ≅ N) (n : ℕ) :
    IsFlatOverInDimensionsGE B S hS ψ M n ↔ IsFlatOverInDimensionsGE B S hS ψ N n :=
  isFlatOverInDimensionsGEOnEveryChartDiagram_iff_of_moduleIso B S hS Xs.2 ψ.hom e n

/-! ### The base-change clause -/

variable {X' Y' : AlgebraicSpaces B S hS}

include hf in
/-- **The base-change clause of Stacks 0CWS through condition (3).** In a cartesian square of
algebraic spaces over `S` whose right vertical arrow `f` is locally of finite type, the bound
`trdeg < n` at the points at which `F` is not flat over `Y` passes to the inverse image
`(g')^*F` on the source of the base change.

Condition (3) of Stacks 0CWS mentions no chart, so the transport needs only two chart-free
inputs.  The first is Stacks 05VW read at a point,
`AlgebraicGeometry.Space.mem_flatLocus_modulePullback_of_mem_flatLocus`, used in the form that
non-flatness of the inverse image descends to non-flatness of `F`.  The second is that base
change does not increase the transcendence degree of a point over its image, which is part (2)
of Stacks 04NS, available here as
`AlgebraicGeometry.Space.transcendenceDegreeAt_le_of_isPullback`.  The transcendence degree at
`x'` exists and is finite because `f'` is locally of finite type (Stacks 0EDN), and the two
dimensions of local rings of fibres that part (2) of Stacks 04NS compares alongside it exist by
`AlgebraicGeometry.Space.exists_hasFiberLocalRingDimension`. -/
theorem hasTrdegLtAtNonflatPoints_modulePullback_of_isPullback {g' : X' ⟶ Xs} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Ys} (sq : IsPullback g'.hom f'.hom f.hom g.hom)
    {n : ℕ} (h : HasTrdegLtAtNonflatPoints B S hS Xs.2 f.hom F n) :
    HasTrdegLtAtNonflatPoints B S hS X'.2 f'.hom ((modulePullback B S hS g').obj F) n := by
  have hcat : IsPullback g' f' f g := IsPullback.of_map_of_faithful (F := ObjectProperty.ι _) sq
  have hf' : IsLocallyOfFiniteType B S hS f'.hom :=
    (isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback hcat hf
  intro x' hx'
  obtain ⟨r, hr, hrn⟩ := h (pointsMap B S hS X'.1 g'.hom x') fun hmem =>
    hx' (mem_flatLocus_modulePullback_of_mem_flatLocus B S hS sq F x' hmem)
  obtain ⟨m, hm⟩ := exists_finite_transcendenceDegreeAt B S hS f'.hom hf' x'
  obtain ⟨e, he⟩ :=
    exists_hasFiberLocalRingDimension B S hS Xs.2 Ys.2 f.hom (pointsMap B S hS X'.1 g'.hom x')
  obtain ⟨e', he'⟩ := exists_hasFiberLocalRingDimension B S hS X'.2 Y'.2 f'.hom x'
  exact ⟨(m : ℕ∞), hm, lt_of_le_of_lt (transcendenceDegreeAt_le_of_isPullback B S hS sq
    X'.2 Xs.2 Y'.2 Ys.2 hf x' e r e' (m : ℕ∞) he hr he' hm) hrn⟩

include hf in
/-- **Condition (3) of Stacks 0CWS descends along a jointly surjective family of flat base
changes.** Let `f : X ⟶ Y` be locally of finite type and let `(Z i, q i, r i)` be a family of
cartesian squares

```
Z i --p i--> X
|q i         |f
v            v
W i --r i--> Y
```

in which every `r i` is flat at every point of `|W i|` and the `r i` are jointly surjective on
points. If the bound `trdeg < n` holds at the points at which the inverse image `(p i)^*F` is
not flat over `W i`, for every `i`, then it holds at the points at which `F` is not flat over
`Y`.

Condition (3) mentions no chart, so the descent is pointwise. A point `x` of `|X|` at which `F`
is not flat over `Y` has its image in `|Y|` hit by some `r i`, and part (3) of **Stacks 04NS**,
`AlgebraicGeometry.Space.exists_point_preserving_fiberLocalRingDimension_and_trdeg`, lifts `x`
and that point of `|W i|` to a common point `x'` of `|Z i|` at which the transcendence degree
over the image takes the same value. The module `(p i)^*F` is not flat over `W i` at `x'`,
because flatness there would descend to flatness of `F` over `Y` at `x` by part (2) of
**Stacks 05VW** at a point,
`AlgebraicGeometry.Space.mem_flatLocus_of_mem_flatLocus_modulePullback`, whose hypothesis is
exactly flatness of `r i` at the image of `x'`. So the bound assumed at `x'` is the bound
at `x`. -/
theorem hasTrdegLtAtNonflatPoints_of_jointlySurjective_flat_baseChange {I : Type v}
    {Z W : I → AlgebraicSpaces B S hS} {p : ∀ i, Z i ⟶ Xs} {q : ∀ i, Z i ⟶ W i}
    {r : ∀ i, W i ⟶ Ys} (sq : ∀ i, IsPullback (p i).hom (q i).hom f.hom (r i).hom)
    (hflat : ∀ (i : I) (w : points B S hS (W i).1), IsFlatAt B S hS (r i).hom w)
    (hsurj : ∀ y : points B S hS Ys.1, ∃ (i : I) (w : points B S hS (W i).1),
      pointsMap B S hS (W i).1 (r i).hom w = y)
    {n : ℕ} (h : ∀ i, HasTrdegLtAtNonflatPoints B S hS (Z i).2 (q i).hom
      ((modulePullback B S hS (p i)).obj F) n) :
    HasTrdegLtAtNonflatPoints B S hS Xs.2 f.hom F n := by
  intro x hx
  obtain ⟨i, w, hw⟩ := hsurj (pointsMap B S hS Xs.1 f.hom x)
  obtain ⟨x', hxp, -, -, htr⟩ :=
    exists_point_preserving_fiberLocalRingDimension_and_trdeg B S hS (sq i)
      (Z i).2 Xs.2 (W i).2 Ys.2 hf x w hw.symm
  refine (h i x' fun hmem => hx ?_).imp fun t ht => ⟨(htr t).2 ht.1, ht.2⟩
  have hdesc := mem_flatLocus_of_mem_flatLocus_modulePullback B S hS (sq i) F x'
    (hflat i (pointsMap B S hS (Z i).1 (q i).hom x')) hmem
  rwa [hxp] at hdesc

include hf in
/-- **Stacks 0CWS, the base-change clause.** Let `f : X ⟶ Y` be locally of finite type, let `F`
be quasi-coherent of finite type, and let the square be cartesian over a morphism `Y' ⟶ Y`.
If the transcendence degree over its image of every point of `|X|` at which `F` is not flat
over `Y` is less than `n`, then the inverse image `(g')^*F` of `F` on `X' = X ×_Y Y'` is flat
over `Y'` in dimensions `≥ n`.

The hypothesis is condition (3) of Stacks 0CWS written out: the flat locus is
`AlgebraicGeometry.Space.flatLocus` of Stacks 0DLR and the transcendence degree is
`AlgebraicGeometry.Space.HasTranscendenceDegreeAt` of Stacks 04NM, and by
`AlgebraicGeometry.Space.isFlatOverInDimensionsGE_iff_hasTrdegLt` it is exactly flatness over
`Y` in dimensions `≥ n` in the sense of Stacks 0CWT, which is what
`AlgebraicGeometry.Space.isFlatOverInDimensionsGE_modulePullback_of_isPullback` below states it
as.  Writing it out is what keeps the registered form of the clause free of the abbreviations
introduced in this file, so that no hypothesis of it is read as standing in for an input.

The clause is that condition on the two sides together with
`AlgebraicGeometry.Space.hasTrdegLtAtNonflatPoints_modulePullback_of_isPullback`, which is where
Stacks 05VW at a point enters.

The hypotheses on `F` are the source's, read on the small étale site: quasi-coherence and finite
type there, which the inverse image inherits by Stacks 03GA and by Stacks 03DO for the clause
03DL (5), `AlgebraicGeometry.Space.isFiniteTypeOnSite_modulePullback`.  The chartwise forms of
the two, which the equivalence of Stacks 0CWS consumes, follow for both modules by
`AlgebraicGeometry.Space.isQuasicoherentOnCharts_of_isQuasicoherentOnSite` and
`AlgebraicGeometry.Space.isFiniteTypeOnCharts_of_isFiniteTypeOnSite`, so neither is assumed of
the inverse image. -/
@[stacks 0CWS "the base-change clause: if the transcendence degree over its image of every \
point at which the module is not flat over the target is < n -- condition (3) of the tag, \
written out -- then the inverse image of the module is flat over the new target in \
dimensions >= n"]
theorem isFlatOverInDimensionsGE_modulePullback_of_hasTrdegLt
    (hftS : SheafOfModules.IsFiniteTypeOnSite F) {g' : X' ⟶ Xs} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Ys} (sq : IsPullback g'.hom f'.hom f.hom g.hom) (n : ℕ)
    (h : ∀ x : points B S hS Xs.1, x ∉ flatLocus B S hS Xs.2 f.hom F →
      ∃ r : ℕ∞, HasTranscendenceDegreeAt B S hS f.hom x r ∧ r < (n : ℕ∞)) :
    IsFlatOverInDimensionsGE B S hS f' ((modulePullback B S hS g').obj F) n := by
  have hcat : IsPullback g' f' f g := IsPullback.of_map_of_faithful (F := ObjectProperty.ι _) sq
  have hf' : IsLocallyOfFiniteType B S hS f'.hom :=
    (isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback hcat hf
  have hqcS' : ((modulePullback B S hS g').obj F).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS g' F inferInstance
  have hftS' : SheafOfModules.IsFiniteTypeOnSite ((modulePullback B S hS g').obj F) :=
    isFiniteTypeOnSite_modulePullback B S hS g' F hftS
  exact (isFlatOverInDimensionsGE_iff_hasTrdegLt B S hS f' _ hf'
      (isQuasicoherentOnCharts_of_isQuasicoherentOnSite B S hS X' _ hqcS')
      (isFiniteTypeOnCharts_of_isFiniteTypeOnSite B S hS X' _ hqcS' hftS') n).2
    (hasTrdegLtAtNonflatPoints_modulePullback_of_isPullback B S hS f F hf sq h)

include hf in
/-- **The base-change clause of Stacks 0CWS with the condition of Stacks 0CWT on both sides.**
Let `f : X ⟶ Y` be locally of finite type, let `F` be quasi-coherent of finite type and flat
over `Y` in dimensions `≥ n` in the sense of Stacks 0CWT, and let the square be cartesian over
a morphism `Y' ⟶ Y`.  Then the inverse image `(g')^*F` of `F` on `X' = X ×_Y Y'` is flat over
`Y'` in dimensions `≥ n`.

This is `AlgebraicGeometry.Space.isFlatOverInDimensionsGE_modulePullback_of_hasTrdegLt`, which
is where the tag is registered, with its hypothesis converted through
`AlgebraicGeometry.Space.isFlatOverInDimensionsGE_iff_hasTrdegLt`, the equivalence of
conditions (2) and (3) of Stacks 0CWS.  It is the form a consumer holding the definition of
Stacks 0CWT wants; it asserts nothing the registered statement does not. -/
theorem isFlatOverInDimensionsGE_modulePullback_of_isPullback
    (hftS : SheafOfModules.IsFiniteTypeOnSite F) {g' : X' ⟶ Xs} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Ys} (sq : IsPullback g'.hom f'.hom f.hom g.hom)
    (n : ℕ) (h : IsFlatOverInDimensionsGE B S hS f F n) :
    IsFlatOverInDimensionsGE B S hS f' ((modulePullback B S hS g').obj F) n :=
  isFlatOverInDimensionsGE_modulePullback_of_hasTrdegLt B S hS f F hf hftS sq n
    ((isFlatOverInDimensionsGE_iff_hasTrdegLt B S hS f F hf
      (isQuasicoherentOnCharts_of_isQuasicoherentOnSite B S hS Xs F inferInstance)
      (isFiniteTypeOnCharts_of_isFiniteTypeOnSite B S hS Xs F inferInstance hftS) n).1 h)

end AlgebraicGeometry.Space

end
