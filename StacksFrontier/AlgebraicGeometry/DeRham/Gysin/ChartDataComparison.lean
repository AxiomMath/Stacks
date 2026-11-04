module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinChartClsImmersionComp
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinChartLocal

/-!
# The input of [Stacks, Tag 0G86], assembled from the hypotheses of the tag

`Stacks.Gysin.GysinChartData.comparison` asks, for every open `V` contained in two equation
charts, for a covering of `V` by opens over which the two charts' data are comparable in the
sense of `Stacks.Gysin.ChartComparison`.  `ChartComparison` has five fields, and four of them are
theorems of this library:

* `matrix` and `equations_eq`, the change-of-equations matrix, are
  `Stacks.Gysin.exists_changeOfEquations`, which also produces the covering and makes it affine;
* `wedge_det`, the congruence of the two equation wedges, is `Stacks.Gysin.chartWedgeDet`, i.e.
  `AlgebraicGeometry.Scheme.Hom.wedge_det_self`;
* `lift`, the liftability of a relative `p`-form from the closed subscheme, is
  `Stacks.Gysin.exists_subschemeFormPullback_of_isAffineOpen`, which is why the covering is taken
  affine.

This file performs that assembly, and then **proves** that fifth field: `cls_det` — the
determinant rule of [Stacks, Tag 0G7S] *across two charts* — is `Stacks.Gysin.clsDetAcrossCharts`
below.  Everything the input of [Stacks, Tag 0G86] asks for is therefore a theorem of this
library and the record is **built** rather than assumed.

What this file proves is the tag for a rank of the form `c = d + 1`, that being what the chart
route can reach: `Stacks.Gysin.exists_gysinCharts` needs `c ≠ 0`, since away from the closed
subscheme the chart equations must generate the unit ideal and an empty family cannot.  The tag
itself asks for an arbitrary `c`, and is registered in
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinConormalRankAny.lean` on
`Stacks.Gysin.existsUnique_gysinHom_of_conormalRank`, which splits on `c` and calls
`Stacks.Gysin.existsUnique_gysinHom_of_conormalRank_succ` below for the positive case.

## Main definitions

* `Stacks.Gysin.chartClsOfGen`: the class map of a chart whose equations generate the ideal of
  the closed subscheme, in the shape the `cls` field of `Stacks.Gysin.GysinChartData` takes.
* `Stacks.Gysin.ClsDetAcrossCharts`: the determinant rule of [Stacks, Tag 0G7S] for the class
  maps of two different charts, stated for arbitrary charts.
* `Stacks.Gysin.gysinChartDataOfClsDet`: **the input of [Stacks, Tag 0G86], every field proved**,
  from a family of equation charts whose equations generate the ideal of the closed subscheme,
  together with `ClsDetAcrossCharts`.
* `Stacks.Gysin.EquationChart`: an open of the ambient scheme together with `c` functions on it
  generating the ideal of the closed subscheme.  Taking *every* equation chart as a chart is what
  makes the conclusion of [Stacks, Tag 0G86] quantify over every local family of equations.

## Main results

* `Stacks.Gysin.chartComparisonOfClsDet`: a `Stacks.Gysin.ChartComparison` over an affine open,
  built from the change-of-equations matrix and the determinant rule alone.
* `Stacks.Gysin.exists_chartComparison_of_cls_det`: **the `comparison` field of
  `Stacks.Gysin.GysinChartData`, in exactly its shape, from the determinant rule alone.**
* `Stacks.Gysin.clsDetAcrossCharts`: **the determinant rule of [Stacks, Tag 0G7S] across two
  charts, proved.**  Both charts are refined to the common open `V'` through
  `AlgebraicGeometry.Scheme.homOfLE` by `Stacks.Gysin.chartCls_homOfLE`, which is the
  open-immersion case of [Stacks, Tag 0G7U] assembled onto the chart transport; on the one chart
  `V'` the rule is `Stacks.Gysin.chartCls_det`, i.e. [Stacks, Tag 0G7S].
* `Stacks.Gysin.exists_gysinChartData`: **the input of [Stacks, Tag 0G86] exists, from the
  hypotheses of the tag** — `i` a closed immersion of finite presentation whose conormal sheaf is
  locally free of rank `d + 1`.
* `Stacks.Gysin.existsUnique_gysinHom_of_conormalRank_succ`: **[Stacks, Tag 0G86] for a rank of
  the form `c = d + 1`**, which is the branch the chart route reaches.

## Implementation notes

**How `cls_det` across two charts is proved.**  For one chart and two families of equations the
rule is `Stacks.Gysin.chartCls_det`, which is [Stacks, Tag 0G7S].  Two *different* charts `Wa`,
`Wb` meeting in `V'` are reduced to that case by the locality of the class map of
[Stacks, Tag 0G7Q] — that `Stacks.Gysin.chartClsHom` of a chart `W`, restricted to a smaller
open, is `chartClsHom` of that open with the restricted equations — which is the open-immersion
case of [Stacks, Tag 0G7U].  Both charts are refined through the chart-to-chart leg
`AlgebraicGeometry.Scheme.homOfLE`, which lands both class maps on the one scheme `V'.toScheme`,
where `Stacks.Perfect.SupportedFraction.supportedFractionSource_eq_det_smul` applies.

**That the leg is not `AlgebraicGeometry.Scheme.Opens.ι` is why the whole tower had to be
generalised.**  An open immersion factors as an isomorphism onto its range followed by
`Opens.ι`, so that factorisation reduces the general case to the isomorphism case and not the
other way round.  The Čech base change of
`StacksFrontier/AlgebraicGeometry/Perfect/SupportClosedSubset/` therefore holds along an arbitrary
open immersion `g : X' ⟶ X` throughout, its degree-`p` reading is
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinClassBaseChangeImmersion.lean`, the excision
factor is `Stacks.Gysin.supportCohomologyOpenImmersionIso` of `ChartDataExcision.lean`, and the
assembly onto the chart transport is `Stacks.Gysin.chartClsHom_homOfLE` and
`Stacks.Gysin.chartCls_homOfLE` of `GysinChartClsImmersionComp.lean`.  The
generalisation is almost free — the underlying presheaf of
`AlgebraicGeometry.Scheme.Modules.restrictFunctor g` is `g.opensFunctor.op ⋙ X.presheaf` for every
open immersion, so every identification of sections is the same `rfl` it was for `W.ι`, and the
derived machinery was already stated for an arbitrary open immersion of ringed spaces.  The one
place where an open immersion genuinely differs from the inclusion of an open is the comparison
`AlgebraicGeometry.Scheme.Hom.appIso` of the two structure sheaves, the identity for `W.ι` by
`AlgebraicGeometry.Scheme.Opens.ι_appIso`; it enters only where a *scalar* acts, namely at the
denominator of the fraction cochain, and
`Stacks.Perfect.PushforwardRestrict.restrict_smul_eq`, `…appTop_restrict` and `…hom_ringInverse`
absorb it.

**The sections layer.**  `Stacks.Gysin.chartCls` conjugates `chartClsHom` by two restriction maps
read off the open `Stacks.Perfect.LocalCohomologyExcision.chartOpen W hV` of the chart.  Crossing
from one chart to another therefore has to move between two opens of two different schemes whose
images in `X` agree; `Stacks.Gysin.chartClsOn` takes that open and the identification of its
image as arguments instead of deriving them, and `Stacks.Gysin.chartClsOn_congr` says the result
does not depend on the choice, because `W.ι` is injective on opens.  After that every transport
is a restriction map of a module presheaf between sections over opens all equal to `V'`, and
composites of those collapse.

## References

* [Stacks Project, Tag 0G86](https://stacks.math.columbia.edu/tag/0G86)
* [Stacks Project, Tag 0G7S](https://stacks.math.columbia.edu/tag/0G7S)
* [Stacks Project, Tag 0G7U](https://stacks.math.columbia.edu/tag/0G7U)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom
open Stacks.AlgebraicGeometry.RegularIdealSheaf
open Stacks.RingedSpace
open Stacks.AlgebraicGeometry.ConormalEquations

universe u

namespace Stacks.Gysin

variable {Z X S : Scheme.{u}}

/-- **A chart comparison over an affine open, from the determinant rule alone.**  Of the five
fields of `Stacks.Gysin.ChartComparison`, `matrix` and `equations_eq` are the change-of-equations
matrix supplied by `Stacks.Gysin.exists_changeOfEquations`, `wedge_det` is
`Stacks.Gysin.chartWedgeDet` and `lift` is
`Stacks.Gysin.exists_subschemeFormPullback_of_isAffineOpen`; only `cls_det`, the determinant rule
of [Stacks, Tag 0G7S] for the two charts' class maps, is a parameter of this constructor, and it
is `Stacks.Gysin.clsDetAcrossCharts` below. -/
def chartComparisonOfClsDet (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {c p : ℕ}
    {V : X.Opens} (hV : IsAffineOpen V) {T : X.Modules}
    (clsa clsb : Γ(relativeDifferentialForms π ((p : ℤ) + (c : ℤ)), V) →+ Γ(T, V))
    (f g : Fin c → Γ(X, V)) (N : Matrix (Fin c) (Fin c) Γ(X, V))
    (hg : ∀ j, g j = ∑ l, N j l * f l)
    (hdet : ∀ y, clsa y = clsb (N.det • y)) :
    ChartComparison i π c p clsa clsb f g where
  matrix := N
  equations_eq := hg
  cls_det := hdet
  wedge_det := chartWedgeDet π V N f g hg
  lift := exists_subschemeFormPullback_of_isAffineOpen i π p V hV

/-- **The `comparison` field of `Stacks.Gysin.GysinChartData`, in exactly its shape, from the
determinant rule of [Stacks, Tag 0G7S] across two charts alone.**

Everything else the field asks for is proved here: the covering of the common open by affine
opens carrying a change-of-equations matrix is `Stacks.Gysin.exists_changeOfEquations`, and on
each member of it the remaining fields of `Stacks.Gysin.ChartComparison` are discharged by
`chartComparisonOfClsDet`.  The hypothesis `hdet` is the determinant rule for the two charts'
class maps over an affine open on which the change-of-equations matrix exists, and it is a
theorem of this library: `Stacks.Gysin.clsDetAcrossCharts` below. -/
theorem exists_chartComparison_of_cls_det (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S)
    {c p : ℕ} {T : X.Modules} {Wa Wb : X.Opens} {fa : Fin c → Γ(X, Wa)} {fb : Fin c → Γ(X, Wb)}
    (hgen : IsGeneratedByOn X.toRingedSpace (definingIdealOfHom i) Wa fa)
    (hvanish : ∀ (O : X.Opens) (hO : O ≤ Wb) (j : Fin c),
      (i.app O).hom (X.presheaf.map (homOfLE hO).op (fb j)) = 0)
    (clsa : (U : X.Opens) → U ≤ Wa →
      Γ(relativeDifferentialForms π ((p : ℤ) + (c : ℤ)), U) →+ Γ(T, U))
    (clsb : (U : X.Opens) → U ≤ Wb →
      Γ(relativeDifferentialForms π ((p : ℤ) + (c : ℤ)), U) →+ Γ(T, U))
    (V : X.Opens) (ha : V ≤ Wa) (hb : V ≤ Wb)
    (hdet : ∀ (V' : X.Opens) (ha' : V' ≤ Wa) (hb' : V' ≤ Wb), IsAffineOpen V' →
      ∀ N : Matrix (Fin c) (Fin c) Γ(X, V'),
        (∀ j, X.presheaf.map (homOfLE hb').op (fb j) =
            ∑ l, N j l * X.presheaf.map (homOfLE ha').op (fa l)) →
          ∀ y, clsa V' ha' y = clsb V' hb' (N.det • y)) :
    ∃ (J : Type u) (V' : J → X.Opens) (hle : ∀ k, V' k ≤ V)
        (_ : ∀ k, ChartComparison i π c p (clsa (V' k) ((hle k).trans ha))
          (clsb (V' k) ((hle k).trans hb))
          (fun j => X.presheaf.map (homOfLE ((hle k).trans ha)).op (fa j))
          (fun j => X.presheaf.map (homOfLE ((hle k).trans hb)).op (fb j))),
      V ≤ ⨆ k, V' k := by
  classical
  obtain ⟨V', hle, haff, hmat, hcov⟩ := exists_changeOfEquations i hgen hvanish V ha hb
  refine ⟨↥V, V', hle, fun k => ?_, hcov⟩
  exact chartComparisonOfClsDet i π (haff k) _ _ _ _ (hmat k).choose (hmat k).choose_spec
    (hdet (V' k) ((hle k).trans ha) ((hle k).trans hb) (haff k) (hmat k).choose
      (hmat k).choose_spec)

/-! ### The chart data, assembled -/

section Assemble

variable (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {d : ℕ} (p : ℕ)

/-- The class map of a chart whose equations generate the ideal of the closed subscheme, in the
shape the `cls` field of `Stacks.Gysin.GysinChartData` takes: the two hypotheses `chartCls` needs
beyond the chart are `Stacks.Gysin.isClosed_preimage_range_base` and
`Stacks.Gysin.equationsClosedSet_restrictEquations`, and both are available here. -/
def chartClsOfGen (W : X.Opens) (f : Fin (d + 1) → Γ(X, W))
    (hgen : IsGeneratedByOn X.toRingedSpace (definingIdealOfHom i) W f)
    (hvanish : ∀ (V : X.Opens) (hV : V ≤ W) (j : Fin (d + 1)),
      (i.app V).hom (X.presheaf.map (homOfLE hV).op (f j)) = 0)
    (V : X.Opens) (hV : V ≤ W) :
    Γ(relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ)), V) →+
      Γ(gysinTarget i π (d + 1) p, V) :=
  chartCls i π p W (restrictEquations W f) (isClosed_preimage_range_base i W)
    (equationsClosedSet_restrictEquations i W
      (isCutOutByEquationsOn_of_isGeneratedByOn i hgen hvanish)).le V hV

/-- **The input of [Stacks, Tag 0G86], assembled from the tag's own hypotheses and the
determinant rule of [Stacks, Tag 0G7S] across two charts.**

Every field is a theorem of this library: `target` is `Stacks.Gysin.gysinTarget`; `ambient`,
`equations`, `equations_vanish` and `ambient_cover` are the equation charts, which
`Stacks.Gysin.exists_gysinCharts` produces from a closed immersion of finite presentation with
conormal sheaf locally free of rank `d + 1`; `cls` is `Stacks.Gysin.chartCls` and `cls_vanish` is
`Stacks.Gysin.chartCls_vanish`; `loc` is the Gysin map of [Stacks, Tag 0G83] for the chart's
equations, `Stacks.Gysin.chartLoc`, with its three laws and the Gysin formula
`Stacks.Gysin.chartLoc_subschemeFormPullback`; and `comparison` is
`Stacks.Gysin.exists_chartComparison_of_cls_det`.

The single hypothesis `hdet` is the determinant rule of [Stacks, Tag 0G7S] for the class maps of
two *different* charts over an affine open carrying a change-of-equations matrix, and it is
discharged by `Stacks.Gysin.clsDetAcrossCharts` below; `Stacks.Gysin.exists_gysinChartData` is
this constructor with that input supplied. -/
def gysinChartDataOfClsDet (Chart : Type u) (ambient : Chart → X.Opens)
    (equations : (a : Chart) → Fin (d + 1) → Γ(X, ambient a))
    (hvanish : ∀ (a : Chart) (V : X.Opens) (hV : V ≤ ambient a) (j : Fin (d + 1)),
      (i.app V).hom (X.presheaf.map (homOfLE hV).op (equations a j)) = 0)
    (hcover : ∀ x : X, ∃ a, x ∈ ambient a)
    (hgen : ∀ a, IsGeneratedByOn X.toRingedSpace (definingIdealOfHom i) (ambient a) (equations a))
    (hdet : ∀ (a b : Chart) (V' : X.Opens) (ha' : V' ≤ ambient a) (hb' : V' ≤ ambient b),
      IsAffineOpen V' → ∀ N : Matrix (Fin (d + 1)) (Fin (d + 1)) Γ(X, V'),
        (∀ j, X.presheaf.map (homOfLE hb').op (equations b j) =
            ∑ l, N j l * X.presheaf.map (homOfLE ha').op (equations a l)) →
          ∀ y, chartClsOfGen i π p (ambient a) (equations a) (hgen a) (hvanish a) V' ha' y =
            chartClsOfGen i π p (ambient b) (equations b) (hgen b) (hvanish b) V' hb'
              (N.det • y)) :
    GysinChartData i π (d + 1) p where
  target := gysinTarget i π (d + 1) p
  Chart := Chart
  ambient := ambient
  equations := equations
  equations_vanish := hvanish
  ambient_cover := hcover
  cls a V hV := chartClsOfGen i π p (ambient a) (equations a) (hgen a) (hvanish a) V hV
  cls_vanish a V hV r ω hr :=
    chartCls_vanish i π p (ambient a) (equations a) (hgen a) _ _ V hV r ω hr
  loc a V hV := chartLoc i π p (ambient a) (equations a)
    (isCutOutByEquationsOn_of_isGeneratedByOn i (hgen a) (hvanish a))
    (equationsClosedSet_restrictEquations i (ambient a)
      (isCutOutByEquationsOn_of_isGeneratedByOn i (hgen a) (hvanish a))) V hV
  loc_add a V hV x y := chartLoc_add i π p (ambient a) (equations a) _ _ V hV x y
  loc_smul a V hV r x := chartLoc_smul i π p (ambient a) (equations a) _ _ V hV r x
  loc_res a V V' hV' hV x := chartLoc_res i π p (ambient a) (equations a) _ _ V V' hV' hV x
  loc_subschemeFormPullback a V hV ω :=
    chartLoc_subschemeFormPullback i π p (ambient a) (equations a) _ _ _ V hV ω
  comparison a b V ha hb :=
    exists_chartComparison_of_cls_det i π (hgen a) (hvanish b)
      (fun U hU => chartClsOfGen i π p (ambient a) (equations a) (hgen a) (hvanish a) U hU)
      (fun U hU => chartClsOfGen i π p (ambient b) (equations b) (hgen b) (hvanish b) U hU)
      V ha hb (hdet a b)

/-- **The determinant rule of [Stacks, Tag 0G7S] across two equation charts**, stated for
arbitrary charts so that it does not mention a particular choice of them.  This was the last
clause of [Stacks, Tag 0G86] that this library did not have; it is now proved.

For two families of equations on **one** chart the rule is `Stacks.Gysin.chartCls_det`; what
turns that into this is the locality of the class map of [Stacks, Tag 0G7Q] along
`AlgebraicGeometry.Scheme.homOfLE`, the open-immersion case of [Stacks, Tag 0G7U].  Both halves
hold at that generality, so this is **proved**, as `Stacks.Gysin.clsDetAcrossCharts` below; it is
kept as a named predicate because `Stacks.Gysin.gysinChartDataOfClsDet` and the results of
`GysinDeRhamTarget.lean` are stated against it. -/
def ClsDetAcrossCharts (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) (d p : ℕ) : Prop :=
  ∀ (Wa Wb : X.Opens) (fa : Fin (d + 1) → Γ(X, Wa)) (fb : Fin (d + 1) → Γ(X, Wb))
    (hgena : IsGeneratedByOn X.toRingedSpace (definingIdealOfHom i) Wa fa)
    (hvana : ∀ (V : X.Opens) (hV : V ≤ Wa) (j : Fin (d + 1)),
      (i.app V).hom (X.presheaf.map (homOfLE hV).op (fa j)) = 0)
    (hgenb : IsGeneratedByOn X.toRingedSpace (definingIdealOfHom i) Wb fb)
    (hvanb : ∀ (V : X.Opens) (hV : V ≤ Wb) (j : Fin (d + 1)),
      (i.app V).hom (X.presheaf.map (homOfLE hV).op (fb j)) = 0)
    (V' : X.Opens) (ha' : V' ≤ Wa) (hb' : V' ≤ Wb), IsAffineOpen V' →
    ∀ N : Matrix (Fin (d + 1)) (Fin (d + 1)) Γ(X, V'),
      (∀ j, X.presheaf.map (homOfLE hb').op (fb j) =
          ∑ l, N j l * X.presheaf.map (homOfLE ha').op (fa l)) →
        ∀ y, chartClsOfGen i π p Wa fa hgena hvana V' ha' y =
          chartClsOfGen i π p Wb fb hgenb hvanb V' hb' (N.det • y)

/-! ### The determinant rule across two charts, proved -/

/-- **The chart-local cut-out hypothesis restricts to a smaller open.** -/
theorem isCutOutByEquationsOn_restrict {i : Z ⟶ X} {W V : X.Opens} (e : V ≤ W) {I : Type*}
    [Fintype I] {f : I → Γ(X, W)} (h : IsCutOutByEquationsOn i W f) :
    IsCutOutByEquationsOn i V (fun k => X.presheaf.map (homOfLE e).op (f k)) where
  app_eq_zero j := app_map_eq_zero i _ (h.app_eq_zero j)
  exists_eq_sum U hUV a ha x hx := by
    obtain ⟨V₀, hVU, hxV, c, hc⟩ := h.exists_eq_sum U (hUV.trans e) a ha x hx
    refine ⟨V₀, hVU, hxV, c, hc.trans (Finset.sum_congr rfl fun j _ => ?_)⟩
    refine congrArg (fun z => c j * z) ?_
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    exact presheaf_map_congr _ _ (f j)

/-- A function on an open `V` of `X`, read as a global section of the open subscheme
`V.toScheme`, as a ring homomorphism. -/
def restrictScalarHom (V : X.Opens) : Γ(X, V) →+* Γ(V.toScheme, ⊤) :=
  ConcreteCategory.hom (X.presheaf.map (eqToHom V.ι_image_top).op)

/-- `restrictScalarHom V r` is the one-element family `r` read as a global section of
`V.toScheme` by `Stacks.Gysin.restrictEquations`. -/
theorem restrictScalarHom_apply (V : X.Opens) (r : Γ(X, V)) :
    restrictScalarHom V r = restrictEquations V (fun _ : Unit => r) () := rfl

/-- Carrying a function on `V` to `V.toScheme` by `Stacks.Gysin.restrictScalarHom` and back to `V`
by `Stacks.Gysin.chartScalar` returns the function itself. -/
theorem chartScalar_self (V : X.Opens) (r : Γ(X, V)) :
    chartScalar V (le_refl V) (restrictScalarHom V r) = r := by
  show X.presheaf.map _ (V.toScheme.presheaf.map _ (X.presheaf.map _ r)) = r
  refine Eq.trans (presheaf_map_comp_apply _ _ _) ?_
  refine Eq.trans (presheaf_map_comp_apply _ _ r) ?_
  refine Eq.trans (presheaf_map_congr _ (𝟙 (op V)) r) ?_
  rw [X.presheaf.map_id]
  rfl

/-- **The determinant rule of [Stacks, Tag 0G7S] across two equation charts**: the class maps of
two charts agree on a common affine open, up to the determinant of the matrix expressing one
family of equations in terms of the other. -/
theorem clsDetAcrossCharts (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) (d p : ℕ) :
    ClsDetAcrossCharts i π d p := by
  intro Wa Wb fa fb hgena hvana hgenb hvanb V ha hb _haff N hN y
  have hcuta := isCutOutByEquationsOn_restrict ha
    (isCutOutByEquationsOn_of_isGeneratedByOn i hgena hvana)
  have hcutb := isCutOutByEquationsOn_restrict hb
    (isCutOutByEquationsOn_of_isGeneratedByOn i hgenb hvanb)
  have hTV := isClosed_preimage_range_base i V
  have hfTa := equationsClosedSet_restrictEquations i V hcuta
  have hfTb := equationsClosedSet_restrictEquations i V hcutb
  have hA : ∀ j,
      restrictEquations V (fun k => X.presheaf.map (homOfLE hb).op (fb k)) j =
      ∑ l, (N.map (restrictScalarHom V)) j l *
        restrictEquations V (fun k => X.presheaf.map (homOfLE ha).op (fa k)) l := by
    intro j
    show restrictScalarHom V _ = _
    refine Eq.trans (congrArg (fun z => restrictScalarHom V z) (hN j)) ?_
    refine Eq.trans (map_sum (restrictScalarHom V) _ _) ?_
    exact Finset.sum_congr rfl fun l _ => map_mul (restrictScalarHom V) _ _
  refine Eq.trans (chartCls_homOfLE i π p ha fa _ _ hTV hfTa.le y) ?_
  refine Eq.trans (chartCls_det i π p V _ _ (N.map (restrictScalarHom V)) hA hTV hfTa hfTb
    V le_rfl y) ?_
  refine Eq.trans ?_ (chartCls_homOfLE i π p hb fb _ _ hTV hfTb.le (N.det • y)).symm
  refine congrArg (chartCls i π p V _ hTV hfTb.le V le_rfl) ?_
  refine congrArg (fun r => r • y) ?_
  refine Eq.trans (congrArg (chartScalar V (le_refl V))
    (RingHom.map_det (restrictScalarHom V) N).symm) ?_
  exact chartScalar_self V N.det

/-! ### The input of Tag 0G86 exists, and the tag follows -/

/-- **The input of [Stacks, Tag 0G86] exists, from the hypotheses of the tag alone.**  For a
closed immersion of finite presentation whose conormal sheaf is locally free of rank `d + 1`, the
equation charts of `Stacks.Gysin.exists_equationCharts_of_conormalRank` carry all the data of
`Stacks.Gysin.GysinChartData`, and every field is discharged by a theorem of this library — the
determinant rule across two charts by `clsDetAcrossCharts`. -/
theorem exists_gysinChartData (i : Z ⟶ X) [IsClosedImmersion i] [LocallyOfFinitePresentation i]
    (π : X ⟶ S) {d : ℕ} (p : ℕ) (hE : ConormalRank i (d + 1)) :
    Nonempty (GysinChartData i π (d + 1) p) := by
  obtain ⟨ambient, equations, hvanish, hcover, _, hgen, _⟩ :=
    exists_gysinCharts i (d + 1) hE (Nat.succ_ne_zero d)
  exact ⟨gysinChartDataOfClsDet i π p ↥X ambient equations hvanish hcover hgen
    fun a b => clsDetAcrossCharts i π d p (ambient a) (ambient b) (equations a) (equations b)
      (hgen a) (hvanish a) (hgen b) (hvanish b)⟩

/-- **An equation chart of a closed immersion `i`**: an open `W` of the ambient scheme together
with `c` functions on `W` that generate the ideal of the closed subscheme over every open
contained in `W` and vanish on the closed subscheme.

The number of equations is an arbitrary natural number, `c = 0` included: an empty family
generates the ideal of the closed subscheme over `W` exactly when that ideal vanishes on `W`,
which at conormal rank `0` happens on a neighbourhood of every point of the image.  Such a chart
is therefore contained in the image, and at that rank the charts cover the image rather than the
whole of `X` — see `Stacks.Gysin.range_subset_iSup_equationChart_ambient`.

Taking *every* equation chart as a chart of `Stacks.Gysin.GysinChartData` is what makes the glued
map of [Stacks, Tag 0G86] restrict to the Gysin map of **every** local family of equations that
cuts out the closed subscheme, which is what the tag asserts, rather than only to those of one
chosen covering family. -/
structure EquationChart (i : Z ⟶ X) (c : ℕ) where
  /-- The open of `X` on which the chart is defined. -/
  ambient : X.Opens
  /-- The `c` equations of the chart. -/
  equations : Fin c → Γ(X, ambient)
  /-- The equations generate the ideal of the closed subscheme over the chart. -/
  gen : IsGeneratedByOn X.toRingedSpace (definingIdealOfHom i) ambient equations
  /-- The equations vanish on the closed subscheme. -/
  vanish : ∀ (V : X.Opens) (hV : V ≤ ambient) (j : Fin c),
    (i.app V).hom (X.presheaf.map (homOfLE hV).op (equations j)) = 0

/-- **The canonical Gysin map of a closed immersion whose conormal rank is positive.**  Let
`π : X ⟶ S` be a morphism of schemes and `i : Z ⟶ X` a closed immersion of finite presentation
whose conormal sheaf is locally free of rank `c = d + 1`.  Then there is **one** map

`γ^p : i_*Ω^p_{Z/S} ⟶ i_*ℋ^c_Z(Ω^{p+c}_{X/S})`

which, over every open contained in an open on which `c` functions generate the ideal of `Z`,
is the Gysin map `γ^p_{f₁, …, f_c}` of [Stacks, Tag 0G83] of those functions, and it is the only
map with that property.

Both hypotheses are consumed where [Stacks, Tag 0G86] consumes them: they produce the equation
charts, by `Stacks.Gysin.exists_gysinCharts`.  Every other input of the gluing is a theorem of
this library: the local maps of [Stacks, Tag 0G83] and their Gysin formula, the class maps of
[Stacks, Tag 0G7Q], the determinant rule of [Stacks, Tag 0G7S] on one chart and
`clsDetAcrossCharts` across two charts, the congruence of the equation wedges and the local
liftability of relative forms.  The gluing itself is
`Stacks.Gysin.GysinChartData.existsUnique_gysinHom`.

The charts here are *all* the equation charts, which is what makes the conclusion quantify over
every local family of equations and not only over a chosen covering family.

**This is the `c = d + 1` branch of the tag, not the tag.**  [Stacks, Tag 0G86] states the rank
to be an arbitrary `c`, and [Stacks, Tag 0G8A] says `c ≥ 0` explicitly; the registration is
`Stacks.Gysin.existsUnique_gysinHom_of_conormalRank`, which takes `c : ℕ` unrestricted and calls
this theorem for `c = d + 1`.  What forces the split is `Stacks.Gysin.exists_gysinCharts`, which
needs `c ≠ 0`: away from the closed subscheme the chart equations must generate the unit ideal
and an empty family cannot.  The other branch is
`Stacks.Gysin.existsUnique_gysinHom_of_conormalRank_zero`. -/
theorem existsUnique_gysinHom_of_conormalRank_succ (i : Z ⟶ X) [IsClosedImmersion i]
    [LocallyOfFinitePresentation i] (π : X ⟶ S) {d : ℕ} (p : ℕ) (hE : ConormalRank i (d + 1)) :
    ∃! φ : pushforwardRelativeForms i π (p : ℤ) ⟶ gysinTarget i π (d + 1) p,
      ∀ (a : EquationChart i (d + 1)) (V : X.Opens) (hV : V ≤ a.ambient)
        (x : Γ(pushforwardRelativeForms i π (p : ℤ), V)),
        φ.app V x =
          chartLoc i π p a.ambient a.equations
            (isCutOutByEquationsOn_of_isGeneratedByOn i a.gen a.vanish)
            (equationsClosedSet_restrictEquations i a.ambient
              (isCutOutByEquationsOn_of_isGeneratedByOn i a.gen a.vanish)) V hV x := by
  obtain ⟨ambient, equations, hvanish, hcover, _, hgen, _⟩ :=
    exists_gysinCharts i (d + 1) hE (Nat.succ_ne_zero d)
  have hcov : ∀ x : X, ∃ a : EquationChart i (d + 1), x ∈ a.ambient := fun x => by
    obtain ⟨a, ha⟩ := hcover x
    exact ⟨⟨ambient a, equations a, hgen a, hvanish a⟩, ha⟩
  exact (gysinChartDataOfClsDet i π p (EquationChart i (d + 1)) (fun a => a.ambient)
    (fun a => a.equations) (fun a => a.vanish) hcov (fun a => a.gen)
    (fun a b => clsDetAcrossCharts i π d p a.ambient b.ambient a.equations b.equations
      a.gen a.vanish b.gen b.vanish)).existsUnique_gysinHom

end Assemble

end Stacks.Gysin

end
