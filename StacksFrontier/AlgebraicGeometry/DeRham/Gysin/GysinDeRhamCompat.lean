module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinChartLift
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.WedgeDifferential
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.MapCommutesWithDifferential
public import StacksFrontier.AlgebraicGeometry.ExternalTensorPullback.ComparisonSections

/-!
# Stacks 0G87: the glued Gysin map is compatible with the de Rham differentials

Let `π : X ⟶ S` be a morphism of schemes and let `i : Z ⟶ X` be as in [Stacks, Tag 0G86]: a
closed immersion of finite presentation whose conormal sheaf is locally free of rank `c`. Tag
0G86 produces the canonical Gysin map

`γ^p : Ω^p_{Z/S} ⟶ ℋ^c_Z(Ω^{p+c}_{X/S})`,

glued from the Gysin maps of the local equations, and [Stacks, Tag 0G87] says that `γ^p` is
compatible with the de Rham differentials on `Ω^•_{X/S}` and `Ω^•_{Z/S}`.  The source's proof is
one sentence: the assertion is local, and locally it is [Stacks, Tag 0G85].

This file carries out that reduction for the Gysin map the library actually builds,
`Stacks.Gysin.GysinChartData.gysinHom`, which is the shape every 0G86 statement in this
development takes: the chart data is a hypothesis, and so are the three ingredients of the
chart-local square that the abstractness of that hypothesis puts out of reach.  The design is the
one `StacksFrontier/AlgebraicGeometry/DeRham/Gysin/Transverse.lean` already uses for
[Stacks, Tag 0G89], the base-change square for the same glued map.

## Main definitions

* `Stacks.Gysin.pushforwardDeRham`: **the left vertical arrow of the square** — the relative de
  Rham differential of `Z/S`, read on the sections of `i_*Ω^p_{Z/S}` over an open of `X`.  It is
  constructed, not assumed.
* `Stacks.Gysin.ambientDeRhamShift`: the relative de Rham differential of `X/S` in the degree the
  Gysin map lands in, carried into the degree the next Gysin map lands in.  The transport is the
  degree bookkeeping `p + c + 1 = p + 1 + c`, which is not an identity of natural numbers for
  variable `p` and `c`.
* `Stacks.Gysin.GysinDeRhamData`: **the input of the comparison**, for the Gysin maps of
  [Stacks, Tag 0G86] in two consecutive degrees.  No field says anything about the Gysin maps:
  the commutativity of the square is `GysinDeRhamData.gysinHom_comm_deRham`.

## Main results

* `Stacks.Gysin.d_equationsWedgeOn_eq_zero` and `Stacks.Gysin.d_gysinWedgeOn`: **the wedge factor
  of the Gysin formula of a chart commutes with the de Rham differential** —
  `d(ω ∧ d f₁ ∧ ⋯ ∧ d f_c) = d(ω) ∧ d f₁ ∧ ⋯ ∧ d f_c` for equations defined only on a chart.
  This is step (iii) of the proof of [Stacks, Tag 0G85], localised to a chart;
  `Stacks.Gysin.ambientDeRhamShift_gysinWedgeOn` is the same with the degree transport absorbed.
* `Stacks.Gysin.pushforwardDeRham_subschemeFormPullback`: **restriction of relative forms to the
  closed subscheme commutes with the de Rham differentials**, on sections.  This is
  `AlgebraicGeometry.Scheme.Hom.deRhamComplex_d_relativeDifferentialFormsPullback` at the square
  with `𝟙 S` on the base.
* `Stacks.Gysin.exists_chart_lift_cover`: **every section of `i_*Ω^p_{Z/S}` is, on a covering by
  opens each inside an equation chart, the restriction of an ambient relative `p`-form.**  This
  is `Stacks.Gysin.exists_subschemeFormPullback_restrict` spread over the covering by charts of
  `Stacks.Gysin.GysinChartData.ambient_cover`; it is proved, not assumed, which is why the
  corresponding field of `Stacks.Gysin.GysinBaseChange` has no counterpart below.
* `Stacks.Gysin.GysinDeRhamData.gysinHom_comm_deRham_subschemeFormPullback`: the square commutes
  on a form lifted to the ambient scheme over an equation chart.
* `Stacks.Gysin.GysinDeRhamData.gysinHom_comm_deRham`: **[Stacks, Tag 0G87]** — the square
  commutes.
* `Stacks.Gysin.GysinDeRhamData.tgt_gysinHom_eq`: the carried right vertical arrow is not a free
  parameter — on the image of the Gysin map any two choices agree.

## Implementation notes

**What is proved and what is carried.**  The reduction is proved: the square is local, the
lifting that makes it local is proved, the Gysin formula of [Stacks, Tag 0G86] turns both Gysin
maps into class maps applied to equation wedges, the left vertical arrow is constructed and
carried past restriction to `Z`, and the equation wedge is carried past the differential.  What
is carried, in `GysinDeRhamData`, is exactly what an *abstract* `Stacks.Gysin.GysinChartData`
puts out of reach — and, for the chart data of [Stacks, Tag 0G86] built by
`Stacks.Gysin.gysinChartDataOfClsDet`, which is **not** abstract, all of it but `tgt_cls` is
discharged in
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinDeRhamTarget.lean`:

* `GysinDeRhamData.tgt` and `tgt_res`: **the right vertical arrow**, the action of
  `i_*ℋ ᶜ_Z` on the de Rham differential of `X/S`.  `GysinChartData.target` is an abstract
  object of `X.Modules`, so no functor acts on it; and the differential is only `π⁻¹𝒪_S`-linear,
  so even at the concrete target the arrow is additive and not `𝒪_X`-linear, which is why the
  field is an `AddMonoidHom` on sections.  At the concrete target `Stacks.Gysin.gysinTarget` the
  library has this arrow, by [Stacks, Tag 0G74] part (2): it is
  `Stacks.Gysin.gysinTargetDeRhamHom`, and `Stacks.Gysin.gysinDeRhamDataOfAbHom` reads both
  fields off it, so **neither is an input where such an arrow is available**.  (In the
  `AlgebraicGeometry.Scheme.Hom.pushforwardLocalCohomology` spelling of the *chart* Gysin map of
  [Stacks, Tag 0G83] the same construction is
  `AlgebraicGeometry.Scheme.Hom.gysinTargetDeRhamMap`.)
* `GysinDeRhamData.tgt_cls`: **steps (i) and (ii) of the proof of [Stacks, Tag 0G85]** in the
  chart spelling — the class map `c_{f₁, …, f_c}` of [Stacks, Tag 0G7Q] is natural along the de
  Rham differential **on the equation wedges**.  `GysinChartData.cls` is an arbitrary additive map
  on sections, so nothing about a differential can be derived from it.  For a *global* family of
  equations the library proves this, as
  `Stacks.Perfect.SupportedEndoForgetDegreewise.gysinFormulaCommutesWithDeRham`, and
  `AlgebraicGeometry.Scheme.Hom.gysinMapCommutesWithDeRham` of
  `StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinMapDeRham.lean` is [Stacks, Tag 0G85] itself,
  for the chart Gysin map `AlgebraicGeometry.Scheme.Hom.gysinMap`.  What is missing is only its
  chart-local form; see **what the remaining input is** below.

**Why `tgt_cls` is quantified over the ambient form and not over an arbitrary section.**  The
field says

`tgt(c_{f₁, …, f_c}(ω ∧ d f₁ ∧ ⋯ ∧ d f_c)) = c_{f₁, …, f_c}(d(ω ∧ d f₁ ∧ ⋯ ∧ d f_c))`

and **not** the same equation for an arbitrary section `y` of `Ω^{p+c}_{X/S}`.  That stronger
reading is not merely unproved, it is **false**, and false for every choice of `tgt`, so a field
carrying it would leave this structure uninhabited at the chart data of [Stacks, Tag 0G86] and
make `gysinHom_comm_deRham` vacuous there.  The counterexample: take `S = Spec k`,
`X = Spec k[t, s]`, `Z = {t = 0}`, one equation `f₁ = t`, so `c = 1`, and `p = 0`.  The class map
of [Stacks, Tag 0G7Q] sends a section `y` to the class of the fraction `y / t`.  At `y = t · d s`
the fraction is `d s`, a global form, so `c_t(y) = 0` and hence `tgt(c_t(y)) = 0` for every
additive `tgt`; but `d y = d t ∧ d s`, whose fraction `(d t ∧ d s) / t` is not a global
`2`-form, so `c_t(d y) ≠ 0` in `ℋ ¹_Z(Ω²_{X/S})`.  What goes wrong in general is the Leibniz
term: `d(y / (f₁ ⋯ f_c))` is `(d y) / (f₁ ⋯ f_c)` **plus** `d(1 / (f₁ ⋯ f_c)) ∧ y`, and the
correction vanishes exactly when the `d f_j` already occur in `y` — which is the case of an
equation wedge, and is step (iii) of the source's proof,
`Stacks.Gysin.ambientDeRhamShift_gysinWedgeOn`.  The Gysin formula of [Stacks, Tag 0G83]
evaluates the class map only at such wedges (`GysinChartData.loc_subschemeFormPullback`), so the
restricted field is all the reduction ever uses and `gysinHom_comm_deRham` is unchanged.
* `GysinDeRhamData.chart`, `chart_ambient` and `chart_equations`: the identification of the
  equation charts of the degree-`p` and degree-`p + 1` chart data.  `GysinChartData` is indexed
  by the degree and carries its own chart index type, so two chart data for the same `i` need
  not have the same charts; the field says the degree-`p + 1` data may be taken with the same
  equations, which is how `Stacks.Gysin.exists_gysinCharts` produces them — and for the chart
  data of [Stacks, Tag 0G86] that is how they *are* produced, so the three fields are the
  identity, reflexivity and the functoriality of the structure presheaf at the identity
  (`Stacks.Gysin.chartGysinMatch` and `Stacks.Gysin.gysinDeRhamDataOfClsDet`).

**Why the statement is read on sections.**  `GysinChartData.gysinHom` is a morphism of sheaves of
`𝒪_X`-modules, but neither vertical arrow of the square is: the de Rham differential is only
`π⁻¹𝒪_S`-linear.  On sections over an open all four arrows are maps of abelian groups and the
square is an honest equation, which is the idiom of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/Transverse.lean` and of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/WedgeDifferential.lean`.  Nothing is lost: a morphism
of sheaves is its family of maps on sections.

**Why a degree transport appears.**  The Gysin map in degree `p` lands in degree `p + c`, so the
right vertical arrow lands in `p + c + 1`, whereas the Gysin map in degree `p + 1` lands in
`p + 1 + c`.  For variable `p` and `c` those two natural numbers are equal but not definitionally
so — `Nat.add` recurses on its second argument — and the transport is isolated in
`ambientDeRhamShift`, exactly as the corresponding one in [Stacks, Tag 0G85] for the Gysin map is
isolated in `AlgebraicGeometry.Scheme.Hom.gysinTargetReindex`.

**The carried arrow is pinned, not free.**  `tgt_cls` determines `tgt` on every class
`c_{f₁, …, f_c}(y)`, and over an equation chart the Gysin map takes only such values by the
Gysin formula of [Stacks, Tag 0G83]; so the square cannot be satisfied by a degenerate choice of
right vertical arrow.  `GysinDeRhamData.tgt_gysinHom_eq` records this: on the image of the Gysin
map any two choices of the hypothesis agree.

**There is no `@[stacks 0G87]` attribute in this module.**  `gysinHom_comm_deRham` states the
tag for the Gysin map of [Stacks, Tag 0G86] as this library defines it, but relative to the three
assumed fields listed above, none of which is proved here.  A tag counts only on a declaration
proved under the source's own hypotheses, so a registration — suffixed or not — would be a
conditional one.  At the chart data of [Stacks, Tag 0G86] all of them but `tgt_cls` are
discharged in `StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinDeRhamTarget.lean`, `tgt_cls`
itself is discharged there too by now, and the tag is registered on
`Stacks.Gysin.gysinHom_comm_deRham_of_conormalRank` of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinDeRhamConormalRank.lean`, under the hypotheses of
[Stacks, Tag 0G86] and no others.

**What the remaining input is, and that it is not the input of [Stacks, Tag 0G86].**  `tgt_cls`
at the chart data of [Stacks, Tag 0G86] is the square of [Stacks, Tag 0G85] for the Gysin map of
a chart — `Stacks.Gysin.chartLoc`, which is `AlgebraicGeometry.Scheme.Hom.gysinMap` on
`W.toScheme` for the chart's equations, transported to the global target by
`Stacks.Gysin.chartTargetHom`.  The square on `W.toScheme` is proved, unconditionally:
`AlgebraicGeometry.Scheme.Hom.gysinMapCommutesWithDeRham`.  Of the transport's four factors three
are reachable — the spelling comparison
`Stacks.Perfect.CechSupportTransport.supportCohomologyToPushforward` is compatible with
[Stacks, Tag 0G74] part (2) by
`Stacks.Perfect.SupportedEndoForgetDegreewise.forgetIsoApp`, the identification
`Stacks.AlgebraicGeometry.DifferentialsRestrict.relativeDifferentialFormsRestrictIso` of
`(Ω^•_{X/S})|_W` with `Ω^•_{W/S}` carries the differentials by
`AlgebraicGeometry.Scheme.Hom.deRhamComplex_d_relativeDifferentialFormsMap` read through
`Stacks.Gysin.relativeDifferentialFormsRestrictIso_hom_app`, and
`Stacks.Gysin.supportCohomologySheaf_congr` is a transport along an equality of closed subsets.
The fourth is **the derived excision `Stacks.Gysin.supportCohomologyRestrictIso` read through the
forgetful functor to abelian sheaves**, now named:
`Stacks.Gysin.SupportCohomologyRestrictAbNatural` of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinTargetExcisionAbelian.lean`, where the
restriction of a morphism of abelian sheaves is `Stacks.Gysin.restrictAbHom` and the `𝒪`-linear
half of the compatibility is proved,
`Stacks.Gysin.supportCohomologyRestrictAbNatural_abelianSheaf_map`.  It is **not** a factor of the
same kind as the other three.  The action of [Stacks, Tag 0G74] part (2) is a conjugation of the
*abelian* local cohomology functor, so the compatibility, quantified over the morphism of abelian
sheaves, *is* the statement that the abelian reading of the derived excision is excision for the
abelian local cohomology sheaves — the identification of the derived with the abelian excision
that the respelling of `Stacks.Gysin.gysinTarget` was chosen to avoid, and that the module
docstring of `StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinTargetExcision.lean` records as
absent.  The implementation notes of `GysinTargetExcisionAbelian.lean` say what is still owed.
The underived base change of [Stacks, Tag 08FE] for modules on ringed spaces is in the library;
what is owed is the abelian material listed there.

**[Stacks, Tag 0G86] is not a second gap.**  Its own input — the determinant rule of
[Stacks, Tag 0G7S] across two equation charts — is in the library:
`Stacks.Gysin.clsDetAcrossCharts` of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/ChartDataComparison.lean` proves it at every degree,
[Stacks, Tag 0G86] is registered there unconditionally and unsuffixed on
`Stacks.Gysin.existsUnique_gysinHom_of_conormalRank`, and the square at the chart data of
[Stacks, Tag 0G86] —
`Stacks.Gysin.gysinHom_comm_deRham_chartGysinChartData` of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinDeRhamTarget.lean` — carries `tgt_cls` and
nothing else.  `Stacks.Gysin.ClsCommutesWithDeRham` and the abelian reading of the excision, the remaining
inputs of an unsuffixed 0G87, are both theorems —
`Stacks.Gysin.chartFractionCommutesWithDeRham` with
`Stacks.Gysin.clsCommutesWithDeRham_of_excision` of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinChartFractionDeRham.lean`, and
`Stacks.Gysin.excisionAbComparisonEqAbelianExcision` of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinExcisionAbelianAgreement.lean` — and 0G87 is
registered, unsuffixed, on `Stacks.Gysin.gysinHom_comm_deRham_of_conormalRank` of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinDeRhamConormalRank.lean`.

## References

* [Stacks Project, Tag 0G87](https://stacks.math.columbia.edu/tag/0G87)
* [Stacks Project, Tag 0G86](https://stacks.math.columbia.edu/tag/0G86)
* [Stacks Project, Tag 0G85](https://stacks.math.columbia.edu/tag/0G85)
* [Stacks Project, Tag 0G83](https://stacks.math.columbia.edu/tag/0G83)
* [Stacks Project, Tag 0G7Q](https://stacks.math.columbia.edu/tag/0G7Q)
* [Stacks Project, Tag 0G74](https://stacks.math.columbia.edu/tag/0G74)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme.Hom
open Stacks.Tag01VSPullbackTensor (homApp_presheaf_map)

universe u

namespace Stacks.Gysin

variable {Z X S : Scheme.{u}}

/-! ### The equation wedge of a chart is closed -/

/-- **The equation wedge of a chart is closed:** `d(d f₁ ∧ ⋯ ∧ d f_c) = 0` for a family of
functions defined on an open `W` of `X`, read over an open `V ≤ W`.  It is an ordered wedge of
exact one-forms, so this is
`AlgebraicGeometry.SheafOfModules.d_prodDegOne_exactOne_eq_zero`; it is the chart-local form of
`AlgebraicGeometry.Scheme.Hom.d_equationsWedge_eval_eq_zero`. -/
theorem d_equationsWedgeOn_eq_zero (π : X ⟶ S) {W : X.Opens} {c : ℕ} (f : Fin c → Γ(X, W))
    {V : X.Opens} (hV : V ≤ W) :
    ((deRhamComplex π).d c (c + 1)).val.app (op V) (equationsWedgeOn π f hV) = 0 :=
  AlgebraicGeometry.SheafOfModules.d_prodDegOne_exactOne_eq_zero (deRhamAlgebras π)
    (AlgebraicGeometry.SheafOfModules.deRhamDifferential (deRhamAlgebras π)) c (op V)
    fun j => X.presheaf.map (homOfLE hV).op (f j)

/-- **The wedge factor of the Gysin formula of a chart commutes with the de Rham differential:**

`d(ω ∧ d f₁ ∧ ⋯ ∧ d f_c) = d(ω) ∧ d f₁ ∧ ⋯ ∧ d f_c`,

the two sides compared in degree `p + c + 1` through the identification of that degree with
`p + 1 + c`.  This is step (iii) of the proof of [Stacks, Tag 0G85], for equations defined only
on a chart: the equation wedge is closed, so the graded Leibniz rule leaves only the term in
which `ω` is differentiated.  It is the chart-local form of
`AlgebraicGeometry.Scheme.Hom.d_gysinWedgeHom_app`. -/
theorem d_gysinWedgeOn (π : X ⟶ S) {W : X.Opens} {c : ℕ} (f : Fin c → Γ(X, W)) (p : ℕ)
    {V : X.Opens} (hV : V ≤ W) (ω : Γ(relativeDifferentialForms π (p : ℤ), V)) :
    ((deRhamComplex π).d (p + c) (p + c + 1)).val.app (op V) (gysinWedgeOn π f (p : ℤ) hV ω) =
      ((deRhamComplex π).XIsoOfEq (show p + 1 + c = p + c + 1 by omega)).hom.val.app (op V)
        (gysinWedgeOn π f ((p + 1 : ℕ) : ℤ) hV
          (((deRhamComplex π).d p (p + 1)).val.app (op V) ω)) :=
  AlgebraicGeometry.SheafOfModules.d_formProduct_of_closed_right (deRhamAlgebras π)
    (AlgebraicGeometry.SheafOfModules.deRhamDifferential (deRhamAlgebras π)) p c (op V) ω
    (equationsWedgeOn π f hV) (d_equationsWedgeOn_eq_zero π f hV)

/-! ### The two vertical arrows of the square, on sections -/

/-- Two terms of the relative de Rham complex of equal degree are identified by transports in
either direction, which cancel. -/
private theorem xIsoOfEq_hom_app_xIsoOfEq_hom_app (π : X ⟶ S) {m n : ℕ} (h : m = n)
    (U : X.Opensᵒᵖ) (z : ((deRhamComplex π).X m).val.obj U) :
    ((deRhamComplex π).XIsoOfEq h.symm).hom.val.app U
        (((deRhamComplex π).XIsoOfEq h).hom.val.app U z) = z := by
  subst h
  simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom]
  rfl

/-- **The relative de Rham differential of `X/S` in the degree the Gysin map lands in, read in
the degree the next Gysin map lands in.**  The Gysin map of degree `p` lands in `Ω^{p+c}_{X/S}`,
so its differential lands in degree `p + c + 1`, whereas the Gysin map of degree `p + 1` lands in
`Ω^{p+1+c}_{X/S}`; the two degrees are equal and the identification is carried here. -/
def ambientDeRhamShift (π : X ⟶ S) (c p : ℕ) (V : X.Opens)
    (y : Γ(relativeDifferentialForms π ((p : ℤ) + (c : ℤ)), V)) :
    Γ(relativeDifferentialForms π (((p + 1 : ℕ) : ℤ) + (c : ℤ)), V) :=
  ((deRhamComplex π).XIsoOfEq (show p + c + 1 = p + 1 + c by omega)).hom.val.app (op V)
    (((deRhamComplex π).d (p + c) (p + c + 1)).val.app (op V) y)

/-- **Step (iii) of the proof of [Stacks, Tag 0G85] in a chart, with the degree transport
absorbed:** the differential of the equation wedge of a `p`-form is the equation wedge of its
differential. -/
theorem ambientDeRhamShift_gysinWedgeOn (π : X ⟶ S) {W : X.Opens} {c : ℕ} (f : Fin c → Γ(X, W))
    (p : ℕ) {V : X.Opens} (hV : V ≤ W) (ω : Γ(relativeDifferentialForms π (p : ℤ), V)) :
    ambientDeRhamShift π c p V (gysinWedgeOn π f (p : ℤ) hV ω) =
      gysinWedgeOn π f ((p + 1 : ℕ) : ℤ) hV (((deRhamComplex π).d p (p + 1)).val.app (op V) ω) :=
  (congrArg
      (((deRhamComplex π).XIsoOfEq (show p + c + 1 = p + 1 + c by omega)).hom.val.app (op V))
      (d_gysinWedgeOn π f p hV ω)).trans
    (xIsoOfEq_hom_app_xIsoOfEq_hom_app π (show p + 1 + c = p + c + 1 by omega) (op V) _)

/-- **The left vertical arrow of the square**: the relative de Rham differential of `Z/S`, on the
sections of `i_*Ω^p_{Z/S}` over an open of `X`.  Sections of the direct image over `V` are
sections of `Ω^p_{Z/S}` over `i⁻¹V`, so no comparison map is involved. -/
def pushforwardDeRham (i : Z ⟶ X) (π : X ⟶ S) (p : ℕ) (V : X.Opens)
    (x : Γ(pushforwardRelativeForms i π (p : ℤ), V)) :
    Γ(pushforwardRelativeForms i π ((p + 1 : ℕ) : ℤ), V) :=
  ((deRhamComplex (i ≫ π)).d p (p + 1)).val.app (op (i ⁻¹ᵁ V)) x

/-- The left vertical arrow is additive. -/
theorem pushforwardDeRham_add (i : Z ⟶ X) (π : X ⟶ S) (p : ℕ) (V : X.Opens)
    (x y : Γ(pushforwardRelativeForms i π (p : ℤ), V)) :
    pushforwardDeRham i π p V (x + y) =
      pushforwardDeRham i π p V x + pushforwardDeRham i π p V y :=
  map_add _ _ _

/-- The left vertical arrow commutes with restriction, being the action on sections of a morphism
of presheaves. -/
theorem pushforwardDeRham_res (i : Z ⟶ X) (π : X ⟶ S) (p : ℕ) {V V' : X.Opens} (hV' : V' ≤ V)
    (x : Γ(pushforwardRelativeForms i π (p : ℤ), V)) :
    pushforwardDeRham i π p V'
        ((pushforwardRelativeForms i π (p : ℤ)).presheaf.map (homOfLE hV').op x) =
      (pushforwardRelativeForms i π ((p + 1 : ℕ) : ℤ)).presheaf.map (homOfLE hV').op
        (pushforwardDeRham i π p V x) :=
  PresheafOfModules.naturality_apply ((deRhamComplex (i ≫ π)).d p (p + 1)).val
    (homOfLE (show i ⁻¹ᵁ V' ≤ i ⁻¹ᵁ V from fun _ hz => hV' hz)).op x

/-- **Restriction of relative forms to the closed subscheme commutes with the de Rham
differentials**, on sections: `d(ω̃|_Z) = (d ω̃)|_Z`.  This is
`AlgebraicGeometry.Scheme.Hom.deRhamComplex_d_relativeDifferentialFormsPullback` at the square
with `𝟙 S` on the base, which is the square `Stacks.Gysin.subschemeFormPullback` is built at. -/
theorem pushforwardDeRham_subschemeFormPullback (i : Z ⟶ X) (π : X ⟶ S) (p : ℕ) (V : X.Opens)
    (ω : Γ(relativeDifferentialForms π (p : ℤ), V)) :
    pushforwardDeRham i π p V (subschemeFormPullback i π (p : ℤ) V ω) =
      subschemeFormPullback i π ((p + 1 : ℕ) : ℤ) V
        (((deRhamComplex π).d p (p + 1)).val.app (op V) ω) :=
  deRhamComplex_d_relativeDifferentialFormsPullback i π (i ≫ π) (𝟙 S)
    (Category.comp_id (i ≫ π)).symm p V ω

/-! ### Every section lifts to the ambient scheme on a covering by charts -/

/-- Restricting a section along two inclusions of opens is restricting along the composite. -/
private theorem presheaf_map_homOfLE_map_homOfLE {C : Type*} [Category C] {FC : C → C → Type*}
    {CC : C → Type*} [∀ A B, FunLike (FC A B) (CC A) (CC B)] [ConcreteCategory C FC]
    (F : (Opens X)ᵒᵖ ⥤ C) {U V W : Opens X} (h₁ : U ≤ V) (h₂ : V ≤ W) (h : U ≤ W)
    (x : ToType (F.obj (op W))) :
    F.map (homOfLE h₁).op (F.map (homOfLE h₂).op x) = F.map (homOfLE h).op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  exact congrArg (fun m : U ⟶ W => F.map m.op x) (Subsingleton.elim _ _)

/-- **Every section of `i_*Ω^p_{Z/S}` is, on a covering of its open by opens each inside an
equation chart, the restriction of an ambient relative `p`-form.**  The charts cover `X` by
`Stacks.Gysin.GysinChartData.ambient_cover`, and restriction of `p`-forms to `Z` is locally
surjective by `Stacks.Gysin.exists_subschemeFormPullback_restrict`, so each point of the open has
a neighbourhood inside a chart over which the section lifts.

This is the `lift` field of `Stacks.Gysin.GysinBaseChange`, here proved rather than assumed. -/
theorem exists_chart_lift_cover (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {c p : ℕ}
    (D : GysinChartData i π c p) (V : X.Opens)
    (x : Γ(pushforwardRelativeForms i π (p : ℤ), V)) :
    ∃ (J : Type u) (V₀ : J → X.Opens) (hle : ∀ k, V₀ k ≤ V) (a : J → D.Chart),
      (∀ k, V₀ k ≤ D.ambient (a k)) ∧ (V ≤ ⨆ k, V₀ k) ∧
        ∀ k, ∃ ω, subschemeFormPullback i π (p : ℤ) (V₀ k) ω =
          (pushforwardRelativeForms i π (p : ℤ)).presheaf.map (homOfLE (hle k)).op x := by
  have key : ∀ z : ↥V, ∃ (W : X.Opens) (a : D.Chart) (hWV : W ≤ V),
      (z : X) ∈ W ∧ W ≤ D.ambient a ∧
        ∃ ω, subschemeFormPullback i π (p : ℤ) W ω =
          (pushforwardRelativeForms i π (p : ℤ)).presheaf.map (homOfLE hWV).op x := by
    rintro ⟨z, hz⟩
    obtain ⟨a, ha⟩ := D.ambient_cover z
    have hzU : z ∈ V ⊓ D.ambient a := ⟨hz, ha⟩
    have hUV : V ⊓ D.ambient a ≤ V := inf_le_left
    obtain ⟨W, hWU, hzW, ω, hω⟩ := exists_subschemeFormPullback_restrict i π p
      (V ⊓ D.ambient a)
      ((pushforwardRelativeForms i π (p : ℤ)).presheaf.map (homOfLE hUV).op x) z hzU
    refine ⟨W, a, hWU.trans hUV, hzW, hWU.trans inf_le_right, ω, hω.trans ?_⟩
    exact presheaf_map_homOfLE_map_homOfLE _ _ _ _ _
  choose W a hWV hzW hWa ω hω using key
  refine ⟨↥V, W, hWV, a, hWa, fun z hz => Opens.mem_iSup.mpr ⟨⟨z, hz⟩, hzW ⟨z, hz⟩⟩,
    fun k => ⟨ω k, hω k⟩⟩

/-! ### The input of the comparison -/

/-- **The input of [Stacks, Tag 0G87]**, for the Gysin maps of [Stacks, Tag 0G86] in two
consecutive degrees.  The module docstring says which field stands for which result of the Stacks
project and why each is an input rather than a consequence.  No field says anything about the
Gysin maps: the commutativity of the square is `GysinDeRhamData.gysinHom_comm_deRham`. -/
structure GysinDeRhamData (i : Z ⟶ X) (π : X ⟶ S) {c p : ℕ}
    (D : GysinChartData i π c p) (D' : GysinChartData i π c (p + 1)) where
  /-- **The right vertical arrow of the square**: the action of `i_*ℋ ᶜ_Z` on the relative de
  Rham differential of `X/S`, on sections.  It is additive and not `𝒪_X`-linear, the differential
  being only `π⁻¹𝒪_S`-linear.  Its construction at the concrete target is [Stacks, Tag 0G74]
  part (2). -/
  tgt : (V : X.Opens) → Γ(D.target, V) →+ Γ(D'.target, V)
  /-- It commutes with restriction, being a map of sheaves. -/
  tgt_res : ∀ (V V₀ : X.Opens) (hV₀ : V₀ ≤ V) (y : Γ(D.target, V)),
    tgt V₀ (D.target.presheaf.map (homOfLE hV₀).op y)
      = D'.target.presheaf.map (homOfLE hV₀).op (tgt V y)
  /-- The equation chart of the degree-`p + 1` data attached to one of the degree-`p` data. -/
  chart : D.Chart → D'.Chart
  /-- Its open contains the open of the chart it comes from. -/
  chart_ambient : ∀ a, D.ambient a ≤ D'.ambient (chart a)
  /-- **Its equations are the same equations.** -/
  chart_equations : ∀ (a : D.Chart) (j : Fin c),
    X.presheaf.map (homOfLE (chart_ambient a)).op (D'.equations (chart a) j) = D.equations a j
  /-- **Steps (i) and (ii) of the proof of [Stacks, Tag 0G85]**: the class map
  `c_{f₁, …, f_c}` of [Stacks, Tag 0G7Q] of a chart is natural along the de Rham differential
  **on the equation wedges** — the sections at which the Gysin formula of [Stacks, Tag 0G83]
  evaluates it.

  The quantifier is over the ambient `p`-form `ω`, not over an arbitrary section of
  `Ω^{p+c}_{X/S}`: at an arbitrary section the equation is **false**, and so would make this
  structure uninhabited at the chart data of [Stacks, Tag 0G86]. The counterexample is in the
  implementation notes. -/
  tgt_cls : ∀ (a : D.Chart) (V : X.Opens) (hV : V ≤ D.ambient a)
    (ω : Γ(relativeDifferentialForms π (p : ℤ), V)),
    tgt V (D.cls a V hV (gysinWedgeOn π (D.equations a) (p : ℤ) hV ω))
      = D'.cls (chart a) V (hV.trans (chart_ambient a))
          (ambientDeRhamShift π c p V (gysinWedgeOn π (D.equations a) (p : ℤ) hV ω))

namespace GysinDeRhamData

variable {i : Z ⟶ X} {π : X ⟶ S} {c p : ℕ} {D : GysinChartData i π c p}
  {D' : GysinChartData i π c (p + 1)} (B : GysinDeRhamData i π D D')

/-- The equations of the degree-`p + 1` chart, restricted to an open of the chart they come from,
are the restrictions of the equations of the degree-`p` chart.  This is `chart_equations` spread
over a smaller open by functoriality of the structure presheaf. -/
theorem chart_equations_res (a : D.Chart) {V : X.Opens} (hV : V ≤ D.ambient a) (j : Fin c) :
    X.presheaf.map (homOfLE (hV.trans (B.chart_ambient a))).op (D'.equations (B.chart a) j)
      = X.presheaf.map (homOfLE hV).op (D.equations a j) := by
  rw [← B.chart_equations a j]
  exact (presheaf_map_homOfLE_map_homOfLE _ _ _ _ _).symm

/-- **The square commutes on a form lifted to the ambient scheme over an equation chart.**  This
is the computation of [Stacks, Tag 0G87]: on the restriction `ω̃|_Z` of an ambient `p`-form both
Gysin maps are given by the Gysin formula of [Stacks, Tag 0G83], the class maps are natural along
the differential by `tgt_cls`, restriction to `Z` commutes with the differentials by
`pushforwardDeRham_subschemeFormPullback`, and the equation wedge is carried past the
differential by `ambientDeRhamShift_gysinWedgeOn`. -/
theorem gysinHom_comm_deRham_subschemeFormPullback (a : D.Chart) (V : X.Opens)
    (hV : V ≤ D.ambient a) (ω : Γ(relativeDifferentialForms π (p : ℤ), V)) :
    B.tgt V (D.gysinHom.app V (subschemeFormPullback i π (p : ℤ) V ω))
      = D'.gysinHom.app V
          (pushforwardDeRham i π p V (subschemeFormPullback i π (p : ℤ) V ω)) := by
  have hV' : V ≤ D'.ambient (B.chart a) := hV.trans (B.chart_ambient a)
  have hright := D'.gysinHom_app_subschemeFormPullback (B.chart a) V hV'
    (((deRhamComplex π).d p (p + 1)).val.app (op V) ω)
  rw [pushforwardDeRham_subschemeFormPullback i π p V ω, hright,
    D.gysinHom_app_subschemeFormPullback a V hV ω, B.tgt_cls a V hV ω]
  refine congrArg (D'.cls (B.chart a) V hV') ?_
  refine Eq.trans (congrArg (ambientDeRhamShift π c p V)
    (gysinWedgeOn_restrict π (D.equations a) (p : ℤ) hV ω).symm) ?_
  refine Eq.trans (ambientDeRhamShift_gysinWedgeOn π
    (fun j => X.presheaf.map (homOfLE hV).op (D.equations a j)) p (le_refl V) ω) ?_
  refine Eq.trans (congrArg
    (fun z : Fin c → Γ(X, V) => gysinWedgeOn π z ((p + 1 : ℕ) : ℤ) (le_refl V)
      (((deRhamComplex π).d p (p + 1)).val.app (op V) ω))
    (funext fun j => (B.chart_equations_res a hV j).symm)) ?_
  exact gysinWedgeOn_restrict π (D'.equations (B.chart a)) ((p + 1 : ℕ) : ℤ) hV' _

/-- **Stacks Project, Tag 0G87.**  For `X → S` and `i : Z → X` as in [Stacks, Tag 0G86], the
Gysin map `γ^p` of that lemma is compatible with the de Rham differentials on `Ω^•_{X/S}` and
`Ω^•_{Z/S}`: the square

`i_*Ω^p_{Z/S} ⟶ i_*ℋ ᶜ_Z(Ω^{p+c}_{X/S})`,  `i_*Ω^{p+1}_{Z/S} ⟶ i_*ℋ ᶜ_Z(Ω^{p+c+1}_{X/S})`

whose horizontal arrows are the Gysin maps `Stacks.Gysin.GysinChartData.gysinHom` of degrees `p`
and `p + 1`, whose left vertical arrow is the de Rham differential of `Z/S` and whose right
vertical arrow is the action of `i_*ℋ ᶜ_Z` on the de Rham differential of `X/S`, commutes.

The source checks this locally and appeals to [Stacks, Tag 0G85], and so does this proof: every
section is, on a covering by opens inside equation charts, the restriction of an ambient form
(`Stacks.Gysin.exists_chart_lift_cover`), there the square is
`gysinHom_comm_deRham_subschemeFormPullback`, and the target is a sheaf, so the square holds over
the open itself. -/
/- **No `@[stacks 0G87]` attribute.** The square below is proved relative to a `GysinDeRhamData`,
whose fields are not all derived *here*: `tgt` with `tgt_res` (the action of `i_*ℋ ᶜ_Z` on the de
Rham differential of `X/S`), `tgt_cls` (steps (i) and (ii) of the proof of [Stacks, Tag 0G85] —
naturality of the class map of [Stacks, Tag 0G7Q] along the de Rham differential — in the
chart-local spelling), and `chart` with `chart_ambient`/`chart_equations` (matching the degree-`p`
and degree-`p+1` charts).

For the chart data of [Stacks, Tag 0G86] all of these but `tgt_cls` are derived, in
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinDeRhamTarget.lean`: `tgt` and `tgt_res` from
[Stacks, Tag 0G74] part (2) at the Gysin target, and the chart matching from the fact that one
family of equation charts serves both degrees.

A tag counts only on a declaration proved under the source's own hypotheses, so registering
0G87 would still be a conditional registration while `tgt_cls` stands. What is genuinely proved
here is everything else: the local liftability of forms (`exists_chart_lift_cover`), the
wedge-factor step (iii) of 0G85 (`ambientDeRhamShift_gysinWedgeOn`), the left vertical arrow
(`pushforwardDeRham`) and its compatibility with restriction to `Z`, and the gluing of the square
from a covering by opens inside equation charts. `tgt_gysinHom_eq` shows the assumed data adds no
freedom where the square lives.

The remaining input is the square of [Stacks, Tag 0G85] for the chart Gysin map transported to
the global target, whose one missing factor is the derived excision read through the forgetful
functor to abelian sheaves; the implementation notes say which three of the four factors are
available and why this is not the input of [Stacks, Tag 0G86].

That remaining input is itself split in two by
`Stacks.Gysin.clsCommutesWithDeRham_of_excision_of_chartFraction` of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinDeRhamClsReduction.lean`: at the chart data of
[Stacks, Tag 0G86], `tgt_cls` follows from `Stacks.Gysin.SupportCohomologyRestrictAbNatural` of
each chart at the de Rham differential together with
`Stacks.Gysin.ChartFractionCommutesWithDeRham` of each chart, and from nothing else.  Both halves
are open statements, so that reduction carries no tag either. -/
theorem gysinHom_comm_deRham [IsClosedImmersion i] (V : X.Opens)
    (x : Γ(pushforwardRelativeForms i π (p : ℤ), V)) :
    B.tgt V (D.gysinHom.app V x)
      = D'.gysinHom.app V (pushforwardDeRham i π p V x) := by
  obtain ⟨J, V₀, hle, a, ha, hcov, hlift⟩ := exists_chart_lift_cover i π D V x
  have key : ∀ k : J, D'.target.presheaf.map (homOfLE (hle k)).op
        (B.tgt V (D.gysinHom.app V x))
      = D'.target.presheaf.map (homOfLE (hle k)).op
        (D'.gysinHom.app V (pushforwardDeRham i π p V x)) := by
    intro k
    obtain ⟨ω, hω⟩ := hlift k
    rw [← B.tgt_res V (V₀ k) (hle k) (D.gysinHom.app V x),
      ← homApp_presheaf_map D.gysinHom (homOfLE (hle k)) x,
      ← homApp_presheaf_map D'.gysinHom (homOfLE (hle k)) _,
      ← pushforwardDeRham_res i π p (hle k) x, ← hω]
    exact B.gysinHom_comm_deRham_subschemeFormPullback (a k) (V₀ k) (ha k) ω
  exact TopCat.Sheaf.eq_of_locally_eq'
    (F := (⟨D'.target.presheaf, D'.target.isSheaf⟩ : TopCat.Sheaf Ab.{u} X))
    V₀ V (fun k => homOfLE (hle k)) hcov _ _ key

/-- **The carried right vertical arrow is not a free parameter:** on the image of the Gysin map
any two choices of `GysinDeRhamData` for the same chart data agree, both being the Gysin map of
the next degree applied to the de Rham differential of `Z/S`.  The hypothesis `tgt_cls` pins the
arrow on every class `c_{f₁, …, f_c}(y)`, and over an equation chart the Gysin map takes only
such values. -/
theorem tgt_gysinHom_eq [IsClosedImmersion i] (B₁ B₂ : GysinDeRhamData i π D D') (V : X.Opens)
    (x : Γ(pushforwardRelativeForms i π (p : ℤ), V)) :
    B₁.tgt V (D.gysinHom.app V x) = B₂.tgt V (D.gysinHom.app V x) :=
  (B₁.gysinHom_comm_deRham V x).trans (B₂.gysinHom_comm_deRham V x).symm

end GysinDeRhamData

end Stacks.Gysin

end
