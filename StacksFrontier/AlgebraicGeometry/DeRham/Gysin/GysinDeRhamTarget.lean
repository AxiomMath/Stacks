module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinDeRhamCompat
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.ChartDataComparison
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinDeRhamDifferential

/-!
# The right vertical arrow of the square of Stacks 0G87, at the concrete Gysin target

`Stacks.Gysin.GysinDeRhamData` of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinDeRhamCompat.lean` is the input of
[Stacks, Tag 0G87] for the glued Gysin map of [Stacks, Tag 0G86].  It is stated for an *abstract*
`Stacks.Gysin.GysinChartData`, whose `target` is an arbitrary object of `X.Modules`; no functor
acts on such an object, so the right vertical arrow of the square — the action of `i_*ℋ ᶜ_Z` on the
de Rham differential of `X/S` — had to be a field there, and so had the matching of the equation
charts of two consecutive degrees.

`Stacks.Gysin.gysinChartDataOfClsDet` of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/ChartDataComparison.lean` builds the chart data at
the
**concrete** target `Stacks.Gysin.gysinTarget`, and this file discharges those two inputs there:

* the right vertical arrow is [Stacks, Tag 0G74] part (2) at the Gysin map's target, which the
  library has as `Stacks.Perfect.GysinAbelianSquare.supportCohomologySheafAbelianMap`, applied to
  the de Rham differential read as a morphism of the underlying abelian sheaves;
* the two degrees' charts are matched because they are the *same* charts:
  `Stacks.Gysin.exists_gysinCharts` does not depend on the exterior degree, so the degree-`p` and
  degree-`p + 1` chart data may be built from one family of equation charts, and the matching is
  the identity.

What is left of `Stacks.Gysin.GysinDeRhamData` is the single field `tgt_cls`, isolated below as
`Stacks.Gysin.ClsCommutesWithDeRham`.

## Main definitions

* `Stacks.Gysin.abSectionsHom`: the action on sections of a morphism of the underlying abelian
  sheaves of two `𝒪_X`-modules, as an additive map.
* `Stacks.Gysin.ambientDeRhamShiftAbHom`: the relative de Rham differential of `X/S` in the degree
  the degree-`p` Gysin map lands in, carried into the degree the degree-`p + 1` Gysin map lands in,
  as a morphism of the **underlying abelian sheaves** — the differential being only
  `π⁻¹𝒪_S`-linear, it is not a morphism of `X.Modules` at all.
* `Stacks.Gysin.gysinTargetDeRhamHom` and `Stacks.Gysin.gysinTargetDeRhamSections`: **the right
  vertical arrow of the square of [Stacks, Tag 0G87]** at the concrete target
  `Stacks.Gysin.gysinTarget`, as a morphism of abelian sheaves and on sections.  This is
  [Stacks, Tag 0G74] part (2) at the Gysin map's target, applied to that differential;
  `Stacks.Gysin.gysinTargetDeRhamHomOfEq` carries it to a chart data whose target is that sheaf.
* `Stacks.Gysin.ClsCommutesWithDeRham`: **steps (i) and (ii) of the proof of [Stacks, Tag 0G85] in
  the chart-local spelling** — the class map `c_{f₁, …, f_c}` of [Stacks, Tag 0G7Q] of a chart is
  natural along the de Rham differential **on the equation wedges**, which is where the Gysin
  formula of [Stacks, Tag 0G83] evaluates it, and which is the strongest form that is true: see
  the counterexample in the implementation notes of
  `StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinDeRhamCompat.lean`.  It is the one field of
  `Stacks.Gysin.GysinDeRhamData` this file does not discharge.
* `Stacks.Gysin.gysinDeRhamDataOfAbHom`: **a `Stacks.Gysin.GysinDeRhamData` from an arrow on the
  two targets** — the fields `tgt` and `tgt_res` are read off such an arrow and are never inputs
  where one is available.
* `Stacks.Gysin.chartGysinChartData`: the chart data of [Stacks, Tag 0G86] on a given family of
  equation charts, with `Stacks.Gysin.chartGysinMatch` the matching of the charts of two
  consecutive degrees and `Stacks.Gysin.chartGysinTargetDeRhamHom` the arrow on its targets.
* `Stacks.Gysin.gysinDeRhamDataOfClsDet`: **the input of [Stacks, Tag 0G87] for the chart data of
  [Stacks, Tag 0G86], with `tgt`, `tgt_res`, `chart`, `chart_ambient` and `chart_equations`
  derived** and `tgt_cls` the only remaining hypothesis.

## Main results

* `Stacks.Gysin.abSectionsHom_ambientDeRhamShiftAbHom`: the morphism of abelian sheaves fed to
  [Stacks, Tag 0G74] part (2) acts on sections as `Stacks.Gysin.ambientDeRhamShift`, which is the
  differential-with-degree-transport that the other fields of `Stacks.Gysin.GysinDeRhamData` speak
  about.  So the right vertical arrow built here is the arrow the square is about, not merely a
  map of the right type.
* `Stacks.Gysin.supportCohomologySheafAbelianMap_map_range`: at a morphism of `X.Modules` the
  abelian action is the `𝒪_X`-linear one, which pins the construction down in the same way, and
  `Stacks.Gysin.gysinTargetDeRhamHomOfEq_rfl`: at the Gysin target the carried arrow is that
  arrow, so the transport adds nothing.
* `Stacks.Gysin.gysinTargetDeRhamSections_res`: the right vertical arrow commutes with
  restriction.
* `Stacks.Gysin.chartGysinChartData_target` and `Stacks.Gysin.chartGysinChartData_cls`: **the
  chart data of [Stacks, Tag 0G86] has the Gysin target and the chart class maps of
  [Stacks, Tag 0G7Q]** — which is what makes `Stacks.Gysin.ClsCommutesWithDeRham` at that data the
  chart-local naturality of the class map of [Stacks, Tag 0G7Q] along `d`, and nothing weaker.
* `Stacks.Gysin.gysinHom_comm_deRham_chartGysinChartData`: **the square of [Stacks, Tag 0G87] with
  its right vertical arrow constructed rather than assumed** — the left one is
  `Stacks.Gysin.pushforwardDeRham` and the horizontal arrows are the glued Gysin maps of the two
  degrees' chart data.
* `Stacks.Gysin.exists_gysinDeRhamData_of_clsCommutesWithDeRham`: **from the hypotheses of
  [Stacks, Tag 0G86] alone — `i` a closed immersion of finite presentation whose conormal sheaf
  is locally free of rank `d + 1` — the input of [Stacks, Tag 0G87] is one statement away**:
  chart data with the Gysin target, an arrow on the targets and a matching of the charts, for
  which only `Stacks.Gysin.ClsCommutesWithDeRham` remains.  The determinant rule
  `Stacks.Gysin.ClsDetAcrossCharts` of [Stacks, Tag 0G7S] across two charts was assumed here in
  both degrees for as long as it was unproved; it is now the theorem
  `Stacks.Gysin.clsDetAcrossCharts` and is supplied rather than assumed.

## Implementation notes

**Why no `@[stacks 0G87]` attribute is added here.**  The square proved below carries **one**
hypothesis, `Stacks.Gysin.ClsCommutesWithDeRham`.  A tag counts only on a declaration proved
under the source's own hypotheses, so registering 0G87 here — suffixed or not — would be a
conditional registration, and a suffix names a partial object and can never license an assumed
input.  That hypothesis is discharged at the chart data of [Stacks, Tag 0G86] by
`Stacks.Gysin.clsCommutesWithDeRham_of_excision` of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinChartFractionDeRham.lean` together with
`Stacks.Gysin.supportCohomologyRestrictAbNatural` of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinExcisionAbelianAgreement.lean`, and the tag is
registered on `Stacks.Gysin.gysinHom_comm_deRham_of_conormalRank` of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinDeRhamConormalRank.lean`.  For a *global* family
of equations the naturality along `d` is
`AlgebraicGeometry.Scheme.Hom.gysinMapCommutesWithDeRham` of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinMapDeRham.lean`, which carries
`@[stacks 0G85]`.

**What changed: the determinant rule is no longer a hypothesis.**  Every statement below used to
carry `Stacks.Gysin.ClsDetAcrossCharts` in the degrees `p` and `p + 1` as well — the determinant
rule of [Stacks, Tag 0G7S] across two equation charts, which was the one input of
[Stacks, Tag 0G86] itself — and the notes here said that discharging `ClsCommutesWithDeRham`
would still leave 0G87 unregistrable because of it.  That is **no longer so**:
`Stacks.Gysin.clsDetAcrossCharts` of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/ChartDataComparison.lean` proves the rule at every
degree, [Stacks, Tag 0G86] is registered unconditionally and without a suffix on
`Stacks.Gysin.existsUnique_gysinHom_of_conormalRank`, and the hypothesis has been removed from
`chartGysinChartData`, `gysinHom_comm_deRham_chartGysinChartData` and
`exists_gysinDeRhamData_of_clsCommutesWithDeRham` here.  `Stacks.Gysin.ClsCommutesWithDeRham` is
the only statement left between this file and an unsuffixed 0G87.

**`ClsCommutesWithDeRham` is now split in two, and the split is proved.**
`Stacks.Gysin.clsCommutesWithDeRham_of_excision_of_chartFraction` of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinDeRhamClsReduction.lean` derives
`ClsCommutesWithDeRham` at the chart data of [Stacks, Tag 0G86] from exactly two hypotheses and
nothing else: the excision half `Stacks.Gysin.SupportCohomologyRestrictAbNatural` of each chart,
at the relative de Rham differential of `X/S` read as a morphism of the underlying abelian
sheaves, and the class-map half `Stacks.Gysin.ChartFractionCommutesWithDeRham` of each chart —
the same naturality for `Stacks.Perfect.SupportedFraction.supportedFractionSource` alone, on the
chart, with no excision in it.  That reduction is what makes the two paragraphs below meet: before
it, `SupportCohomologyRestrictAbNatural` had no consumer and this file did not even import
`GysinTargetExcisionAbelian.lean`, so granting it left `ClsCommutesWithDeRham` no closer.

**What `ClsCommutesWithDeRham` needs.**  It needs the derived excision
`Stacks.Gysin.supportCohomologyRestrictIso`, along the leg `W.ι` which *is* available, read
through the forgetful functor to abelian sheaves — which is
`Stacks.Gysin.SupportCohomologyRestrictAbNatural` of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinTargetExcisionAbelian.lean`, proved there for an
`𝒪_X`-linear morphism of coefficient modules.  For an arbitrary morphism of the underlying
abelian sheaves it is down to the single equation
`Stacks.Gysin.ExcisionAbComparisonEqAbelianExcision` of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinAbelianExcisionBridge.lean`, by
`Stacks.Gysin.supportCohomologyRestrictAbNatural_of_excisionAbComparison_eq` there; that equation
is the derived-versus-classical comparison of the two excisions, and it is proved —
`Stacks.Gysin.excisionAbComparisonEqAbelianExcision` of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinExcisionAbelianAgreement.lean` — so the
arbitrary
case is `Stacks.Gysin.supportCohomologyRestrictAbNatural` there.  The naturality of the class map
of [Stacks, Tag 0G7Q] in an arbitrary morphism of the
**underlying abelian sheaves** is not open: it is
`Stacks.Perfect.SupportedEndoForgetDegreewise.topCechClassAbelianNatural`, and with it the square
of [Stacks, Tag 0G85] for the Gysin formula, and hence [Stacks, Tag 0G85] itself, hold for an
arbitrary morphism `ψ` of the underlying abelian sheaves of two **quasi-coherent** coefficient
modules — unconditional in `ψ`, which is the half that matters here, but not unconditional.

**Why the arrow is built in the `supportCohomologySheaf` spelling.**
`Stacks.Gysin.gysinTarget` is the degree-`c` cohomology sheaf of `i_* R𝓗_Z(ℱ[0])`, i.e.
`Stacks.Perfect.SupportedFraction.supportCohomologySheafFunctor`, because that is the spelling in
which [Stacks, Tag 0G7Q] and [Stacks, Tag 0G7S] are stated and in which the derived excision of
[Stacks, Tag 0G78] is available.  The abelian action of [Stacks, Tag 0G74] part (2) is available in
exactly that spelling, as `supportCohomologySheafAbelianMap`, so no comparison of spellings occurs
here; `AlgebraicGeometry.Scheme.Hom.gysinTargetDeRhamMap` is the same construction in the
`AlgebraicGeometry.Scheme.Hom.pushforwardLocalCohomology` spelling of the *chart* Gysin map of
[Stacks, Tag 0G83], which is not the target of the glued map.

**Why a degree transport appears.**  The Gysin map of degree `p` lands in `Ω^{p+c}_{X/S}`, so its
differential lands in degree `p + c + 1`, whereas the Gysin map of degree `p + 1` lands in
`Ω^{p+1+c}_{X/S}`.  For variable `p` and `c` those two natural numbers are equal but not
definitionally so, and the transport is
`AlgebraicGeometry.Scheme.Hom.deRhamReindexPresheafHom`, exactly the one
`Stacks.Gysin.ambientDeRhamShift` carries on sections.

**Why one family of charts serves both degrees.**  `Stacks.Gysin.GysinChartData` is indexed by the
exterior degree and carries its own chart index type, so two chart data for the same `i` need not
have the same charts — which is why `Stacks.Gysin.GysinDeRhamData` has the fields `chart`,
`chart_ambient` and `chart_equations` at all.  But the equation charts of
`Stacks.Gysin.exists_gysinCharts` are produced from the conormal sheaf alone and do not mention
the degree, so the two chart data below are built from one family and the matching is the
identity.

**Why the arrow on the targets is transported rather than used directly.**
`Stacks.Gysin.GysinChartData.target` is a field, so for the chart data built by
`Stacks.Gysin.gysinChartDataOfClsDet` it is the Gysin target only after that construction is
unfolded.  Both spellings denote the same sheaf and `chartGysinChartData_target` is `rfl`, but
unfolding `Stacks.Gysin.gysinTarget` to a constructor means unfolding the derived-category
machinery it is built from, which is why every statement below is phrased at `D.target` and the
arrow is carried once, through `Stacks.Gysin.gysinTargetDeRhamHomOfEq`, by an equality of objects
of `X.Modules`.  For the same reason the matching of the charts is the named
`Stacks.Gysin.chartGysinMatch` rather than an anonymous `fun a => a`.

## References

* [Stacks Project, Tag 0G87](https://stacks.math.columbia.edu/tag/0G87)
* [Stacks Project, Tag 0G86](https://stacks.math.columbia.edu/tag/0G86)
* [Stacks Project, Tag 0G85](https://stacks.math.columbia.edu/tag/0G85)
* [Stacks Project, Tag 0G7U](https://stacks.math.columbia.edu/tag/0G7U)
* [Stacks Project, Tag 0G7S](https://stacks.math.columbia.edu/tag/0G7S)
* [Stacks Project, Tag 0G7Q](https://stacks.math.columbia.edu/tag/0G7Q)
* [Stacks Project, Tag 0G74](https://stacks.math.columbia.edu/tag/0G74)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom
open Stacks.AlgebraicGeometry.ConormalEquations
open Stacks.AlgebraicGeometry.RegularIdealSheaf
open Stacks.Perfect.AbelianFraction (abelianSheaf abHom sectionsHom sectionsHom_naturality)
open Stacks.Perfect.GysinAbelianSquare (supportCohomologySheafAbelianMap)
open Stacks.Perfect.SupportedFraction (supportCohomologySheafMap)
open Stacks.RingedSpace

universe u

namespace Stacks.Gysin

variable {Z X S : Scheme.{u}}

/-! ### Sections of a morphism of the underlying abelian sheaves -/

/-- **The action on sections of a morphism of the underlying abelian sheaves of two
`𝒪_X`-modules**, as an additive map.  It is *not* assumed to commute with the `𝒪_X`-action, which
is the whole point: the de Rham differential does not.  This is
`Stacks.Perfect.AbelianFraction.sectionsHom` read on a morphism of abelian *sheaves* rather than of
abelian presheaves, which is the form the constructions of [Stacks, Tag 0G74] part (2) produce.

It is stated for arbitrary `F` and `G` so that the two lemmas below can be applied to the Gysin
target without the elaborator having to recover `F` and `G` from the type of a morphism between
two large objects. -/
def abSectionsHom {F G : X.Modules} (ψ : (abelianSheaf X).obj F ⟶ (abelianSheaf X).obj G)
    (V : X.Opens) : Γ(F, V) →+ Γ(G, V) :=
  sectionsHom ψ.hom V

/-- A morphism of abelian sheaves commutes with restriction, so its action on sections does. -/
theorem abSectionsHom_res {F G : X.Modules}
    (ψ : (abelianSheaf X).obj F ⟶ (abelianSheaf X).obj G)
    {V V₀ : X.Opens} (hV₀ : V₀ ≤ V) (y : Γ(F, V)) :
    abSectionsHom ψ V₀ (F.presheaf.map (homOfLE hV₀).op y)
      = G.presheaf.map (homOfLE hV₀).op (abSectionsHom ψ V y) :=
  sectionsHom_naturality ψ.hom (homOfLE hV₀) y

/-- **A morphism of the underlying abelian sheaves is determined by its action on sections.**  Two
morphisms `(abelianSheaf X).obj ℱ ⟶ (abelianSheaf X).obj 𝒢` agreeing on the sections over every
open of `X` are equal: the category of abelian sheaves is a full subcategory of the presheaves,
so a morphism is its underlying natural transformation, and a natural transformation of
presheaves of abelian groups is determined by its components on elements.

This is what turns a square stated on sections — the shape the squares of [Stacks, Tag 0G85] and
[Stacks, Tag 0G87] take, the vertical arrows being only additive — into an equality of morphisms,
which is the shape the cohomological constructions consume. -/
theorem abSectionsHom_ext {F G : X.Modules}
    {α β : (abelianSheaf X).obj F ⟶ (abelianSheaf X).obj G}
    (h : ∀ (V : X.Opens) (y : Γ(F, V)), abSectionsHom α V y = abSectionsHom β V y) :
    α = β :=
  Sheaf.hom_ext (NatTrans.ext (funext fun V =>
    AddCommGrpCat.hom_ext (AddMonoidHom.ext (h V.unop))))

/-! ### The de Rham differential of the ambient scheme, as a morphism of abelian sheaves -/

/-- **The relative de Rham differential of `X/S` in the degree the degree-`p` Gysin map lands in,
carried into the degree the degree-`p + 1` Gysin map lands in, as a morphism of the underlying
abelian sheaves on `X`.**

The differential obeys `d(g ω) = d g ∧ ω + g · d ω`, so it is only `π⁻¹𝒪_S`-linear and is a
morphism of `X.Modules` for no scheme `X`; `AlgebraicGeometry.Scheme.Hom.deRhamDifferentialAbHom`
is the passage to the underlying abelian sheaves, which is what lets the local cohomology sheaf act
on it.  The second factor is the degree bookkeeping `p + c + 1 = p + 1 + c`. -/
def ambientDeRhamShiftAbHom (π : X ⟶ S) (c p : ℕ) :
    (abelianSheaf X).obj (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))) ⟶
      (abelianSheaf X).obj (relativeDifferentialForms π (((p + 1 : ℕ) : ℤ) + (c : ℤ))) :=
  deRhamDifferentialAbHom π (p + c) ≫
    abHom (deRhamReindexPresheafHom π (show p + c + 1 = p + 1 + c by omega))

/-- **The morphism of abelian sheaves fed to [Stacks, Tag 0G74] part (2) is the differential the
square of [Stacks, Tag 0G87] is about:** on sections it is `Stacks.Gysin.ambientDeRhamShift`, the
relative de Rham differential of `X/S` with the degree transport absorbed, which is what the field
`Stacks.Gysin.GysinDeRhamData.tgt_cls` speaks about. -/
theorem abSectionsHom_ambientDeRhamShiftAbHom (π : X ⟶ S) (c p : ℕ) (V : X.Opens)
    (y : Γ(relativeDifferentialForms π ((p : ℤ) + (c : ℤ)), V)) :
    abSectionsHom (ambientDeRhamShiftAbHom π c p) V y = ambientDeRhamShift π c p V y := rfl

/-! ### The right vertical arrow of the square, at the concrete target -/

/-- **The right vertical arrow of the square of [Stacks, Tag 0G87]**: the action of `i_*ℋ ᶜ_Z` on
the relative de Rham differential of `X/S`, at the concrete target `Stacks.Gysin.gysinTarget` of
the glued Gysin map of [Stacks, Tag 0G86].

It is `Stacks.Perfect.GysinAbelianSquare.supportCohomologySheafAbelianMap`, which is
[Stacks, Tag 0G74] part (2) at the Gysin map's target conjugating the abelian local cohomology
functor, applied to `Stacks.Gysin.ambientDeRhamShiftAbHom`.  No hypothesis beyond the closedness of
the image of `i`, which `Stacks.Gysin.isClosed_range_base` supplies; in particular no
quasi-coherence. -/
def gysinTargetDeRhamHom (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) (c p : ℕ) :
    (abelianSheaf X).obj (gysinTarget i π c p) ⟶
      (abelianSheaf X).obj (gysinTarget i π c (p + 1)) :=
  supportCohomologySheafAbelianMap (isClosed_range_base i) c (ambientDeRhamShiftAbHom π c p)

/-- **The abelian action of `i_*ℋ ᶜ_Z` at the concrete target extends the `𝒪_X`-linear one:** on
the underlying morphism of abelian sheaves of a morphism of `X.Modules` it is the underlying
morphism of the functorial action.  It says nothing about a differential, and is recorded to pin
down that `Stacks.Gysin.gysinTargetDeRhamHom` is the right notion rather than merely a map of the
right type. -/
theorem supportCohomologySheafAbelianMap_map_range (i : Z ⟶ X) [IsClosedImmersion i] (c : ℕ)
    {F G : X.Modules} (φ : F ⟶ G) :
    supportCohomologySheafAbelianMap (isClosed_range_base i) c ((abelianSheaf X).map φ) =
      (abelianSheaf X).map (supportCohomologySheafMap (isClosed_range_base i) φ (c : ℤ)) :=
  Stacks.Perfect.GysinAbelianSquare.supportCohomologySheafAbelianMap_map _ c φ

/-- **The right vertical arrow of the square of [Stacks, Tag 0G87], on sections.**  The two
vertical arrows of the square are only additive, the de Rham differential being only
`π⁻¹𝒪_S`-linear, so this is the shape the field `Stacks.Gysin.GysinDeRhamData.tgt` takes. -/
def gysinTargetDeRhamSections (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) (c p : ℕ)
    (V : X.Opens) : Γ(gysinTarget i π c p, V) →+ Γ(gysinTarget i π c (p + 1), V) :=
  abSectionsHom (gysinTargetDeRhamHom i π c p) V

/-- The right vertical arrow commutes with restriction, being the action on sections of a morphism
of sheaves.  This is the field `Stacks.Gysin.GysinDeRhamData.tgt_res`. -/
theorem gysinTargetDeRhamSections_res (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) (c p : ℕ)
    {V V₀ : X.Opens} (hV₀ : V₀ ≤ V) (y : Γ(gysinTarget i π c p, V)) :
    gysinTargetDeRhamSections i π c p V₀
        ((gysinTarget i π c p).presheaf.map (homOfLE hV₀).op y)
      = (gysinTarget i π c (p + 1)).presheaf.map (homOfLE hV₀).op
          (gysinTargetDeRhamSections i π c p V y) :=
  abSectionsHom_res (gysinTargetDeRhamHom i π c p) hV₀ y

/-! ### The arrow carried to the target of an arbitrary chart data -/

/-- **The right vertical arrow of the square, carried to a chart data whose target is the Gysin
target.**  `Stacks.Gysin.GysinChartData.target` is a field, so for a chart data built by
`Stacks.Gysin.gysinChartDataOfClsDet` it is the Gysin target only up to unfolding the construction;
the two equalities `hT` and `hT'` are the unfoldings, and the arrow is transported along them.

The transport is taken on the objects of `X.Modules`, before the forgetful functor, so that the
type of the result mentions `D.target` and `D'.target` and nothing has to be identified with the
Gysin target again when the field `Stacks.Gysin.GysinDeRhamData.tgt` is read off it.  At the Gysin
target itself the transport is the identity, which is `gysinTargetDeRhamHomOfEq_rfl`. -/
def gysinTargetDeRhamHomOfEq {T T' : X.Modules} (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S)
    (c p : ℕ) (hT : T = gysinTarget i π c p) (hT' : T' = gysinTarget i π c (p + 1)) :
    (abelianSheaf X).obj T ⟶ (abelianSheaf X).obj T' :=
  (abelianSheaf X).map (eqToHom hT) ≫ gysinTargetDeRhamHom i π c p ≫
    (abelianSheaf X).map (eqToHom hT'.symm)

/-- At the Gysin target itself the carried arrow is the arrow of
`Stacks.Gysin.gysinTargetDeRhamHom`, so the transport adds nothing. -/
theorem gysinTargetDeRhamHomOfEq_rfl (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) (c p : ℕ) :
    gysinTargetDeRhamHomOfEq i π c p (rfl : gysinTarget i π c p = _) rfl =
      gysinTargetDeRhamHom i π c p := by
  simp only [gysinTargetDeRhamHomOfEq, eqToHom_refl, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id]

/-! ### The one statement that remains -/

/-- **Steps (i) and (ii) of the proof of [Stacks, Tag 0G85] in the chart-local spelling**: the
class map `c_{f₁, …, f_c}` of [Stacks, Tag 0G7Q] of an equation chart of a chart data is natural
along the relative de Rham differential of `X/S` **on the equation wedges**
`ω ∧ d f₁ ∧ ⋯ ∧ d f_c`, the local cohomology sheaf acting on the differential through
[Stacks, Tag 0G74] part (2).

**The wedge is not a convenience, it is the whole statement.**  At an arbitrary section `y` of
`Ω^{p+c}_{X/S}` the equation `ψ(c_{f₁,…,f_c}(y)) = c_{f₁,…,f_c}(d y)` is *false*, and false for
every `ψ`, so a field quantified over `y` would leave `Stacks.Gysin.GysinDeRhamData` uninhabited
at the chart data of [Stacks, Tag 0G86]; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinDeRhamCompat.lean`, which carry the
counterexample.  On a wedge the Leibniz correction that refutes it vanishes, because the
differentials of the equations already occur in the form — that is step (iii) of the source's
proof, `Stacks.Gysin.ambientDeRhamShift_gysinWedgeOn`.

For the chart data of [Stacks, Tag 0G86] the class maps are the chart class maps of
[Stacks, Tag 0G7Q] — `Stacks.Gysin.chartGysinChartData_cls` says so — and this is exactly the
chart-local form of the square of [Stacks, Tag 0G85] for the Gysin formula.  For a *global* family
of equations that square is proved, unconditionally, by
`Stacks.Perfect.SupportedEndoForgetDegreewise.gysinFormulaCommutesWithDeRham`, and
`AlgebraicGeometry.Scheme.Hom.gysinMapCommutesWithDeRham` is [Stacks, Tag 0G85] itself.  What
turns that into this is the passage from `W.toScheme` to `X` across the derived excision the chart
transport is built from. -/
def ClsCommutesWithDeRham {i : Z ⟶ X} {π : X ⟶ S} {c p : ℕ}
    (D : GysinChartData i π c p) (D' : GysinChartData i π c (p + 1))
    (ψ : (abelianSheaf X).obj D.target ⟶ (abelianSheaf X).obj D'.target)
    (chart : D.Chart → D'.Chart)
    (chart_ambient : ∀ a, D.ambient a ≤ D'.ambient (chart a)) : Prop :=
  ∀ (a : D.Chart) (V : X.Opens) (hV : V ≤ D.ambient a)
    (ω : Γ(relativeDifferentialForms π (p : ℤ), V)),
    abSectionsHom ψ V (D.cls a V hV (gysinWedgeOn π (D.equations a) (p : ℤ) hV ω))
      = D'.cls (chart a) V (hV.trans (chart_ambient a))
          (ambientDeRhamShift π c p V (gysinWedgeOn π (D.equations a) (p : ℤ) hV ω))

/-! ### Two fields of the input of Stacks 0G87, discharged -/

/-- **What a `Stacks.Gysin.GysinDeRhamData` amounts to**: an arrow on the two targets which is a
morphism of the **underlying abelian sheaves** — the de Rham differential being only
`π⁻¹𝒪_S`-linear, an `𝒪_X`-linear arrow would not do — a matching of the equation charts of the two
degrees, and the chart-local naturality of the class map of [Stacks, Tag 0G7Q] along the de Rham
differential.

The two fields `tgt` and `tgt_res` are **read off the arrow**: `tgt` is its action on sections and
`tgt_res` is that a morphism of sheaves commutes with restriction.  So the right vertical arrow of
the square of [Stacks, Tag 0G87] never has to be assumed where such an arrow is available, and
[Stacks, Tag 0G74] part (2) makes one available at the target of the Gysin map of
[Stacks, Tag 0G86]. -/
def gysinDeRhamDataOfAbHom {i : Z ⟶ X} {π : X ⟶ S} {c p : ℕ}
    (D : GysinChartData i π c p) (D' : GysinChartData i π c (p + 1))
    (ψ : (abelianSheaf X).obj D.target ⟶ (abelianSheaf X).obj D'.target)
    (chart : D.Chart → D'.Chart)
    (chart_ambient : ∀ a, D.ambient a ≤ D'.ambient (chart a))
    (chart_equations : ∀ (a : D.Chart) (j : Fin c),
      X.presheaf.map (homOfLE (chart_ambient a)).op (D'.equations (chart a) j) = D.equations a j)
    (tgt_cls : ClsCommutesWithDeRham D D' ψ chart chart_ambient) :
    GysinDeRhamData i π D D' where
  tgt V := abSectionsHom ψ V
  tgt_res _ _ hV₀ y := abSectionsHom_res ψ hV₀ y
  chart := chart
  chart_ambient := chart_ambient
  chart_equations := chart_equations
  tgt_cls := tgt_cls

/-! ### The input of Stacks 0G87 for the chart data of Stacks 0G86 -/

section Assemble

variable (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {d : ℕ} (p : ℕ) (Chart : Type u)
  (ambient : Chart → X.Opens) (equations : (a : Chart) → Fin (d + 1) → Γ(X, ambient a))
  (hvanish : ∀ (a : Chart) (V : X.Opens) (hV : V ≤ ambient a) (j : Fin (d + 1)),
    (i.app V).hom (X.presheaf.map (homOfLE hV).op (equations a j)) = 0)
  (hcover : ∀ x : X, ∃ a, x ∈ ambient a)
  (hgen : ∀ a, IsGeneratedByOn X.toRingedSpace (definingIdealOfHom i) (ambient a) (equations a))

/-- **The chart data of [Stacks, Tag 0G86] on a given family of equation charts**, which is
`Stacks.Gysin.gysinChartDataOfClsDet` with the determinant rule of [Stacks, Tag 0G7S] across two
charts supplied by the theorem `Stacks.Gysin.clsDetAcrossCharts`.  Named so that the two degrees'
data below are one construction at two degrees.

The rule used to be a hypothesis here, in the chart-free form
`Stacks.Gysin.ClsDetAcrossCharts`, because it was unproved; it is now a theorem at every degree
and nothing below assumes it. -/
def chartGysinChartData : GysinChartData i π (d + 1) p :=
  gysinChartDataOfClsDet i π p Chart ambient equations hvanish hcover hgen
    fun a b => clsDetAcrossCharts i π d p (ambient a) (ambient b) (equations a) (equations b)
      (hgen a) (hvanish a) (hgen b) (hvanish b)

/-- **Its target is the Gysin target** `Stacks.Gysin.gysinTarget`, on which
[Stacks, Tag 0G74] part (2) acts. -/
theorem chartGysinChartData_target :
    (chartGysinChartData i π p Chart ambient equations hvanish hcover hgen).target
      = gysinTarget i π (d + 1) p := rfl

/-- Its equation charts are the given ones. -/
theorem chartGysinChartData_ambient (a : Chart) :
    (chartGysinChartData i π p Chart ambient equations hvanish hcover hgen).ambient a
      = ambient a := rfl

/-- Its equations are the given ones. -/
theorem chartGysinChartData_equations (a : Chart) (j : Fin (d + 1)) :
    (chartGysinChartData i π p Chart ambient equations hvanish hcover hgen).equations a j
      = equations a j := rfl

/-- **Its class maps are the chart class maps of [Stacks, Tag 0G7Q]**,
`Stacks.Gysin.chartClsOfGen`.  This is what makes
`Stacks.Gysin.ClsCommutesWithDeRham` at this data the chart-local naturality of the class map of
[Stacks, Tag 0G7Q] along the de Rham differential, and nothing weaker. -/
theorem chartGysinChartData_cls (a : Chart) (V : X.Opens) (hV : V ≤ ambient a) :
    (chartGysinChartData i π p Chart ambient equations hvanish hcover hgen).cls a V hV
      = chartClsOfGen i π p (ambient a) (equations a) (hgen a) (hvanish a) V hV := rfl

/-- **The right vertical arrow of the square at the chart data of a family of equation charts.**
It is `Stacks.Gysin.gysinTargetDeRhamHom` — [Stacks, Tag 0G74] part (2) applied to the de Rham
differential of `X/S` — carried along the two unfoldings of `chartGysinChartData_target`, which
are `rfl`. -/
def chartGysinTargetDeRhamHom :
    (abelianSheaf X).obj
        (chartGysinChartData i π p Chart ambient equations hvanish hcover hgen).target ⟶
      (abelianSheaf X).obj
        (chartGysinChartData i π (p + 1) Chart ambient equations hvanish hcover hgen).target :=
  gysinTargetDeRhamHomOfEq i π (d + 1) p rfl rfl

/-- **The matching of the equation charts of the two degrees' chart data**: they are the *same*
charts, so the matching is the identity.  `Stacks.Gysin.exists_gysinCharts` produces the equation
charts from the conormal sheaf alone and does not mention the exterior degree, which is what lets
one family serve both degrees. -/
def chartGysinMatch :
    (chartGysinChartData i π p Chart ambient equations hvanish hcover hgen).Chart →
      (chartGysinChartData i π (p + 1) Chart ambient equations hvanish hcover hgen).Chart :=
  fun a => a

/-- The open of a matched chart is the open of the chart it comes from, so the inclusion asked for
by the field `Stacks.Gysin.GysinDeRhamData.chart_ambient` is reflexivity. -/
theorem chartGysinMatch_ambient :
    ∀ a, (chartGysinChartData i π p Chart ambient equations hvanish hcover hgen).ambient a ≤
      (chartGysinChartData i π (p + 1) Chart ambient equations hvanish hcover hgen).ambient
        (chartGysinMatch i π p Chart ambient equations hvanish hcover hgen a) :=
  fun a => le_refl (ambient a)

/-- **The input of [Stacks, Tag 0G87] for the chart data of [Stacks, Tag 0G86], with `tgt`,
`tgt_res`, `chart`, `chart_ambient` and `chart_equations` derived and only `tgt_cls` assumed.**

The two chart data are `Stacks.Gysin.chartGysinChartData` in the degrees `p` and `p + 1`, built
from **one** family of equation charts, so the matching of the charts is
`Stacks.Gysin.chartGysinMatch` with `Stacks.Gysin.chartGysinMatch_ambient`, and the matching of
the equations is `AlgebraicGeometry.Scheme.Hom.presheaf_map_le_refl` — the equations are the
same equations
and the comparison is restriction along the identity inclusion.  The right vertical arrow is
[Stacks, Tag 0G74] part (2) at the Gysin target, carried to this data by
`Stacks.Gysin.chartGysinTargetDeRhamHom`, and `tgt_res` is its compatibility with restriction.

The one remaining hypothesis is `Stacks.Gysin.ClsCommutesWithDeRham`, which is the field `tgt_cls`
itself: steps (i) and (ii) of the proof of [Stacks, Tag 0G85] in the chart-local spelling. -/
def gysinDeRhamDataOfClsDet
    (hcls : ClsCommutesWithDeRham
      (chartGysinChartData i π p Chart ambient equations hvanish hcover hgen)
      (chartGysinChartData i π (p + 1) Chart ambient equations hvanish hcover hgen)
      (chartGysinTargetDeRhamHom i π p Chart ambient equations hvanish hcover hgen)
      (chartGysinMatch i π p Chart ambient equations hvanish hcover hgen)
      (chartGysinMatch_ambient i π p Chart ambient equations hvanish hcover hgen)) :
    GysinDeRhamData i π
      (chartGysinChartData i π p Chart ambient equations hvanish hcover hgen)
      (chartGysinChartData i π (p + 1) Chart ambient equations hvanish hcover hgen) :=
  gysinDeRhamDataOfAbHom
    (chartGysinChartData i π p Chart ambient equations hvanish hcover hgen)
    (chartGysinChartData i π (p + 1) Chart ambient equations hvanish hcover hgen)
    (chartGysinTargetDeRhamHom i π p Chart ambient equations hvanish hcover hgen)
    (chartGysinMatch i π p Chart ambient equations hvanish hcover hgen)
    (chartGysinMatch_ambient i π p Chart ambient equations hvanish hcover hgen)
    (fun a j => AlgebraicGeometry.Scheme.Hom.presheaf_map_le_refl (ambient a) (equations a j)) hcls

/-- **The square of [Stacks, Tag 0G87] for the glued Gysin map of [Stacks, Tag 0G86], with its
right vertical arrow constructed rather than assumed.**  The horizontal arrows are the glued Gysin
maps of the chart data of the two degrees, the left vertical arrow is the relative de Rham
differential of `Z/S` (`Stacks.Gysin.pushforwardDeRham`) and the right vertical arrow is the
action of `i_*ℋ ᶜ_Z` on the relative de Rham differential of `X/S` supplied by
[Stacks, Tag 0G74] part (2).

This is `Stacks.Gysin.GysinDeRhamData.gysinHom_comm_deRham` — the reduction of the square to a
chart, which is proved — at the data assembled by `Stacks.Gysin.gysinDeRhamDataOfClsDet`.  Its
one hypothesis is `Stacks.Gysin.ClsCommutesWithDeRham`.  It also carried
`Stacks.Gysin.ClsDetAcrossCharts` in the two degrees for as long as that was unproved; the
theorem `Stacks.Gysin.clsDetAcrossCharts` discharges it, so the statement here is the square
under no hypothesis of [Stacks, Tag 0G86]'s own beyond the tag's. -/
theorem gysinHom_comm_deRham_chartGysinChartData
    (hcls : ClsCommutesWithDeRham
      (chartGysinChartData i π p Chart ambient equations hvanish hcover hgen)
      (chartGysinChartData i π (p + 1) Chart ambient equations hvanish hcover hgen)
      (chartGysinTargetDeRhamHom i π p Chart ambient equations hvanish hcover hgen)
      (chartGysinMatch i π p Chart ambient equations hvanish hcover hgen)
      (chartGysinMatch_ambient i π p Chart ambient equations hvanish hcover hgen))
    (V : X.Opens) (x : Γ(pushforwardRelativeForms i π (p : ℤ), V)) :
    abSectionsHom
        (chartGysinTargetDeRhamHom i π p Chart ambient equations hvanish hcover hgen)
        V ((chartGysinChartData i π p Chart ambient equations hvanish hcover
          hgen).gysinHom.app V x)
      = (chartGysinChartData i π (p + 1) Chart ambient equations hvanish hcover
          hgen).gysinHom.app V (pushforwardDeRham i π p V x) :=
  (gysinDeRhamDataOfClsDet i π p Chart ambient equations hvanish hcover hgen
    hcls).gysinHom_comm_deRham V x

end Assemble

/-- **From the hypotheses of [Stacks, Tag 0G86], the input of [Stacks, Tag 0G87] is one statement
away.**  For a closed immersion of finite presentation whose conormal sheaf is locally free of
rank `d + 1` — and under no further hypothesis, the determinant rule of [Stacks, Tag 0G7S] across
two charts being the theorem `Stacks.Gysin.clsDetAcrossCharts` rather than, as it once was here,
an assumption in each of the two degrees — there are chart data of the degrees `p` and `p + 1`
whose targets are the Gysin target
`Stacks.Gysin.gysinTarget`, an arrow on those targets and a matching of their equation charts, for
which the **only** remaining ingredient of `Stacks.Gysin.GysinDeRhamData` is
`Stacks.Gysin.ClsCommutesWithDeRham`: the right vertical arrow of the square and its compatibility
with restriction are derived from [Stacks, Tag 0G74] part (2) by
`Stacks.Gysin.gysinDeRhamDataOfAbHom`, and the matching of the two degrees' charts is the
identity.

The equation charts come from `Stacks.Gysin.exists_gysinCharts`, which produces them from the
conormal sheaf alone and so produces one family for both degrees. -/
theorem exists_gysinDeRhamData_of_clsCommutesWithDeRham (i : Z ⟶ X) [IsClosedImmersion i]
    [LocallyOfFinitePresentation i] (π : X ⟶ S) {d : ℕ} (p : ℕ)
    (hE : ConormalRank i (d + 1)) :
    ∃ (D : GysinChartData i π (d + 1) p) (D' : GysinChartData i π (d + 1) (p + 1))
        (_ : D.target = gysinTarget i π (d + 1) p)
        (_ : D'.target = gysinTarget i π (d + 1) (p + 1))
        (ψ : (abelianSheaf X).obj D.target ⟶ (abelianSheaf X).obj D'.target)
        (chart : D.Chart → D'.Chart)
        (chart_ambient : ∀ a, D.ambient a ≤ D'.ambient (chart a)),
      ClsCommutesWithDeRham D D' ψ chart chart_ambient →
        Nonempty (GysinDeRhamData i π D D') := by
  obtain ⟨ambient, equations, hvanish, hcover, _, hgen, _⟩ :=
    exists_gysinCharts i (d + 1) hE (Nat.succ_ne_zero d)
  exact ⟨chartGysinChartData i π p ↥X ambient equations hvanish hcover hgen,
    chartGysinChartData i π (p + 1) ↥X ambient equations hvanish hcover hgen, rfl, rfl,
    chartGysinTargetDeRhamHom i π p ↥X ambient equations hvanish hcover hgen,
    chartGysinMatch i π p ↥X ambient equations hvanish hcover hgen,
    chartGysinMatch_ambient i π p ↥X ambient equations hvanish hcover hgen,
    fun hcls => ⟨gysinDeRhamDataOfClsDet i π p ↥X ambient equations hvanish hcover hgen hcls⟩⟩

end Stacks.Gysin

end
