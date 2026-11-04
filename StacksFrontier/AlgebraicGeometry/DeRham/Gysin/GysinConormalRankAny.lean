module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.ChartDataComparison
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinChartClsAnyCount
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinConormalRankZero
public import StacksFrontier.AlgebraicGeometry.Modules.PushforwardDisjointRange

/-!
# [Stacks, Tag 0G86] for an arbitrary conormal rank

[Stacks, Tag 0G86] produces the Gysin map `γ^p` of a closed immersion of finite presentation
whose conormal sheaf is locally free of rank `c`, and [Stacks, Tag 0G8A] says `c ≥ 0`: the rank
is an unqualified natural number.  The chart route of
`Stacks.Gysin.ChartDataComparison` proves the tag for `c = d + 1`, because
`Stacks.Gysin.exists_gysinCharts` needs an index of `Fin c` at which to put the unit ideal away
from the closed subscheme and an empty family has none.  This file removes that restriction.

## What is different at `c = 0`, and what is not

At rank `0` an equation chart carries the **empty** family, which generates the ideal of `Z` over
an open exactly when that ideal vanishes there; so a chart is contained in `Set.range i.base`,
and the charts cover the image rather than the whole of `X` —
`range_subset_iSup_equationChart_ambient`.  The field
`Stacks.Gysin.GysinChartData.ambient_cover` is therefore not available and no `GysinChartData`
exists; the record is left untouched and the gluing is run directly, on the chart family
**augmented by the complement of the image**, where the local map is `0`.

That augmentation costs nothing because the source of the Gysin map is a direct image along `i`:
over an open missing `Set.range i.base` it has only the zero section, by
`AlgebraicGeometry.Scheme.Modules.subsingleton_pushforward_sections_of_disjoint_range`.  The same
observation makes the characterisation by charts determine the map **uniquely** at every rank,
including `0`, which is why the statement of the tag needs no case distinction:
`hom_ext_of_app_eq_equationChart`.

The agreement of two charts, which at `c = d + 1` is `Stacks.Gysin.GysinChartData.locAgree` and
rests on the change-of-equations matrix of [Stacks, Tag 0G7S], is at `c = 0` the statement that
both charts restrict to *the* chart `V` with the empty family: the `0 × 0` change-of-equations
matrix has determinant `1`, and no `cls_vanish` input is needed because the correction term of
`Stacks.Gysin.ChartComparison.wedge_det` is a sum over `Fin 0`.  Concretely it is
`Stacks.Gysin.chartClsOfClassMap_homOfLE` together with
`Stacks.Gysin.chartLoc_subschemeFormPullbackOfClassMap`, both of which are already stated for an
arbitrary number of equations.

## Main results

* `Stacks.Gysin.range_subset_iSup_equationChart_ambient`: the equation charts cover the image of
  `i`, at every rank.
* `Stacks.Gysin.hom_ext_of_app_eq_equationChart`: two maps out of `i_*Ω^p_{Z/S}` agreeing on the
  sections over every open contained in an equation chart are equal, at every rank.
* `Stacks.Gysin.existsUnique_gysinHom_of_conormalRank_zero`: [Stacks, Tag 0G86] at `c = 0`.
* `Stacks.Gysin.existsUnique_gysinHom_of_conormalRank`: **[Stacks, Tag 0G86]** for an arbitrary
  `c : ℕ`.

## References

* [Stacks Project, Tag 0G86](https://stacks.math.columbia.edu/tag/0G86)
* [Stacks Project, Tag 0G8A](https://stacks.math.columbia.edu/tag/0G8A)
* [Stacks Project, Tag 0G7S](https://stacks.math.columbia.edu/tag/0G7S)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom
open Stacks.AlgebraicGeometry.ConormalEquations
open Stacks.AlgebraicGeometry.RegularIdealSheaf
open Stacks.Perfect.CechDerivedSupport
open Stacks.Perfect.FractionClass
open Stacks.Perfect.SupportedFraction
open Stacks.RingedSpace

universe u

namespace Stacks.Gysin

variable {Z X S : Scheme.{u}}

/-! ### The charts cover the image -/

/-- **The equation charts of a closed immersion of conormal rank `c` cover the image of `i`**, for
every `c`.

`Stacks.AlgebraicGeometry.ConormalEquations.exists_affineOpen_equations_of_conormalRank` carries
no hypothesis on `c`, and around every point of the image it produces an open together with `c`
functions generating the ideal of the closed subscheme there; that is an equation chart.

At `c = d + 1` the charts in fact cover the whole of `X` —
`Stacks.Gysin.iSup_equationChart_ambient` — because away from the closed subscheme the equations
may be taken to generate the unit ideal.  At `c = 0` they do not: an empty family generates the
ideal of `Z` over an open only where that ideal vanishes, which happens on no nonempty open
outside the image.  The image is all that is covered uniformly in `c`, and all that the gluing
of this file needs. -/
theorem range_subset_iSup_equationChart_ambient (i : Z ⟶ X) [IsClosedImmersion i]
    [LocallyOfFinitePresentation i] {c : ℕ} (hE : ConormalRank i c) :
    Set.range i.base ⊆ ((⨆ a : EquationChart i c, a.ambient : X.Opens) : Set X) := by
  rintro x ⟨z, rfl⟩
  obtain ⟨W, -, hzW, f, hmem, hgen, -⟩ := exists_affineOpen_equations_of_conormalRank i c hE z
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨⟨W, f, hgen, fun V hV j => ?_⟩, hzW⟩
  exact (mem_definingIdealOfHom_iff_app_eq_zero i V _).mp
    (restrict_mem _ (homOfLE hV) (hmem j))

/-- The complement of the image of a closed immersion, as an open of the ambient scheme. -/
def complRangeOpens (i : Z ⟶ X) [IsClosedImmersion i] : X.Opens :=
  ⟨(Set.range i.base)ᶜ, (isClosed_range_base i).isOpen_compl⟩

/-- An open contained in the complement of the image misses the image. -/
theorem disjoint_of_le_complRangeOpens (i : Z ⟶ X) [IsClosedImmersion i] {V : X.Opens}
    (hV : V ≤ complRangeOpens i) : (V : Set X) ∩ Set.range i.base = ∅ := by
  ext x
  exact ⟨fun hx => hV hx.1 hx.2, fun hx => hx.elim⟩

/-- **The source of the Gysin map has only the zero section over an open missing the image.**  It
is the direct image `i_*Ω^n_{Z/S}`, whose sections over such an open are its sections over the
empty open of `Z`. -/
theorem subsingleton_pushforwardRelativeForms_of_disjoint (i : Z ⟶ X) [IsClosedImmersion i]
    (π : X ⟶ S) (n : ℤ) (V : X.Opens) (hV : (V : Set X) ∩ Set.range i.base = ∅) :
    Subsingleton Γ(pushforwardRelativeForms i π n, V) :=
  Scheme.Modules.subsingleton_pushforward_sections_of_disjoint_range i _ V hV

/-- A section of the source of the Gysin map over an open inside the complement of the image
is zero. -/
private theorem pushforwardRelativeForms_eq_zero_of_le_complRangeOpens (i : Z ⟶ X)
    [IsClosedImmersion i] (π : X ⟶ S) (n : ℤ) {V : X.Opens} (hV : V ≤ complRangeOpens i)
    (x : Γ(pushforwardRelativeForms i π n, V)) : x = 0 :=
  have := subsingleton_pushforwardRelativeForms_of_disjoint i π n V
    (disjoint_of_le_complRangeOpens i hV)
  Subsingleton.elim _ _

/-- **The equation charts together with the complement of the image cover the ambient scheme**,
at every rank.  This is the covering the gluing of [Stacks, Tag 0G86] is run on when the charts
alone do not cover `X`. -/
theorem equationChart_option_cover (i : Z ⟶ X) [IsClosedImmersion i]
    [LocallyOfFinitePresentation i] {c : ℕ} (hE : ConormalRank i c) (x : X) :
    ∃ a : Option (EquationChart i c),
      x ∈ (fun b => Option.elim b (complRangeOpens i) (fun a => a.ambient)) a := by
  by_cases hx : x ∈ Set.range i.base
  · obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1
      (range_subset_iSup_equationChart_ambient i hE hx)
    exact ⟨some a, ha⟩
  · exact ⟨none, hx⟩

/-! ### Uniqueness, at every rank -/

/-- **Two maps out of `i_*Ω^p_{Z/S}` that agree on the sections over every open contained in an
equation chart are equal**, at every conormal rank.

The charts cover the image by `range_subset_iSup_equationChart_ambient`, and over an open missing
the image the source has only the zero section by
`subsingleton_pushforwardRelativeForms_of_disjoint`, where therefore *every* pair of maps agrees.
So the two maps agree over every open of the covering of `equationChart_option_cover`, and
`Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_app_eq_of_cover` concludes.

This is the uniqueness clause of [Stacks, Tag 0G86], and it is what makes the tag's
characterisation of `γ^p` by the equation charts determine the map even at `c = 0`, where the
charts do not cover `X`. -/
theorem hom_ext_of_app_eq_equationChart (i : Z ⟶ X) [IsClosedImmersion i]
    [LocallyOfFinitePresentation i] (π : X ⟶ S) {c : ℕ} {n : ℤ} {N : X.Modules}
    (hE : ConormalRank i c) {φ ψ : pushforwardRelativeForms i π n ⟶ N}
    (h : ∀ (a : EquationChart i c) (V : X.Opens), V ≤ a.ambient → φ.app V = ψ.app V) :
    φ = ψ := by
  refine Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_app_eq_of_cover
    (fun b : Option (EquationChart i c) =>
      Option.elim b (complRangeOpens i) (fun a => a.ambient))
    (equationChart_option_cover i hE) fun b V hV => ?_
  match b with
  | some a => exact h a V hV
  | none =>
      ext m
      rw [pushforwardRelativeForms_eq_zero_of_le_complRangeOpens i π n hV m, map_zero, map_zero]

/-! ### The agreement of two charts at an empty family of equations -/

section Zero

variable (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) (p : ℕ)

omit [IsClosedImmersion i] in
/-- The equations of a chart cut out the closed subscheme over the chart. -/
theorem isCutOutByEquationsOn_equationChart {c : ℕ} (a : EquationChart i c) :
    IsCutOutByEquationsOn i a.ambient a.equations :=
  isCutOutByEquationsOn_of_isGeneratedByOn i a.gen a.vanish

/-- The common zero locus of a chart's equations is the part of the closed subscheme lying over
the chart. -/
theorem equationsClosedSet_equationChart {c : ℕ} (a : EquationChart i c) :
    equationsClosedSet (restrictEquations a.ambient a.equations) =
      a.ambient.ι ⁻¹' Set.range i.base :=
  equationsClosedSet_restrictEquations i a.ambient (isCutOutByEquationsOn_equationChart i a)

/-- **The class map of [Stacks, Tag 0G7Q] at an empty family of equations does not depend on the
family.**  There is only one function out of `Fin 0`, and the two remaining arguments are proofs
of the same proposition once the families are identified.

This is the whole content of the `cls_det` field of `Stacks.Gysin.ChartComparison` at `c = 0`:
the change-of-equations matrix is the `0 × 0` matrix, whose determinant is `1`, so the two class
maps are not merely proportional but equal. -/
theorem chartClsOfClassMap_zero_congr_apply (V : X.Opens) (f g : Fin 0 → Γ(V.toScheme, ⊤))
    (hT : IsClosed (V.ι ⁻¹' Set.range i.base))
    (hTf : equationsClosedSet f ⊆ V.ι ⁻¹' Set.range i.base)
    (hTg : equationsClosedSet g ⊆ V.ι ⁻¹' Set.range i.base)
    (y : Γ(relativeDifferentialForms π ((p : ℤ) + ((0 : ℕ) : ℤ)), V)) :
    chartClsOfClassMap i π p V f hT hTf V le_rfl y =
      chartClsOfClassMap i π p V g hT hTg V le_rfl y := by
  obtain rfl : f = g := funext fun j => j.elim0
  rfl

/-- **At an empty family of equations the local Gysin maps of two charts agree over an affine open
contained in both.**

This is `Stacks.Gysin.GysinChartData.locAgreeOn` at `c = 0`, with the two inputs that
`Stacks.Gysin.ChartComparison` carries discharged outright rather than assumed:

* the correction term of `wedge_det` is a sum over `Fin 0`, so no `cls_vanish` is needed; and
* the change-of-equations matrix is the `0 × 0` matrix, whose determinant is `1`, so `cls_det` is
  the plain locality `Stacks.Gysin.chartClsOfClassMap_homOfLE` of the class map of
  [Stacks, Tag 0G7Q].

The form on the closed subscheme is lifted to an ambient form by
`Stacks.Gysin.exists_subschemeFormPullback_of_isAffineOpen`, which is why the open is taken
affine; `Stacks.Gysin.chartLoc_subschemeFormPullbackOfClassMap` then evaluates both local Gysin
maps as class maps of the chart applied to the equation wedge, and at an empty family that wedge
is the unit of `Ω^•_{X/S}` by `Stacks.Gysin.prodDegOne_zero` — the same element for both charts.
Both class maps are then moved down to the chart `V` itself, where the two empty families are the
same function out of `Fin 0`. -/
theorem chartLoc_agree_zero_of_isAffineOpen (a b : EquationChart i 0) (V : X.Opens)
    (hVaff : IsAffineOpen V) (ha : V ≤ a.ambient) (hb : V ≤ b.ambient)
    (x : Γ(pushforwardRelativeForms i π (p : ℤ), V)) :
    chartLoc i π p a.ambient a.equations (isCutOutByEquationsOn_equationChart i a)
        (equationsClosedSet_equationChart i a) V ha x =
      chartLoc i π p b.ambient b.equations (isCutOutByEquationsOn_equationChart i b)
        (equationsClosedSet_equationChart i b) V hb x := by
  obtain ⟨ω, hω⟩ := exists_subschemeFormPullback_of_isAffineOpen i π p V hVaff x
  subst hω
  have key : ∀ (a : EquationChart i 0) (ha : V ≤ a.ambient),
      ∃ (f : Fin 0 → Γ(V.toScheme, ⊤)) (hT : IsClosed (V.ι ⁻¹' Set.range i.base))
        (hTf : equationsClosedSet f ⊆ V.ι ⁻¹' Set.range i.base),
        chartLoc i π p a.ambient a.equations (isCutOutByEquationsOn_equationChart i a)
            (equationsClosedSet_equationChart i a) V ha (subschemeFormPullback i π (p : ℤ) V ω) =
          chartClsOfClassMap i π p V f hT hTf V le_rfl
            (gysinWedgeOn π a.equations (p : ℤ) ha ω) := by
    intro a ha
    rw [chartLoc_subschemeFormPullbackOfClassMap i π p a.ambient a.equations
        (isCutOutByEquationsOn_equationChart i a) (isClosed_preimage_range_base i a.ambient)
        (equationsClosedSet_equationChart i a)
        (fun {_ _} φ => fracTermTop_naturality_zero (restrictEquations a.ambient a.equations) φ)
        V ha ω,
      chartClsOfClassMap_homOfLE i π p ha a.equations
        (isClosed_preimage_range_base i a.ambient) (equationsClosedSet_equationChart i a).le
        (isClosed_preimage_range_base i V)
        (equationsClosedSet_restrictEquations i V (isCutOutByEquationsOn_restrict ha
          (isCutOutByEquationsOn_equationChart i a))).le
        (fun M => map_fracTermTop_comp_restrictCplxIso_zero (X.homOfLE ha)
          (restrictEquations a.ambient a.equations) M)
        (fun {_ _} φ => fracTermTop_naturality_zero
          (fun j => (X.homOfLE ha).appTop (restrictEquations a.ambient a.equations j)) φ)]
    exact ⟨_, _, _, rfl⟩
  obtain ⟨f, hT, hTf, hf⟩ := key a ha
  obtain ⟨g, _, hTg, hg⟩ := key b hb
  rw [hf, hg]
  exact chartClsOfClassMap_zero_congr_apply i π p V f g hT hTf hTg _

/-- **At an empty family of equations the local Gysin maps of two charts agree over every open
contained in both.**  The previous result holds over the affine opens inside such an open, those
cover it because the affine opens are a basis, and the target is a sheaf. -/
theorem chartLoc_agree_zero (a b : EquationChart i 0) (V : X.Opens) (ha : V ≤ a.ambient)
    (hb : V ≤ b.ambient) (x : Γ(pushforwardRelativeForms i π (p : ℤ), V)) :
    chartLoc i π p a.ambient a.equations (isCutOutByEquationsOn_equationChart i a)
        (equationsClosedSet_equationChart i a) V ha x =
      chartLoc i π p b.ambient b.equations (isCutOutByEquationsOn_equationChart i b)
        (equationsClosedSet_equationChart i b) V hb x := by
  have hcov : V ≤ ⨆ W : {W : X.affineOpens // (W : X.Opens) ≤ V}, (W.1 : X.Opens) := by
    intro y hy
    obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWV⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hy V.2
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨W, hW⟩, hWV⟩, hyW⟩
  refine TopCat.Sheaf.eq_of_locally_eq'
    (F := (⟨(gysinTarget i π 0 p).presheaf, (gysinTarget i π 0 p).isSheaf⟩ :
      TopCat.Sheaf Ab.{u} X))
    (fun W : {W : X.affineOpens // (W : X.Opens) ≤ V} => (W.1 : X.Opens))
    V (fun W => homOfLE W.2) hcov _ _ fun W => ?_
  rw [← chartLoc_res i π p _ _ _ _ V (W.1 : X.Opens) W.2 ha x,
    ← chartLoc_res i π p _ _ _ _ V (W.1 : X.Opens) W.2 hb x]
  exact chartLoc_agree_zero_of_isAffineOpen i π p a b (W.1 : X.Opens) W.1.2
    (W.2.trans ha) (W.2.trans hb) _

end Zero

/-- The local Gysin map of a chart kills the zero section, being additive. -/
theorem chartLoc_zero (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {c : ℕ} (p : ℕ)
    (W : X.Opens) (f : Fin c → Γ(X, W)) (hcut : IsCutOutByEquationsOn i W f)
    (hgT : equationsClosedSet (restrictEquations W f) = W.ι ⁻¹' Set.range i.base)
    (V : X.Opens) (hV : V ≤ W) :
    chartLoc i π p W f hcut hgT V hV 0 = 0 := by
  have h := chartLoc_add i π p W f hcut hgT V hV 0 0
  rw [add_zero] at h
  exact add_eq_left.mp h.symm

/-! ### [Stacks, Tag 0G86] at conormal rank zero -/

/-- **[Stacks, Tag 0G86] at conormal rank `0`.**  There is exactly one map
`γ^p : i_*Ω^p_{Z/S} ⟶ i_*ℋ^0_Z(Ω^p_{X/S})` which over every open contained in an open where the
**empty** family cuts out `Z` is the Gysin map of [Stacks, Tag 0G83] of that empty family.

Neither half can be read off `Stacks.Gysin.GysinChartData`, whose `ambient_cover` field asks the
charts to cover `X`: at this rank a chart lies inside `Set.range i.base`, which need not be all
of `X`.  Both halves are instead run on the chart family **augmented by the complement of the
image** — `equationChart_option_cover` — with the local map there taken to be `0`.  Nothing has
to be checked on the complement: the source has only the zero section there, by
`subsingleton_pushforwardRelativeForms_of_disjoint`, so the agreement with a chart is
`chartLoc_zero` and uniqueness is `hom_ext_of_app_eq_equationChart`.

The agreement of two charts is `chartLoc_agree_zero`, which replaces the change-of-equations
matrix of [Stacks, Tag 0G7S] by the observation that at an empty family there is nothing to
change. -/
theorem existsUnique_gysinHom_of_conormalRank_zero (i : Z ⟶ X) [IsClosedImmersion i]
    [LocallyOfFinitePresentation i] (π : X ⟶ S) (p : ℕ) (hE : ConormalRank i 0) :
    ∃! φ : pushforwardRelativeForms i π (p : ℤ) ⟶ gysinTarget i π 0 p,
      ∀ (a : EquationChart i 0) (V : X.Opens) (hV : V ≤ a.ambient)
        (x : Γ(pushforwardRelativeForms i π (p : ℤ), V)),
        φ.app V x = chartLoc i π p a.ambient a.equations
          (isCutOutByEquationsOn_equationChart i a)
          (equationsClosedSet_equationChart i a) V hV x := by
  obtain ⟨φ, hφ⟩ := Stacks.AlgebraicGeometry.ModuleLimits.exists_hom_app_eq_of_cover
    (M := pushforwardRelativeForms i π (p : ℤ)) (N := gysinTarget i π 0 p)
    (fun b : Option (EquationChart i 0) =>
      Option.elim b (complRangeOpens i) fun a => a.ambient)
    (equationChart_option_cover i hE)
    (fun b => match b with
      | some a => fun U hU x => chartLoc i π p a.ambient a.equations
          (isCutOutByEquationsOn_equationChart i a)
          (equationsClosedSet_equationChart i a) U hU x
      | none => fun _ _ _ => 0)
    (fun b => match b with
      | some a => fun U hU x y => chartLoc_add i π p a.ambient a.equations _ _ U hU x y
      | none => fun _ _ _ _ => (add_zero 0).symm)
    (fun b => match b with
      | some a => fun U hU r x => chartLoc_smul i π p a.ambient a.equations _ _ U hU r x
      | none => fun _ _ r _ => (smul_zero r).symm)
    (fun b => match b with
      | some a => fun U V hUV hV x =>
          chartLoc_res i π p a.ambient a.equations _ _ V U hUV hV x
      | none => fun _ _ _ _ _ => (map_zero _).symm)
    (fun b b' => match b, b' with
      | some a, some a' => fun U hb hb' m => chartLoc_agree_zero i π p a a' U hb hb' m
      | some a, none => fun U hb hb' m => by
          rw [pushforwardRelativeForms_eq_zero_of_le_complRangeOpens i π _ hb' m]
          exact chartLoc_zero i π p a.ambient a.equations _ _ U hb
      | none, some a' => fun U hb hb' m => by
          rw [pushforwardRelativeForms_eq_zero_of_le_complRangeOpens i π _ hb m]
          exact (chartLoc_zero i π p a'.ambient a'.equations _ _ U hb').symm
      | none, none => fun _ _ _ _ => rfl)
  refine ⟨φ, fun a V hV x => hφ (some a) V hV x, fun ψ hψ => ?_⟩
  refine hom_ext_of_app_eq_equationChart i π hE fun a V hV => ?_
  ext x
  exact (hψ a V hV x).trans (hφ (some a) V hV x).symm

/-! ### Stacks 0G86 -/

/-- **Stacks Project, Tag 0G86: the canonical Gysin map of a closed immersion.**  Let
`π : X ⟶ S` be a morphism of schemes and `i : Z ⟶ X` a closed immersion of finite presentation
whose conormal sheaf is locally free of rank `c`.  Then there is **one** map

`γ^p : i_*Ω^p_{Z/S} ⟶ i_*ℋ^c_Z(Ω^{p+c}_{X/S})`

which, over every open contained in an open on which `c` functions generate the ideal of `Z`, is
the Gysin map `γ^p_{f₁, …, f_c}` of [Stacks, Tag 0G83] of those functions, and it is the only map
with that property.

**The rank is an arbitrary natural number.**  [Stacks, Tag 0G8A] says `c ≥ 0` explicitly, so
`c = 0` is part of the statement and not a degenerate exclusion; it is the case in which `Z` is a
*clopen* piece of `X`, by `Stacks.Gysin.isClopen_range_base_of_conormalRank_zero`, and in which a
chart carries the empty family of equations.  The hypotheses are exactly the tag's: no bound on
`c`, and in particular neither `c ≠ 0` nor a rank of the form `d + 1`.

The proof splits on `c` and nothing else does:

* for `c = d + 1`, `Stacks.Gysin.existsUnique_gysinHom_of_conormalRank_succ`, the chart route
  through `Stacks.Gysin.GysinChartData` — the charts then cover `X`, because away from the closed
  subscheme the equations may be taken to generate the unit ideal;
* for `c = 0`, `existsUnique_gysinHom_of_conormalRank_zero`, where the charts cover only the
  image and the gluing is run on the family augmented by its complement.

The charts are *all* the equation charts of `Stacks.Gysin.EquationChart`, which is what makes the
conclusion quantify over every local family of `c` equations cutting out `Z` and not only over a
chosen covering family. -/
@[stacks 0G86]
theorem existsUnique_gysinHom_of_conormalRank (i : Z ⟶ X) [IsClosedImmersion i]
    [LocallyOfFinitePresentation i] (π : X ⟶ S) {c : ℕ} (p : ℕ) (hE : ConormalRank i c) :
    ∃! φ : pushforwardRelativeForms i π (p : ℤ) ⟶ gysinTarget i π c p,
      ∀ (a : EquationChart i c) (V : X.Opens) (hV : V ≤ a.ambient)
        (x : Γ(pushforwardRelativeForms i π (p : ℤ), V)),
        φ.app V x =
          chartLoc i π p a.ambient a.equations
            (isCutOutByEquationsOn_of_isGeneratedByOn i a.gen a.vanish)
            (equationsClosedSet_restrictEquations i a.ambient
              (isCutOutByEquationsOn_of_isGeneratedByOn i a.gen a.vanish)) V hV x := by
  match c, hE with
  | 0, hE => exact existsUnique_gysinHom_of_conormalRank_zero i π p hE
  | _ + 1, hE => exact existsUnique_gysinHom_of_conormalRank_succ i π p hE

end Stacks.Gysin

end
