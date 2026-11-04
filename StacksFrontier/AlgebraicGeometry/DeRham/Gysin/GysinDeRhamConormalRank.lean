module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinChartFractionDeRham
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinDeRhamConormalRankZero
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinExcisionAbelianAgreement

/-!
# Stacks 0G87: the Gysin map of Stacks 0G86 is compatible with the de Rham differentials

Let `π : X ⟶ S` be a morphism of schemes and let `i : Z ⟶ X` be as in [Stacks, Tag 0G86]: a
closed immersion of finite presentation whose conormal sheaf is locally free of rank `c`, an
**arbitrary** natural number — [Stacks, Tag 0G8A] says `c ≥ 0` explicitly.
[Stacks, Tag 0G86] produces the canonical Gysin map

`γ^p : i_*Ω^p_{Z/S} ⟶ i_*ℋ^c_Z(Ω^{p+c}_{X/S})`,

the unique map that is, over every open contained in an equation chart, the Gysin map of that
chart's equations.  [Stacks, Tag 0G87] says that `γ^p` is compatible with the de Rham
differentials on `Ω^•_{X/S}` and `Ω^•_{Z/S}`, and this file states and proves it.

The square is

`γ^{p+1} ∘ d_{Z/S} = ℋ^c_Z(d_{X/S}) ∘ γ^p`,

its left vertical arrow the relative de Rham differential of `Z/S` read on the sections of
`i_*Ω^p_{Z/S}` (`Stacks.Gysin.pushforwardDeRham`) and its right vertical arrow the action of
`i_*ℋ ᶜ_Z` on the relative de Rham differential of `X/S` supplied by [Stacks, Tag 0G74] part (2)
(`Stacks.Gysin.gysinTargetDeRhamHom`).  Both are constructed, not assumed; the differentials are
only `π⁻¹𝒪_S`-linear, so the two verticals are morphisms of the underlying abelian sheaves and the
square is read on sections, which is the idiom of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/Transverse.lean` for the base-change square
[Stacks, Tag 0G89] of the same glued map.

## Main results

* `Stacks.Gysin.gysinHom_comm_deRham_of_conormalRank_succ`: the square at a rank of the form
  `d + 1`, where the equation charts cover the whole of `X` and the chart route applies.
* `Stacks.Gysin.gysinHom_comm_deRham_of_conormalRank`: **[Stacks, Tag 0G87]**, under the
  hypotheses of [Stacks, Tag 0G86] and nothing else — in particular at an **arbitrary** conormal
  rank `c : ℕ`, with neither `c ≠ 0` nor a rank of the form `d + 1` assumed.  The two Gysin maps
  are quantified over rather than constructed, each characterised exactly as
  `Stacks.Gysin.existsUnique_gysinHom_of_conormalRank` — the registration of
  [Stacks, Tag 0G86] — characterises it: locally the Gysin map of every equation chart.  So the
  statement is about *the* Gysin map of [Stacks, Tag 0G86], which that tag shows exists and is
  unique.

## Implementation notes

**Why the rank splits into two cases.**  The chart route needs the equation charts to cover `X`,
which `Stacks.Gysin.exists_gysinCharts` supplies only for `c ≠ 0`: away from the closed subscheme
the equations may be taken to generate the unit ideal, and that asks for an index of `Fin c`.  At
`c = 0` a chart carries the empty family, lies inside `Set.range i.base`, and the charts cover
only the image; the square is then glued on the chart family augmented by the complement of the
image, in
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinDeRhamConormalRankZero.lean`.  This is the same
split, for the same reason, that [Stacks, Tag 0G86] itself is proved by in
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinConormalRankAny.lean`.

**Where each hypothesis of the source is consumed.**  `IsClosedImmersion i`,
`LocallyOfFinitePresentation i` and `Stacks.Gysin.ConormalRank i (d + 1)` are consumed, in the
`c = d + 1` case, exactly where [Stacks, Tag 0G86] consumes them, by
`Stacks.Gysin.exists_gysinCharts`, which turns them
into a covering of `X` by equation charts.  There is no further hypothesis: the chart data of
[Stacks, Tag 0G86] is `Stacks.Gysin.chartGysinChartData` on the family of *all* equation charts,
the same family `Stacks.Gysin.existsUnique_gysinHom_of_conormalRank` uses, so the characterisation
of `γ` pins it to that data's glued map by
`Stacks.Gysin.GysinChartData.eq_of_app_eq_loc`.

**How the two assumed inputs of the reduction were discharged.**  The reduction of the square to
one chart is `Stacks.Gysin.GysinDeRhamData.gysinHom_comm_deRham`; at the chart data of
[Stacks, Tag 0G86] it took the single hypothesis `Stacks.Gysin.ClsCommutesWithDeRham`, which
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinDeRhamClsReduction.lean` splits into a class-map
half and an excision half.  Both are now theorems:

* the class-map half is `Stacks.Gysin.chartFractionCommutesWithDeRham`, proved unconditionally in
  `StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinChartFractionDeRham.lean` from the localized
  Leibniz rule;
* the excision half is `Stacks.Gysin.supportCohomologyRestrictAbNatural` of
  `StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinExcisionAbelianAgreement.lean`, for an
  arbitrary morphism of the underlying abelian sheaves — which is the case the de Rham
  differential needs, being `𝒪_X`-linear for no `X`.

So `Stacks.Gysin.gysinHom_comm_deRham_of_excision` loses its last hypothesis, and that is all this
file does.

**Why the right vertical arrow is transported.**  The square at a chart data is stated with
`Stacks.Gysin.chartGysinTargetDeRhamHom`, which is
`Stacks.Gysin.gysinTargetDeRhamHom` carried along the two unfoldings of
`Stacks.Gysin.chartGysinChartData_target`; those are reflexivity, and
`Stacks.Gysin.gysinTargetDeRhamHomOfEq_rfl` is what says the transport adds nothing, so the
statement here speaks the untransported arrow — [Stacks, Tag 0G74] part (2) at the Gysin target —
and no chart data occurs in it.

**How the two spellings of the Gysin target are reconciled, and what does not work.**
`Stacks.Gysin.GysinChartData.target` is a field, so for the chart data of [Stacks, Tag 0G86] it is
the Gysin target only after the construction is unfolded; `chartGysinChartData_target` is that
unfolding and it is `rfl`.  The square proved at the chart data therefore speaks
`D.target`, and the statement here speaks `Stacks.Gysin.gysinTarget`.  The reconciliation is
affordable only one occurrence at a time, and in particular **not** under the coercion of a
section:

* an equality of two *objects* of `X.Modules` across the pair (`chartGysinChartData_target`
  itself), of two *morphisms* (`harrow` below), or of two `Stacks.Gysin.abSectionsHom`
  applications differing only in the implicit modules: each goes through on its own;
* `exact` of the chart-data square at the goal does **not**, and reports
  `maximum recursion depth has been reached` rather than a timeout.  What exceeds the depth is the
  pair of occurrences inside `CategoryTheory.ConcreteCategory.hom`: the goal is elaborated with
  `γ : _ ⟶ gysinTarget …`, so `γ.app V x` carries the Gysin-target spelling in the *implicit
  object arguments* of that coercion, while the chart-data square carries `D.target` there, and
  unifying the two means unfolding the chart data beneath an instance argument.  Raising
  `maxRecDepth` is forbidden here, and `convert … using 2` only reduces the goal to an `Iff`
  between the two readings, which is the same check.

So the two sections are converted first, by `congrArg` at an explicit lambda — `hz` and `hw`
below.  Each of those crosses the pair exactly once, in a declaration of its own and not under a
coercion's instance arguments, and after rewriting with them the goal is the chart-data square
verbatim.  This is the same discipline the implementation notes of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinForgetLocalCohomologySheafRestrict.lean` record
for the two readings of the category of abelian sheaves.

## References

* [Stacks Project, Tag 0G87](https://stacks.math.columbia.edu/tag/0G87)
* [Stacks Project, Tag 0G86](https://stacks.math.columbia.edu/tag/0G86)
* [Stacks Project, Tag 0G85](https://stacks.math.columbia.edu/tag/0G85)
* [Stacks Project, Tag 0G83](https://stacks.math.columbia.edu/tag/0G83)
* [Stacks Project, Lemma 20.34.8 (Tag 0G74)](https://stacks.math.columbia.edu/tag/0G74)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open Stacks.AlgebraicGeometry.ConormalEquations
open Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

namespace Stacks.Gysin

variable {Z X S : Scheme.{u}}

/-! ### The square at a family of equation charts -/

/-- **The square of [Stacks, Tag 0G87] for any pair of maps that are locally the Gysin maps of a
given family of equation charts.**  By
`Stacks.Gysin.GysinChartData.eq_of_app_eq_loc` such a map is the glued map of that family's chart
data, so this is `Stacks.Gysin.gysinHom_comm_deRham_of_excision` with its excision hypothesis
discharged by `Stacks.Gysin.supportCohomologyRestrictAbNatural` and its right vertical arrow
untransported by `Stacks.Gysin.gysinTargetDeRhamHomOfEq_rfl`. -/
private theorem gysinHom_comm_deRham_charts (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S)
    {d : ℕ} (p : ℕ) (Chart : Type u) (ambient : Chart → X.Opens)
    (equations : (a : Chart) → Fin (d + 1) → Γ(X, ambient a))
    (hvanish : ∀ (a : Chart) (V : X.Opens) (hV : V ≤ ambient a) (j : Fin (d + 1)),
      (i.app V).hom (X.presheaf.map (homOfLE hV).op (equations a j)) = 0)
    (hcover : ∀ y : X, ∃ a, y ∈ ambient a)
    (hgen : ∀ a, IsGeneratedByOn X.toRingedSpace (definingIdealOfHom i) (ambient a) (equations a))
    (γ : pushforwardRelativeForms i π (p : ℤ) ⟶ gysinTarget i π (d + 1) p)
    (γ' : pushforwardRelativeForms i π ((p + 1 : ℕ) : ℤ) ⟶ gysinTarget i π (d + 1) (p + 1))
    (hγ : ∀ (a : Chart) (V : X.Opens) (hV : V ≤ ambient a)
      (x : Γ(pushforwardRelativeForms i π (p : ℤ), V)),
      γ.app V x =
        (chartGysinChartData i π p Chart ambient equations hvanish hcover hgen).loc a V hV x)
    (hγ' : ∀ (a : Chart) (V : X.Opens) (hV : V ≤ ambient a)
      (x : Γ(pushforwardRelativeForms i π ((p + 1 : ℕ) : ℤ), V)),
      γ'.app V x =
        (chartGysinChartData i π (p + 1) Chart ambient equations hvanish hcover hgen).loc
          a V hV x)
    (V : X.Opens) (x : Γ(pushforwardRelativeForms i π (p : ℤ), V)) :
    abSectionsHom (gysinTargetDeRhamHom i π (d + 1) p) V (γ.app V x) =
      γ'.app V (pushforwardDeRham i π p V x) := by
  have happ : ∀ (q : ℕ)
      (g : pushforwardRelativeForms i π (q : ℤ) ⟶ gysinTarget i π (d + 1) q),
      (∀ (a : Chart) (V : X.Opens) (hV : V ≤ ambient a)
        (x : Γ(pushforwardRelativeForms i π (q : ℤ), V)),
        g.app V x =
          (chartGysinChartData i π q Chart ambient equations hvanish hcover hgen).loc a V hV x) →
      ∀ (y : Γ(pushforwardRelativeForms i π (q : ℤ), V)),
        g.app V y =
          (chartGysinChartData i π q Chart ambient equations hvanish hcover hgen).gysinHom.app
            V y := fun q g hg y =>
    congrArg (fun φ => φ.app V y)
      (GysinChartData.eq_of_app_eq_loc
        (chartGysinChartData i π q Chart ambient equations hvanish hcover hgen) hg
        fun a V₀ hV₀ y => GysinChartData.gysinHom_app _ a V₀ hV₀ y)
  have harrow : chartGysinTargetDeRhamHom i π p Chart ambient equations hvanish hcover hgen =
      gysinTargetDeRhamHom i π (d + 1) p := gysinTargetDeRhamHomOfEq_rfl i π (d + 1) p
  rw [happ p γ hγ x, happ (p + 1) γ' hγ' (pushforwardDeRham i π p V x)]
  rw [← harrow]
  exact gysinHom_comm_deRham_of_excision i π p Chart ambient equations hvanish hcover hgen
    (fun a => supportCohomologyRestrictAbNatural (ambient a) (isClosed_range_base i)
      (isClosed_preimage_range_base i (ambient a)) (d + 1)
      (ambientDeRhamShiftAbHom π (d + 1) p)) V x

/-! ### The square at a rank of the form `d + 1` -/

/-- **The square of [Stacks, Tag 0G87] at a conormal rank of the form `d + 1`.**

Let `π : X ⟶ S` be a morphism of schemes and `i : Z ⟶ X` a closed immersion of finite
presentation whose conormal sheaf is locally free of rank `c = d + 1`.  Let `γ` and `γ'` be the
Gysin maps of [Stacks, Tag 0G86] in the degrees `p` and `p + 1`, each characterised as that tag
characterises it: over every open contained in an equation chart it is the Gysin map
`γ^p_{f₁, …, f_c}` of [Stacks, Tag 0G83] of that chart's equations.  Then the square

`ℋ ᶜ_Z(d_{X/S}) ∘ γ^p = γ^{p+1} ∘ d_{Z/S}`

commutes, on the sections over every open of `X`.  The left vertical arrow is the relative de
Rham differential of `Z/S` (`Stacks.Gysin.pushforwardDeRham`), the right one the action of
`i_*ℋ ᶜ_Z` on the relative de Rham differential of `X/S` given by [Stacks, Tag 0G74] part (2)
(`Stacks.Gysin.gysinTargetDeRhamHom`).

Both maps `γ`, `γ'` with these properties exist and are unique, by
`Stacks.Gysin.existsUnique_gysinHom_of_conormalRank`, which is the registration of
[Stacks, Tag 0G86]; the characterisations are stated here verbatim as they are there.  The source
proves the tag in one sentence — the assertion is local, and locally it is [Stacks, Tag 0G85] —
and that is the shape of the proof: `Stacks.Gysin.gysinHom_comm_deRham_of_excision` is the
localisation, whose two inputs are the chart-local naturality of the class map of
[Stacks, Tag 0G7Q] along `d` and the abelian reading of the derived excision of
[Stacks, Tag 0G78].

**This is not the registration of the tag**, whose hypotheses leave the rank unqualified: it is
the half of it that the chart route reaches, the rank being of the form `d + 1` exactly so that
`Stacks.Gysin.exists_gysinCharts` produces a covering of `X`.
`gysinHom_comm_deRham_of_conormalRank` below carries the tag, at an arbitrary `c : ℕ`. -/
theorem gysinHom_comm_deRham_of_conormalRank_succ (i : Z ⟶ X) [IsClosedImmersion i]
    [LocallyOfFinitePresentation i] (π : X ⟶ S) {d : ℕ} (p : ℕ)
    (hE : ConormalRank i (d + 1))
    (γ : pushforwardRelativeForms i π (p : ℤ) ⟶ gysinTarget i π (d + 1) p)
    (γ' : pushforwardRelativeForms i π ((p + 1 : ℕ) : ℤ) ⟶ gysinTarget i π (d + 1) (p + 1))
    (hγ : ∀ (a : EquationChart i (d + 1)) (V : X.Opens) (hV : V ≤ a.ambient)
      (x : Γ(pushforwardRelativeForms i π (p : ℤ), V)),
      γ.app V x =
        chartLoc i π p a.ambient a.equations
          (isCutOutByEquationsOn_of_isGeneratedByOn i a.gen a.vanish)
          (equationsClosedSet_restrictEquations i a.ambient
            (isCutOutByEquationsOn_of_isGeneratedByOn i a.gen a.vanish)) V hV x)
    (hγ' : ∀ (a : EquationChart i (d + 1)) (V : X.Opens) (hV : V ≤ a.ambient)
      (x : Γ(pushforwardRelativeForms i π ((p + 1 : ℕ) : ℤ), V)),
      γ'.app V x =
        chartLoc i π (p + 1) a.ambient a.equations
          (isCutOutByEquationsOn_of_isGeneratedByOn i a.gen a.vanish)
          (equationsClosedSet_restrictEquations i a.ambient
            (isCutOutByEquationsOn_of_isGeneratedByOn i a.gen a.vanish)) V hV x)
    (V : X.Opens) (x : Γ(pushforwardRelativeForms i π (p : ℤ), V)) :
    abSectionsHom (gysinTargetDeRhamHom i π (d + 1) p) V (γ.app V x) =
      γ'.app V (pushforwardDeRham i π p V x) := by
  obtain ⟨ambient, equations, hvanish, hcover, _, hgen, _⟩ :=
    exists_gysinCharts i (d + 1) hE (Nat.succ_ne_zero d)
  have hcov : ∀ y : X, ∃ a : EquationChart i (d + 1), y ∈ a.ambient := fun y => by
    obtain ⟨a, ha⟩ := hcover y
    exact ⟨⟨ambient a, equations a, hgen a, hvanish a⟩, ha⟩
  exact gysinHom_comm_deRham_charts i π p (EquationChart i (d + 1)) (fun a => a.ambient)
    (fun a => a.equations) (fun a => a.vanish) hcov (fun a => a.gen) γ γ' hγ hγ' V x

/-! ### Stacks 0G87 -/

/-- **Stacks Project, Tag 0G87: the Gysin map is compatible with the de Rham differentials.**

Let `π : X ⟶ S` be a morphism of schemes and `i : Z ⟶ X` a closed immersion of finite
presentation whose conormal sheaf is locally free of rank `c` — the hypotheses of
[Stacks, Tag 0G86], and nothing more.  Let `γ` and `γ'` be the Gysin maps of [Stacks, Tag 0G86]
in the degrees `p` and `p + 1`, each characterised as that tag characterises it: over every open
contained in an equation chart it is the Gysin map `γ^p_{f₁, …, f_c}` of [Stacks, Tag 0G83] of
that chart's equations.  Then the square

`ℋ ᶜ_Z(d_{X/S}) ∘ γ^p = γ^{p+1} ∘ d_{Z/S}`

commutes, on the sections over every open of `X`.  The left vertical arrow is the relative de
Rham differential of `Z/S` (`Stacks.Gysin.pushforwardDeRham`), the right one the action of
`i_*ℋ ᶜ_Z` on the relative de Rham differential of `X/S` given by [Stacks, Tag 0G74] part (2)
(`Stacks.Gysin.gysinTargetDeRhamHom`).

**The rank is an arbitrary natural number**, as [Stacks, Tag 0G86] states it and as
[Stacks, Tag 0G8A] says explicitly (`c ≥ 0`).  In particular `c = 0` — the case in which `Z` is a
*clopen* piece of `X`, by `Stacks.Gysin.isClopen_range_base_of_conormalRank_zero`, and in which
an equation chart carries the empty family — is part of the statement and not a degenerate
exclusion; neither `c ≠ 0` nor a rank of the form `d + 1` is assumed.

Both maps `γ`, `γ'` with these properties exist and are unique at every rank, by
`Stacks.Gysin.existsUnique_gysinHom_of_conormalRank`, the registration of [Stacks, Tag 0G86]; the
characterisations are stated here verbatim as they are there.

The proof splits on `c` and nothing else does:

* for `c = d + 1`, `gysinHom_comm_deRham_of_conormalRank_succ`, the chart route — the charts then
  cover `X`, and the square at one chart family is `gysinHom_comm_deRham_charts`;
* for `c = 0`, `Stacks.Gysin.gysinHom_comm_deRham_of_conormalRank_zero`, where the charts cover
  only the image of `i` and the square is glued on the family augmented by its complement. -/
@[stacks 0G87]
theorem gysinHom_comm_deRham_of_conormalRank (i : Z ⟶ X) [IsClosedImmersion i]
    [LocallyOfFinitePresentation i] (π : X ⟶ S) {c : ℕ} (p : ℕ)
    (hE : ConormalRank i c)
    (γ : pushforwardRelativeForms i π (p : ℤ) ⟶ gysinTarget i π c p)
    (γ' : pushforwardRelativeForms i π ((p + 1 : ℕ) : ℤ) ⟶ gysinTarget i π c (p + 1))
    (hγ : ∀ (a : EquationChart i c) (V : X.Opens) (hV : V ≤ a.ambient)
      (x : Γ(pushforwardRelativeForms i π (p : ℤ), V)),
      γ.app V x =
        chartLoc i π p a.ambient a.equations
          (isCutOutByEquationsOn_of_isGeneratedByOn i a.gen a.vanish)
          (equationsClosedSet_restrictEquations i a.ambient
            (isCutOutByEquationsOn_of_isGeneratedByOn i a.gen a.vanish)) V hV x)
    (hγ' : ∀ (a : EquationChart i c) (V : X.Opens) (hV : V ≤ a.ambient)
      (x : Γ(pushforwardRelativeForms i π ((p + 1 : ℕ) : ℤ), V)),
      γ'.app V x =
        chartLoc i π (p + 1) a.ambient a.equations
          (isCutOutByEquationsOn_of_isGeneratedByOn i a.gen a.vanish)
          (equationsClosedSet_restrictEquations i a.ambient
            (isCutOutByEquationsOn_of_isGeneratedByOn i a.gen a.vanish)) V hV x)
    (V : X.Opens) (x : Γ(pushforwardRelativeForms i π (p : ℤ), V)) :
    abSectionsHom (gysinTargetDeRhamHom i π c p) V (γ.app V x) =
      γ'.app V (pushforwardDeRham i π p V x) := by
  match c, hE, γ, γ', hγ, hγ' with
  | 0, hE, γ, γ', hγ, hγ' =>
      exact gysinHom_comm_deRham_of_conormalRank_zero i π p hE γ γ' hγ hγ' V x
  | _ + 1, hE, γ, γ', hγ, hγ' =>
      exact gysinHom_comm_deRham_of_conormalRank_succ i π p hE γ γ' hγ hγ' V x

end Stacks.Gysin

end
