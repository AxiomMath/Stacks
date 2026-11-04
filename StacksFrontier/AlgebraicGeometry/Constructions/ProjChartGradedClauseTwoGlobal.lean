module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartFullGradedGluing
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedClauseTwo
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistAwayPiece
public import StacksFrontier.Topology.Sheaves.Glueing.OModuleMapGluing

/-!
# Clause (2) of Stacks Tag 01NK between global section groups

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring, `T` a scheme, `L` an invertible `𝒪_T`-module and
`ψ : A → Γ_*(T, L)` a graded map in the degreewise spelling
`Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections`. Clause (2) of [Stacks, Tag 01NK] is
the commuting square

  `A_d --ψ--> Γ(T, L^{⊗ d})`
  `  |                 |` restrict
  `  v` (Tag 01MP)      `v`
  `Γ(X, 𝒪_X(d)) --θ--> Γ(U(ψ), L^{⊗ d})`

The sibling file `StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedClauseTwo` states it
on **one** member `T_{ψ(f)}` of the cover of `U(ψ)`, at the spelling `(A_f)_d` that the
chart-level comparison `θ_f` is defined on. This file states it over **all of `U(ψ)`**, between
the global section groups of the square.

## What makes that possible without assembling `θ`

Going down then right in the square produces, for `a ∈ 𝒜 d`, a section of `L^{⊗ d}` over `U(ψ)`:
on each chart `T_{ψ(f)}` it is `θ_f` applied to the global section of `𝒪_X(d)` attached to `a` by
[Stacks, Tag 01MP], restricted to `D₊(f)` and read in `(A_f)_d` through
`Stacks.AlgebraicGeometry.ProjTwistAwayPiece.sectionsTwistEquivGradedPiece`. The two routes to the
square's lower right corner are therefore compared **as sections over `U(ψ)`**, and a section of a
sheaf over an open is determined by its restrictions to any family covering that open. The opens
`T_{ψ(f)}` cover `U(ψ)` by the *definition* of
`Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.coveringOpen`, which is literally
their supremum, so the covering hypothesis is `le_rfl`.

So no morphism `r_{L, ψ}^*(⨁_{d ∈ ℤ} 𝒪_X(d)) ⟶ ⨁_{d ∈ ℤ} L^{⊗ d}|_{U(ψ)}` of graded
`𝒪_T`-algebras has to be built to state clause (2) at the square's own global section groups: the
square is an identity between two sections of one sheaf over one open, and the chart-level values
of `θ` determine it.

## Main results

* `…ProjChartGradedClauseTwoGlobal.res_coveringOpen_eq_chartSection` and
  `…res_coveringOpen_eq_chartSection_degreeSection` — the restriction of `ψ(a)|_{U(ψ)}` to each
  chart is the chart-level value of `θ`, the second at the honest [Stacks, Tag 01MP] section.
* `…ProjChartGradedClauseTwoGlobal.eq_resTop_of_res_eq_chartSection` — **clause (2) of
  [Stacks, Tag 01NK] between the global section groups of the square**: a section of `L^{⊗ d}` over
  `U(ψ)` whose restriction to every chart is the chart-level value of `θ` on the [Stacks, Tag 01MP]
  section of `a` is `ψ(a)` restricted to `U(ψ)`.
* `…ProjChartGradedClauseTwoGlobal.existsUnique_section_res_eq_chartSection` — that section exists
  and is unique, so the lower-left route of the square is defined on the image of
  [Stacks, Tag 01MP] and lands where the upper-right route does.

## Implementation notes

**Why the charts are indexed by `(k : ℕ) × 𝒜 (k + 1)`.** That is the index of
`GradedSections.coveringOpen`'s supremum: a positive degree written as `k + 1` together with a
homogeneous element of it. Indexing the cover any other way would need the covering hypothesis
proved rather than `le_rfl`. The statements that take a chart as `hf : f ∈ 𝒜 e` with `0 < e`
instead go through `GradedSections.nonvanishingOpenAt_le_coveringOpen_of_pos`.

**The chart degree and the twist degree are independent.** `θ_f` on the chart of `f ∈ 𝒜 e` is
defined in every twist degree `d`, so `e` and `d` are unrelated below; the square is about one `d`
and every chart.

## References

* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01MP](https://stacks.math.columbia.edu/tag/01MP)
* [Stacks Project, Tag 00AN](https://stacks.math.columbia.edu/tag/00AN)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj (integerGrading twistingSheaf)
open Stacks.AlgebraicGeometry.ProjChartFullGraded (GradedSections)
open Stacks.AlgebraicGeometry.ProjChartGradedClauseTwo (chartSection_mk_one)
open Stacks.AlgebraicGeometry.ProjChartGradedDivision (chartSection)
open Stacks.AlgebraicGeometry.ProjTwistAwayPiece (sectionsTwistEquivGradedPiece
  coe_sectionsTwistEquivGradedPiece_degreeSection)
open AlgebraicGeometry.ProjectiveSpectrum.Proj (degreeSection)
open Stacks.GradedLocalization (gradedPiece)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.TensorPowerTrivialize (resTop res_resTop)
open Stacks.TensorPowers (natTensorPow)
open scoped Stacks.GradedLocalization

universe u w

namespace Stacks.AlgebraicGeometry.ProjChartGradedClauseTwoGlobal

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {T : Scheme.{u}} {L : T.Modules}
  [Stacks.Ample.IsInvertibleModule T L] (ψ : GradedSections 𝒜 L) {d : ℕ}

/-- **The restriction of `ψ(a)|_{U(ψ)}` to the chart of `f` is the chart-level value of `θ`** on
any element of `(A_f)_d` represented by the fraction `a / 1`.

Restricting a global section twice is restricting it once
(`Stacks.TensorPowerTrivialize.res_resTop`), so the left side is `ψ(a)` restricted to the chart;
that is the chart-level clause (2) of [Stacks, Tag 01NK], which is
`Stacks.AlgebraicGeometry.ProjChartGradedClauseTwo.chartSection_mk_one`. -/
theorem res_coveringOpen_eq_chartSection {a : A} (ha : a ∈ 𝒜 d) {e : ℕ} {f : A}
    (hf : f ∈ 𝒜 e) (he : 0 < e)
    (y : gradedPiece 𝒜 (integerGrading (S := A) 𝒜) f (d : ℤ))
    (hrep : (y : LocalizedModule.Away f A)
      = LocalizedModule.mk a (1 : Submonoid.powers f)) :
    (natTensorPow L d).presheaf.map
        (homOfLE (ψ.nonvanishingOpenAt_le_coveringOpen_of_pos hf he)).op
        (resTop (natTensorPow L d) (ψ.toFun d ⟨a, ha⟩) ψ.coveringOpen)
      = chartSection ψ hf (le_refl _) d y := by
  rw [res_resTop]
  exact (chartSection_mk_one ψ hf (le_refl _) d ha y hrep).symm

/-- **The same, at the honest global section of [Stacks, Tag 01MP].** The global section of
`𝒪_X(d)` attached to `a ∈ 𝒜 d`, restricted to `D₊(f)` and read in `(A_f)_d` through
`Stacks.AlgebraicGeometry.ProjTwistAwayPiece.sectionsTwistEquivGradedPiece`, is the fraction
`a / 1` (`…coe_sectionsTwistEquivGradedPiece_degreeSection`), so this is the previous statement at
that element.

The left side is the upper-right route of the square of clause (2) — apply `ψ`, restrict to
`U(ψ)`, restrict to the chart — and the right side is the lower-left route read on the chart. -/
theorem res_coveringOpen_eq_chartSection_degreeSection {a : A} (ha : a ∈ 𝒜 d) {e : ℕ} {f : A}
    (hf : f ∈ 𝒜 e) (he : 0 < e) :
    (natTensorPow L d).presheaf.map
        (homOfLE (ψ.nonvanishingOpenAt_le_coveringOpen_of_pos hf he)).op
        (resTop (natTensorPow L d) (ψ.toFun d ⟨a, ha⟩) ψ.coveringOpen)
      = chartSection ψ hf (le_refl _) d
          (sectionsTwistEquivGradedPiece 𝒜 hf he (d : ℤ)
            ((twistingSheaf 𝒜 (d : ℤ)).val.map
              (homOfLE (le_top : ProjectiveSpectrum.basicOpen 𝒜 f ≤ ⊤)).op
              (degreeSection 𝒜 d ⟨a, ha⟩))) :=
  res_coveringOpen_eq_chartSection 𝒜 ψ ha hf he _
    (coe_sectionsTwistEquivGradedPiece_degreeSection 𝒜 hf he d ⟨a, ha⟩)

/-- **Clause (2) of [Stacks, Tag 01NK], between the global section groups of its square.**

Let `a ∈ 𝒜 d` and let `s` be a section of `L^{⊗ d}` over `U(ψ)` whose restriction to every chart
`T_{ψ(f)}` of the cover is the chart-level comparison `θ_f` applied to the global section of
`𝒪_X(d)` attached to `a` by [Stacks, Tag 01MP] — that is, `s` is the image of `a` under the
lower-left route of the square, down the map of [Stacks, Tag 01MP] and across `θ`. Then `s` is
`ψ(a)` restricted to `U(ψ)`, the image of `a` under the upper-right route. This is the
commutativity of the square, over all of `U(ψ)` rather than on one chart.

The proof is the separation half of the sheaf axiom
(`TopCat.Sheaf.eq_of_locally_eq_of_isSheafPresheaf`): both sections restrict on each chart to the
same thing, by hypothesis on the left and by
`res_coveringOpen_eq_chartSection_degreeSection` on the right, and the charts cover `U(ψ)` by the
definition of `GradedSections.coveringOpen`. -/
theorem eq_resTop_of_res_eq_chartSection {a : A} (ha : a ∈ 𝒜 d)
    (s : Γ(natTensorPow L d, ψ.coveringOpen))
    (hs : ∀ p : (k : ℕ) × 𝒜 (k + 1),
      (natTensorPow L d).presheaf.map
          (homOfLE (ψ.nonvanishingOpenAt_le_coveringOpen p.1 p.2)).op s
        = chartSection ψ p.2.2 (le_refl _) d
            (sectionsTwistEquivGradedPiece 𝒜 p.2.2 (Nat.succ_pos p.1) (d : ℤ)
              ((twistingSheaf 𝒜 (d : ℤ)).val.map
                (homOfLE (le_top : ProjectiveSpectrum.basicOpen 𝒜 p.2.1 ≤ ⊤)).op
                (degreeSection 𝒜 d ⟨a, ha⟩)))) :
    s = resTop (natTensorPow L d) (ψ.toFun d ⟨a, ha⟩) ψ.coveringOpen :=
  TopCat.Sheaf.eq_of_locally_eq_of_isSheafPresheaf (natTensorPow L d).isSheaf
    (fun p : (k : ℕ) × 𝒜 (k + 1) => ψ.nonvanishingOpenAt (p.1 + 1) p.2)
    (fun p => ψ.nonvanishingOpenAt_le_coveringOpen p.1 p.2) le_rfl
    fun p => (hs p).trans
      (res_coveringOpen_eq_chartSection_degreeSection 𝒜 ψ ha p.2.2 (Nat.succ_pos p.1)).symm

/-- **The lower-left route of the square of clause (2) is defined on the image of
[Stacks, Tag 01MP], and lands where the upper-right route does.** For `a ∈ 𝒜 d` there is exactly
one section of `L^{⊗ d}` over `U(ψ)` restricting on every chart to the chart-level comparison `θ_f`
of the [Stacks, Tag 01MP] section of `a`, and it is `ψ(a)|_{U(ψ)}`.

Existence is `res_coveringOpen_eq_chartSection_degreeSection` with `ψ(a)|_{U(ψ)}` as the witness;
uniqueness is `eq_resTop_of_res_eq_chartSection`. Stating both at once is what makes the square's
lower-left corner a well-defined element of `Γ(U(ψ), L^{⊗ d})` rather than a family of chart
values. -/
theorem existsUnique_section_res_eq_chartSection {a : A} (ha : a ∈ 𝒜 d) :
    ∃! s : Γ(natTensorPow L d, ψ.coveringOpen),
      ∀ p : (k : ℕ) × 𝒜 (k + 1),
        (natTensorPow L d).presheaf.map
            (homOfLE (ψ.nonvanishingOpenAt_le_coveringOpen p.1 p.2)).op s
          = chartSection ψ p.2.2 (le_refl _) d
              (sectionsTwistEquivGradedPiece 𝒜 p.2.2 (Nat.succ_pos p.1) (d : ℤ)
                ((twistingSheaf 𝒜 (d : ℤ)).val.map
                  (homOfLE (le_top : ProjectiveSpectrum.basicOpen 𝒜 p.2.1 ≤ ⊤)).op
                  (degreeSection 𝒜 d ⟨a, ha⟩))) :=
  ⟨resTop (natTensorPow L d) (ψ.toFun d ⟨a, ha⟩) ψ.coveringOpen,
    fun p => res_coveringOpen_eq_chartSection_degreeSection 𝒜 ψ ha p.2.2 (Nat.succ_pos p.1),
    fun _ hs => eq_resTop_of_res_eq_chartSection 𝒜 ψ ha _ hs⟩

end Stacks.AlgebraicGeometry.ProjChartGradedClauseTwoGlobal

end
