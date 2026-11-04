module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedAlphaMatch

/-!
# `θ|_V = α` as an equality of maps on the chart of `f`

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring, `T` a scheme, `L` an invertible `𝒪_T`-module and
`ψ : A → Γ_*(T, L)` a graded map in the degreewise spelling
`Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections`. Fix `d > 0` and `f ∈ 𝒜 d`, and let
`V` be an open of `T` on which `ψ(f)` does not vanish. The final clause of [Stacks, Tag 01NK] asks
that the comparison `θ` of that tag restrict on an open where `ψ(A_d)` generates `L ^⊗ d` to the
isomorphism `α : φ^*𝒪_X(d) → L ^⊗ d|_V` of [Stacks, Tag 01N8] attached to `ψ|_{A^{(d)}}`.

The sibling module `StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedAlphaMatch` proves
that clause *at one element*: the value of the chart-level comparison `θ_f` on the degree-`d`
section of `f` — the very element cutting out the chart — is `α`'s value there. This file upgrades
that to an equality of **maps**, in the two steps the upgrade factors into.

* **Every degree-`d` global section, not just `f`.** `alphaVeronese_hom_app_top` and
  `Stacks.AlgebraicGeometry.ProjChartGradedClauseTwo.chartSection_mk_one` are each already stated
  for an arbitrary homogeneous element, so the agreement holds on the fraction `a / 1` for every
  `a ∈ 𝒜 d`, with the chart still cut out by `f`. This is the agreement of `θ_f` and `α` on the
  whole image of the map of [Stacks, Tag 01MP] in degree `d`.

* **Hence on all of `(A_f)_d`, by semilinearity.** The degree-`d` part of `A_f` is generated over
  the degree-zero subring `A_{(f)}` by the single element `f / 1`: a fraction `x / f ^ j` of
  `A_f`-degree `d` is `(x / f ^ (j + 1)) · (f / 1)` and the first factor has degree zero. Since
  `θ_f` is `A_{(f)}`-semilinear along the dehomogenisation ring map
  (`Stacks.AlgebraicGeometry.ProjChartGradedDivision.chartSection_smul`), its value at `f / 1`
  fixes it everywhere. So `θ_f` is the *unique* `A_{(f)}`-semilinear map whose value at `f / 1` is
  `α`'s, which is the equality `θ|_V = α` of the tag's final clause read as an equality of maps on
  the chart.

## Main results

* `Stacks.AlgebraicGeometry.ProjChartGradedAlphaMaps.exists_smul_mk_one` — **`f / 1` generates
  `(A_f)_d` over `A_{(f)}`.**
* `Stacks.AlgebraicGeometry.ProjChartGradedAlphaMaps.chartSection_eq_alphaVeronese_of_mem` and
  `…chartSection_degreeSection_eq_alphaVeronese_of_mem` — **`θ_f` and `α` agree on the degree-`d`
  section of every `a ∈ 𝒜 d`**, the second with the identification
  `Γ(D₊(f), 𝒪_X(d)) ≅ (A_f)_d` composed in.
* `Stacks.AlgebraicGeometry.ProjChartGradedAlphaMaps.eq_chartSection_of_smul_of_alpha` —
  **`θ_f` is the unique `A_{(f)}`-semilinear map agreeing with `α` at `f / 1`**, and
  `…chartSection_eq_smul_alphaVeronese` — its value at an arbitrary element of `(A_f)_d` is the
  corresponding multiple of `α`'s value.

## Implementation notes

**Why no additivity is asked of the competitor.** `eq_chartSection_of_smul_of_alpha` constrains an
arbitrary function, not an additive map: semilinearity over `A_{(f)}` together with one value
already determines a map on a cyclic `A_{(f)}`-module, so additivity is never used. Asking for it
would weaken the statement.

**The scalar action is spelled by hand.** `(A_f)_d` carries the `A_{(f)}`-action only through
membership (`Stacks.GradedLocalization.smul_mem_gradedPiece`), so a scaled element is written as
the subtype pair it is, exactly as in `chartSection_smul`. The two sides of each statement below
are then at the spelling that lemma applies at.

## References

* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Tag 01MP](https://stacks.math.columbia.edu/tag/01MP)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj (integerGrading twistingSheaf)
open Stacks.AlgebraicGeometry.ProjChartAlphaInstance (pullbackDegreeSection)
open Stacks.AlgebraicGeometry.ProjChartFullGraded (GradedSections)
open Stacks.AlgebraicGeometry.ProjChartGradedAlphaMatch (alphaVeronese alphaVeronese_hom_app_top
  chartSection_degreeSection_eq_alphaVeronese)
open Stacks.AlgebraicGeometry.ProjChartGradedClauseTwo (chartSection_mk_one)
open Stacks.AlgebraicGeometry.ProjChartGradedDivision (chartSection chartSection_smul exists_rep)
open Stacks.AlgebraicGeometry.ProjChartGradedVeronese (gluedVeronese)
open Stacks.AlgebraicGeometry.ProjTwistAwayPiece (sectionsTwistEquivGradedPiece
  coe_sectionsTwistEquivGradedPiece_degreeSection)
open AlgebraicGeometry.ProjectiveSpectrum.Proj (degreeSection)
open Stacks.AlgebraicGeometry.ProjVeroneseRestrict (mem_graded_of_eq)
open Stacks.GradedLocalization (gradedPiece smul_mem_gradedPiece)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.TensorPowerTrivialize (resTop)
open Stacks.TensorPowers (natTensorPow)
open scoped Stacks.GradedLocalization

universe u w

namespace Stacks.AlgebraicGeometry.ProjChartGradedAlphaMaps

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {f : A} {d : ℕ}

/-! ### `f / 1` generates the degree-`d` part of `A_f` -/

/-- **The degree-`d` part of `A_f` is generated by the single element `f / 1` over the degree-zero
subring `A_{(f)}`**, for `f` homogeneous of degree `d`.

A fraction of `A_f`-degree `d` is `x / f ^ j` with `x` homogeneous of degree `j d + d`
(`Stacks.AlgebraicGeometry.ProjChartGradedDivision.exists_rep`); since `(j + 1) d = j d + d`, the
fraction `x / f ^ (j + 1)` is an element of `A_{(f)}`, and multiplying it by `f / 1` returns
`x / f ^ j`. -/
theorem exists_smul_mk_one (hf : f ∈ 𝒜 d)
    (y : gradedPiece 𝒜 (integerGrading (S := A) 𝒜) f (d : ℤ)) :
    ∃ r : HomogeneousLocalization.Away 𝒜 f,
      (y : LocalizedModule.Away f A)
        = HomogeneousLocalization.val r • LocalizedModule.mk f (1 : Submonoid.powers f) := by
  obtain ⟨j, x, hx, hy⟩ := exists_rep (𝒜 := 𝒜) (d := d) d y hf
  have hx' : x ∈ 𝒜 ((j + 1) • d) :=
    mem_graded_of_eq 𝒜 (by simp only [smul_eq_mul]; ring) hx
  refine ⟨HomogeneousLocalization.Away.mk 𝒜 hf (j + 1) x hx', ?_⟩
  rw [HomogeneousLocalization.Away.val_mk, hy, LocalizedModule.mk_smul_mk]
  exact LocalizedModule.mk_eq.2 ⟨1, by simp [Submonoid.smul_def, smul_eq_mul, pow_succ]; ring⟩

section Alpha

variable {T : Scheme.{u}} {L : T.Modules} [Stacks.Ample.IsInvertibleModule T L]
  (ψ : GradedSections 𝒜 L) (hd : 0 < d)
  (hgen : ⨆ g : 𝒜 d, nonvanishingOpen T (natTensorPow L d) (ψ.toFun d g) = ⊤)

/-! ### Agreement on the degree-`d` section of an arbitrary homogeneous element -/

/-- **The comparison `θ` of [Stacks, Tag 01NK] and the isomorphism `α` of [Stacks, Tag 01N8] agree
on the degree-`d` section of every `a ∈ 𝒜 d`**, on the chart cut out by any `f ∈ 𝒜 d`.

For `V` an open of `T` on which `ψ(f)` does not vanish, the value of the chart-level comparison
`θ_f` on the fraction `a / 1` of `A_f`-degree `d` is the restriction to `V` of the value of `α` on
the pullback of the degree-`d` section of `a`. Both are `ψ(a)|_V`: the left side by clause (2) of
[Stacks, Tag 01NK] read on the chart of `f`
(`Stacks.AlgebraicGeometry.ProjChartGradedClauseTwo.chartSection_mk_one`), the right side by
`Stacks.AlgebraicGeometry.ProjChartGradedAlphaMatch.alphaVeronese_hom_app_top`.

The element `a` is unconstrained apart from its degree, so this is the agreement of `θ_f` with `α`
on the whole image of the map of [Stacks, Tag 01MP] in degree `d`; the sibling file's
`chartSection_eq_alphaVeronese` is the case `a = f`. -/
theorem chartSection_eq_alphaVeronese_of_mem (hf : f ∈ 𝒜 d) {V : T.Opens}
    (hV : V ≤ nonvanishingOpen T (natTensorPow L d) (ψ.toFun d ⟨f, hf⟩))
    {a : A} (ha : a ∈ 𝒜 d)
    (y : gradedPiece 𝒜 (integerGrading (S := A) 𝒜) f (d : ℤ))
    (hrep : (y : LocalizedModule.Away f A)
      = LocalizedModule.mk a (1 : Submonoid.powers f)) :
    chartSection ψ hf hV d y
      = resTop (natTensorPow L d) ((alphaVeronese 𝒜 ψ hd hgen).hom.app ⊤
          (pullbackDegreeSection 𝒜 (gluedVeronese 𝒜 ψ hd hgen) ⟨a, ha⟩)) V :=
  (chartSection_mk_one ψ hf hV d ha y hrep).trans
    (congrArg (fun z => resTop (natTensorPow L d) z V)
      (alphaVeronese_hom_app_top 𝒜 ψ hd hgen a ha).symm)

/-- **The same agreement with the identification `Γ(D₊(f), 𝒪_X(d)) ≅ (A_f)_d` composed in**, for an
arbitrary `a ∈ 𝒜 d`.

The global section of `𝒪_X(d)` attached to `a` by [Stacks, Tag 01MP], restricted to `D₊(f)` and
read in `(A_f)_d`, is the fraction `a / 1`
(`Stacks.AlgebraicGeometry.ProjTwistAwayPiece.coe_sectionsTwistEquivGradedPiece_degreeSection`), so
this is `chartSection_eq_alphaVeronese_of_mem` at that element. -/
theorem chartSection_degreeSection_eq_alphaVeronese_of_mem (hf : f ∈ 𝒜 d) {V : T.Opens}
    (hV : V ≤ nonvanishingOpen T (natTensorPow L d) (ψ.toFun d ⟨f, hf⟩))
    {a : A} (ha : a ∈ 𝒜 d) :
    chartSection ψ hf hV d
        (sectionsTwistEquivGradedPiece 𝒜 hf hd (d : ℤ)
          ((twistingSheaf 𝒜 (d : ℤ)).val.map
            (homOfLE (le_top : ProjectiveSpectrum.basicOpen 𝒜 f ≤ ⊤)).op
            (degreeSection 𝒜 d ⟨a, ha⟩)))
      = resTop (natTensorPow L d) ((alphaVeronese 𝒜 ψ hd hgen).hom.app ⊤
          (pullbackDegreeSection 𝒜 (gluedVeronese 𝒜 ψ hd hgen) ⟨a, ha⟩)) V :=
  chartSection_eq_alphaVeronese_of_mem 𝒜 ψ hd hgen hf hV ha _
    (coe_sectionsTwistEquivGradedPiece_degreeSection 𝒜 hf hd d ⟨a, ha⟩)

/-! ### `θ|_V = α` as an equality of maps -/

/-- Every `y ∈ (A_f)_d` is `r • g` for a coefficient `r ∈ A_{(f)}` and the generator `g = f / 1`,
whose `θ_f`-value is that of `α`. -/
private theorem exists_smul_generator_chartSection (hf : f ∈ 𝒜 d) {V : T.Opens}
    (hV : V ≤ nonvanishingOpen T (natTensorPow L d) (ψ.toFun d ⟨f, hf⟩))
    (y : gradedPiece 𝒜 (integerGrading (S := A) 𝒜) f (d : ℤ)) :
    ∃ (r : HomogeneousLocalization.Away 𝒜 f)
      (g : gradedPiece 𝒜 (integerGrading (S := A) 𝒜) f (d : ℤ)),
      (g : LocalizedModule.Away f A) = LocalizedModule.mk f (1 : Submonoid.powers f) ∧
      chartSection ψ hf hV d g
        = resTop (natTensorPow L d) ((alphaVeronese 𝒜 ψ hd hgen).hom.app ⊤
            (pullbackDegreeSection 𝒜 (gluedVeronese 𝒜 ψ hd hgen) ⟨f, hf⟩)) V ∧
      y = ⟨HomogeneousLocalization.val r • (g : LocalizedModule.Away f A),
        smul_mem_gradedPiece 𝒜 _ hf (d : ℤ) r g.2⟩ := by
  obtain ⟨r, hr⟩ := exists_smul_mk_one 𝒜 hf y
  have hg := coe_sectionsTwistEquivGradedPiece_degreeSection 𝒜 hf hd d ⟨f, hf⟩
  exact ⟨r, _, hg, chartSection_degreeSection_eq_alphaVeronese 𝒜 ψ hd hgen f hf hV,
    Subtype.ext (hr.trans (congrArg (HomogeneousLocalization.val r • ·) hg.symm))⟩

/-- **`θ_f` is the unique `A_{(f)}`-semilinear map on `(A_f)_d` whose value at `f / 1` is the
restriction of `α`'s**, which is the clause `θ|_V = α` of the final assertion of [Stacks, Tag 01NK]
read as an equality of maps on the chart of `f`.

No additivity is asked of `F`: the degree-`d` part of `A_f` is a cyclic `A_{(f)}`-module generated
by `f / 1` (`exists_smul_mk_one`), so semilinearity along the dehomogenisation ring map together
with the one value at the generator already determines `F` everywhere. The value of `θ_f` at the
generator is `α`'s by
`Stacks.AlgebraicGeometry.ProjChartGradedAlphaMatch.chartSection_degreeSection_eq_alphaVeronese`,
and `θ_f` is semilinear by
`Stacks.AlgebraicGeometry.ProjChartGradedDivision.chartSection_smul`; so `θ_f` itself satisfies the
two hypotheses, and the conclusion says every map that does is `θ_f`. -/
theorem eq_chartSection_of_smul_of_alpha (hf : f ∈ 𝒜 d) {V : T.Opens}
    (hV : V ≤ nonvanishingOpen T (natTensorPow L d) (ψ.toFun d ⟨f, hf⟩))
    (F : gradedPiece 𝒜 (integerGrading (S := A) 𝒜) f (d : ℤ) → Γ(natTensorPow L d, V))
    (hsmul : ∀ (r : HomogeneousLocalization.Away 𝒜 f)
        (y : gradedPiece 𝒜 (integerGrading (S := A) 𝒜) f (d : ℤ)),
        F ⟨HomogeneousLocalization.val r • (y : LocalizedModule.Away f A),
            smul_mem_gradedPiece 𝒜 _ hf (d : ℤ) r y.2⟩
          = (ψ.homogeneousRatios hf hV).lift hd r • F y)
    (halpha : ∀ y : gradedPiece 𝒜 (integerGrading (S := A) 𝒜) f (d : ℤ),
        (y : LocalizedModule.Away f A) = LocalizedModule.mk f (1 : Submonoid.powers f) →
        F y = resTop (natTensorPow L d) ((alphaVeronese 𝒜 ψ hd hgen).hom.app ⊤
            (pullbackDegreeSection 𝒜 (gluedVeronese 𝒜 ψ hd hgen) ⟨f, hf⟩)) V) :
    F = chartSection ψ hf hV d := by
  funext y
  obtain ⟨r, g, hg, hθg, hy⟩ := exists_smul_generator_chartSection 𝒜 ψ hd hgen hf hV y
  rw [hy, hsmul, chartSection_smul ψ hf hV hd d r g, halpha g hg, hθg]

/-- **The value of `θ_f` at an arbitrary element of `(A_f)_d` is a multiple of `α`'s value at the
degree-`d` section of `f`**, the multiple being the coefficient in `A_{(f)}` that writes the
element over the generator `f / 1`.

This is `exists_smul_mk_one` together with the semilinearity of `θ_f`; it is the computational form
of `eq_chartSection_of_smul_of_alpha`. -/
theorem chartSection_eq_smul_alphaVeronese (hf : f ∈ 𝒜 d) {V : T.Opens}
    (hV : V ≤ nonvanishingOpen T (natTensorPow L d) (ψ.toFun d ⟨f, hf⟩))
    (y : gradedPiece 𝒜 (integerGrading (S := A) 𝒜) f (d : ℤ)) :
    ∃ r : HomogeneousLocalization.Away 𝒜 f,
      (y : LocalizedModule.Away f A)
          = HomogeneousLocalization.val r • LocalizedModule.mk f (1 : Submonoid.powers f) ∧
        chartSection ψ hf hV d y
          = (ψ.homogeneousRatios hf hV).lift hd r •
            resTop (natTensorPow L d) ((alphaVeronese 𝒜 ψ hd hgen).hom.app ⊤
              (pullbackDegreeSection 𝒜 (gluedVeronese 𝒜 ψ hd hgen) ⟨f, hf⟩)) V := by
  obtain ⟨r, g, hg, hθg, hy⟩ := exists_smul_generator_chartSection 𝒜 ψ hd hgen hf hV y
  refine ⟨r, (congrArg Subtype.val hy).trans (congrArg (HomogeneousLocalization.val r • ·) hg),
    ?_⟩
  rw [hy, chartSection_smul ψ hf hV hd d r g, hθg]

end Alpha

end Stacks.AlgebraicGeometry.ProjChartGradedAlphaMaps

end
