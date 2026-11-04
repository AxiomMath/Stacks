module

public import StacksFrontier.AlgebraicGeometry.ProjBundleProjectiveSpace.BaseChange
public import StacksFrontier.AlgebraicGeometry.ProjBundleProjectiveSpace.Descent
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Assembled

/-!
# A relative homogeneous spectrum whose charts are projective spaces IS a projective space

`Stacks.Tag087S.IsHProjective` is *defined* as the existence of a closed immersion into
`AlgebraicGeometry.projectiveSpaceOver n S`, so nothing stated about relative `Proj` can reach it
until some relative `Proj` is identified with `ℙⁿ_S`. This file performs that identification from
purely **affine-local** input: if the chart of `Proj_S(𝒜)` over every affine open `U` of the base
is identified with `ℙⁿ_U` over `U`, compatibly with the transitions, then `Proj_S(𝒜) ≅ ℙⁿ_S` over
`S`.

The two inputs it consumes are therefore separated: everything global is done here, and what
remains for a particular `𝒜` is a statement about one affine open at a time.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjIsProjectiveSpace.ProjectiveSpaceCharts`: the
  affine-local input — an identification of each chart with a relative projective space over the
  affine open, over that open and compatible with the transitions.
* `Stacks.AlgebraicGeometry.RelativeProjIsProjectiveSpace.chartFamily`: the induced chart family
  on `ℙⁿ_S`.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjIsProjectiveSpace.ProjectiveSpaceCharts.schemeIso`:
  **`Proj_S(𝒜) ≅ ℙⁿ_S`**, with `schemeIso_hom_fst` recording that it is an isomorphism over `S`
  and `chart_schemeIso_hom` that it carries each chart to the given local identification.
* `Stacks.AlgebraicGeometry.RelativeProjIsProjectiveSpace.exists_iso_relativeProj`: the same for
  the assembled `Stacks.AlgebraicGeometry.RelativeProj.relativeProj` of a sheaf-level graded
  algebra, which is the form the projective bundle of a module is built at.

## Implementation notes

The three fields of `ProjectiveSpaceCharts` are exactly what
`Stacks.AlgebraicGeometry.RelativeProjDescent.ChartFamily` asks for, once
`Stacks.AlgebraicGeometry.ProjectiveSpaceBaseChange.isPullback_map` is available: cartesianness
of the chart of `ℙⁿ_S` over an affine open is base change of projective space, and the
compatibility of the charts with the transitions is the given compatibility composed with
functoriality of that base change. The isomorphism is then
`Stacks.AlgebraicGeometry.RelativeProjDescent.ChartFamily.iso`.

Nothing here is specific to the symmetric algebra, and nothing here needs `n` to be related to
`𝒜`: the relation is entirely inside the hypothesis.

## References

* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
* [Stacks Project, Tag 087S](https://stacks.math.columbia.edu/tag/087S)

## Not done here

**No project tag is attached.** The hypothesis `ProjectiveSpaceCharts` is not discharged for any
graded algebra in this file, and in particular not for the sheafified symmetric algebra of a free
module, which is what part (1) of Tag 087S needs. What that discharge requires, for
`𝒜 = Sym(𝒪_S^{⊕(n+1)})`, is a graded identification of the section ring
`Γ(U, Sym(𝒪_S^{⊕(n+1)}))` with the polynomial ring `Γ(S, U)[T₀, …, Tₙ]` natural in the affine
open `U`, after which
`Stacks.AlgebraicGeometry.ProjPolyChart.PolynomialComparison` — formalized as
`Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison`, which says precisely that
`Proj R[T₀, …, Tₙ] ≅ ℙⁿ_{Spec R}` over `Spec R` — supplies each `iso`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.RelativeProj Stacks.AlgebraicGeometry.RelativeProjGlue
open Stacks.AlgebraicGeometry.RelativeProjBridge

namespace Stacks.AlgebraicGeometry.RelativeProjIsProjectiveSpace

universe u

variable {S : Scheme.{u}} (𝒜 : GradedAlgebra S) (n : ℕ)

/-- **The affine-local identification of the charts of a relative homogeneous spectrum with
relative projective spaces.**

For each affine open `U` of the base an isomorphism of the chart `Proj Γ(U, 𝒜)` with `ℙⁿ_U`, over
`U`, and compatible with the transition morphisms of the chart functor: the transition from `U` to
`V` corresponds to the base change of `ℙⁿ` along the inclusion `U ⊆ V`. -/
public structure ProjectiveSpaceCharts where
  /-- The identification of the chart over an affine open with projective space over it. -/
  iso (U : S.AffineZariskiSite) : 𝒜.projOver U ≅ projectiveSpaceOver n U.toOpens.toScheme
  /-- The identification is an isomorphism over the affine open. -/
  iso_fst (U : S.AffineZariskiSite) :
    (iso U).hom ≫ pullback.fst _ _ = 𝒜.toOpen U
  /-- The identifications are compatible with the transition morphisms. -/
  iso_transition {U V : S.AffineZariskiSite} (φ : U ⟶ V) :
    (chartFunctor 𝒜).map φ ≫ (iso V).hom =
      (iso U).hom ≫ ProjectiveSpaceBaseChange.map n
        (S.homOfLE (Scheme.AffineZariskiSite.toOpens_mono φ.le))

namespace ProjectiveSpaceCharts

variable {𝒜 n} (hc : ProjectiveSpaceCharts 𝒜 n)

/-- The chart of `ℙⁿ_S` over an affine open `U` of `S`: the given identification of
`Proj Γ(U, 𝒜)` with `ℙⁿ_U`, followed by the base change of `ℙⁿ` along `U ⊆ S`. -/
public def chart (U : S.AffineZariskiSite) :
    𝒜.projOver U ⟶ projectiveSpaceOver n S :=
  (hc.iso U).hom ≫ ProjectiveSpaceBaseChange.map n U.toOpens.ι

/-- Each chart of `ℙⁿ_S` is cartesian over its affine open. -/
public theorem isPullback_chart (U : S.AffineZariskiSite) :
    IsPullback (𝒜.toOpen U) (hc.chart U) U.toOpens.ι
      (pullback.fst (terminal.from S)
        (terminal.from (projectiveSpaceAtUniverse.{u} n))) := by
  refine (ProjectiveSpaceBaseChange.isPullback_map n U.toOpens.ι).of_iso
    (hc.iso U).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · rw [Iso.symm_hom, Iso.refl_hom, Category.comp_id, ← hc.iso_fst U, Iso.inv_hom_id_assoc]
  · rw [Iso.symm_hom, Iso.refl_hom, Category.comp_id, chart, Iso.inv_hom_id_assoc]

/-- The charts of `ℙⁿ_S` are compatible with the transition morphisms. -/
public theorem chart_transition {U V : S.AffineZariskiSite} (φ : U ⟶ V) :
    (chartFunctor 𝒜).map φ ≫ hc.chart V = hc.chart U := by
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (hc.iso_transition φ)).trans ?_)
  exact ProjectiveSpaceBaseChange.comp_map_comp_map n _ _ _ _ (S.homOfLE_ι _)

/-- **Relative projective space carries the chart family of `𝒜`.** -/
public def chartFamily :
    RelativeProjDescent.ChartFamily 𝒜 (projectiveSpaceOver n S)
      (pullback.fst (terminal.from S)
        (terminal.from (projectiveSpaceAtUniverse.{u} n))) where
  chart := hc.chart
  isPullback := hc.isPullback_chart
  transition := hc.chart_transition

/-- **`Proj_S(𝒜) ≅ ℙⁿ_S`.** A relative homogeneous spectrum whose charts over the affine opens of
the base are relative projective spaces, compatibly, is itself a relative projective space. -/
public def schemeIso : relativeProj 𝒜 ≅ projectiveSpaceOver n S :=
  hc.chartFamily.iso

/-- The isomorphism is an isomorphism **over `S`**. -/
public theorem schemeIso_hom_fst :
    hc.schemeIso.hom ≫ pullback.fst (terminal.from S)
        (terminal.from (projectiveSpaceAtUniverse.{u} n)) = relativeProjToBase 𝒜 :=
  hc.chartFamily.iso_hom_comp

/-- The isomorphism carries each chart of `Proj_S(𝒜)` to the given local identification. -/
public theorem chart_schemeIso_hom (U : S.AffineZariskiSite) :
    RelativeProjGlue.chart 𝒜 U ≫ hc.schemeIso.hom = hc.chart U :=
  hc.chartFamily.chart_iso_hom U

end ProjectiveSpaceCharts

/-- **The assembled form.** For a sheaf-level graded algebra whose charts are projective spaces,
the relative homogeneous spectrum built by
`Stacks.AlgebraicGeometry.RelativeProj.relativeProj` is `ℙⁿ_S` over `S`.

This is the form `Stacks.Tag087SBundle.projectiveBundle` is built at, so it is the shape part (1)
of Stacks Tag 087S consumes. -/
public theorem exists_iso_relativeProj (A : SheafGradedAlgebra S) (n : ℕ)
    (hc : ProjectiveSpaceCharts A.toGradedAlgebra n) :
    ∃ e : (RelativeProj.relativeProj A).scheme ≅ projectiveSpaceOver n S,
      e.hom ≫ pullback.fst (terminal.from S)
        (terminal.from (projectiveSpaceAtUniverse.{u} n)) =
        (RelativeProj.relativeProj A).toBase :=
  ⟨hc.schemeIso, hc.schemeIso_hom_fst⟩

end Stacks.AlgebraicGeometry.RelativeProjIsProjectiveSpace

end
