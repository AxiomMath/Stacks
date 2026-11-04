module

public import StacksFrontier.AlgebraicGeometry.ProjBundleProjectiveSpace.Charts

/-!
# The chart data of a projective space, cut down to a family of maps to the integral model

`Stacks.AlgebraicGeometry.RelativeProjIsProjectiveSpace.ProjectiveSpaceCharts` asks, for each
affine open `U` of the base, for an isomorphism `Proj Γ(U, 𝒜) ≅ ℙⁿ_U` *over* `U` and compatible
with the transitions. This file replaces that by strictly less data.

`ℙⁿ_U` is the product of `U` with the integral model over the terminal scheme, so a morphism
`Proj Γ(U, 𝒜) ⟶ ℙⁿ_U` over `U` is *exactly* a morphism `Proj Γ(U, 𝒜) ⟶ ℙⁿ_ℤ`: the first
component is forced to be the structure morphism of the chart and the commutativity obligation
of the lift is uniqueness of a morphism to the terminal scheme. So the data reduces to a
compatible family of morphisms to the integral model, and the "over `U`" half of
`ProjectiveSpaceCharts` becomes free.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjIsProjectiveSpace.IntegralCharts`: a family of morphisms
  from the charts to the integral model `AlgebraicGeometry.projectiveSpaceAtUniverse n`,
  compatible with the transition morphisms. **This is the whole of the data.**
* `Stacks.AlgebraicGeometry.RelativeProjIsProjectiveSpace.IntegralCharts.chart`: the induced
  morphism `Proj Γ(U, 𝒜) ⟶ ℙⁿ_U`.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjIsProjectiveSpace.IntegralCharts.toProjectiveSpaceCharts`:
  **once each `chart` is an isomorphism, the chart data of a projective space is complete** — so
  the global statement `Proj_S(𝒜) ≅ ℙⁿ_S` over `S` follows from
  `Stacks.AlgebraicGeometry.RelativeProjIsProjectiveSpace.ProjectiveSpaceCharts.schemeIso`.
* `Stacks.AlgebraicGeometry.RelativeProjIsProjectiveSpace.IntegralCharts.exists_schemeIso`: that
  conclusion, stated outright.

## Implementation notes

**The compatibility is proved generically and instantiated.** The statement of
`ProjectiveSpaceCharts.iso_transition` mentions `AlgebraicGeometry.Scheme.homOfLE` applied to
`AlgebraicGeometry.Scheme.AffineZariskiSite.toOpens_mono`, and
`AlgebraicGeometry.Scheme.AffineZariskiSite` is a `def` for a subtype, so a goal carrying that
term is not type-correct at `implicit` transparency and `rw [Category.assoc]` on it fails with
"did not find an occurrence of the pattern" on a pattern that is present. The proof is therefore
`IntegralCharts.chart_transition_of`, in which the transition morphism and the inclusion of the
affine opens are both plain **variables**, instantiated by `exact`, which elaborates at default
transparency. This is the standard way around that failure.

## References

* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)

## Not done here

No project tag is attached, and `IntegralCharts` is not constructed for any graded algebra. For
the sheafified symmetric algebra of a free module the family of morphisms to the integral model
should be `AlgebraicGeometry.Proj.map` of the graded ring homomorphism from the integral
polynomial grading determined by a graded identification of `Γ(U, Sym(𝒪_S^{⊕(n+1)}))` with
`Γ(S, U)[T₀, …, Tₙ]`, in which case the compatibility is
`AlgebraicGeometry.Proj.map_comp` together with
`Stacks.AlgebraicGeometry.RelativeProj.mapHomOfTop_eq_map`. Note that
`AlgebraicGeometry.projectiveSpaceAtUniverse` is a plain `def`, so a term mixing it with
`AlgebraicGeometry.Proj` of the integral polynomial grading is type-correct only at default
transparency; the existing workaround is
`Stacks.AlgebraicGeometry.ProjPolyChart.coordinateProjMap`, which is `Proj.map` already retyped
as a morphism into `projectiveSpaceAtUniverse`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.RelativeProj Stacks.AlgebraicGeometry.RelativeProjGlue

namespace Stacks.AlgebraicGeometry.RelativeProjIsProjectiveSpace

universe u

variable {S : Scheme.{u}} (𝒜 : GradedAlgebra S) (n : ℕ)

/-- **A compatible family of morphisms from the charts of `Proj_S(𝒜)` to the integral model of
projective `n`-space.** This is all the data `ProjectiveSpaceCharts` needs. -/
public structure IntegralCharts where
  /-- The morphism from the chart over an affine open to the integral model. -/
  toIntegral (U : S.AffineZariskiSite) :
    𝒜.projOver U ⟶ projectiveSpaceAtUniverse.{u} n
  /-- The morphisms are compatible with the transition morphisms. -/
  toIntegral_transition {U V : S.AffineZariskiSite} (φ : U ⟶ V) :
    (chartFunctor 𝒜).map φ ≫ toIntegral V = toIntegral U

namespace IntegralCharts

variable {𝒜 n} (hd : IntegralCharts 𝒜 n)

/-- The induced morphism from the chart over an affine open `U` to `ℙⁿ_U`: the structure
morphism of the chart and the given morphism to the integral model, assembled by the universal
property of the product over the terminal scheme. -/
public def chart (U : S.AffineZariskiSite) :
    𝒜.projOver U ⟶ projectiveSpaceOver n U.toOpens.toScheme :=
  pullback.lift (𝒜.toOpen U) (hd.toIntegral U) (terminal.hom_ext _ _)

/-- The induced morphism is a morphism over the affine open. -/
@[reassoc (attr := simp)]
public theorem chart_fst (U : S.AffineZariskiSite) :
    hd.chart U ≫ pullback.fst _ _ = 𝒜.toOpen U :=
  pullback.lift_fst _ _ _

/-- The induced morphism recovers the given morphism to the integral model. -/
@[reassoc (attr := simp)]
public theorem chart_snd (U : S.AffineZariskiSite) :
    hd.chart U ≫ pullback.snd _ _ = hd.toIntegral U :=
  pullback.lift_snd _ _ _

/-- **The generic form of the compatibility of the induced morphisms.** The transition morphism
and the inclusion of the affine opens are plain variables, so that the statement is type-correct
at every transparency; see the implementation notes. -/
public theorem chart_transition_of {U V : S.AffineZariskiSite}
    (τ : 𝒜.projOver U ⟶ 𝒜.projOver V) (t : U.toOpens.toScheme ⟶ V.toOpens.toScheme)
    (h₁ : τ ≫ 𝒜.toOpen V = 𝒜.toOpen U ≫ t)
    (h₂ : τ ≫ hd.toIntegral V = hd.toIntegral U) :
    τ ≫ hd.chart V = hd.chart U ≫ ProjectiveSpaceBaseChange.map n t := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, hd.chart_fst, h₁, ProjectiveSpaceBaseChange.comp_map_comp_fst,
      hd.chart_fst]
  · rw [Category.assoc, hd.chart_snd, h₂, ProjectiveSpaceBaseChange.comp_map_comp_snd,
      hd.chart_snd]

/-- The induced morphisms are compatible with the transition morphisms. -/
public theorem chart_transition {U V : S.AffineZariskiSite} (φ : U ⟶ V) :
    (chartFunctor 𝒜).map φ ≫ hd.chart V =
      hd.chart U ≫ ProjectiveSpaceBaseChange.map n
        (S.homOfLE (Scheme.AffineZariskiSite.toOpens_mono φ.le)) :=
  hd.chart_transition_of _ _
    (𝒜.transition_toOpen (Scheme.AffineZariskiSite.toOpens_mono φ.le)
      (RelativeProjGlue.mapDomain_res_eq_top_of_le 𝒜 φ.le _))
    (hd.toIntegral_transition φ)

/-- **The chart data of a projective space**, from a compatible family of morphisms to the
integral model each of which induces an isomorphism onto `ℙⁿ_U`. -/
public def toProjectiveSpaceCharts (hiso : ∀ U : S.AffineZariskiSite, IsIso (hd.chart U)) :
    ProjectiveSpaceCharts 𝒜 n where
  iso U := haveI := hiso U; asIso (hd.chart U)
  iso_fst U := hd.chart_fst U
  iso_transition φ := hd.chart_transition φ

/-- **`Proj_S(𝒜) ≅ ℙⁿ_S` over `S`**, from a compatible family of morphisms to the integral model
each of which induces an isomorphism onto the relative projective space over its affine open. -/
public theorem exists_schemeIso (hiso : ∀ U : S.AffineZariskiSite, IsIso (hd.chart U)) :
    ∃ e : relativeProj 𝒜 ≅ projectiveSpaceOver n S,
      e.hom ≫ pullback.fst (terminal.from S)
        (terminal.from (projectiveSpaceAtUniverse.{u} n)) = relativeProjToBase 𝒜 :=
  ⟨(hd.toProjectiveSpaceCharts hiso).schemeIso,
    (hd.toProjectiveSpaceCharts hiso).schemeIso_hom_fst⟩

end IntegralCharts

end Stacks.AlgebraicGeometry.RelativeProjIsProjectiveSpace

end
