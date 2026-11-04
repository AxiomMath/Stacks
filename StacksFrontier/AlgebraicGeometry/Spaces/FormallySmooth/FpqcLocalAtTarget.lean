module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.ChartGlue.Main061K
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmoothFpqcLocalAtTarget

/-!
# Formal smoothness of morphisms of algebraic spaces is fpqc local on the base

The class `AlgebraicGeometry.Space.FormallySmoothEtaleChartDescent`, the implication (3) ⟹ (1)
of Stacks 061K with condition (3) read on affine opens, holds for every big fppf site and every
base scheme. Consequently formal smoothness of morphisms of algebraic spaces is local on the base
for the fpqc topology (Stacks 06CS).

## Main results

* `AlgebraicGeometry.Space.formallySmoothEtaleChartDescent`: the implication (3) ⟹ (1) of
  Tag 061K with condition (3) read on affine opens.
* `AlgebraicGeometry.Space.formallySmooth_isLocalAtTarget_fpqc'`: **Stacks 06CS**, formal
  smoothness of morphisms of algebraic spaces is local on the base for the fpqc topology.

## References

* [Stacks Project, Tag 061K](https://stacks.math.columbia.edu/tag/061K)
* [Stacks Project, Tag 06CS](https://stacks.math.columbia.edu/tag/06CS)
* [Stacks Project, Tag 0D0F](https://stacks.math.columbia.edu/tag/0D0F)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

/-- **The implication (3) ⟹ (1) of [Stacks Project, Tag 061K], with condition (3) read on affine
opens.** A morphism of algebraic spaces over `S` with one commuting square of étale scheme charts,
the chart of the source surjective, whose scheme morphism is affine-locally formally smooth is
formally smooth. -/
instance formallySmoothEtaleChartDescent (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : FormallySmoothEtaleChartDescent B S hS where
  formallySmooth_of_holdsOnSurjectiveEtaleChart := by
    intro X Y f hX hY hsurj
    obtain ⟨U, V, a, b, ψ, ha, hb, haSurj, hdiag, hψ⟩ := hsurj
    exact formallySmooth_of_surjectiveEtaleChart_of_formallySmoothScheme B S hS hX hY a b ψ ha hb
      haSurj hdiag.symm
      (Stacks.Smooth.formallySmooth_of_formallySmooth_appLE _ fun W hW V₀ hV₀ e =>
        (Stacks.Smooth.formallySmoothAffineLocally_iff_appLE _).mp hψ ⟨V₀, hV₀⟩ ⟨W, hW⟩ e)

/-- Formal smoothness of morphisms of algebraic spaces over `S` is local on the base for the fpqc
topology of Stacks 03YH: for every fpqc covering `{Yᵢ ⟶ Y}` of algebraic spaces, a morphism
`f : X ⟶ Y` is formally smooth if and only if every base change `X ×_Y Yᵢ ⟶ Yᵢ` is. -/
@[stacks 06CS]
theorem formallySmooth_isLocalAtTarget_fpqc' (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    (formallySmoothProperty B S hS).IsLocalAtTarget
      (Topology.precoverage.{u, v} .fpqc B S hS) :=
  formallySmooth_isLocalAtTarget_fpqc_of_chartDescent.{u, v} B S hS
    (formallySmoothEtaleChartDescent B S hS)

end AlgebraicGeometry.Space

end
