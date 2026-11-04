module

public import StacksFrontier.AlgebraicGeometry.AmpleNoetherianReduction.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleThickeningLimit.Converse

/-!
# Stacks Tag 09P0: an ample invertible sheaf on a scheme whose reduction is a curve

[Stacks, Tag 09P0](https://stacks.math.columbia.edu/tag/09P0) is a remark attached to
[Tag 09NZ](https://stacks.math.columbia.edu/tag/09NZ):

> In fact, if `X` is a scheme whose reduction is a Noetherian separated scheme of dimension `1`,
> then `X` has an ample invertible sheaf.  The argument to prove this is the same as the proof of
> Proposition 09NZ except one uses Limits, Lemma 09MW instead of Cohomology of Schemes,
> Lemma 09MS.

`./Basic.lean` carries that route out, granted the converse half of
[Stacks, Tag 09MW] as the hypothesis
`Stacks.AmpleNoetherianReduction.AmpleDescendsAlongThickening`. That converse is now proved, as
`Stacks.AmpleThickeningLimit.isAmple_of_isAmple_modulePullback_of_isHomeomorph`, so this file
discharges the hypothesis and states the remark with no hypothesis beyond the source's.

## The dimension hypothesis

The source says the reduction has dimension `1`. The statement below asks only that its
dimension be at most `1`, which is weaker, so the theorem is more general than the source.

## Main results

* `Stacks.AmpleNoetherianReduction.ampleDescendsAlongThickening`:
  `Stacks.AmpleNoetherianReduction.AmpleDescendsAlongThickening`, proved.
* `Stacks.AmpleNoetherianReduction.exists_isAmple_of_reduction_of_topologicalKrullDim_le_one`:
  **[Stacks, Tag 09P0]**.

## References

* [Stacks Project, Tag 09P0](https://stacks.math.columbia.edu/tag/09P0)
* [Stacks Project, Tag 09NZ](https://stacks.math.columbia.edu/tag/09NZ)
* [Stacks Project, Tag 09MW](https://stacks.math.columbia.edu/tag/09MW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.IdealSheafData
open Stacks.Ample

universe u

namespace Stacks.AmpleNoetherianReduction

/-- **Ampleness descends along a surjective closed immersion.** This is the converse half of
[Stacks, Tag 09MW]: a surjective closed immersion is a closed embedding which is onto, hence a
homeomorphism of underlying spaces, and
`Stacks.AmpleThickeningLimit.isAmple_of_isAmple_modulePullback_of_isHomeomorph` applies. -/
theorem ampleDescendsAlongThickening : AmpleDescendsAlongThickening.{u} := by
  intro Z X i _ _ L _ h
  exact Stacks.AmpleThickeningLimit.isAmple_of_isAmple_modulePullback_of_isHomeomorph i L
    (isHomeomorph_iff_isEmbedding_surjective.mpr
      ⟨i.isClosedEmbedding.isEmbedding, i.surjective⟩) h

/-- **[Stacks, Tag 09P0].** A scheme whose reduction is a Noetherian separated scheme of
dimension at most one has an ample invertible sheaf.

The hypotheses are on the reduction `X_red = (vanishingIdeal ⊤).subscheme` only; `X` itself is
not assumed Noetherian. -/
@[stacks 09P0]
theorem exists_isAmple_of_reduction_of_topologicalKrullDim_le_one (X : Scheme.{u})
    [IsNoetherian (vanishingIdeal (⊤ : Closeds X)).subscheme]
    [(vanishingIdeal (⊤ : Closeds X)).subscheme.IsSeparated]
    (hdim : topologicalKrullDim ((vanishingIdeal (⊤ : Closeds X)).subscheme : Type u) ≤ 1) :
    ∃ (L : X.Modules) (hL : IsInvertibleModule X L), @IsAmple X L hL :=
  exists_isAmple_of_reduction X ampleDescendsAlongThickening hdim

end Stacks.AmpleNoetherianReduction

end
