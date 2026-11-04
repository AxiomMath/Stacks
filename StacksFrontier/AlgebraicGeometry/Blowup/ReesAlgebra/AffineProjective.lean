module

public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.BlowupTwist
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.Proper
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.AffineProjectiveImmersion

/-!
# The blowup of an affine scheme is projective over it

Let `X` be an affine scheme and `ℐ ⊆ 𝒪_X` a quasi-coherent sheaf of ideals which is finitely
generated on the whole of `X`. The Rees algebra is generated in degree one over every affine open
([Stacks, Tag 01OG]'s construction, `AlgebraicGeometry.reesSituation_isGeneratedInDegreeOne`), its
degree-zero identification is an isomorphism
(`AlgebraicGeometry.isIso_sectionRingZeroMap_reesSituation`), and its degree-one global sections
are spanned by the images of a finite generating set of `ℐ(X)`
(`AlgebraicGeometry.exists_finset_span_reesSituation_degreeOne`). Those are exactly the three
hypotheses of `Stacks.RelativeProj.Situation.topImmersion`, so the blowup immerses into a
projective space over `X`, over `X`, with the hyperplane sheaf pulling back to `𝒪_{X'}(1)`.

This is **part (1) of [Stacks, Tag 02NS] over an affine base** — the blowup morphism is
projective — in the concrete form the source's own proof produces: an immersion into `ℙⁿ_X` for
`n + 1` the number of generators of the ideal.

## Main results

* `AlgebraicGeometry.exists_isImmersion_blowUp_projectiveSpaceOver`: **the blowup of an affine
  scheme in a finitely generated quasi-coherent sheaf of ideals immerses into a projective space
  over that scheme, over it, and the hyperplane sheaf pulls back to the twisting sheaf
  `𝒪_{X'}(1)`.**

## Implementation notes

Part (1) of [Stacks, Tag 02NS] is about an arbitrary base, and what is below is its affine case.
The passage to an arbitrary base is the glueing of the local closed immersions, which needs the
comparison of the chart twists of [Stacks, Tag 01NO].

The finiteness hypothesis is asked only at the top open, which is the only open the argument looks
at; over an affine scheme that is no weaker than `AlgebraicGeometry.Scheme.IdealSheafData
.IsFiniteType`, since the top open is affine.

## References

* [Stacks Project, Tag 02NS](https://stacks.math.columbia.edu/tag/02NS)
* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} [IsAffine X] (I : X.IdealSheafData)

/-- **The blowup of an affine scheme in a finitely generated quasi-coherent sheaf of ideals
immerses into a projective space over that scheme.** The immersion lies over the base and the
hyperplane sheaf pulls back to `𝒪_{X'}(1)`.

This is part (1) of [Stacks, Tag 02NS] over an affine base, with the dimension of the projective
space given by a finite generating set of the ideal. -/
theorem exists_isImmersion_blowUp_projectiveSpaceOver
    (hfg : (I.ideal ⟨⊤, isAffineOpen_top X⟩).FG) :
    ∃ (n : ℕ) (r : blowUp I ⟶ AlgebraicGeometry.projectiveSpaceOver.{u} n X),
      IsImmersion r ∧
        r ≫ pullback.fst (terminal.from X)
            (terminal.from (AlgebraicGeometry.projectiveSpaceAtUniverse.{u} n)) =
          blowUpToBase I ∧
        Nonempty (blowUpTwist I 1 ≅ (Scheme.Modules.pullback r).obj
          (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n X)) := by
  obtain ⟨g, hg⟩ := exists_finset_span_reesSituation_degreeOne I ⟨⊤, isAffineOpen_top X⟩ hfg
  have hgen := reesSituation_isGeneratedInDegreeOne I ⟨⊤, isAffineOpen_top X⟩
  have hzero : Function.Surjective
      (Stacks.RelativeProj.Situation.sectionRingZeroMap (reesSituation I) ⊤).hom :=
    have := isIso_sectionRingZeroMap_reesSituation I ⟨⊤, isAffineOpen_top X⟩
    (ConcreteCategory.bijective_of_isIso
      (Stacks.RelativeProj.Situation.sectionRingZeroMap (reesSituation I) ⊤)).2
  refine ⟨g.card, Stacks.RelativeProj.Situation.topImmersion (reesSituation I) g hgen hg hzero,
    ?_, ?_, ?_⟩
  · exact Stacks.RelativeProj.Situation.isImmersion_topImmersion (reesSituation I) g hgen hg hzero
  · exact Stacks.RelativeProj.Situation.topImmersion_comp_fst (reesSituation I) g hgen hg hzero
  · exact Stacks.RelativeProj.Situation.nonempty_twistSheaf_iso_pullback_topImmersion
      (reesSituation I) g hgen hg hzero

end AlgebraicGeometry

end
