module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.EmbeddingIntoAffineSpace
public import StacksFrontier.Examples.Spaces.AffineOverSpaceNoImmersion

/-!
# Local separatedness cannot be dropped from Stacks 088L

Stacks 088L says that an affine scheme `U` locally of finite type over a quasi-separated,
locally separated algebraic space `X` admits an immersion into a relative affine space
`𝔸ⁿ_X` over `X`.  Stacks 088M records two things about that lemma: that the hypothesis
that `X` be locally separated cannot be dropped, by the example of Stacks 088V, and an
open question — whether the lemma survives dropping quasi-separatedness instead — which
the Stacks project asks the reader to answer by email.  Only the first is a mathematical
assertion, and it is the only one formalized here; the question is not stated as a
theorem, a conjecture, or an existence claim anywhere in this file.

The witness is the one of Stacks 088W: over a field in which two is invertible, the chart
`𝔸¹_k ⟶ 𝔸¹_k/R` of the quotient of Stacks 02Z1 by the diagonal together with the graph of
negation on the punctured line.  Its source is affine, it is of finite type, its target is
a quasi-separated algebraic space, and no immersion of the source into relative affine
space over the target exists.  By Stacks 088L the target is therefore not locally
separated, which is the hypothesis the remark is about.

## Main results

* `AlgebraicGeometry.Space.exists_not_isAbsolutelyLocallySeparated_not_isImmersion`: the
  statement of Stacks 088M, derived through Stacks 088L.  Stacks 088M itself is
  `AlgebraicGeometry.Space.exists_not_isAbsolutelyLocallySeparated_not_isImmersion'` in
  `StacksFrontier/AlgebraicGeometry/Spaces/Limits/EmbeddingIntoAffineSpaceSharpUnconditional.lean`,
  which needs none of the hypotheses `hreg`, `hdiag`, `hchart` of this file.

## Implementation notes

The negation of local separatedness is obtained here from Stacks 088L by contraposition,
from the failure of the conclusion of Stacks 088L.  The half of Stacks 02Z1 asserting that
this quotient is not locally separated is proved directly, as
`AlgebraicGeometry.AffineLineInvolution.not_isAbsolutelyLocallySeparated_involutionQuotient`
in `StacksFrontier/Examples/Spaces/AffineLineInvolutionNotLocallySeparated.lean`, and the
unconditional form of Stacks 088M uses it instead.

Regularity of the site's size cutoff is used because this development's Stacks 088L
carries a cardinality side condition on the sections of `U`, which Stacks 088L itself does
not have; `AlgebraicGeometry.Space.exists_isImmersion_affineSpaceOver_of_isRegular` is the
form in which that condition disappears, and the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/EmbeddingIntoAffineSpace.lean` explain why it
cannot simply be removed.  The hypothesis cannot be discharged here, since the witness
arrives inside an existential statement and its ring of sections is therefore not
available to be bounded.

`hdiag` and `hchart` are inherited verbatim from Stacks 088W, which is conditional on them
in this library; they are the two undischarged inputs of Stacks 0265 here, documented at
`AlgebraicGeometry.Space.IsEffectiveDescentAlongCoveringSieve` in
`StacksFrontier/AlgebraicGeometry/Spaces/QuotientSheafAlgebraic.lean`.

## References

* [Stacks Project, Tag 088M](https://stacks.math.columbia.edu/tag/088M)
* [Stacks Project, Tag 088L](https://stacks.math.columbia.edu/tag/088L)
* [Stacks Project, Tag 088W](https://stacks.math.columbia.edu/tag/088W)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- The statement of Stacks 088M, reached through Stacks 088L: the hypothesis of Stacks
088L that `X` be locally separated cannot be dropped.  Stacks 088M itself is the primed
`exists_not_isAbsolutelyLocallySeparated_not_isImmersion'`, with no `hreg`, `hdiag` or
`hchart`.

Over a field in which two is invertible there is a finite type morphism `f : Y ⟶ X` of
algebraic spaces with `Y` an affine scheme and `X` quasi-separated — so every hypothesis
of Stacks 088L except local separatedness holds — such that `X` is *not* locally separated
and `Y` admits no immersion over `X` into relative affine `n`-space over `X`, for any `n`.

The witness is the one of Stacks 088W, the chart `𝔸¹_k ⟶ 𝔸¹_k/R` of Stacks 02Z1; failure
of local separatedness is read off from the failure of the conclusion of Stacks 088L by
contraposition, which is what `hreg` is for.  See the implementation notes of this file for
`hreg`, `hdiag` and `hchart`, none of which Stacks 088M has.

The remark also raises the question whether Stacks 088L holds without quasi-separatedness.
That is an open question, not a result, and nothing here formalizes it. -/
theorem exists_not_isAbsolutelyLocallySeparated_not_isImmersion
    (k : Type u) [Field k] (hchar : (2 : k) ≠ 0)
    (B : BigFppfSite.{u}) (hreg : B.cutoff.IsRegular)
    (hS : B.Contains (Spec (.of k))) (hZ : B.Contains (⊤_ Scheme.{u}))
    [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hS) (Type u)]
    (_hdiag : IsEffectiveDescentAlongCoveringSieve B (Spec (.of k)) hS
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType))
    (_hchart : IsEffectiveDescentAlongCoveringSieve B (Spec (.of k)) hS
      (@_root_.AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓
        @LocallyOfFiniteType ⊓ @Surjective ⊓ @Etale : MorphismProperty Scheme.{u})) :
    ∃ (Y : BigFppfOver B (Spec (.of k)) hS)
      (X : (BigFppfOver B (Spec (.of k)) hS)ᵒᵖ ⥤ Type u)
      (f : yoneda.obj Y ⟶ X),
      IsAffine ((BigFppfOver.toScheme B (Spec (.of k)) hS).obj Y) ∧
      IsAlgebraicSpace B (Spec (.of k)) hS X ∧
      IsFiniteType B (Spec (.of k)) hS f ∧
      IsAbsolutelyQuasiSeparated B (Spec (.of k)) hS hZ X ∧
      ¬ IsAbsolutelyLocallySeparated B (Spec (.of k)) hS hZ X ∧
      ∀ (n : ℕ) (j : yoneda.obj Y ⟶ affineSpaceOver B (Spec (.of k)) hS X n),
        j ≫ prod.fst = f → ¬ IsImmersion B (Spec (.of k)) hS j := by
  obtain ⟨Y, X, f, hY, -, hX, hft, hqs, hno⟩ :=
    Stacks.Examples.exists_finiteType_affine_not_immersion_into_affineSpace
      k hchar B hS hZ
  refine ⟨Y, X, f, hY, hX, hft, hqs, ?_, hno⟩
  intro hls
  obtain ⟨n, j, hjf, hjim⟩ := exists_isImmersion_affineSpaceOver_of_isRegular
    B (Spec (.of k)) hS hZ hreg Y X f hY hX hft.1 hls
  exact hno n j hjf hjim

end AlgebraicGeometry.Space

end
