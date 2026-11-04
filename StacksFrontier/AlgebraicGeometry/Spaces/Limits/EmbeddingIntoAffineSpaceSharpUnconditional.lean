module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.EmbeddingIntoAffineSpaceSharp
public import StacksFrontier.Examples.Spaces.AffineLineInvolutionNotLocallySeparated

/-!
# Stacks 088M, with no hypothesis beyond the remark's

The statement of Stacks 088M — the hypothesis of Stacks 088L that `X` be locally separated cannot
be dropped — assembled from the two halves of the example of Stacks 088W and Stacks 02Z1 for the
concrete witness, so that nothing is assumed.  The failure of local separatedness is
`AlgebraicGeometry.AffineLineInvolution.not_isAbsolutelyLocallySeparated_involutionQuotient`, the
corresponding half of Stacks 02Z1, and the failure of the conclusion of Stacks 088L for the chart
is `Stacks.Examples.AffineOverAlgebraicSpace.not_isImmersion_affineSpaceOver_quotientSpaceMap`,
Stacks 088W for the same witness.  Stacks 088L is not used, so none of the three hypotheses of
`AlgebraicGeometry.Space.exists_not_isAbsolutelyLocallySeparated_not_isImmersion` in
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/EmbeddingIntoAffineSpaceSharp.lean` — which reaches
the same conclusion by contraposition through Stacks 088L — is needed here.

## Main results

* `AlgebraicGeometry.Space.exists_not_isAbsolutelyLocallySeparated_not_isImmersion'`:
  **Stacks 088M**.

## References

* [Stacks Project, Tag 088M](https://stacks.math.columbia.edu/tag/088M)
* [Stacks Project, Tag 088W](https://stacks.math.columbia.edu/tag/088W)
* [Stacks Project, Tag 02Z1](https://stacks.math.columbia.edu/tag/02Z1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

open Stacks.Examples.AffineOverAlgebraicSpace in
/-- **Stacks 088M**, the half of the remark which is a theorem: the hypothesis of Stacks
088L that `X` be locally separated cannot be dropped.

Over a field in which two is invertible there is a finite type morphism `f : Y ⟶ X` of
algebraic spaces with `Y` an affine scheme and `X` quasi-separated — so every hypothesis
of Stacks 088L except local separatedness holds — such that `X` is *not* locally separated
and `Y` admits no immersion over `X` into relative affine `n`-space over `X`, for any `n`.

The witness is the one of Stacks 088W, the chart `𝔸¹_k ⟶ 𝔸¹_k/R` of Stacks 02Z1, and the
failure of local separatedness is the corresponding half of Stacks 02Z1, so the conclusion
rests on nothing beyond what Stacks 088M itself assumes.  The unprimed
`exists_not_isAbsolutelyLocallySeparated_not_isImmersion` is the same conclusion reached
instead by contraposition through Stacks 088L, which costs three further hypotheses
(`hreg`, `hdiag`, `hchart`).

The remark also raises the question whether Stacks 088L holds without quasi-separatedness.
That is an open question, not a result, and nothing here formalizes it. -/
@[stacks 088M "the failure of 088L without local separatedness; the open question the \
remark raises about quasi-separatedness is not a theorem and is not formalized"]
theorem exists_not_isAbsolutelyLocallySeparated_not_isImmersion'
    (k : Type u) [Field k] (hchar : (2 : k) ≠ 0)
    (B : BigFppfSite.{u})
    (hS : B.Contains (Spec (.of k))) (hZ : B.Contains (⊤_ Scheme.{u}))
    [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hS) (Type u)] :
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
  have : NeZero (2 : k) := ⟨hchar⟩
  have := isEtaleEquivalenceRelation_relation k B hS
  refine ⟨AffineLineInvolution.affineLineChart k B hS, quotientSpace k B hS,
    quotientSpaceMap k B hS,
    inferInstance, isAlgebraicSpace_quotientSpace k B hS hchar,
    isFiniteType_quotientSpaceMap k B hS hchar hZ,
    isAbsolutelyQuasiSeparated_quotientSpace k B hS hchar hZ, ?_,
    not_isImmersion_affineSpaceOver_quotientSpaceMap k B hS⟩
  rw [quotientSpace_eq]
  exact AffineLineInvolution.not_isAbsolutelyLocallySeparated_involutionQuotient
    k B hS hchar hZ

end AlgebraicGeometry.Space

end
