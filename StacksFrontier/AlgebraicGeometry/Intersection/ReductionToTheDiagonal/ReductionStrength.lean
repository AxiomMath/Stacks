module

public import StacksFrontier.AlgebraicGeometry.Intersection.ReductionToTheDiagonal.PositiveMultiplicity
public import StacksFrontier.AlgebraicGeometry.Intersection.ReductionToTheDiagonal.SerreMultiplicity

/-!
# How strong the reduction-to-the-diagonal hypothesis is

`Stacks.Intersection.ReductionToTheDiagonal` is a `Prop` quantified over **every** regular local
ring in a universe, with no ground field and no finiteness over one. This file measures it: it
implies Serre's positivity conjecture for a pair of cyclic modules over an arbitrary regular
local ring, the conjecture that
`StacksFrontier.AlgebraicGeometry.Intersection.ReductionToTheDiagonal.SerreMultiplicity` states as
`Stacks.Intersection.SerrePositivityConjecture` and leaves unproved.

So the hypothesis `h0B0U` of `Stacks.Intersection.localIntersectionMultiplicity_pos` and of
`Stacks.Intersection.intersectionMultiplicity_pos` cannot be discharged at the generality at
which it is stated: discharging it would prove, for every regular local ring `A` and ideals `I`,
`J` with `A ⧸ (I ⊔ J)` of dimension zero and
`dim A ≤ dim (A ⧸ I) + dim (A ⧸ J)`, that `∑ᵢ (-1)ⁱ length Torᵢ(A ⧸ I, A ⧸ J) > 0`. The
reduction to the diagonal that the source uses to prove this replaces `A` by a local ring of
`X ×_k X`, which is available for a local ring of a variety over a field and not for a regular
local ring in general — in mixed characteristic there need be no field at all, and for a complete
regular local ring the tensor square is not even Noetherian.

The positivity of `e(X, V · W, Z)` **is** proved in this development, at the source's hypotheses,
by `Stacks.Intersection.Diagonal.intersectionMultiplicity_pos_of_isRegular`, which carries
`@[stacks 0B0V]` and assumes no reduction: it is stated for a nonsingular variety over an
algebraically closed field, which is the setting of Stacks 0B0V, and the reduction to the
diagonal is proved there rather than assumed.

## Main results

* `Stacks.Intersection.serrePositivity_cyclic_of_reductionToTheDiagonal` — the reduction to the
  diagonal implies Serre's positivity conjecture for a pair of cyclic modules.

## Implementation notes

The hypotheses are literally those of `Stacks.Intersection.SerrePositivityConjecture` at
`M = A ⧸ I` and `N = A ⧸ J`, and the conclusion is literally its conclusion, so the statement
below is an instance of that conjecture and not a variant of it. Translating them into the two
numerical hypotheses of `Stacks.Intersection.localIntersectionMultiplicity_pos` is bookkeeping:
`(A ⧸ I) ⊗_A (A ⧸ J)` is `A ⧸ (I ⊔ J)` through
`TensorProduct.quotTensorEquivQuotSMul` and `Stacks.Intersection.quotSmulTopEquivQuotSup`, the
support dimension of a cyclic module is the dimension of the quotient ring, and in a local ring
two proper ideals have a proper join, which is what turns the inequality
`dim (A ⧸ (I ⊔ J)) ≤ 0` into the equality the hypothesis wants.

## References

* [Stacks Project, Tag 0B0V](https://stacks.math.columbia.edu/tag/0B0V)
* [Stacks Project, Tag 0B0U](https://stacks.math.columbia.edu/tag/0B0U)
* [Stacks Project, Tag 0B0X](https://stacks.math.columbia.edu/tag/0B0X)
* [Serre, *Algèbre locale. Multiplicités*][Serre_algebre_locale]
-/

@[expose] public section

open scoped TensorProduct

universe u

namespace Stacks.Intersection

/-- **The reduction to the diagonal implies Serre's positivity conjecture for cyclic modules.**
Assume `Stacks.Intersection.ReductionToTheDiagonal`. Let `A` be a regular local ring and `I`, `J`
ideals with `A ⧸ I` and `A ⧸ J` nonzero and `(A ⧸ I) ⊗_A (A ⧸ J)` supported in the maximal
ideal, and suppose `dim (Supp (A ⧸ I)) + dim (Supp (A ⧸ J)) = dim A`. Then
`χ(A ⧸ I, A ⧸ J) > 0`.

These are the hypotheses and the conclusion of
`Stacks.Intersection.SerrePositivityConjecture` at the cyclic pair `(A ⧸ I, A ⧸ J)`, a
conjecture this library states and does not prove. The reduction to the diagonal is therefore
not available at the generality at which
`Stacks.Intersection.ReductionToTheDiagonal` is stated, and the two statements that carry it as
an explicit hypothesis cannot be made unconditional there. At the source's hypotheses the
positivity is proved without any such hypothesis, by
`Stacks.Intersection.Diagonal.intersectionMultiplicity_pos_of_isRegular`. -/
theorem serrePositivity_cyclic_of_reductionToTheDiagonal (h0B0U : ReductionToTheDiagonal.{u})
    {A : Type u} [CommRing A] [IsRegularLocalRing A] (I J : Ideal A)
    [Nontrivial (A ⧸ I)] [Nontrivial (A ⧸ J)]
    (hsupp : Module.support A ((A ⧸ I) ⊗[A] (A ⧸ J)) ⊆ {IsLocalRing.closedPoint A})
    (hdim : Module.supportDim A (A ⧸ I) + Module.supportDim A (A ⧸ J) = ringKrullDim A) :
    0 < torEulerCharacteristic A (A ⧸ I) (A ⧸ J) := by
  have hsup : Module.supportDim A ((A ⧸ I) ⊗[A] (A ⧸ J)) =
      ringKrullDim (A ⧸ (I ⊔ J)) := by
    rw [Module.supportDim_eq_of_equiv (TensorProduct.quotTensorEquivQuotSMul (A ⧸ J) I),
      Module.supportDim_eq_of_equiv (quotSmulTopEquivQuotSup I J),
      Module.supportDim_quotient_eq_ringKrullDim]
  have hIne : I ≠ ⊤ := fun hI =>
    not_subsingleton (A ⧸ I) (Ideal.Quotient.subsingleton_iff.mpr hI)
  have hJne : J ≠ ⊤ := fun hJ =>
    not_subsingleton (A ⧸ J) (Ideal.Quotient.subsingleton_iff.mpr hJ)
  have hsupne : I ⊔ J ≠ ⊤ := by
    intro hst
    have hle : I ⊔ J ≤ IsLocalRing.maximalIdeal A :=
      sup_le (IsLocalRing.le_maximalIdeal hIne) (IsLocalRing.le_maximalIdeal hJne)
    rw [hst, top_le_iff] at hle
    exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top hle
  have hnt : Nontrivial (A ⧸ (I ⊔ J)) := by
    rw [← not_subsingleton_iff_nontrivial, Ideal.Quotient.subsingleton_iff]
    exact hsupne
  have h0 : ringKrullDim (A ⧸ (I ⊔ J)) = 0 := by
    refine le_antisymm
      (hsup ▸ supportDim_le_zero_of_support_subset_closedPoint _ hsupp) ?_
    exact (zero_le_ringKrullDim_iff_nontrivial (R := A ⧸ (I ⊔ J))).mpr hnt
  have hproper : ringKrullDim A ≤ ringKrullDim (A ⧸ I) + ringKrullDim (A ⧸ J) := by
    rw [← Module.supportDim_quotient_eq_ringKrullDim I,
      ← Module.supportDim_quotient_eq_ringKrullDim J]
    exact le_of_eq hdim.symm
  rw [← localIntersectionMultiplicity_eq_torEulerCharacteristic]
  exact localIntersectionMultiplicity_pos h0B0U I J h0 hproper

end Stacks.Intersection

end
