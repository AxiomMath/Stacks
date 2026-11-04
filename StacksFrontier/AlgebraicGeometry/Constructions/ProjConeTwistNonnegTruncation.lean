module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeTwistAlgebraSheaf
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeTwistPuncturedAlgebraSheaf
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.NonnegTruncationFunctorial

/-!
# The nonnegative twist algebra is the nonnegative truncation of the integral one

`Stacks.AlgebraicGeometry.ProjConeTwist.nonnegTwistAlgebra` is `⨁_{m ≥ 0} 𝒪_P(m)`, built by a
match on the constructors of `ℤ` from the twisting sheaves and the zero sheaf, and
`Stacks.AlgebraicGeometry.NonnegTruncation.nonnegTruncation` is the general nonnegative
truncation of a sheaf of graded algebras, built by the same match. **This file records that the
two agree**, so that the general truncation's functoriality applies to the left-hand entries of
[Stacks, Tag 0EKG]'s diagram.

The agreement is definitional and the proof is `rfl`: `nonnegTwistingSheaf` and
`Stacks.AlgebraicGeometry.NonnegTruncation.piece` of `integerTwistAlgebra` are the same match,
`nonnegTwistMul` and `…NonnegTruncation.mul` likewise, the zero bilinear maps agreeing by proof
irrelevance in their two `Prop`-valued fields, and the units are `twistOne 𝒜` on both sides.
Nothing has to be transported.

## Main results

* `Stacks.AlgebraicGeometry.ProjConeTwist.nonnegTwistAlgebra_eq_nonnegTruncation`: **the algebra
  of nonnegative twists is the nonnegative truncation of the algebra of all integral twists.**
* `Stacks.AlgebraicGeometry.ProjConeTwist.nonnegTwistAlgebraSheaf_eq`: the same, read between
  the algebra sheaves, so that a relative spectrum named with one is named with the other.

## References

* [Stacks Project, Tag 0EKG](https://stacks.math.columbia.edu/tag/0EKG)
* [Stacks Project, Tag 01CF](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.ProjConeTwist

variable {A : Type u} {σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- **The algebra of nonnegative twists `⨁_{m ≥ 0} 𝒪_P(m)` is the nonnegative truncation of the
algebra of all integral twists `⨁_{m ∈ ℤ} 𝒪_P(m)`.**

Both sides match on the constructors of `ℤ`: in a nonnegative degree both are the twisting sheaf
with the twist multiplication, in a negative degree both are a zero sheaf with a zero bilinear
map, and both units are `Stacks.AlgebraicGeometry.ProjConeTwist.twistOne`. The two zero bilinear
maps are separate declarations with the same data field, hence equal by proof irrelevance in the
remaining fields, so the whole identification is definitional. -/
theorem nonnegTwistAlgebra_eq_nonnegTruncation :
    nonnegTwistAlgebra 𝒜 =
      Stacks.AlgebraicGeometry.NonnegTruncation.nonnegTruncation (integerTwistAlgebra 𝒜) :=
  rfl

/-- **The algebra sheaf of the nonnegative twists is the algebra sheaf of the nonnegative
truncation of the integral twists**, which is what lets the general truncation's functoriality
be applied to [Stacks, Tag 0EKG]'s nonnegatively graded left-hand entry. -/
theorem nonnegTwistAlgebraSheaf_eq :
    nonnegTwistAlgebraSheaf 𝒜 =
      Stacks.RelativeSpec.gradedAlgebraSheaf (AlgebraicGeometry.Proj 𝒜)
        (Stacks.AlgebraicGeometry.NonnegTruncation.nonnegTruncation (integerTwistAlgebra 𝒜))
        (Stacks.AlgebraicGeometry.NonnegTruncation.isCommutative_nonnegTruncation
          (integerTwistAlgebra 𝒜) (heq_twistMul_comm 𝒜)) :=
  rfl

end Stacks.AlgebraicGeometry.ProjConeTwist

end
