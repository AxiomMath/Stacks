module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.SubAdditiveProof
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.SubbundleTwist
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.SubbundleZeroScheme
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.TopHalfProof

/-!
# The geometry of `𝐏(𝒬) ⊂ 𝐏(𝒢)`, and the first Chern class along an invertible subsheaf

For a short exact sequence `0 ⟶ ℳ ⟶ 𝒢 ⟶ 𝒬 ⟶ 0` of finite locally free modules on a scheme with
`ℳ` invertible and `𝒬` of positive constant rank, the closed immersion `ι : 𝐏(𝒬) ⟶ 𝐏(𝒢)` induced
by `𝒢 ⟶ 𝒬` pulls `𝒪_{𝐏(𝒢)}(1)` back to `𝒪_{𝐏(𝒬)}(1)`
(`Stacks.Chow.GenuineChern.bundleEmbeddingTwistIso`), and its image is the zero scheme of the
section of `ℒ = 𝒪(1) ⊗ π^*ℳ^{-1}` attached to `π^*ℳ ⟶ π^*𝒢 ⟶ 𝒪(1)`, a relative effective
Cartier divisor over `X`
(`Stacks.Chow.GenuineChern.exists_relativeEffectiveCartierDivisor_bundleEmbedding`).
This is `Stacks.Chow.GenuineChern.SubbundleHolds`, and with the top half of [Stacks, Tag 02TW] it
gives the first Chern class part of [Stacks, Tag 02UH]:

  `c₁(𝒢) ∩ α = c₁(𝒬) ∩ α + c₁(ℳ) ∩ α`.

## Main results

* `Stacks.Chow.GenuineChern.subbundleHolds`.
* `Stacks.Chow.GenuineChern.subAdditive`.

## References

* [Stacks Project, Tag 02UH](https://stacks.math.columbia.edu/tag/02UH)
* [Stacks Project, Tag 02TW](https://stacks.math.columbia.edu/tag/02TW)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Chow.GenuineChern

/-- **The geometry of `𝐏(𝒬) ⊂ 𝐏(𝒢)`.** -/
theorem subbundleHolds : SubbundleHolds.{u} := by
  intro X S hS _ _ _ r _
  have : Epi S.g := hS.epi_g
  exact ⟨⟨bundleEmbeddingTwistIso S.g⟩,
    exists_relativeEffectiveCartierDivisor_bundleEmbedding S hS r⟩

/-- **Stacks 02UH for the first Chern class**: `c₁(𝒢) ∩ α = c₁(𝒬) ∩ α + c₁(ℳ) ∩ α` for
`0 ⟶ ℳ ⟶ 𝒢 ⟶ 𝒬 ⟶ 0` short exact with `ℳ` invertible and `𝒬` of positive rank. -/
theorem subAdditive (C : ChowSituation.{u}) : SubAdditive C :=
  subAdditive_of C (topHalf C) subbundleHolds

end Stacks.Chow.GenuineChern

end
