module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackFirstChernCap
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaCoefficients

/-!
# The defining sum of the cap product over a pushed-forward cycle

In Situation 0EDT let `X/B` be good, let `W ⊆ X` be an integral closed subspace and let
`c ∈ Z_k(W)`.  The coefficient of the pushforward `(i_W)_* c ∈ Z_k(X)` vanishes at every
integral closed subspace of `X` outside the image of the integral closed subspaces of `W`, and
at the image of `T₀ ⊆ W` it is `c(T₀)`.  So a sum over the integral closed subspaces of `X`
weighted by that coefficient family is a sum over the integral closed subspaces of `W`:

`∑_T ((i_W)_* c)(T) · γ(T) = ∑_{T₀} c(T₀) · γ(i_W(T₀))`.

The weight `γ` is arbitrary, and the application is to the defining sum of the cap product of
Stacks 0EQJ, whose weight at `T` is the coefficient at a fixed subspace of the component cycle
of `T`.  This is the reindexing the proof of Stacks 0EQY needs in order to compare
`c₁(𝒩) ∩ (i_W)_* c` with a cycle assembled on `W`: after it, the two sums are indexed by the
same type and may be compared term by term.

## Main results

* `AlgebraicGeometry.Space.finsum_integralClosedSubspacePushforward_mul_eq`: the reindexing of a
  weighted sum of the coefficients of a pushforward along the image map
  `AlgebraicGeometry.Space.integralClosedSubspaceImage`.  Unconditional.
* `AlgebraicGeometry.Space.firstChernCapCycleMap_integralClosedSubspacePushforward_apply`: its
  instance at the cap product of Stacks 0EQJ, which reads the coefficient of
  `c₁(𝒩) ∩ (i_W)_* c` as a sum over the integral closed subspaces of `W`.

## Implementation notes

Local finiteness plays no role: the two sums have, term by term, the same nonzero values, the
image map being injective (`AlgebraicGeometry.Space.injective_integralClosedSubspaceImage`), so
the identity is the composite of `finsum_mem_range` with the restriction of the left sum to the
range of the image map, which is licensed because the summand vanishes off that range by
`AlgebraicGeometry.Space.integralClosedSubspacePushforward_apply_of_forall_ne`.  Neither side is
asserted to be a finite sum, and neither needs to be.

## References

* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
* [Stacks Project, Tag 0EQY](https://stacks.math.columbia.edu/tag/0EQY)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)

/-- **A weighted sum of the coefficients of a pushforward is a sum over the subspace pushed
from.**  For `W ⊆ X` an integral closed subspace of a good algebraic space, `c ∈ Z_k(W)` and an
arbitrary weight `γ` on the integral closed subspaces of `X`,

`∑_T ((i_W)_* c)(T) · γ(T) = ∑_{T₀} c(T₀) · γ(i_W(T₀))`,

the right sum running over the integral closed subspaces of `W` and `i_W(T₀)` being the image
`AlgebraicGeometry.Space.integralClosedSubspaceImage`.

The coefficient of the pushforward vanishes off the range of the image map and is `c(T₀)` at
`i_W(T₀)`, and the image map is injective. -/
theorem finsum_integralClosedSubspacePushforward_mul_eq {k : ℤ}
    (c : CycleGroup D (W.subspace.ι ≫ sX) k)
    (γ : IntegralClosedSubspace D.site D.base D.base_mem X → ℤ) :
    (∑ᶠ T : IntegralClosedSubspace D.site D.base D.base_mem X,
        (integralClosedSubspacePushforward D sX hX W k c).1 T * γ T) =
      ∑ᶠ T₀ : IntegralClosedSubspace D.site D.base D.base_mem W.subspace.toFunctor,
        c.1 T₀ * γ (integralClosedSubspaceImage D sX hX W T₀) := by
  have hsupp : ∀ T ∈ Function.support
      (fun T : IntegralClosedSubspace D.site D.base D.base_mem X =>
        (integralClosedSubspacePushforward D sX hX W k c).1 T * γ T),
      T ∈ Set.range (integralClosedSubspaceImage D sX hX W) ↔ T ∈ Set.univ := by
    intro T hT
    simp only [Set.mem_univ, iff_true]
    by_contra hnot
    refine Function.mem_support.1 hT ?_
    rw [integralClosedSubspacePushforward_apply_of_forall_ne D sX hX W c T
      fun T₀ hT₀ => hnot ⟨T₀, hT₀⟩, zero_mul]
  rw [← finsum_mem_univ (fun T : IntegralClosedSubspace D.site D.base D.base_mem X =>
      (integralClosedSubspacePushforward D sX hX W k c).1 T * γ T),
    ← finsum_mem_inter_support_eq' _ (Set.range (integralClosedSubspaceImage D sX hX W))
      Set.univ hsupp,
    finsum_mem_range (injective_integralClosedSubspaceImage D sX hX W)]
  exact finsum_congr fun T₀ => by
    rw [integralClosedSubspacePushforward_apply_pushforward]

/-- **The coefficient of `c₁(𝒩) ∩ (i_W)_* c` as a sum over the subspace pushed from.**  The
defining sum of the cap product of Stacks 0EQJ over a pushed-forward cycle, reindexed along the
image map: at an integral closed subspace `T ⊆ X`,

`(c₁(𝒩) ∩ (i_W)_* c)(T) = ∑_{T₀ ⊆ W} c(T₀) · (c₁(𝒩) ∩ [i_W(T₀)])(T)`.

This is the form in which the cap product of a pushed-forward cycle is compared with a cycle
assembled on `W`, both sides then being indexed by the integral closed subspaces of `W`. -/
theorem firstChernCapCycleMap_integralClosedSubspacePushforward_apply (k : ℤ)
    (chern : FirstChernComponentCycleRule D sX k)
    (c : CycleGroup D (W.subspace.ι ≫ sX) (k + 1))
    (T : IntegralClosedSubspace D.site D.base D.base_mem X) :
    (firstChernCapCycleMap D sX hX k chern
        (integralClosedSubspacePushforward D sX hX W (k + 1) c)).1 T =
      ∑ᶠ T₀ : IntegralClosedSubspace D.site D.base D.base_mem W.subspace.toFunctor,
        c.1 T₀ * (firstChernComponentCycle D sX hX k chern
          (integralClosedSubspaceImage D sX hX W T₀)).1 T := by
  rw [firstChernCapCycleMap_apply]
  exact finsum_integralClosedSubspacePushforward_mul_eq D sX hX W c
    fun V => (firstChernComponentCycle D sX hX k chern V).1 T

end AlgebraicGeometry.Space

end
