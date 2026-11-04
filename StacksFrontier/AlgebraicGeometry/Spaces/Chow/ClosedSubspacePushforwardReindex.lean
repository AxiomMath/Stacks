module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FirstChernCapPushforwardReindex
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.LocalizationSequence

/-!
# A weighted sum over a pushforward from a closed subspace

In Situation 0EDT let `X/B` be good, let `i : Y ⟶ X` be the inclusion of a closed subspace and
let `c ∈ Z_k(Y)`.  The coefficient of `i_*c` vanishes at every integral closed subspace of `X`
outside the image of the integral closed subspaces of `Y`, and at the image of `T₀ ⊆ Y` it is
`c(T₀)`.  So a sum over the integral closed subspaces of `X` weighted by that coefficient family
is a sum over the integral closed subspaces of `Y`:

`∑_T (i_*c)(T) · γ(T) = ∑_{T₀} c(T₀) · γ(i(T₀))`.

`AlgebraicGeometry.Space.finsum_integralClosedSubspacePushforward_mul_eq` is the same statement
for an *integral* closed subspace `W ⊆ X`, which is what the proof of Stacks 0EQY needs.  The
proof of Stacks 0ER9 needs it for an effective Cartier divisor `D ⊆ X`, which is not integral:
there the cycle `[D]_{n-1}` lives on `D` and its pushforward `div_ℒ(s)` lives on `X`, and the
two readings of the cap product of Stacks 0EQJ — one indexed by the integral closed subspaces of
`D`, as `AlgebraicGeometry.Space.cycleClosedPushforward_firstChernCapCycleMap_eq_finsum` gives
it, the other by those of `X`, as Section 0EQU gives it — are compared by this reindexing.

## Main results

* `AlgebraicGeometry.Space.finsum_cycleGroupClosedPushforward_mul_eq`: the reindexing.
* `AlgebraicGeometry.Space.firstChernCapCycleMap_cycleGroupClosedPushforward_apply`: its
  instance at the cap product of Stacks 0EQJ, which reads the coefficient of
  `c₁(𝒩) ∩ i_*c` as a sum over the integral closed subspaces of `Y`.

## Implementation notes

Local finiteness plays no role: the two sums have, term by term, the same nonzero values, the
image map being injective
(`AlgebraicGeometry.Space.IntegralClosedSubspace.injective_pushforward`), so the identity is the
composite of `finsum_mem_range` with the restriction of the left sum to the range of the image
map, which is licensed because the summand vanishes off that range by
`AlgebraicGeometry.Space.cycleClosedPushforward_apply_of_forall_ne`.  Neither side is asserted
to be a finite sum, and neither needs to be.

## References

* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
* [Stacks Project, Tag 0ER9](https://stacks.math.columbia.edu/tag/0ER9)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (hY : IsAlgebraicSpace D.site D.base D.base_mem Y) {i : Y ⟶ X}
    (hi : IsClosedImmersion D.site D.base D.base_mem i) (sY : Y ⟶ D.space) (hic : i ≫ sX = sY)

/-- **A weighted sum of the coefficients of a pushforward from a closed subspace is a sum over
that subspace.**  For `i : Y ⟶ X` the inclusion of a closed subspace of a good algebraic space,
`c ∈ Z_k(Y)` and an arbitrary weight `γ` on the integral closed subspaces of `X`,

`∑_T (i_*c)(T) · γ(T) = ∑_{T₀} c(T₀) · γ(i(T₀))`,

the right sum running over the integral closed subspaces of `Y` and `i(T₀)` being the image
`AlgebraicGeometry.Space.IntegralClosedSubspace.pushforward`.

The coefficient of the pushforward vanishes off the range of the image map and is `c(T₀)` at
`i(T₀)`, and the image map is injective. -/
theorem finsum_cycleGroupClosedPushforward_mul_eq {k : ℤ} (c : CycleGroup D sY k)
    (γ : IntegralClosedSubspace D.site D.base D.base_mem X → ℤ) :
    (∑ᶠ T : IntegralClosedSubspace D.site D.base D.base_mem X,
        (cycleGroupClosedPushforward D hX.1 hY (D.isDecentSpace_of_isGood sX hX) hi sX hX.2.2
          sY hic k c).1 T * γ T) =
      ∑ᶠ T₀ : IntegralClosedSubspace D.site D.base D.base_mem Y,
        c.1 T₀ * γ (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY
          (D.isDecentSpace_of_isGood sX hX) hi T₀) := by
  have hsupp : ∀ T ∈ Function.support
      (fun T : IntegralClosedSubspace D.site D.base D.base_mem X =>
        (cycleGroupClosedPushforward D hX.1 hY (D.isDecentSpace_of_isGood sX hX) hi sX hX.2.2
          sY hic k c).1 T * γ T),
      T ∈ Set.range (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY
          (D.isDecentSpace_of_isGood sX hX) hi) ↔ T ∈ Set.univ := by
    intro T hT
    simp only [Set.mem_univ, iff_true]
    by_contra hnot
    exact Function.mem_support.1 hT (mul_eq_zero_of_left
      (cycleClosedPushforward_apply_of_forall_ne D hX.1 hY (D.isDecentSpace_of_isGood sX hX) hi
        c.1 T fun T₀ hT₀ => hnot ⟨T₀, hT₀⟩) _)
  rw [← finsum_mem_univ (fun T : IntegralClosedSubspace D.site D.base D.base_mem X =>
      (cycleGroupClosedPushforward D hX.1 hY (D.isDecentSpace_of_isGood sX hX) hi sX hX.2.2
        sY hic k c).1 T * γ T),
    ← finsum_mem_inter_support_eq' _
      (Set.range (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY
        (D.isDecentSpace_of_isGood sX hX) hi)) Set.univ hsupp,
    finsum_mem_range (IntegralClosedSubspace.injective_pushforward D.site D.base D.base_mem
      hX.1 hY (D.isDecentSpace_of_isGood sX hX) hi)]
  exact finsum_congr fun T₀ => congrArg (· * _) (cycleClosedPushforward_apply_pushforward D hX.1
    hY (D.isDecentSpace_of_isGood sX hX) hi c.1 T₀)

/-- **The coefficient of `c₁(𝒩) ∩ i_*c` as a sum over the closed subspace pushed from.**  The
defining sum of the cap product of Stacks 0EQJ over a cycle pushed forward from a closed
subspace `Y ⊆ X`, reindexed along the image map: at an integral closed subspace `T ⊆ X`,

`(c₁(𝒩) ∩ i_*c)(T) = ∑_{T₀ ⊆ Y} c(T₀) · (c₁(𝒩) ∩ [i(T₀)])(T)`.

This is the form in which the cap product on `X` of a cycle formed on `D` is compared with the
cap product formed on `D` itself, both sides then being indexed by the integral closed subspaces
of `D`. -/
theorem firstChernCapCycleMap_cycleGroupClosedPushforward_apply (k : ℤ)
    (chern : FirstChernComponentCycleRule D sX k) (c : CycleGroup D sY (k + 1))
    (T : IntegralClosedSubspace D.site D.base D.base_mem X) :
    (firstChernCapCycleMap D sX hX k chern
        (cycleGroupClosedPushforward D hX.1 hY (D.isDecentSpace_of_isGood sX hX) hi sX hX.2.2
          sY hic (k + 1) c)).1 T =
      ∑ᶠ T₀ : IntegralClosedSubspace D.site D.base D.base_mem Y,
        c.1 T₀ * (firstChernComponentCycle D sX hX k chern
          (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY
            (D.isDecentSpace_of_isGood sX hX) hi T₀)).1 T := by
  rw [firstChernCapCycleMap_apply]
  exact finsum_cycleGroupClosedPushforward_mul_eq D sX hX hY hi sY hic c
    fun V => (firstChernComponentCycle D sX hX k chern V).1 T

end AlgebraicGeometry.Space

end
