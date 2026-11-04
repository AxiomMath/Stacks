module

public import StacksFrontier.AlgebraicGeometry.Chow.DimensionFunction

/-!
# Codimension one and delta-dimension `n - 1`

Let `C = (S, δ)` be a Chow situation and let `X` be integral and locally of finite type over `S`
with `dim_δ(X) = n`. The relative dimension function of Stacks 02JW takes the value `n` at the
generic point of `X` and strictly decreases along every nontrivial specialization, and it drops
by exactly one along an immediate specialization. Consequently a point of `X` has relative
dimension `n - 1` exactly when it has codimension one, that is, exactly when it is the generic
point of a prime divisor. This is the form of Stacks 02RK that the pushforward of a principal
divisor needs: it is what identifies the points contributing to `div(f)` on the source with the
points contributing to `div(g)` on the target.

## Main results

* `Stacks.Chow.relativeDimension_eq_sub_one_of_coheight_eq_one` — a point of codimension one has
  relative dimension `n - 1`.
* `Stacks.Chow.relativeDimension_eq_sub_one_iff_coheight_eq_one` — the converse, hence the
  equivalence.

## Implementation notes

The specialization preorder on the points of a scheme has `x ≤ y` iff `y ⤳ x`, so the generic
point of an integral scheme is the greatest element and `Order.coheight x` is the codimension of
`closure {x}`. The bound `Order.coheight x ≤ 1` is obtained from `Order.coheight_le_coe_iff`:
every point strictly above a point of relative dimension `n - 1` has relative dimension at least
`n`, hence is the generic point, which is maximal.

## References

* [Stacks Project, Tag 02RK](https://stacks.math.columbia.edu/tag/02RK)
* [Stacks Project, Tag 02JW](https://stacks.math.columbia.edu/tag/02JW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (s : X ⟶ C.S) [LocallyOfFiniteType s]
  [IsIntegral X] {n : ℤ}

/-- **Stacks 02RK.** A point of codimension one on an integral scheme of delta-dimension `n`
over the base has relative dimension `n - 1`. -/
theorem relativeDimension_eq_sub_one_of_coheight_eq_one
    (hn : schemeDeltaDimension C s = (n : EInt)) {x : X} (hx : Order.coheight x = 1) :
    relativeDimension C.dimensionFunction s x = n - 1 := by
  have hdim := deltaDimension_closure_singleton_eq_sub_one C s hn hx
  rwa [deltaDimension_eq_of_isGenericPoint C s _ x isGenericPoint_closure] at hdim

/-- The relative dimension function of Stacks 02JW takes the value `n` at the generic point of an
integral scheme of delta-dimension `n`. -/
theorem deltaDimensionFunction_genericPoint (hn : schemeDeltaDimension C s = (n : EInt)) :
    deltaDimensionFunction C s (genericPoint X) = n := by
  rw [deltaDimensionFunction_apply]
  exact WithBotTop.coe_injective ((schemeDeltaDimension_eq_genericPoint C s).symm.trans hn)

/-- Every point of an integral scheme of delta-dimension `n` other than the generic point has
relative dimension at most `n - 1`. -/
theorem relativeDimension_le_sub_one_of_ne_genericPoint
    (hn : schemeDeltaDimension C s = (n : EInt)) {x : X} (hx : x ≠ genericPoint X) :
    relativeDimension C.dimensionFunction s x ≤ n - 1 := by
  have hlt := (deltaDimensionFunction C s).strictAnti_specializes
    (genericPoint_specializes x) (Ne.symm hx)
  rw [deltaDimensionFunction_genericPoint C s hn, deltaDimensionFunction_apply] at hlt
  omega

/-- **Stacks 02RK.** On an integral scheme of delta-dimension `n` over the base, a point has
relative dimension `n - 1` exactly when it has codimension one. -/
theorem relativeDimension_eq_sub_one_iff_coheight_eq_one
    (hn : schemeDeltaDimension C s = (n : EInt)) (x : X) :
    relativeDimension C.dimensionFunction s x = n - 1 ↔ Order.coheight x = 1 := by
  refine ⟨fun hx ↦ ?_, relativeDimension_eq_sub_one_of_coheight_eq_one C s hn⟩
  have hgen := deltaDimensionFunction_genericPoint C s hn
  have hxval : deltaDimensionFunction C s x = n - 1 := by
    rw [deltaDimensionFunction_apply]; exact hx
  have hne : x ≠ genericPoint X := fun h ↦ by rw [h, hgen] at hxval; omega
  have hmax : IsMax (genericPoint X) := fun b _ ↦ genericPoint_specializes b
  have hle : x ≤ genericPoint X := genericPoint_specializes x
  have hlt : x < genericPoint X :=
    lt_iff_le_not_ge.mpr ⟨hle, fun h ↦ hne (Specializes.antisymm h hle).eq⟩
  refine le_antisymm (Order.coheight_le_coe_iff.mpr fun y hy ↦ ?_) ?_
  · have hyval : deltaDimensionFunction C s x < deltaDimensionFunction C s y :=
      (deltaDimensionFunction C s).strictAnti_specializes hy.le (ne_of_gt hy)
    have hyeq : y = genericPoint X := by
      by_contra hyne
      have hle : relativeDimension C.dimensionFunction s y ≤ n - 1 :=
        relativeDimension_le_sub_one_of_ne_genericPoint C s hn hyne
      rw [deltaDimensionFunction_apply, deltaDimensionFunction_apply] at hyval
      omega
    rw [hyeq, Order.coheight_eq_zero.mpr hmax]
    exact zero_lt_one
  · have hstep := Order.coheight_add_one_le hlt
    rw [Order.coheight_eq_zero.mpr hmax, zero_add] at hstep
    exact hstep

end Stacks.Chow

end
