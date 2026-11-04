module

public import StacksFrontier.AlgebraicGeometry.Chow.CycleAdditivity
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ClosedImmersionCycles

/-!
# Assembling a carried rational equivalence from a locally finite family

If two cycles are presented as locally finite sums of two families, each member supported in its
carrier, and the members' differences are rationally equivalent to zero within their carriers, then
the difference of the two cycles is rationally equivalent to zero within the union of the carriers.
This file proves that, together with the compatibility of proper pushforward along a closed
immersion with locally finite sums.

## Main results

* `Stacks.Chow.properPushforward_apply_finsum_of_isClosedImmersion` — pushforward along a closed
  immersion of a locally finite sum of cycles.
* `Stacks.Chow.isRationallyEquivalentToZeroWithin_sub_of_finsum` — the difference of two cycles
  presented by locally finite families is rationally equivalent to zero within the union of the
  carriers, as soon as each member's difference is.

## References

* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
* [Stacks Project, Tag 02R4](https://stacks.math.columbia.edu/tag/02R4)
* [Stacks Project, Tag 0B73](https://stacks.math.columbia.edu/tag/0B73)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Pushforward along a closed immersion of a locally finite sum -/

/-- **Proper pushforward along a closed immersion commutes with a locally finite sum.** If the
coefficients of `γ` are pointwise the sums `∑ᶠ a, γ' a`, then so are those of its pushforward along
the closed immersion `i`. -/
theorem properPushforward_apply_finsum_of_isClosedImmersion (C : ChowSituation.{u})
    {Z X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (i : Z ⟶ X) [IsClosedImmersion i] (hi : i ≫ sX = sZ) (k : ℤ)
    {J : Type*} (γ : CycleGroup C sZ k) (γ' : J → CycleGroup C sZ k)
    (hγ : ∀ z : Z, γ.1 z = ∑ᶠ a : J, (γ' a).1 z) (y : X) :
    (properPushforward C sZ sX i hi k γ).1 y =
      ∑ᶠ a : J, (properPushforward C sZ sX i hi k (γ' a)).1 y := by
  by_cases hr : y ∈ Set.range i.base
  · obtain ⟨z, rfl⟩ := hr
    rw [properPushforward_apply_image_of_isClosedImmersion C sZ sX i hi k γ z, hγ z]
    exact finsum_congr fun a ↦
      (properPushforward_apply_image_of_isClosedImmersion C sZ sX i hi k (γ' a) z).symm
  · rw [properPushforward_apply_of_notMem_range C sZ sX i hi k γ hr]
    refine ((finsum_congr fun a ↦ ?_).trans finsum_zero).symm
    exact properPushforward_apply_of_notMem_range C sZ sX i hi k (γ' a) hr

/-! ### The carried assembly -/

/-- **A difference of two locally finite sums, with the carrier kept.** If two `k`-cycles `A` and
`B` are coefficientwise the locally finite sums of two families `u` and `v`, each member of each
family being supported inside its carrier `E j`, and if `u j - v j` is rationally equivalent to
zero within `E j`, then `A - B` is rationally equivalent to zero within `⋃ j, E j`. -/
theorem isRationallyEquivalentToZeroWithin_sub_of_finsum (C : ChowSituation.{u})
    {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ) {J : Type u} (E : J → Set X)
    (hE : LocallyFinite E) (A B : CycleGroup C p k) (u v : J → CycleGroup C p k)
    (hu : ∀ j, Function.support (u j).1 ⊆ E j) (hv : ∀ j, Function.support (v j).1 ⊆ E j)
    (hA : ∀ x : X, A.1 x = ∑ᶠ j : J, (u j).1 x)
    (hB : ∀ x : X, B.1 x = ∑ᶠ j : J, (v j).1 x)
    (hD : ∀ j, IsRationallyEquivalentToZeroWithin C p k (u j - v j) (E j)) :
    IsRationallyEquivalentToZeroWithin C p k (A - B) (⋃ j, E j) := by
  refine rationallyEquivalentToZeroWithin_finsum C p k (fun j ↦ u j - v j) E hE hD fun x ↦ ?_
  have hf {w : J → CycleGroup C p k} (hw : ∀ j, Function.support (w j).1 ⊆ E j) :
      Function.HasFiniteSupport fun j ↦ (w j).1 x := (hE.point_finite x).subset fun j hj ↦ hw j hj
  rw [show (A - B).1 x = A.1 x - B.1 x by simp, hA x, hB x, ← finsum_sub_distrib (hf hu) (hf hv)]
  simp

end Stacks.Chow

end
