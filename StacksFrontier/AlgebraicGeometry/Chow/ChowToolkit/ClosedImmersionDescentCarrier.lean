module

public import StacksFrontier.AlgebraicGeometry.Chow.ChowToolkit.ClosedImmersionDescent

/-!
# Descent of a rational equivalence into a closed subscheme, with its carrier

Along a closed immersion `j : Z ⟶ Y`, a rational equivalence to zero of a proper pushforward
that is carried inside a subset `T` of the image of `j` descends to a rational equivalence to zero
carried inside the preimage `j^{-1}(T)`. This refines
`Stacks.Chow.isRationallyEquivalentToZero_of_properPushforward_isRationallyEquivalentToZeroWithin`,
which does not record the carrier.

## Main results

* `Stacks.Chow.isRationallyEquivalentToZeroWithin_of_properPushforward` — the descent, with the
  carrier retained as a preimage.

## References

* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 0B73](https://stacks.math.columbia.edu/tag/0B73)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-- **Descent of a rational equivalence into a closed subscheme, with its carrier.** Along a
closed immersion `j : Z ⟶ Y` over the base, if the proper pushforward of a `k`-cycle `β` on `Z`
is rationally equivalent to zero within a subset `T` of the image of `j`, then `β` is rationally
equivalent to zero within `j^{-1}(T)`. -/
theorem isRationallyEquivalentToZeroWithin_of_properPushforward
    (C : ChowSituation.{u}) {Z Y : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (j : Z ⟶ Y) [IsClosedImmersion j]
    (hj : j ≫ sY = sZ) (k : ℤ) (β : CycleGroup C sZ k) {T : Set Y}
    (hT : T ⊆ Set.range j.base)
    (h : IsRationallyEquivalentToZeroWithin C sY k
      (properPushforward C sZ sY j hj k β) T) :
    IsRationallyEquivalentToZeroWithin C sZ k β (j.base ⁻¹' T) := by
  obtain ⟨A, W, hW, hDim, hLocal, hsub, g, hg⟩ := h
  choose hV hVDim g' hcoeff using fun a ↦ exists_descent_principalDivisorPushforward_comap j C
    sZ sY hj k (W a) (hW a) (hDim a) ((hsub a).trans hT) (g a)
  have hsupp (a : A) :
      (((W a).comap j).support : Set Z) = j.base ⁻¹' ((W a).support : Set Y) := by
    rw [Scheme.IdealSheafData.support_comap]
    rfl
  refine ⟨A, fun a ↦ (W a).comap j, hV, hVDim, ?_, fun a ↦ ?_, g', fun z ↦ ?_⟩
  · rw [funext hsupp]
    exact hLocal.preimage_continuous j.continuous
  · exact (hsupp a).trans_subset (Set.preimage_mono (hsub a))
  · rw [← properPushforward_apply_image_of_isClosedImmersion C sZ sY j hj k β z,
      hg (j.base z)]
    exact (finsum_congr fun a ↦ hcoeff a z).symm

end Stacks.Chow

end
