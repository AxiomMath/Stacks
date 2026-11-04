module

public import StacksFrontier.AlgebraicGeometry.Algebraization.DepthInequalities
public import StacksFrontier.AlgebraicGeometry.Algebraization.DistanceSpecialization

/-!
# Distance one at an immediate specialization, and the closed set `Z` inside `Y`

Two small facts about the distance function `δ^Y_Z` of a closed subset, both used when the
`(a, b)`-inequalities of chapter 52 are run at a point just outside the closed set.

The first pins the distance down exactly, rather than merely bounding it: if `r ⤳ s` is an
immediate specialization, `s` lies in the closed set `Z` and `r` does not, then the distance of
`r` from `Z` is exactly `1`. The bound `δ(r) ≤ δ(s) + 1` gives `δ(r) ≤ 1` since `δ(s) = 0`, and
`δ(r) ≠ 0` because `r ∉ Z`.

The second identifies, for an algebraization situation, membership of the closed subset
`Z = V(𝔞)` of `Y = V(I)` with lying in the image of the closed immersion `Z ⟶ X`. Both sides
are a containment of ideals, related by `Ideal.map_le_iff_le_comap`.

## Main results

* `Stacks.Algebraization.distanceFunction_eq_one_of_isImmediateSpecialization_of_notMem`
  computes the distance at the generic point of an immediate specialization into `Z`.
* `Stacks.Algebraization.mem_closedSubsetZ_iff_mem_range_Zι` reads membership of the closed
  subset `Z` of `Y` as membership of the range of `Z ⟶ X` after pushing forward to `X`.

## References

* [Stacks Project, Tag 0EIY](https://stacks.math.columbia.edu/tag/0EIY), the distance function.
* [Stacks Project, Tag 0EHC](https://stacks.math.columbia.edu/tag/0EHC), the situation.
-/

@[expose] public noncomputable section

open AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Algebraization

/-- If `r ⤳ s` is an immediate specialization with `s` in the closed set `Z` and `r` outside
`Z`, then `r` is at distance exactly one from `Z`: the bound along an immediate specialization
gives `δ(r) ≤ δ(s) + 1 = 1`, and `δ(r) ≠ 0` since `r ∉ Z`. -/
public theorem distanceFunction_eq_one_of_isImmediateSpecialization_of_notMem
    (Y : Scheme.{u}) [IsNoetherian Y] (Z : Closeds Y)
    (hY : IrreducibleClosedsCodim.IsCatenarySpace Y) {r s : Y}
    (hrs : IsImmediateSpecialization r s) (hs : s ∈ (Z : Set Y)) (hr : r ∉ (Z : Set Y)) :
    distanceFunction Y Z r = 1 := by
  have hle := distanceFunction_le_add_one_of_isImmediateSpecialization Y Z hY hrs
  rw [(distanceFunction_eq_zero_iff_mem Y Z s).2 hs, zero_add] at hle
  have hne : distanceFunction Y Z r ≠ 0 := fun hz =>
    hr ((distanceFunction_eq_zero_iff_mem Y Z r).mp hz)
  exact le_antisymm hle (Order.one_le_iff_ne_zero.2 hne)

/-- For an algebraization situation, a point `y` of `Y = V(I)` lies in the closed subset
`Z = V(𝔞)` of `Y` exactly when its image in `X = Spec(A)` lies in the image of the closed
immersion `Z ⟶ X`. Both conditions say that `𝔞` is contained in the prime of `A` underlying
`y`: on the left after pushing `𝔞` forward to `A/I`, on the right because the range of
`Spec(A/𝔞) ⟶ Spec(A)` is the zero locus of `𝔞`. -/
public theorem mem_closedSubsetZ_iff_mem_range_Zι (S : AlgebraizationSituation.{u}) (y : S.Y) :
    y ∈ (S.closedSubsetZ : Set S.Y) ↔ S.Yι.base y ∈ Set.range S.Zι.base := by
  have hrange : Set.range S.Zι.base = PrimeSpectrum.zeroLocus (S.a : Set S.A) := by
    have h := _root_.range_comap_of_surjective (S.A ⧸ S.a) (Ideal.Quotient.mk S.a)
      Ideal.Quotient.mk_surjective
    rw [Ideal.mk_ker] at h
    exact h
  have hmemL : y ∈ (S.closedSubsetZ : Set S.Y) ↔
      (S.a.map (Ideal.Quotient.mk S.I) : Ideal (S.A ⧸ S.I)) ≤
        (y : PrimeSpectrum (S.A ⧸ S.I)).asIdeal := Iff.rfl
  have hmemR : S.Yι.base y ∈ PrimeSpectrum.zeroLocus (S.a : Set S.A) ↔
      S.a ≤ Ideal.comap (Ideal.Quotient.mk S.I)
        (y : PrimeSpectrum (S.A ⧸ S.I)).asIdeal := Iff.rfl
  rw [hrange]
  exact hmemL.trans (Ideal.map_le_iff_le_comap.trans hmemR.symm)

end Stacks.Algebraization

end
