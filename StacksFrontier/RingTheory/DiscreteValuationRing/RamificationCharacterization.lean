module

public import StacksFrontier.RingTheory.DiscreteValuationRing.Solution

/-!
# Characterizing the ramification index

For an extension `B/A` of discrete valuation rings with ramification index `e = e(B/A)`:

* `e` is the only exponent `≥ 1` with `𝔪_A B = 𝔪_B ^ e`;
* for any uniformizers `π_A`, `π_B`, the image of `π_A` is a unit times `π_B ^ e`.

## Main results

* `IsDiscreteValuationRing.ramificationIndex_unique`: the exponent is unique.
* `IsDiscreteValuationRing.exists_unit_algebraMap_eq_mul_pow`: the uniformizer description.
* `IsDiscreteValuationRing.map_maximalIdeal_eq_iff_isWeaklyUnramified`: `B/A` is weakly
  unramified if and only if `𝔪_A B = 𝔪_B`.
* `IsDiscreteValuationRing.isWeaklyUnramified_iff_exists_unit_algebraMap_eq_mul`: `B/A` is weakly
  unramified if and only if the image of `π_A` is a unit times `π_B`.

## References

* [Stacks Project, Tag 09E4](https://stacks.math.columbia.edu/tag/09E4)
-/

open Stacks.DiscreteValuationRing.Ramification

@[expose] public section

namespace IsDiscreteValuationRing

variable (A B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [IsExtension A B]

/-- The ramification index is the unique exponent `e ≥ 1` with `𝔪_A B = 𝔪_B ^ e`. -/
theorem ramificationIndex_unique (e : ℕ) (_he : 1 ≤ e)
    (h : (IsLocalRing.maximalIdeal A).map (algebraMap A B) = IsLocalRing.maximalIdeal B ^ e) :
    e = ramificationIndex A B := by
  have hcoe : (e : ℕ∞) = (ramificationIndex A B : ℕ∞) := (idealOrderIsoENat B).symm.injective
    (h.symm.trans (map_maximalIdeal_eq_maximalIdeal_pow_ramificationIdx A B))
  exact_mod_cast hcoe

/-- For any uniformizers `π_A` of `A` and `π_B` of `B`, the image of `π_A` in `B` is a unit times
`π_B ^ e(B/A)`. -/
theorem exists_unit_algebraMap_eq_mul_pow (πA : A) (hπA : Irreducible πA) (πB : B)
    (hπB : Irreducible πB) :
    ∃ u : Bˣ, algebraMap A B πA = (u : B) * πB ^ ramificationIndex A B := by
  have hne : algebraMap A B πA ≠ 0 := fun h =>
    hπA.ne_zero (FaithfulSMul.algebraMap_injective A B (by simpa using h))
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hπB
  have hval := addVal_algebraMap_eq_ramificationIdx A B πA hπA
  rw [hu, addVal_mul, addVal_eq_zero_of_unit, addVal_pow, addVal_uniformizer hπB, nsmul_eq_mul,
    zero_add, mul_one] at hval
  have hn : n = ramificationIndex A B := by exact_mod_cast hval
  exact ⟨u, hn ▸ hu⟩

/-- `B/A` is weakly unramified if and only if the maximal ideal of `A` extends to the maximal
ideal of `B`. -/
theorem map_maximalIdeal_eq_iff_isWeaklyUnramified :
    (IsLocalRing.maximalIdeal A).map (algebraMap A B) = IsLocalRing.maximalIdeal B ↔
      IsWeaklyUnramified A B := by
  obtain ⟨-, hpow, hunique, -⟩ := ramificationIndex_characterization A B
  refine ⟨fun h => (hunique 1 le_rfl (by simpa using h)).symm, fun h => ?_⟩
  change ramificationIndex A B = 1 at h
  simpa [h] using hpow

/-- For uniformizers `π_A` of `A` and `π_B` of `B`, `B/A` is weakly unramified if and only if the
image of `π_A` in `B` is a unit times `π_B`. -/
theorem isWeaklyUnramified_iff_exists_unit_algebraMap_eq_mul
    (πA : A) (hπA : Irreducible πA) (πB : B) (hπB : Irreducible πB) :
    IsWeaklyUnramified A B ↔
      ∃ u : Bˣ, algebraMap A B πA = (u : B) * πB := by
  obtain ⟨v, hv⟩ := exists_unit_algebraMap_eq_mul_pow A B πA hπA πB hπB
  refine ⟨fun h => ⟨v, by simpa [show ramificationIndex A B = 1 from h] using hv⟩,
    fun ⟨u, hu⟩ => ?_⟩
  show ramificationIndex A B = 1
  exact IsDiscreteValuationRing.unit_mul_pow_congr_pow hπB hπB v u
    (ramificationIndex A B) 1 (by simpa using hv.symm.trans hu)

end IsDiscreteValuationRing
