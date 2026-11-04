module

public import Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import Mathlib.RingTheory.Valuation.ValuationRing

/-!
# A fraction with unit image under a local homomorphism is a unit

Let `R` be a valuation ring with fraction field `K`, let `φ : R → T` be a **local** homomorphism
of rings and let `Φ : K → L` be a ring homomorphism to a total ring of fractions of `T` lying over
`φ`. If a fraction `x ∈ K` has, in `L`, the image of a **unit** of `T`, then `x` is already the
image of a unit of `R` — and so has order of vanishing zero.

## Main results

* `Stacks.ValuationRing.exists_isUnit_algebraMap_eq_of_isUnit_map`: the fraction is the image of
  a unit of the valuation ring.
* `Stacks.ValuationRing.ordFrac_eq_one_of_isUnit_map`: consequently its order of vanishing is
  zero, in the multiplicative normalisation `Ring.ordFrac` of Stacks 02MD.

## References

* [Stacks Project, Tag 02MD](https://stacks.math.columbia.edu/tag/02MD)
* [Stacks Project, Tag 0EPX](https://stacks.math.columbia.edu/tag/0EPX)
-/

@[expose] public noncomputable section

namespace Stacks.ValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [_root_.ValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable {T : Type*} [CommRing T] [Nontrivial T]
variable {L : Type*} [CommRing L] [Algebra T L] [IsFractionRing T L]

/-- **A fraction of a valuation ring whose image under a local homomorphism is a unit is the
image of a unit.** Let `R` be a valuation ring with fraction field `K`, let `φ : R →+* T` be a
local homomorphism into a nontrivial ring and let `Φ : K →+* L` be a homomorphism into a total
ring of fractions of `T` extending `φ`. If `Φ x` is the image of a unit of `T`, then `x` is the
image of a unit of `R`. -/
theorem exists_isUnit_algebraMap_eq_of_isUnit_map (φ : R →+* T) [IsLocalHom φ] (Φ : K →+* L)
    (hΦ : ∀ r : R, Φ (algebraMap R K r) = algebraMap T L (φ r)) {x : K} {v : T} (hv : IsUnit v)
    (hx : Φ x = algebraMap T L v) :
    ∃ r : R, IsUnit r ∧ algebraMap R K r = x := by
  have hinj : Function.Injective (algebraMap T L) := IsLocalization.injective L le_rfl
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero, eq_comm, map_eq_zero_iff _ hinj] at hx
    exact not_isUnit_zero (hx ▸ hv)
  rcases _root_.ValuationRing.isInteger_or_isInteger R x with ⟨r, hr⟩ | ⟨r, hr⟩
  · refine ⟨r, (isUnit_map_iff φ r).1 ?_, hr⟩
    rwa [hinj ((hΦ r).symm.trans ((congrArg Φ hr).trans hx))]
  · have hone : φ r * v = 1 := hinj (by
      rw [map_mul, map_one, ← hΦ r, ← hx, ← map_mul, hr, inv_mul_cancel₀ hx0, map_one])
    obtain ⟨u, hu⟩ := (isUnit_map_iff φ r).1 (IsUnit.of_mul_eq_one v hone)
    refine ⟨((u⁻¹ : Rˣ) : R), u⁻¹.isUnit, ?_⟩
    rw [← inv_inv x, ← hr, ← hu, map_units_inv]

variable [IsNoetherianRing R] [Ring.KrullDimLE 1 R]

/-- **A fraction of a valuation ring whose image under a local homomorphism is a unit has order
of vanishing zero**, in the multiplicative normalisation `Ring.ordFrac` of Stacks 02MD, which
sends it to `1`. -/
theorem ordFrac_eq_one_of_isUnit_map (φ : R →+* T) [IsLocalHom φ] (Φ : K →+* L)
    (hΦ : ∀ r : R, Φ (algebraMap R K r) = algebraMap T L (φ r)) {x : K} {v : T} (hv : IsUnit v)
    (hx : Φ x = algebraMap T L v) :
    Ring.ordFrac R (K := K) x = 1 := by
  obtain ⟨r, hr, rfl⟩ := exists_isUnit_algebraMap_eq_of_isUnit_map φ Φ hΦ hv hx
  exact Ring.ordFrac_of_isUnit hr

end Stacks.ValuationRing

end
