module

public import StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.ComponentOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.OrderOfVanishing

/-!
# The order of vanishing along a ring isomorphism

The order of vanishing `Ring.ord R r`, the length of `R ⧸ (r)`, and its extension
`Ring.ordTotalFracInt` to the units of the total ring of fractions, are invariants of the ring:
an isomorphism `σ : R ≃+* R'` carries `R ⧸ (r)` to `R' ⧸ (σ r)` semilinearly over `σ`, hence
preserves lengths, and it extends to an isomorphism of total rings of fractions under which the
two extended orders agree.

## Main definitions

* `Ring.totalFracRingEquiv`: the isomorphism of total rings of fractions induced by a ring
  isomorphism.

## Main results

* `Ring.ordMonoidWithZeroHom_ringEquiv`: the `ℤᵐ⁰`-valued order of vanishing is invariant under
  ring isomorphisms.
* `Ring.ordTotalFrac_ringEquiv`, `Ring.ordTotalFracInt_ringEquiv`: the order of vanishing on the
  total ring of fractions is invariant under the isomorphism `Ring.totalFracRingEquiv`.

## References

* [Stacks Project, Tag 02MD](https://stacks.math.columbia.edu/tag/02MD)
-/

@[expose] public section

open scoped nonZeroDivisors

namespace Ring

variable {R R' : Type*} [CommRing R] [CommRing R'] (σ : R ≃+* R')

/-- Membership in the nonzerodivisors is invariant under ring isomorphisms. -/
theorem mem_nonZeroDivisors_ringEquiv_iff {r : R} : σ r ∈ R'⁰ ↔ r ∈ R⁰ := by
  rw [← MulEquivClass.map_nonZeroDivisors σ]
  exact ⟨fun ⟨s, hs, hsr⟩ => (σ.injective hsr) ▸ hs, fun h => ⟨r, h, rfl⟩⟩

/-- The `ℤᵐ⁰`-valued order of vanishing is invariant under ring isomorphisms. -/
theorem ordMonoidWithZeroHom_ringEquiv [Nontrivial R] [Nontrivial R'] (r : R) :
    ordMonoidWithZeroHom R' (σ r) = ordMonoidWithZeroHom R r := by
  by_cases hr : r ∈ R⁰
  · rw [ordMonoidWithZeroHom_eq_ord hr,
      ordMonoidWithZeroHom_eq_ord ((mem_nonZeroDivisors_ringEquiv_iff σ).2 hr), ← ord_ringEquiv]
  · simp only [ordMonoidWithZeroHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
      mem_nonZeroDivisors_ringEquiv_iff, hr, ↓reduceIte]

variable [IsNoetherianRing R] [Ring.KrullDimLE 1 R] [Nontrivial R]
    [IsNoetherianRing R'] [Ring.KrullDimLE 1 R'] [Nontrivial R']
    {K K' : Type*} [CommRing K] [Algebra R K] [IsFractionRing R K]
    [CommRing K'] [Algebra R' K'] [IsFractionRing R' K']

/-- The isomorphism of total rings of fractions induced by a ring isomorphism. -/
noncomputable abbrev totalFracRingEquiv : K ≃+* K' :=
  IsLocalization.ringEquivOfRingEquiv K K' σ
    (show R⁰.map σ.toMonoidHom = R'⁰ from MulEquivClass.map_nonZeroDivisors σ)

/-- Clearing denominators: `ord (a / b) * ord b = ord a`. -/
private theorem ordTotalFrac_mk'_mul_ord (a : R) (b : R⁰) :
    ordTotalFrac R (IsLocalization.mk' K a b) * ordMonoidWithZeroHom R (b : R) =
      ordMonoidWithZeroHom R a := by
  rw [← ordTotalFrac_algebraMap R (K := K), ← ordTotalFrac_algebraMap R (K := K), ← map_mul,
    IsLocalization.mk'_spec]

/-- The order of vanishing on the total ring of fractions is invariant under ring isomorphisms. -/
theorem ordTotalFrac_ringEquiv (k : K) :
    ordTotalFrac R' (totalFracRingEquiv σ (K := K) (K' := K') k) = ordTotalFrac R k := by
  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective R⁰ k
  have hb : ordMonoidWithZeroHom R (b : R) ≠ 0 := by
    rw [← ordTotalFrac_algebraMap R (K := K)]
    exact ((IsLocalization.map_units K b).map (ordTotalFrac R (K := K))).ne_zero
  have h₁ := ordTotalFrac_mk'_mul_ord (K := K) a b
  have h₂ := ordTotalFrac_mk'_mul_ord (K := K') (σ a)
    ⟨σ b, (mem_nonZeroDivisors_ringEquiv_iff σ).2 b.2⟩
  rw [ordMonoidWithZeroHom_ringEquiv, ordMonoidWithZeroHom_ringEquiv] at h₂
  change ordTotalFrac R' (IsLocalization.ringEquivOfRingEquiv K K' σ
    _ (IsLocalization.mk' K a b)) = _
  rw [IsLocalization.ringEquivOfRingEquiv_mk']
  exact mul_right_cancel₀ hb (h₂.trans h₁.symm)

/-- The integer-valued order of vanishing is invariant under ring isomorphisms. -/
theorem ordTotalFracInt_ringEquiv (k : K) (hk : IsUnit k)
    (hk' : IsUnit (totalFracRingEquiv σ (K := K) (K' := K') k)) :
    ordTotalFracInt R' (totalFracRingEquiv σ (K := K) (K' := K') k) hk' =
      ordTotalFracInt R k hk := by
  unfold ordTotalFracInt
  congr 1
  rw [← WithZero.coe_inj, WithZero.coe_unzero, WithZero.coe_unzero, ordTotalFrac_ringEquiv]

end Ring

end
