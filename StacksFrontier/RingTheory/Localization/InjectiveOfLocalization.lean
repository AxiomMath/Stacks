module

public import Mathlib.RingTheory.Localization.Basic

/-!
# Injectivity of a ring map out of a localization

A ring map out of a localization `S` of `R`, compatible with a map `R → T`, is injective as soon
as `R → T` is. The statement is about a localization and an injective ring map and nothing else,
so it lives here, below every development that needs it.

## Main results

* `injective_of_isLocalization_of_injective`: a compatible map out of a localization inherits
  injectivity from the base.
-/

@[expose] public section

/-- A ring map out of a localization `S` of `R` that is compatible with `R → T` is injective as
soon as `R → T` is. -/
theorem injective_of_isLocalization_of_injective {R S T : Type*} [CommRing R]
    [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] {M : Submonoid R}
    [IsLocalization M S] (g : S →+* T)
    (hg : ∀ x : R, g (algebraMap R S x) = algebraMap R T x)
    (hinj : Function.Injective (algebraMap R T)) : Function.Injective g := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨⟨x, y⟩, rfl⟩ := IsLocalization.mk'_surjective M z
  have hx : algebraMap R T x = 0 := by
    rw [← hg, ← IsLocalization.mk'_spec S x y, map_mul, hz, zero_mul]
  have hx0 : x = 0 := hinj (by rw [map_zero]; exact hx)
  simp [hx0]

end
