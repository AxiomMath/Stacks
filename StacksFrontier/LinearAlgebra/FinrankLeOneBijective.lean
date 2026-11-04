module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Linear maps out of a field into a space of dimension at most one

A nonzero linear map `K → N` from a field into a finite-dimensional `K`-vector space of dimension
at most one is bijective.

## Main results

* `LinearMap.bijective_of_ne_zero_of_finrank_le_one`: a nonzero `K`-linear map from a field `K` to
  a finite `K`-module of rank at most one is bijective.
-/

@[expose] public section

/-- A nonzero `K`-linear map `ℓ : K →ₗ[K] N` from a field `K` to a finite `K`-module `N` with
`Module.finrank K N ≤ 1` is bijective. -/
theorem LinearMap.bijective_of_ne_zero_of_finrank_le_one {K N : Type*} [CommRing K]
    (hK : IsField K) [AddCommGroup N] [Module K N] [Module.Finite K N]
    (hN : Module.finrank K N ≤ 1) (ℓ : K →ₗ[K] N) (hℓ : ℓ ≠ 0) : Function.Bijective ℓ := by
  let := hK.toField
  have h1 : ℓ 1 ≠ 0 := fun h => hℓ (LinearMap.ext_ring h)
  refine ⟨fun a b hab => ?_, fun n => ?_⟩
  · have : (a - b) • ℓ 1 = 0 := by
      rw [sub_smul, ← LinearMap.map_smul, ← LinearMap.map_smul, smul_eq_mul, smul_eq_mul,
        mul_one, mul_one, hab, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 this).resolve_right h1)
  · have hpos : 0 < Module.finrank K (LinearMap.range ℓ) :=
      Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨ℓ 1, 1, rfl⟩, fun h => h1 (congrArg Subtype.val h)⟩
    have htop : LinearMap.range ℓ = ⊤ :=
      Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _)
        (hN.trans (Nat.one_le_iff_ne_zero.2 hpos.ne')))
    exact LinearMap.range_eq_top.1 htop n
