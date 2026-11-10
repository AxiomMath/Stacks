module

public import Mathlib.RingTheory.HopkinsLevitzki
public import StacksFrontier.RingTheory.Length.MaximalIdealPower

/-!
# An artinian module killed by a power of the maximal ideal has finite length

Over a Noetherian local ring `(A, 𝔪)` a module which satisfies the descending chain condition on
submodules and is annihilated by a power of `𝔪` has finite length.  Neither hypothesis can be
dropped: the injective hull of the residue field is artinian and of infinite length, while `A`
itself is killed by a power of `𝔪` only when it already has finite length.

The use for this is local cohomology.  For a finite module `M` over a Noetherian local ring with
a dualizing complex the module `H^i_𝔪(M)` is artinian
(`Stacks.LocalCohomology.isArtinian_localCohomology_maximalIdeal`) but almost never finite, so no
finiteness statement about it is available; what the proof of [Stacks, Tag 0DXU] needs is that a
submodule of it killed by a power of `𝔪` has finite length.

## Main results

* `Stacks.RingTheory.isFiniteLength_of_isArtinian_of_pow_maximalIdeal_smul_eq_bot` — an artinian
  module over a Noetherian local ring annihilated by a power of the maximal ideal has finite
  length.

## Implementation notes

The proof is the Hopkins–Levitzki theorem.  Write `B = A ⧸ 𝔪^{k+1}`.  The module `M` is a
`B`-module because `𝔪^{k+1}` annihilates it, and `B` is an artinian ring because it is Noetherian
local with nilpotent maximal ideal (`isArtinianRing_iff_isNilpotent_maximalIdeal`, as in
`Module.finiteLength_quotient_by_maximalIdealPower`).  The descending chain condition over `A`
gives it over `B` (`isArtinian_of_tower`), and over a semiprimary ring an artinian module is
finite over the base ring (`IsSemiprimaryRing.finite_of_isArtinian`), here over `A` itself.
Finiteness over the Noetherian ring `A` is the ascending chain condition, and the two chain
conditions together are finite length (`isFiniteLength_iff_isNoetherian_isArtinian`).

The exponent is raised to `k + 1` so that the power is a proper ideal and the quotient is a local
ring; the hypothesis at `k` implies the hypothesis at `k + 1`.
-/

@[expose] public section

universe u v

namespace Stacks.RingTheory

/-- **An artinian module annihilated by a power of the maximal ideal has finite length.**  Let
`A` be a Noetherian local ring with maximal ideal `𝔪` and let `M` be an `A`-module satisfying the
descending chain condition on submodules.  If `𝔪^k` annihilates `M` for some `k`, then `M` has
finite length.

This is the Hopkins–Levitzki theorem over `A ⧸ 𝔪^k`: that ring is artinian, so the descending
chain condition over it forces the ascending one, which makes `M` a finite `A`-module; the two
chain conditions over `A` are then finite length. -/
theorem isFiniteLength_of_isArtinian_of_pow_maximalIdeal_smul_eq_bot
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {M : Type v} [AddCommGroup M] [Module A M] (hart : IsArtinian A M) (k : ℕ)
    (hk : IsLocalRing.maximalIdeal A ^ k • (⊤ : Submodule A M) = ⊥) :
    IsFiniteLength A M := by
  classical
  have hpow : IsLocalRing.maximalIdeal A ^ (k + 1) ≤ IsLocalRing.maximalIdeal A ^ k :=
    Ideal.pow_le_pow_right (Nat.le_succ k)
  have hk1 : IsLocalRing.maximalIdeal A ^ (k + 1) • (⊤ : Submodule A M) = ⊥ :=
    le_antisymm (le_trans (Submodule.smul_mono_left hpow) hk.le) bot_le
  -- the quotient by that power is an artinian local ring
  have hJne : IsLocalRing.maximalIdeal A ^ (k + 1) ≠ ⊤ := fun htop =>
    (IsLocalRing.maximalIdeal.isMaximal A).ne_top
      (top_unique (htop ▸ (Ideal.pow_le_self (Nat.succ_ne_zero k)
        : IsLocalRing.maximalIdeal A ^ (k + 1) ≤ IsLocalRing.maximalIdeal A)))
  have : Nontrivial (A ⧸ IsLocalRing.maximalIdeal A ^ (k + 1)) :=
    Ideal.Quotient.nontrivial_iff.mpr hJne
  have : IsLocalRing (A ⧸ IsLocalRing.maximalIdeal A ^ (k + 1)) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ (k + 1)))
      Ideal.Quotient.mk_surjective
  have hnil : IsNilpotent
      (IsLocalRing.maximalIdeal (A ⧸ IsLocalRing.maximalIdeal A ^ (k + 1))) := by
    refine ⟨k + 1, ?_⟩
    rw [← IsLocalRing.map_maximalIdeal_of_surjective
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ (k + 1)))
      Ideal.Quotient.mk_surjective, ← Ideal.map_pow]
    change Ideal.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ (k + 1)))
        (IsLocalRing.maximalIdeal A ^ (k + 1)) = ⊥
    rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
  have : IsArtinianRing (A ⧸ IsLocalRing.maximalIdeal A ^ (k + 1)) :=
    (isArtinianRing_iff_isNilpotent_maximalIdeal _).mpr hnil
  -- `M` is a module over that quotient, and artinian over it
  have htor : Module.IsTorsionBySet A M
      ((IsLocalRing.maximalIdeal A ^ (k + 1) : Ideal A) : Set A) := by
    intro x a
    have hmem : (a : A) • x ∈ IsLocalRing.maximalIdeal A ^ (k + 1) • (⊤ : Submodule A M) :=
      Submodule.smul_mem_smul a.2 Submodule.mem_top
    rw [hk1] at hmem
    simpa using hmem
  let : Module (A ⧸ IsLocalRing.maximalIdeal A ^ (k + 1)) M := htor.module
  have : IsScalarTower A (A ⧸ IsLocalRing.maximalIdeal A ^ (k + 1)) M :=
    Module.IsTorsionBySet.isScalarTower htor
  have : IsArtinian (A ⧸ IsLocalRing.maximalIdeal A ^ (k + 1)) M := isArtinian_of_tower A hart
  -- Hopkins–Levitzki over that quotient makes `M` finite over `A`
  have : Module.Finite A M :=
    IsSemiprimaryRing.finite_of_isArtinian A (A ⧸ IsLocalRing.maximalIdeal A ^ (k + 1)) M
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr
    ⟨isNoetherian_of_isNoetherianRing_of_finite A M, hart⟩

end Stacks.RingTheory

end
