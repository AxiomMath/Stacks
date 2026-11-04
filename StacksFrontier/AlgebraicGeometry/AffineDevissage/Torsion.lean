module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Filtration

/-!
# Artin–Rees removes the ideal-power torsion of a finite module

Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `M` a finite `A`-module. The submodules
`Tₙ = {x ∈ M | Iⁿ x = 0}` form an ascending chain, which stabilises because `M` is a Noetherian
module; the Artin–Rees lemma then produces a single exponent `m` with
`Iᵐ M ∩ Tₙ = 0` for **every** `n`. In other words the submodule `Iᵐ M` has no `I`-power torsion
at all.

This is the devissage step in the proofs of [Stacks, Tag 01PQ] and [Stacks, Tag 01YB]: those
proofs replace a coherent sheaf `F` by `Iᵐ F`, which has the same sections away from `V(I)` and
for which the torsion hypothesis of [Stacks, Tag 01PM] holds. The statement here is the
affine-local content of that step, with the two global inputs of the source — the ascending chain
condition and Artin–Rees — supplied by `Mathlib`'s `monotone_stabilizes_iff_noetherian` and
`Ideal.exists_pow_inf_eq_pow_smul`.

## Main results

* `Stacks.AlgebraicGeometry.IdealPowerSections.exists_pow_smul_inf_torsionBySet_eq_bot`: the
  exponent `m` with `Iᵐ M ⊓ torsionBySet A M (Iⁿ) = ⊥` for all `n`.
* `Stacks.AlgebraicGeometry.IdealPowerSections.exists_forall_smul_eq_zero_imp_eq_zero`: the same
  conclusion for `n = 1`: no nonzero element of the module `Iᵐ M` is annihilated by `I`.

## Implementation notes

The quantification over `n` in the first result is not needed by the second (which uses only
`n = 1`), but it is the honest statement of what Artin–Rees gives and it is what identifies the
conclusion with the vanishing of all the subsheaves `Fₙ` in the source's argument.

`Ideal.exists_pow_inf_eq_pow_smul` states `Iⁿ • ⊤ ⊓ N = I⁽ⁿ⁻ᵏ⁾ • (Iᵏ • ⊤ ⊓ N)` for `n ≥ k`;
taking `n = n₀ + k` with `n₀` the stabilisation index makes the outer factor `I ^ n₀`, which
annihilates `T n₀` by definition, so the right-hand side is zero.

## References

* [Stacks Project, Tag 01PM](https://stacks.math.columbia.edu/tag/01PM)
* [Stacks Project, Tag 01PQ](https://stacks.math.columbia.edu/tag/01PQ)
* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
-/

@[expose] public section

universe u v

namespace Stacks.AlgebraicGeometry.IdealPowerSections

variable (A : Type u) [CommRing A] (M : Type v) [AddCommGroup M] [Module A M]

/-- The ascending chain `n ↦ {x ∈ M | Iⁿ x = 0}` of ideal-power torsion submodules. -/
public def torsionChain (I : Ideal A) : ℕ →o Submodule A M :=
  ⟨fun n => Submodule.torsionBySet A M (↑(I ^ n) : Set A),
    fun _ _ h => Submodule.torsionBySet_le_torsionBySet_pow _ _ h I⟩

/-- The `n`-th term of `torsionChain A M I` is `torsionBySet A M (Iⁿ)`. -/
@[simp]
public lemma torsionChain_apply (I : Ideal A) (n : ℕ) :
    torsionChain A M I n = Submodule.torsionBySet A M (↑(I ^ n) : Set A) := rfl

/-- **Artin–Rees kills the ideal-power torsion.** For a Noetherian ring `A`, an ideal `I` and a
finite `A`-module `M` there is an exponent `m` such that no nonzero element of `Iᵐ M` is
annihilated by any power of `I`. -/
public theorem exists_pow_smul_inf_torsionBySet_eq_bot [IsNoetherianRing A] [Module.Finite A M]
    (I : Ideal A) :
    ∃ m : ℕ, ∀ n : ℕ,
      (I ^ m • (⊤ : Submodule A M)) ⊓ Submodule.torsionBySet A M (↑(I ^ n) : Set A) = ⊥ := by
  obtain ⟨n₀, hn₀⟩ :=
    monotone_stabilizes_iff_noetherian.mpr inferInstance (torsionChain A M I)
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I (torsionChain A M I n₀)
  refine ⟨n₀ + k, fun n => ?_⟩
  have hTn : torsionChain A M I n ≤ torsionChain A M I n₀ := by
    rcases le_total n n₀ with h | h
    · exact (torsionChain A M I).monotone h
    · exact le_of_eq (hn₀ n h).symm
  have key : (I ^ (n₀ + k) • (⊤ : Submodule A M)) ⊓ torsionChain A M I n₀ = ⊥ := by
    rw [hk (n₀ + k) (Nat.le_add_left k n₀), Nat.add_sub_cancel]
    refine le_antisymm (Submodule.smul_le.2 fun r hr x hx => ?_) bot_le
    exact (Submodule.mem_bot A).mpr ((Submodule.mem_torsionBySet_iff _ _).mp hx.2 ⟨r, hr⟩)
  exact le_bot_iff.mp (le_trans (inf_le_inf_left _ hTn) key.le)

/-- **The torsion hypothesis of [Stacks, Tag 01PM], discharged for `Iᵐ M`.** For a Noetherian
ring `A`, an ideal `I` and a finite `A`-module `M` there is an exponent `m` such that no nonzero
element of the submodule `Iᵐ M` is annihilated by all of `I`. -/
public theorem exists_forall_smul_eq_zero_imp_eq_zero [IsNoetherianRing A] [Module.Finite A M]
    (I : Ideal A) :
    ∃ m : ℕ, ∀ y : ↥(I ^ m • (⊤ : Submodule A M)),
      (∀ a ∈ I, a • y = 0) → y = 0 := by
  obtain ⟨m, hm⟩ := exists_pow_smul_inf_torsionBySet_eq_bot A M I
  refine ⟨m, fun y hy => ?_⟩
  have h1 : (y : M) ∈ (I ^ m • (⊤ : Submodule A M)) ⊓
      Submodule.torsionBySet A M (↑(I ^ 1) : Set A) := by
    refine ⟨y.2, (Submodule.mem_torsionBySet_iff _ _).mpr fun a => ?_⟩
    have ha : (a : A) ∈ I := by simpa using a.2
    exact congrArg Subtype.val (hy (a : A) ha)
  rw [hm 1] at h1
  exact Subtype.ext ((Submodule.mem_bot A).mp h1)

end Stacks.AlgebraicGeometry.IdealPowerSections

end
