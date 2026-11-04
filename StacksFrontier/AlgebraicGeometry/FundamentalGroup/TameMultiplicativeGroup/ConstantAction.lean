module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameMultiplicativeGroup.Identification

/-!
# The degree of `π₁ᵗ(𝐆_{m,k}) → Ẑ` is the action on constants

Under `Ẑ^{(q)} ⋊ Ẑ ≃ₜ* π₁ᵗ(𝐆_{m,k}, η̄)`, an element `γ` of degree `d ∈ Ẑ` acts on the constants of
every tame cover as the geometric Frobenius to the power `d`: if `y` is a point of the fibre of a
tame cover `Y` and `c ∈ Γ(Y)` has `ψ_y(c) ∈ 𝔽_{q^n} ⊆ Ω`, then `ψ_{γ y}(c)^{q^{d mod n}} = ψ_y(c)`.
So the degree is the canonical map `π₁ᵗ(𝐆_{m,k}) → Gal(k̄/k) ≅ Ẑ` normalised by the geometric
Frobenius, and the kernel `Ẑ^{(q)}` is the geometric part, acting trivially on constants.

## Main results

* `AlgebraicGeometry.TameMultiplicativeGroup.fiberRingHom_fiberAct_pow_card`.
-/

@[expose] public noncomputable section

open CategoryTheory Polynomial Stacks.TraceFormula

universe u

namespace AlgebraicGeometry.TameMultiplicativeGroup

variable {k : Type u} [Field k] [Fintype k]

/-- The reduction of `x ∈ Ẑ` modulo `n ∣ m!` is that of its reduction modulo `m!`. -/
theorem dvd_val_restrictedMod_sub {m n : ℕ} (hn : n ≠ 0) (hnm : n ∣ m.factorial)
    (x : ProfiniteIntegers) :
    (n : ℤ) ∣ ((restrictedMod 1 n hn (Nat.coprime_one_right n) x).val : ℤ) -
      ((redF m x).val : ℤ) := by
  have : NeZero n := ⟨hn⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, Int.cast_natCast, Int.cast_natCast,
    sub_eq_zero, ZMod.natCast_zmod_val, ZMod.natCast_val, ← ZMod.castHom_apply (h := hnm),
    castHom_restrictedMod_of_dvd]

variable (k) in
/-- **On `𝔽_{q^n} ⊆ 𝔽_{m!}`, `Frob^{d mod n} ∘ Frob^{-(d mod m!)}` is the identity.** -/
theorem coe_frobAut_inv_pow_pow_card {m n : ℕ} (hn : n ≠ 0) (hnm : n ∣ m.factorial)
    (x : ProfiniteIntegers) (a : towerField k m) (ha : (a : Omega k) ∈ frobField k n) :
    ((((frobAut k m)⁻¹ ^ (redF m x).val) a : towerField k m) : Omega k) ^
        (Fintype.card k ^ (restrictedMod 1 n hn (Nat.coprime_one_right n) x).val) = a := by
  obtain ⟨t, ht⟩ := dvd_val_restrictedMod_sub hn hnm x
  have hfix : (frobAut k m ^ n) a = a := by
    rw [frobAut_pow_apply]
    exact Subtype.ext ((SubmonoidClass.coe_pow a _).trans ((mem_frobField k).mp ha))
  have hstab : frobAut k m ^ n ∈ MulAction.stabilizer (RingAut (towerField k m)) a := hfix
  have hg : frobAut k m ^ (restrictedMod 1 n hn (Nat.coprime_one_right n) x).val *
      (frobAut k m)⁻¹ ^ (redF m x).val = (frobAut k m ^ n) ^ t := by
    rw [← zpow_natCast (frobAut k m) (restrictedMod 1 n hn _ x).val, inv_pow,
      ← zpow_natCast (frobAut k m) (redF m x).val, ← zpow_neg, ← zpow_add,
      ← zpow_natCast (frobAut k m) n, ← zpow_mul, ← sub_eq_add_neg, ht]
  have h1 : (frobAut k m ^ (restrictedMod 1 n hn (Nat.coprime_one_right n) x).val)
      (((frobAut k m)⁻¹ ^ (redF m x).val) a) = a := by
    show (frobAut k m ^ (restrictedMod 1 n hn (Nat.coprime_one_right n) x).val *
      (frobAut k m)⁻¹ ^ (redF m x).val) a = a
    rw [hg]
    exact zpow_mem hstab t
  rw [frobAut_pow_apply] at h1
  rw [← SubmonoidClass.coe_pow, h1]

/-- **`γ` acts on constants as the geometric Frobenius to the power `deg γ`.** If `ψ_y(c)` lies in
`𝔽_{q^n} ⊆ Ω`, then `ψ_{γ y}(c)^{q^{deg γ mod n}} = ψ_y(c)`. -/
theorem fiberRingHom_fiberAct_pow_card (γ : Gamma (inverseCharacter (Fintype.card k)))
    (Y : TameCover k) (y : (tameFiberFunctor k).obj Y) (c : Γ(Y.obj.left, ⊤)) {n : ℕ}
    (hn : n ≠ 0) (hc : fiberRingHom y c ∈ frobField k n) :
    fiberRingHom (fiberAct γ Y y) c ^ (Fintype.card k ^
        (restrictedMod 1 n hn (Nat.coprime_one_right n)
          (Multiplicative.toAdd (degree _ γ))).val) = fiberRingHom y c := by
  obtain ⟨m₀, hm₀⟩ := isTowerValued_fiberRingHom y
  obtain ⟨m, hm₀m, hnm⟩ : ∃ m, m₀ ≤ m ∧ n ≤ m := ⟨max m₀ n, le_max_left _ _, le_max_right _ _⟩
  have hm : ∀ c, fiberRingHom y c ∈ (towerPoint k m).range :=
    fun c ↦ range_towerPoint_mono k hm₀m (hm₀ c)
  have hnf : n ∣ m.factorial := Nat.dvd_factorial (Nat.pos_of_ne_zero hn) hnm
  have hω : fiberRingHom y c ∈ towerField k m := frobField_mono k hnf hc
  have hz : towerPoint k m (algebraMap _ (Ring (towerField k m))
      (C (⟨fiberRingHom y c, hω⟩ : towerField k m))) = fiberRingHom y c := by
    rw [towerPoint_algebraMap, eval₂_C]
    rfl
  rw [fiberRingHom_fiberAct, towerAct_eq _ _ _ hm, actAt_apply, tau_eq k γ (hm c) hz, deck_C,
    towerPoint_algebraMap, eval₂_C]
  exact coe_frobAut_inv_pow_pow_card k hn hnf _ _ hc

end AlgebraicGeometry.TameMultiplicativeGroup

end
