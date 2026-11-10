module

public import StacksFrontier.RingTheory.LocalCohomology.LocalizationTriangle.PowerTorsionSequences

/-!
# The two towers of short exact sequences attached to the powers of a ring element

Let `A` be a commutative ring, `f ∈ A` and `M` an `A`-module. For each `n` there are two short
exact sequences

* `0 ⟶ fⁿM ⟶ M ⟶ M / fⁿM ⟶ 0`, and
* `0 ⟶ M[fⁿ] ⟶ M ⟶ fⁿM ⟶ 0`,

and both are towers in `n`. This file constructs the morphisms of short exact sequences that
exhibit them as such.

The quotient sequences form an inverse system through the inclusion `fᵐM ⊆ fⁿM` for `n ≤ m`, the
identity of `M`, and the projection `M / fᵐM ⟶ M / fⁿM`, which is Mathlib's
`AdicCompletion.transitionMap` for the ideal `(f)`.

The torsion sequences carry multiplication by `f ^ (m - n)` in the middle, because `M ⟶ fⁿM` is
multiplication by `fⁿ` and the square `M ⟶ fᵐM ⊆ fⁿM` commutes only after precomposing with
`f ^ (m - n)`. Multiplication by `f ^ (m - n)` carries `M[fᵐ]` into `M[fⁿ]`, and once the torsion
submodules have stabilized it does so by zero, so the first component of the induced morphism of
short exact sequences vanishes. Over a Noetherian module that stabilization is
`Stacks.LocalCohomology.exists_powerTorsion_stable`, and
`Stacks.LocalCohomology.pow_smul_eq_zero_of_powerTorsion_stable` deduces the annihilation
hypothesis from it.

## Main definitions

* `Stacks.LocalCohomology.powerSmulTopLE` — the inclusion `fᵐM ⊆ fⁿM` for `n ≤ m`.
* `Stacks.LocalCohomology.powerQuotientSESMap` — the morphism of quotient sequences.
* `Stacks.LocalCohomology.powerTorsionSESMap` — the morphism of torsion sequences, with zero first
  component.

## Main results

* `Stacks.LocalCohomology.powerSmulToSmulTop_comp_subtype` — `M ⟶ fⁿM ⊆ M` is multiplication by
  `fⁿ`.
* `Stacks.LocalCohomology.powerSmulToSmulTop_comp_powerSmulTopLE` — `M ⟶ fᵖM ⊆ fⁿM` is
  multiplication by `f ^ (p - n)` followed by `M ⟶ fⁿM`.
* `Stacks.LocalCohomology.pow_smul_eq_zero_of_powerTorsion_stable` — past the stabilization level
  of the `fⁿ`-torsion of `M`, the power `f ^ (m - p)` annihilates `M[fᵐ]`.

## References

* [Stacks Project, Tag 0EII](https://stacks.math.columbia.edu/tag/0EII)
-/

@[expose] public noncomputable section

open CategoryTheory

universe v u

namespace Stacks.LocalCohomology

variable {A : Type u} [CommRing A] (f : A) (M : ModuleCat.{v} A)

/-! ### The inclusions between the submodules `fⁿM` -/

/-- The inclusion `fᵐM ⊆ fⁿM` for `n ≤ m`. -/
def powerSmulTopLE {n m : ℕ} (h : n ≤ m) :
    ModuleCat.of A (powerSmulTop f M m) ⟶ ModuleCat.of A (powerSmulTop f M n) :=
  ModuleCat.ofHom (Submodule.inclusion (powerSmulTop_antitone f M h))

/-- The inclusion `fᵐM ⊆ fⁿM` leaves the underlying element of `M` unchanged. -/
theorem powerSmulTopLE_apply_coe {n m : ℕ} (h : n ≤ m) (x : powerSmulTop f M m) :
    (powerSmulTopLE f M h x : M) = (x : M) := rfl

/-- The inclusions between the `fⁿM` compose. -/
theorem powerSmulTopLE_trans {n p m : ℕ} (h₁ : n ≤ p) (h₂ : p ≤ m) :
    powerSmulTopLE f M h₂ ≫ powerSmulTopLE f M h₁ = powerSmulTopLE f M (h₁.trans h₂) :=
  ModuleCat.hom_ext (LinearMap.ext fun _ ↦ rfl)

/-- The inclusion `fᵐM ⊆ fⁿM` followed by `fⁿM ⊆ M` is `fᵐM ⊆ M`. -/
theorem powerSmulTopLE_comp_subtype {n m : ℕ} (h : n ≤ m) :
    powerSmulTopLE f M h ≫ (powerQuotientShortComplex f M n).f =
      (powerQuotientShortComplex f M m).f :=
  ModuleCat.hom_ext (LinearMap.ext fun _ ↦ rfl)

/-! ### Multiplication by a power, in and out of `fⁿM` -/

/-- `M ⟶ fⁿM ⊆ M` is multiplication by `fⁿ`. -/
theorem powerSmulToSmulTop_comp_subtype (n : ℕ) :
    (powerTorsionShortComplex f M n).g ≫ (powerQuotientShortComplex f M n).f =
      (f ^ n) • 𝟙 M :=
  ModuleCat.hom_ext (LinearMap.ext fun _ ↦ rfl)

/-- `M ⟶ fᵖM ⊆ fⁿM` is multiplication by `f ^ (p - n)` followed by `M ⟶ fⁿM`; both send `x` to
`f ^ p • x`. -/
theorem powerSmulToSmulTop_comp_powerSmulTopLE {n p : ℕ} (h : n ≤ p) :
    (powerTorsionShortComplex f M p).g ≫ powerSmulTopLE f M h =
      ((f ^ (p - n)) • 𝟙 M) ≫ (powerTorsionShortComplex f M n).g :=
  ModuleCat.hom_ext (LinearMap.ext fun x ↦ Subtype.ext (by
    change f ^ p • x = f ^ n • (f ^ (p - n) • x)
    rw [smul_smul, ← pow_add, Nat.add_sub_cancel' h]))

/-! ### The morphism of quotient sequences -/

/-- The morphism of quotient sequences `0 ⟶ fᵐM ⟶ M ⟶ M/fᵐM ⟶ 0` to `0 ⟶ fⁿM ⟶ M ⟶ M/fⁿM ⟶ 0`
for `n ≤ m`: the inclusion of submodules, the identity of `M`, and the projection of quotients. -/
def powerQuotientSESMap {n m : ℕ} (h : n ≤ m) :
    powerQuotientShortComplex f M m ⟶ powerQuotientShortComplex f M n where
  τ₁ := powerSmulTopLE f M h
  τ₂ := 𝟙 M
  τ₃ := ModuleCat.ofHom (AdicCompletion.transitionMap (Ideal.span {f}) M h)
  comm₁₂ := (powerSmulTopLE_comp_subtype f M h).trans (Category.comp_id _).symm
  comm₂₃ := ModuleCat.hom_ext (LinearMap.ext fun _ ↦ rfl)

/-- The first component of the morphism of quotient sequences is the inclusion `fᵐM ⊆ fⁿM`. -/
theorem powerQuotientSESMap_τ₁ {n m : ℕ} (h : n ≤ m) :
    (powerQuotientSESMap f M h).τ₁ = powerSmulTopLE f M h := rfl

/-- The third component of the morphism of quotient sequences is the projection
`M / fᵐM ⟶ M / fⁿM`. -/
theorem powerQuotientSESMap_τ₃ {n m : ℕ} (h : n ≤ m) :
    (powerQuotientSESMap f M h).τ₃ =
      ModuleCat.ofHom (AdicCompletion.transitionMap (Ideal.span {f}) M h) := rfl

/-! ### The morphism of torsion sequences -/

/-- The morphism of torsion sequences `0 ⟶ M[fᵐ] ⟶ M ⟶ fᵐM ⟶ 0` to `0 ⟶ M[fᵖ] ⟶ M ⟶ fᵖM ⟶ 0`
for `p ≤ m`, in the situation where `f ^ (m - p)` kills `M[fᵐ]`: the first component is the zero
map, the second is multiplication by `f ^ (m - p)`, and the third is the inclusion
`fᵐM ⊆ fᵖM`. -/
def powerTorsionSESMap {p m : ℕ} (h : p ≤ m)
    (hkill : ∀ x : M, f ^ m • x = 0 → f ^ (m - p) • x = 0) :
    powerTorsionShortComplex f M m ⟶ powerTorsionShortComplex f M p where
  τ₁ := 0
  τ₂ := (f ^ (m - p)) • 𝟙 M
  τ₃ := powerSmulTopLE f M h
  comm₁₂ := by
    rw [Limits.zero_comp]
    symm
    exact ModuleCat.hom_ext (LinearMap.ext fun x ↦ hkill x.1 ((mem_powerTorsion f M).1 x.2))
  comm₂₃ := (powerSmulToSmulTop_comp_powerSmulTopLE f M h).symm

/-- The first component of the morphism of torsion sequences is the zero map. -/
theorem powerTorsionSESMap_τ₁ {p m : ℕ} (h : p ≤ m)
    (hkill : ∀ x : M, f ^ m • x = 0 → f ^ (m - p) • x = 0) :
    (powerTorsionSESMap f M h hkill).τ₁ = 0 := rfl

/-- The third component of the morphism of torsion sequences is the inclusion `fᵐM ⊆ fᵖM`. -/
theorem powerTorsionSESMap_τ₃ {p m : ℕ} (h : p ≤ m)
    (hkill : ∀ x : M, f ^ m • x = 0 → f ^ (m - p) • x = 0) :
    (powerTorsionSESMap f M h hkill).τ₃ = powerSmulTopLE f M h := rfl

/-! ### The annihilation hypothesis from stabilization -/

/-- If the `fⁿ`-torsion of `M` is constant from level `N` on, and `N ≤ m - p` and `N ≤ m`, then
`f ^ (m - p)` annihilates `M[fᵐ]`. -/
theorem pow_smul_eq_zero_of_powerTorsion_stable {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → powerTorsion f M n = powerTorsion f M N) {p m : ℕ}
    (hm : N ≤ m) (hgap : N ≤ m - p) (x : M) (hx : f ^ m • x = 0) : f ^ (m - p) • x = 0 := by
  have hxN : f ^ N • x = 0 := (mem_powerTorsion f M).1 (by
    rw [← hN m hm]
    exact (mem_powerTorsion f M).2 hx)
  rw [← Nat.add_sub_cancel' hgap, pow_add, mul_comm, mul_smul, hxN, smul_zero]

end Stacks.LocalCohomology

end
