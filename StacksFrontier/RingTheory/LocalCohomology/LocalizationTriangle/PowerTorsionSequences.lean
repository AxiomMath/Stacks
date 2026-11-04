module

public import Mathlib
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The two short exact sequences attached to a power of a ring element

Let `A` be a commutative ring, `f ∈ A` and `M` an `A`-module. For each power `fⁿ` there are two
short exact sequences of `A`-modules:

* `0 ⟶ fⁿM ⟶ M ⟶ M / fⁿM ⟶ 0`, which presents the `n`-th term of the quotient tower;
* `0 ⟶ M[fⁿ] ⟶ M ⟶ fⁿM ⟶ 0`, where the second map is multiplication by `fⁿ`, which compares `fⁿM`
  with `M` itself.

Both are given here as terms of `CategoryTheory.ShortComplex (ModuleCat A)` together with their
`ShortExact` proofs.

The torsion submodules `M[fⁿ]` increase with `n`, so over a Noetherian module they stabilize.

## Main definitions

* `Stacks.LocalCohomology.powerSmulTop` — the submodule `fⁿM`, as `(f)ⁿ • ⊤`.
* `Stacks.LocalCohomology.powerTorsion` — the submodule `M[fⁿ]`.
* `Stacks.LocalCohomology.powerQuotientShortComplex` — the sequence `0 ⟶ fⁿM ⟶ M ⟶ M/fⁿM ⟶ 0`.
* `Stacks.LocalCohomology.powerTorsionShortComplex` — the sequence `0 ⟶ M[fⁿ] ⟶ M ⟶ fⁿM ⟶ 0`.

## Main results

* `Stacks.LocalCohomology.exists_powerTorsion_stable` — the `fⁿ`-torsion of a Noetherian module
  stabilizes.
* `Stacks.LocalCohomology.powerQuotientShortComplex_shortExact`,
  `Stacks.LocalCohomology.powerTorsionShortComplex_shortExact` — both sequences are short exact.

## Implementation notes

The submodule `fⁿM` is spelled `(f)ⁿ • ⊤` rather than as the range of multiplication by `fⁿ`,
because that is the spelling in which the quotient tower `M / fⁿM` and its transition maps are
written; `Stacks.LocalCohomology.powerSmulTop_eq_range` identifies the two.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace Stacks.LocalCohomology

variable {A : Type u} [CommRing A] (f : A) (M : ModuleCat.{v} A)

/-! ### The submodule `fⁿM` -/

/-- The submodule `fⁿM` of `M`, in the spelling `(f)ⁿ • ⊤` used by the quotient tower
`M / fⁿM`. -/
def powerSmulTop (n : ℕ) : Submodule A M := (Ideal.span {f}) ^ n • (⊤ : Submodule A M)

/-- Multiplication by `fⁿ`, as an endomorphism of `M`. -/
def powerSmul (n : ℕ) : M →ₗ[A] M := (f ^ n) • (LinearMap.id : M →ₗ[A] M)

/-- Multiplication by `fⁿ` sends `x` to `fⁿ • x`. -/
@[simp]
theorem powerSmul_apply (n : ℕ) (x : M) : powerSmul f M n x = f ^ n • x := rfl

/-- `fⁿM` is the range of multiplication by `fⁿ`. -/
theorem powerSmulTop_eq_range (n : ℕ) :
    powerSmulTop f M n = LinearMap.range (powerSmul f M n) := by
  rw [powerSmulTop, Ideal.span_singleton_pow]
  refine le_antisymm ?_ ?_
  · rw [Submodule.smul_le]
    intro r hr x _
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    exact ⟨c • x, by simp [powerSmul, mul_smul]⟩
  · rintro x ⟨y, rfl⟩
    exact Submodule.smul_mem_smul (Submodule.mem_span_singleton_self _) Submodule.mem_top

/-- Multiplication by `fⁿ` takes its values in `fⁿM`. -/
theorem powerSmul_mem_powerSmulTop (n : ℕ) (x : M) : powerSmul f M n x ∈ powerSmulTop f M n := by
  rw [powerSmulTop_eq_range]
  exact ⟨x, rfl⟩

/-- Higher powers give smaller submodules. -/
theorem powerSmulTop_antitone : Antitone (powerSmulTop f M) := by
  intro n m hnm
  simp only [powerSmulTop_eq_range]
  rintro x ⟨y, rfl⟩
  exact ⟨f ^ (m - n) • y, by simp [smul_smul, ← pow_add, Nat.sub_add_cancel hnm]⟩

/-! ### The torsion submodules `M[fⁿ]` and their stabilization -/

/-- The submodule `M[fⁿ]` of elements killed by `fⁿ`. -/
def powerTorsion (n : ℕ) : Submodule A M := Submodule.torsionBy A M (f ^ n)

/-- An element of `M` lies in `M[fⁿ]` if and only if `fⁿ` annihilates it. -/
@[simp]
theorem mem_powerTorsion {n : ℕ} {x : M} : x ∈ powerTorsion f M n ↔ f ^ n • x = 0 :=
  Submodule.mem_torsionBy_iff _ _

/-- `M[fⁿ]` is the kernel of multiplication by `fⁿ`. -/
theorem powerTorsion_eq_ker (n : ℕ) : powerTorsion f M n = LinearMap.ker (powerSmul f M n) := by
  ext x
  simp

/-- Higher powers kill more. -/
theorem powerTorsion_monotone : Monotone (powerTorsion f M) := by
  intro n m hnm x hx
  rw [mem_powerTorsion] at hx ⊢
  rw [← Nat.add_sub_cancel' hnm, pow_add, mul_comm, mul_smul, hx, smul_zero]

/-- **The `fⁿ`-torsion of a Noetherian module stabilizes.** The submodules `M[fⁿ]` increase with
`n`, so the ascending chain condition gives a level past which they are all equal. -/
theorem exists_powerTorsion_stable [IsNoetherian A M] :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → powerTorsion f M n = powerTorsion f M N := by
  obtain ⟨N, hN⟩ := monotone_stabilizes_iff_noetherian.2 ‹IsNoetherian A M›
    ⟨powerTorsion f M, powerTorsion_monotone f M⟩
  exact ⟨N, fun n hn ↦ (hN n hn).symm⟩

/-! ### The sequence `0 ⟶ fⁿM ⟶ M ⟶ M / fⁿM ⟶ 0` -/

/-- The short exact sequence `0 ⟶ fⁿM ⟶ M ⟶ M / fⁿM ⟶ 0`. -/
def powerQuotientShortComplex (n : ℕ) : ShortComplex (ModuleCat.{v} A) :=
  ShortComplex.mk (ModuleCat.ofHom (powerSmulTop f M n).subtype)
    (ModuleCat.ofHom (powerSmulTop f M n).mkQ) (by
      ext x
      exact (Submodule.Quotient.mk_eq_zero _).2 x.2)

/-- **The quotient sequence is short exact.** -/
theorem powerQuotientShortComplex_shortExact (n : ℕ) :
    (powerQuotientShortComplex f M n).ShortExact := by
  refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
  · intro x
    refine ⟨fun hx ↦ ⟨⟨x, (Submodule.Quotient.mk_eq_zero _).1 hx⟩, rfl⟩, ?_⟩
    rintro ⟨y, rfl⟩
    exact (Submodule.Quotient.mk_eq_zero _).2 y.2
  · exact Subtype.val_injective
  · exact Submodule.mkQ_surjective _

/-! ### The sequence `0 ⟶ M[fⁿ] ⟶ M ⟶ fⁿM ⟶ 0` -/

/-- Multiplication by `fⁿ`, corestricted to its image `fⁿM`. -/
def powerSmulToSmulTop (n : ℕ) : M ⟶ ModuleCat.of A (powerSmulTop f M n) :=
  ModuleCat.ofHom ((powerSmul f M n).codRestrict _ (powerSmul_mem_powerSmulTop f M n))

/-- Multiplication by `fⁿ` corestricted to `fⁿM` sends `x` to `fⁿ • x`. -/
@[simp]
theorem powerSmulToSmulTop_apply_coe (n : ℕ) (x : M) :
    (powerSmulToSmulTop f M n x : M) = f ^ n • x := rfl

/-- The short exact sequence `0 ⟶ M[fⁿ] ⟶ M ⟶ fⁿM ⟶ 0`, whose second map is multiplication by
`fⁿ`. -/
def powerTorsionShortComplex (n : ℕ) : ShortComplex (ModuleCat.{v} A) :=
  ShortComplex.mk (ModuleCat.ofHom (powerTorsion f M n).subtype) (powerSmulToSmulTop f M n) (by
    ext x
    exact (mem_powerTorsion f M).1 x.2)

/-- **The torsion sequence is short exact.** Its exactness at `M` is the definition of `M[fⁿ]`, and
its surjectivity is the description of `fⁿM` as the range of multiplication by `fⁿ`. -/
@[sga "7 VIII 2.3" "special case"]
theorem powerTorsionShortComplex_shortExact (n : ℕ) :
    (powerTorsionShortComplex f M n).ShortExact := by
  refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
  · intro x
    refine ⟨fun hx ↦ ⟨⟨x, (mem_powerTorsion f M).2 (congrArg Subtype.val hx)⟩, rfl⟩, ?_⟩
    rintro ⟨y, rfl⟩
    exact Subtype.ext ((mem_powerTorsion f M).1 y.2)
  · exact Subtype.val_injective
  · rintro ⟨x, hx⟩
    obtain ⟨y, rfl⟩ := (powerSmulTop_eq_range f M n).le hx
    exact ⟨y, rfl⟩

end Stacks.LocalCohomology

end
