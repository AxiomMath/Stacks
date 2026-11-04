module

public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.Combinatorics.Enumerative.Bell
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.Basic
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.OddVariable.Extension

/-!
# Adjoining an odd variable: uniqueness of compatible divided powers

Let `A` carry divided powers on its positive even part and let `d` be odd.  This file defines the
odd part `oddPart` of `A` and the compatibility condition `IsOddVariableDividedPowerExtension` for
divided powers on the odd-variable extension `A⟨T⟩`.  It shows that a compatible structure is
forced to satisfy `γ_n (x + yT) = γ_n(x) + γ_{n-1}(x) y T` on the positive even part, hence is
unique, and introduces the candidate operations given by that formula, together with their basic
properties.

## Main definitions

* `DividedPowers.TateResolution.oddPart` — the sum of the odd homogeneous pieces of `A`.
* `DividedPowers.TateResolution.IsOddVariableDividedPowerExtension` — compatibility of divided
  powers on `A⟨T⟩` with those on `A`.

## References

* [Stacks Project, Tag 09PH](https://stacks.math.columbia.edu/tag/09PH)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v

section OddDividedPowers

open OddVariableExtension
open scoped RightActions

attribute [local implicit_reducible] TwistedModule


variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]

/-- The sum of the odd homogeneous pieces of a nonnegatively graded algebra. -/
public abbrev oddPart (Aᵢ : ℕ → Submodule R A) : Submodule R A :=
  ⨆ e : ℕ, Aᵢ (2 * e + 1)

/-- A divided power structure on an odd-variable extension is compatible with the one on its
coefficient algebra if the canonical inclusion preserves all divided powers. -/
public def IsOddVariableDividedPowerExtension (Aᵢ : ℕ → Submodule R A)
    [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ] (d : ℕ)
    (gamma : DividedPowerStructure Aᵢ)
    (delta : DividedPowerStructure (OddVariableExtension.grade Aᵢ d)) : Prop :=
  ∀ (n : ℕ) (x : A), x ∈ positiveEvenPart Aᵢ →
    delta.dpow n (inclusion Aᵢ d x) = inclusion Aᵢ d (gamma.dpow n x)

/-- The inclusion of `A` preserves membership in a sum of graded pieces indexed by `p`. -/
private theorem inclusion_mem_iSup_grade
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] (d : ℕ) (p : ℕ → ℕ) {x : A}
    (hx : x ∈ ⨆ e, Aᵢ (p e)) :
    inclusion Aᵢ d x ∈ ⨆ e, OddVariableExtension.grade Aᵢ d (p e) := by
  classical
  obtain ⟨f, hf, hfsum⟩ :=
    (Submodule.mem_iSup_iff_exists_finsupp (fun e ↦ Aᵢ (p e)) x).mp hx
  rw [← hfsum, Finsupp.sum]
  change TrivSqZeroExt.inl (∑ e ∈ f.support, f e) ∈ _
  rw [TrivSqZeroExt.inl_sum]
  exact Submodule.sum_mem _ fun e _ ↦ Submodule.mem_iSup_of_mem e
    (OddVariableExtension.inclusion_mem_grade Aᵢ d (p e) (hf e))

/-- Multiplying an odd element by the variable lands in a sum of graded pieces indexed by `p`
as soon as `p (c e) = 2 * e + 1 + d` for all `e`. -/
private theorem inr_mem_iSup_grade
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] (d : ℕ) (p c : ℕ → ℕ)
    (hc : ∀ e, p (c e) = 2 * e + 1 + d) {y : A} (hy : y ∈ oddPart Aᵢ) :
    TrivSqZeroExt.inr (show TwistedModule Aᵢ d from y) ∈
      ⨆ e, OddVariableExtension.grade Aᵢ d (p e) := by
  classical
  obtain ⟨f, hf, hfsum⟩ :=
    (Submodule.mem_iSup_iff_exists_finsupp (fun e : ℕ ↦ Aᵢ (2 * e + 1)) y).mp hy
  rw [← hfsum, Finsupp.sum]
  change TrivSqZeroExt.inr
    (∑ e ∈ f.support, (show TwistedModule Aᵢ d from f e)) ∈ _
  rw [TrivSqZeroExt.inr_sum]
  refine Submodule.sum_mem _ fun e _ ↦ Submodule.mem_iSup_of_mem (c e) ?_
  rw [hc]
  exact OddVariableExtension.inr_mem_grade Aᵢ d (hf e)

private theorem inr_mem_positiveEvenPart
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] (d : ℕ)
    (hd_odd : Odd d) {y : A} (hy : y ∈ oddPart Aᵢ) :
    TrivSqZeroExt.inr (show TwistedModule Aᵢ d from y) ∈
      positiveEvenPart (OddVariableExtension.grade Aᵢ d) := by
  obtain ⟨q, hq⟩ := hd_odd
  exact inr_mem_iSup_grade Aᵢ d (fun e ↦ 2 * (e + 1)) (· + q) (fun e ↦ by omega) hy

private theorem inclusion_mem_positiveEvenPart
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] (d : ℕ)
    {x : A} (hx : x ∈ positiveEvenPart Aᵢ) :
    inclusion Aᵢ d x ∈ positiveEvenPart (OddVariableExtension.grade Aᵢ d) :=
  inclusion_mem_iSup_grade Aᵢ d (fun e ↦ 2 * (e + 1)) hx

/-- Multiplying by an even element preserves a sum of graded pieces of fixed parity `b`. -/
private theorem evenPart_mul_iSup_mem
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] (b : ℕ)
    {x y : A} (hx : x ∈ evenPart Aᵢ) (hy : y ∈ ⨆ e : ℕ, Aᵢ (2 * e + b)) :
    x * y ∈ ⨆ e : ℕ, Aᵢ (2 * e + b) := by
  classical
  obtain ⟨f, hf, hfsum⟩ :=
    (Submodule.mem_iSup_iff_exists_finsupp (fun e : ℕ ↦ Aᵢ (2 * e)) x).mp hx
  obtain ⟨g, hg, hgsum⟩ :=
    (Submodule.mem_iSup_iff_exists_finsupp (fun e : ℕ ↦ Aᵢ (2 * e + b)) y).mp hy
  rw [← hfsum, ← hgsum, Finsupp.sum, Finsupp.sum, Finset.sum_mul_sum]
  refine Submodule.sum_mem _ fun i _ ↦ Submodule.sum_mem _ fun j _ ↦
    Submodule.mem_iSup_of_mem (i + j) ?_
  simpa [Nat.mul_add, Nat.add_assoc] using
    SetLike.mul_mem_graded (i := 2 * i) (j := 2 * j + b) (hf i) (hg j)

private theorem evenPart_mul_oddPart_mem
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ]
    {x y : A} (hx : x ∈ evenPart Aᵢ) (hy : y ∈ oddPart Aᵢ) :
    x * y ∈ oddPart Aᵢ :=
  evenPart_mul_iSup_mem Aᵢ 1 hx hy

private theorem evenPart_mul_evenPart_mem
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ]
    {x y : A} (hx : x ∈ evenPart Aᵢ)
    (hy : y ∈ evenPart Aᵢ) :
    x * y ∈ evenPart Aᵢ :=
  evenPart_mul_iSup_mem Aᵢ 0 hx hy

private theorem evenPart_pow_mem
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ]
    {x : A} (hx : x ∈ evenPart Aᵢ) (n : ℕ) :
    x ^ n ∈ evenPart Aᵢ := by
  induction n with
  | zero =>
      apply Submodule.mem_iSup_of_mem 0
      simpa using (SetLike.GradedOne.one_mem : (1 : A) ∈ Aᵢ 0)
  | succ n ih =>
      rw [pow_succ]
      exact evenPart_mul_evenPart_mem Aᵢ ih hx

private theorem signRingEquiv_eq_self_of_evenPart
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] (d : ℕ)
    {x : A} (hx : x ∈ evenPart Aᵢ) :
    signRingEquiv Aᵢ d x = x := by
  classical
  obtain ⟨f, hf, hfsum⟩ :=
    (Submodule.mem_iSup_iff_exists_finsupp (fun e : ℕ ↦ Aᵢ (2 * e)) x).mp hx
  rw [← hfsum, Finsupp.sum, map_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [signRingEquiv_of_mem Aᵢ d (2 * e) (hf e)]
  have hpow : d * (2 * e) = 2 * (d * e) := by ring
  simp [hpow]

private theorem evenPart_comm_oddPart
    (Aᵢ : ℕ → Submodule R A) [IsStrictlyGradedComm Aᵢ] {x y : A}
    (hx : x ∈ evenPart Aᵢ) (hy : y ∈ oddPart Aᵢ) : x * y = y * x := by
  classical
  obtain ⟨f, hf, hfsum⟩ :=
    (Submodule.mem_iSup_iff_exists_finsupp (fun e : ℕ ↦ Aᵢ (2 * e)) x).mp hx
  obtain ⟨g, hg, hgsum⟩ :=
    (Submodule.mem_iSup_iff_exists_finsupp (fun e : ℕ ↦ Aᵢ (2 * e + 1)) y).mp hy
  rw [← hfsum, ← hgsum, Finsupp.sum, Finsupp.sum,
    Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hcomm := IsStrictlyGradedComm.graded_comm (hf j) (hg i)
  have hpow : (2 * j) * (2 * i + 1) = 2 * (j * (2 * i + 1)) := by ring
  simpa [hpow] using hcomm

/-- The coefficients of an element of a sum of graded pieces indexed by `p` lie in the
corresponding pieces of `A`, and the second one is odd. -/
private theorem coeff_mem_of_mem_iSup_grade
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] (d : ℕ) (p : ℕ → ℕ)
    (hp : ∀ e, d ≤ p e → ∃ e', p e - d = 2 * e' + 1) {z : OddVariableExtension Aᵢ d}
    (hz : z ∈ ⨆ e, OddVariableExtension.grade Aᵢ d (p e)) :
    z.fst ∈ ⨆ e, Aᵢ (p e) ∧ z.snd ∈ oddPart Aᵢ := by
  classical
  obtain ⟨f, hf, hfsum⟩ :=
    (Submodule.mem_iSup_iff_exists_finsupp
      (fun e ↦ OddVariableExtension.grade Aᵢ d (p e)) z).mp hz
  have hfst : z.fst = f.sum (fun e x ↦ x.fst) := by
    rw [← hfsum]
    simp only [Finsupp.sum, TrivSqZeroExt.fst_sum]
  have hsnd : (show A from z.snd) = f.sum (fun e x ↦ (show A from x.snd)) := by
    rw [← hfsum]
    simp only [Finsupp.sum, TrivSqZeroExt.snd_sum]
    rfl
  constructor
  · rw [hfst, Finsupp.sum]
    exact Submodule.sum_mem _ fun e _ ↦ Submodule.mem_iSup_of_mem e
      ((OddVariableExtension.mem_grade_iff Aᵢ d (p e) (f e)).mp (hf e)).1
  · change (show A from z.snd) ∈ oddPart Aᵢ
    rw [hsnd, Finsupp.sum]
    refine Submodule.sum_mem _ fun e _ ↦ ?_
    have hsecond : (show A from (f e).snd) ∈
        (if d ≤ p e then Aᵢ (p e - d) else ⊥) :=
      ((OddVariableExtension.mem_grade_iff Aᵢ d (p e) (f e)).mp (hf e)).2
    by_cases hle : d ≤ p e
    · obtain ⟨e', he'⟩ := hp e hle
      refine Submodule.mem_iSup_of_mem e' ?_
      simpa [hle, he'] using hsecond
    · have hzero : (show A from (f e).snd) = 0 := by
        simpa [hle] using hsecond
      simp [hzero]

/-- An element is determined to lie in a submodule by its two coordinates. -/
private theorem mem_of_inclusion_fst_of_inr_snd
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] (d : ℕ)
    {S : Submodule R (OddVariableExtension Aᵢ d)} (z : OddVariableExtension Aᵢ d)
    (hx : inclusion Aᵢ d z.fst ∈ S)
    (hy : TrivSqZeroExt.inr (show TwistedModule Aᵢ d from (show A from z.snd)) ∈ S) :
    z ∈ S := by
  rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq z]
  exact S.add_mem hx hy

private theorem positiveEvenPart_coeff_iff
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] (d : ℕ) (hd_odd : Odd d)
    (z : OddVariableExtension Aᵢ d) :
    z ∈ positiveEvenPart (OddVariableExtension.grade Aᵢ d) ↔
      z.fst ∈ positiveEvenPart Aᵢ ∧ z.snd ∈ oddPart Aᵢ := by
  refine ⟨fun hz ↦ ?_, fun ⟨hx, hy⟩ ↦ mem_of_inclusion_fst_of_inr_snd Aᵢ d z
    (inclusion_mem_positiveEvenPart Aᵢ d hx) (inr_mem_positiveEvenPart Aᵢ d hd_odd hy)⟩
  obtain ⟨q, hq⟩ := hd_odd
  exact coeff_mem_of_mem_iSup_grade Aᵢ d (fun e ↦ 2 * (e + 1))
    (fun e he ↦ ⟨e - q, by omega⟩) hz

private theorem inclusion_mem_evenPart
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] (d : ℕ)
    {x : A} (hx : x ∈ evenPart Aᵢ) :
    inclusion Aᵢ d x ∈ evenPart (OddVariableExtension.grade Aᵢ d) :=
  inclusion_mem_iSup_grade Aᵢ d (fun e ↦ 2 * e) hx

private theorem inr_mem_evenPart
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] (d : ℕ)
    (hd_odd : Odd d) {y : A} (hy : y ∈ oddPart Aᵢ) :
    TrivSqZeroExt.inr (show TwistedModule Aᵢ d from y) ∈
      evenPart (OddVariableExtension.grade Aᵢ d) := by
  obtain ⟨q, hq⟩ := hd_odd
  exact inr_mem_iSup_grade Aᵢ d (fun e ↦ 2 * e) (· + q + 1) (fun e ↦ by omega) hy

private theorem evenPart_coeff_iff
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] (d : ℕ) (hd_odd : Odd d)
    (z : OddVariableExtension Aᵢ d) :
    z ∈ evenPart (OddVariableExtension.grade Aᵢ d) ↔
      z.fst ∈ evenPart Aᵢ ∧ z.snd ∈ oddPart Aᵢ := by
  refine ⟨fun hz ↦ ?_, fun ⟨hx, hy⟩ ↦ mem_of_inclusion_fst_of_inr_snd Aᵢ d z
    (inclusion_mem_evenPart Aᵢ d hx) (inr_mem_evenPart Aᵢ d hd_odd hy)⟩
  obtain ⟨q, hq⟩ := hd_odd
  exact coeff_mem_of_mem_iSup_grade Aᵢ d (fun e ↦ 2 * e)
    (fun e he ↦ ⟨e - q - 1, by omega⟩) hz

private theorem evenPart_mul_positiveEvenPart_extension_mem
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ]
    [IsStrictlyGradedComm Aᵢ] (d : ℕ) (hd_odd : Odd d)
    {x y : OddVariableExtension Aᵢ d}
    (hx : x ∈ evenPart (OddVariableExtension.grade Aᵢ d))
    (hy : y ∈ positiveEvenPart (OddVariableExtension.grade Aᵢ d)) :
    x * y ∈ positiveEvenPart (OddVariableExtension.grade Aᵢ d) := by
  rcases (evenPart_coeff_iff Aᵢ d hd_odd x).mp hx with ⟨hxa, hxb⟩
  rcases (positiveEvenPart_coeff_iff Aᵢ d hd_odd y).mp hy with ⟨hyc, hyd⟩
  have hycEven : y.fst ∈ evenPart Aᵢ :=
    positiveEvenPart_le_evenPart Aᵢ hyc
  have hfst : x.fst * y.fst ∈ positiveEvenPart Aᵢ :=
    evenPart_mul_positiveEvenPart Aᵢ hxa hyc
  have hsnd₁ : x.fst * (show A from y.snd) ∈ oddPart Aᵢ :=
    evenPart_mul_oddPart_mem Aᵢ hxa hyd
  have hsign : signRingEquiv Aᵢ d y.fst = y.fst :=
    signRingEquiv_eq_self_of_evenPart Aᵢ d hycEven
  have hsnd₂ : (show A from x.snd) * signRingEquiv Aᵢ d y.fst ∈ oddPart Aᵢ := by
    rw [hsign]
    exact (evenPart_comm_oddPart Aᵢ hycEven hxb).symm ▸
      evenPart_mul_oddPart_mem Aᵢ hycEven hxb
  have hsnd : (show A from (x * y).snd) ∈ oddPart Aᵢ := by
    rw [OddVariableExtension.mul_snd]
    exact oddPart Aᵢ |>.add_mem hsnd₁ hsnd₂
  exact (positiveEvenPart_coeff_iff Aᵢ d hd_odd (x * y)).2 ⟨hfst, hsnd⟩

private theorem dpow_add_range
    {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (delta : DividedPowerStructure 𝒜) {n : ℕ} {x y : A}
    (hx : x ∈ positiveEvenPart 𝒜) (hy : y ∈ positiveEvenPart 𝒜) :
    delta.dpow n (x + y) =
      ∑ k ∈ Finset.range (n + 1), delta.dpow k x * delta.dpow (n - k) y := by
  rw [delta.dpow_add hx hy, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]


/-- If the divided powers `γ_m v` vanish for `m > 1`, then `γ_n (u + v) = γ_n u + γ_{n-1} u * v`. -/
private theorem dpow_add_of_dpow_eq_zero
    {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (delta : DividedPowerStructure 𝒜) {n : ℕ} (hn : n ≠ 0) {u v : A}
    (hu : u ∈ positiveEvenPart 𝒜) (hv : v ∈ positiveEvenPart 𝒜)
    (hvan : ∀ m, 1 < m → delta.dpow m v = 0) :
    delta.dpow n (u + v) = delta.dpow n u + delta.dpow (n - 1) u * v := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [delta.dpow_add hu hv, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_eq_zero, zero_add]
  · simp [delta.dpow_zero hv, delta.dpow_one hv, add_comm]
  · intro k hk
    rw [hvan _ (by have := Finset.mem_range.mp hk; omega), mul_zero]

private theorem inclusion_mul_generator
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] (d : ℕ) (a : A) :
    inclusion Aᵢ d a * generator Aᵢ d =
      TrivSqZeroExt.inr (show TwistedModule Aᵢ d from a) := by
  simp [inclusion, generator, TrivSqZeroExt.inl_mul_inr]

private theorem dpow_zero_of_odd_square
    {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (delta : DividedPowerStructure 𝒜) {n : ℕ} (hn : 1 < n) :
    delta.dpow n 0 = 0 := by
  simpa using delta.dpow_mul_odd (d := 0) (e := 0) hn
    (Submodule.zero_mem _) (Submodule.zero_mem _)

private theorem dpow_inr_homogeneous_eq_zero
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ]
    (d : ℕ) (hd_odd : Odd d)
    (delta : DividedPowerStructure (OddVariableExtension.grade Aᵢ d))
    {n e : ℕ} (hn : 1 < n) {y : A} (hy : y ∈ Aᵢ (2 * e + 1)) :
    delta.dpow n (TrivSqZeroExt.inr (show TwistedModule Aᵢ d from y)) = 0 := by
  rcases hd_odd with ⟨q, hq⟩
  rw [← inclusion_mul_generator Aᵢ d y]
  exact delta.dpow_mul_odd (d := e) (e := q) hn
    (OddVariableExtension.inclusion_mem_grade Aᵢ d (2 * e + 1) hy)
    (by simpa [hq] using OddVariableExtension.generator_mem_grade Aᵢ d)

private theorem dpow_sum_inr_eq_zero
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ]
    (d : ℕ) (hd_odd : Odd d)
    (delta : DividedPowerStructure (OddVariableExtension.grade Aᵢ d))
    {f : ℕ →₀ A} (hf : ∀ e, f e ∈ Aᵢ (2 * e + 1)) {n : ℕ} (hn : 1 < n) :
    delta.dpow n (TrivSqZeroExt.inr (show TwistedModule Aᵢ d from f.sum fun _ x ↦ x)) = 0 := by
  classical
  have hsum : ∀ s : Finset ℕ, ∀ n : ℕ, 1 < n →
      delta.dpow n (∑ e ∈ s, TrivSqZeroExt.inr
        (show TwistedModule Aᵢ d from f e)) = 0 := by
    intro s
    induction s using Finset.induction with
    | empty =>
        intro n hn
        simpa using dpow_zero_of_odd_square delta hn
    | @insert e s hes ih =>
        intro n hn
        let w : OddVariableExtension Aᵢ d :=
          ∑ i ∈ s, TrivSqZeroExt.inr (show TwistedModule Aᵢ d from f i)
        let v : OddVariableExtension Aᵢ d :=
          TrivSqZeroExt.inr (show TwistedModule Aᵢ d from f e)
        have hw : w ∈ positiveEvenPart (OddVariableExtension.grade Aᵢ d) := by
          dsimp [w]
          exact Submodule.sum_mem _ fun i _ ↦ inr_mem_positiveEvenPart Aᵢ d hd_odd
            (Submodule.mem_iSup_of_mem i (hf i))
        have hv : v ∈ positiveEvenPart (OddVariableExtension.grade Aᵢ d) := by
          dsimp [v]
          exact inr_mem_positiveEvenPart Aᵢ d hd_odd
            (Submodule.mem_iSup_of_mem e (hf e))
        have hwv : w * v = 0 := by
          dsimp [w, v]
          rw [Finset.sum_mul]
          apply Finset.sum_eq_zero
          intro i hi
          simp [TrivSqZeroExt.inr_mul_inr]
        have hvan : ∀ m, 1 < m → delta.dpow m v = 0 := fun m hm ↦
          dpow_inr_homogeneous_eq_zero Aᵢ d hd_odd delta hm (hf e)
        rw [Finset.sum_insert hes, add_comm,
          dpow_add_of_dpow_eq_zero delta (by omega) hw hv hvan, ih n hn, zero_add]
        by_cases hn2 : n = 2
        · subst n
          rw [Nat.add_one_sub_one, delta.dpow_one hw]
          exact hwv
        · rw [ih (n - 1) (by omega), zero_mul]
  simpa only [Finsupp.sum, TrivSqZeroExt.inr_sum] using hsum f.support n hn

private theorem dpow_inr_eq_if
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ]
    (d : ℕ) (hd_odd : Odd d)
    (delta : DividedPowerStructure (OddVariableExtension.grade Aᵢ d))
    {y : A} (hy : y ∈ oddPart Aᵢ) (n : ℕ) :
    delta.dpow n (TrivSqZeroExt.inr (show TwistedModule Aᵢ d from y)) =
      if n = 0 then 1 else if n = 1 then
        TrivSqZeroExt.inr (show TwistedModule Aᵢ d from y) else 0 := by
  have hy' := inr_mem_positiveEvenPart Aᵢ d hd_odd hy
  cases n with
  | zero => simp [delta.dpow_zero hy']
  | succ n =>
      cases n with
      | zero => simp [delta.dpow_one hy']
      | succ n =>
          obtain ⟨f, hf, hfsum⟩ :=
            (Submodule.mem_iSup_iff_exists_finsupp
              (fun e : ℕ ↦ Aᵢ (2 * e + 1)) y).mp hy
          have h := dpow_sum_inr_eq_zero Aᵢ d hd_odd delta hf
            (n := n + 2) (by omega)
          show delta.dpow (n + 2)
            (TrivSqZeroExt.inr (show TwistedModule Aᵢ d from y)) = 0
          rw [← hfsum]
          exact h

private theorem dpow_inclusion_add_oddFormula
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ]
    (gamma : DividedPowerStructure Aᵢ) (d : ℕ) (hd_odd : Odd d)
    (delta : DividedPowerStructure (OddVariableExtension.grade Aᵢ d))
    (hExt : IsOddVariableDividedPowerExtension Aᵢ d gamma delta)
    (n : ℕ) (hn : n ≠ 0) (x y : A) (hx : x ∈ positiveEvenPart Aᵢ)
    (hy : y ∈ oddPart Aᵢ) :
    delta.dpow n (inclusion Aᵢ d x + inclusion Aᵢ d y * generator Aᵢ d) =
      inclusion Aᵢ d (gamma.dpow n x) +
        inclusion Aᵢ d (gamma.dpow (n - 1) x * y) * generator Aᵢ d := by
  have hleft : inclusion Aᵢ d x ∈ positiveEvenPart (OddVariableExtension.grade Aᵢ d) :=
    inclusion_mem_positiveEvenPart Aᵢ d hx
  have hright : TrivSqZeroExt.inr (show TwistedModule Aᵢ d from y) ∈
      positiveEvenPart (OddVariableExtension.grade Aᵢ d) :=
    inr_mem_positiveEvenPart Aᵢ d hd_odd hy
  have hvan : ∀ m, 1 < m → delta.dpow m
      (TrivSqZeroExt.inr (show TwistedModule Aᵢ d from y)) = 0 := fun m hm ↦ by
    simpa [Nat.ne_of_gt (by omega : 0 < m), show m ≠ 1 by omega] using
      dpow_inr_eq_if Aᵢ d hd_odd delta hy m
  have hmul (a : A) : inclusion Aᵢ d a *
      TrivSqZeroExt.inr (show TwistedModule Aᵢ d from y) =
      TrivSqZeroExt.inr (show TwistedModule Aᵢ d from a * y) := by
    simp [inclusion, TrivSqZeroExt.inl_mul_inr]
  rw [inclusion_mul_generator Aᵢ d y,
    dpow_add_of_dpow_eq_zero delta hn hleft hright hvan, hExt n x hx, hExt (n - 1) x hx,
    hmul, inclusion_mul_generator Aᵢ d]

private theorem sum_range_shift_left {M : Type*} [Semiring M] (n : ℕ)
    (f g : ℕ → M) :
    ∑ k ∈ Finset.range (n + 1), (if k = 0 then 0 else f (k - 1) * g (n - k)) =
      ∑ k ∈ Finset.range n, f k * g (n - 1 - k) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ']
      simp [Nat.succ_sub_succ_eq_sub]

private theorem sum_range_drop_last {M : Type*} [AddCommMonoid M] (n : ℕ)
    (f : ℕ → M) :
    ∑ k ∈ Finset.range (n + 1), (if k = n then 0 else f k) =
      ∑ k ∈ Finset.range n, f k := by
  rw [Finset.sum_range_succ]
  simp only [ite_true, add_zero]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≠ n := (Finset.mem_range.mp hk).ne
  simp [hkn]

/-- The factorial coefficient governing iterated divided powers is a uniform Bell number. -/
private theorem factorial_div_eq_uniformBell (n : ℕ) {m : ℕ} (hm : m ≠ 0) :
    (n * m).factorial / (n.factorial * m.factorial ^ n) = Nat.uniformBell n m := by
  rw [Nat.uniformBell_eq_div n hm, Nat.mul_comm n.factorial (m.factorial ^ n)]

private theorem uniformBell_succ_left_choose (n m : ℕ) :
    Nat.uniformBell (n + 1) m =
      Nat.choose ((n + 1) * m - 1) (n * m) * Nat.uniformBell n m := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp [Nat.uniformBell_zero_right]
  · rw [Nat.uniformBell_succ_left]
    congr 1
    have hN : n * m + m - 1 = (n + 1) * m - 1 := by rw [Nat.succ_mul]
    have hle : m - 1 ≤ n * m + m - 1 := by omega
    rw [← hN, ← Nat.choose_symm hle]
    congr 1
    omega

/-- The recursion satisfied by the coefficient of an iterated divided power. -/
private theorem factorial_div_succ (n m : ℕ) (hm : m ≠ 0) :
    (((n + 1) * m).factorial /
        ((n + 1).factorial * m.factorial ^ (n + 1))) =
      Nat.choose ((n + 1) * m - 1) (n * m) *
        ((n * m).factorial / (n.factorial * m.factorial ^ n)) := by
  rw [factorial_div_eq_uniformBell (n + 1) hm, factorial_div_eq_uniformBell n hm]
  exact uniformBell_succ_left_choose n m

private theorem oddVariableDividedPowerStructure_unique
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ]
    (gamma : DividedPowerStructure Aᵢ) (d : ℕ) (hd_odd : Odd d)
    {delta epsilon : DividedPowerStructure (OddVariableExtension.grade Aᵢ d)}
    (hdelta : IsOddVariableDividedPowerExtension Aᵢ d gamma delta)
    (hepsilon : IsOddVariableDividedPowerExtension Aᵢ d gamma epsilon) :
    delta = epsilon := by
  apply DividedPowerStructure.ext
  funext n z
  by_cases hz : z ∈ positiveEvenPart (OddVariableExtension.grade Aᵢ d)
  · rcases (positiveEvenPart_coeff_iff Aᵢ d hd_odd z).mp hz with ⟨hx, hy⟩
    have hdecomp : z = inclusion Aᵢ d z.fst +
        inclusion Aᵢ d z.snd * generator Aᵢ d := by
      rw [inclusion_mul_generator]
      exact (TrivSqZeroExt.inl_fst_add_inr_snd_eq z).symm
    cases n with
    | zero => simp [delta.dpow_zero hz, epsilon.dpow_zero hz]
    | succ n =>
        have hδ := dpow_inclusion_add_oddFormula Aᵢ gamma d hd_odd delta hdelta
          (n + 1) (by omega) z.fst z.snd hx hy
        have hε := dpow_inclusion_add_oddFormula Aᵢ gamma d hd_odd epsilon hepsilon
          (n + 1) (by omega) z.fst z.snd hx hy
        rw [← hdecomp] at hδ hε
        exact hδ.trans hε.symm
  · rw [delta.dpow_null hz, epsilon.dpow_null hz]

private noncomputable def canonicalOddDpow
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ]
    (gamma : DividedPowerStructure Aᵢ) (d : ℕ) :
    ℕ → OddVariableExtension Aᵢ d → OddVariableExtension Aᵢ d := by
  classical
  exact fun n z ↦ if hz : z ∈ positiveEvenPart (OddVariableExtension.grade Aᵢ d) then
    if n = 0 then 1 else inclusion Aᵢ d (gamma.dpow n z.fst) +
      TrivSqZeroExt.inr (show TwistedModule Aᵢ d from
        gamma.dpow (n - 1) z.fst * (show A from z.snd)) else 0

private theorem canonicalOddDpow_of_mem
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ]
    (gamma : DividedPowerStructure Aᵢ) (d : ℕ)
    {z : OddVariableExtension Aᵢ d}
    (hz : z ∈ positiveEvenPart (OddVariableExtension.grade Aᵢ d)) (n : ℕ) :
    canonicalOddDpow Aᵢ gamma d n z =
      if n = 0 then 1 else inclusion Aᵢ d (gamma.dpow n z.fst) +
        TrivSqZeroExt.inr (show TwistedModule Aᵢ d from
          gamma.dpow (n - 1) z.fst * (show A from z.snd)) := by
  simp [canonicalOddDpow, hz]

private theorem canonicalOddDpow_mem
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ]
    (gamma : DividedPowerStructure Aᵢ) (d : ℕ) (hd_odd : Odd d)
    {z : OddVariableExtension Aᵢ d}
    (hz : z ∈ positiveEvenPart (OddVariableExtension.grade Aᵢ d))
    {n : ℕ} (hn : n ≠ 0) :
    canonicalOddDpow Aᵢ gamma d n z ∈
      positiveEvenPart (OddVariableExtension.grade Aᵢ d) := by
  rcases (positiveEvenPart_coeff_iff Aᵢ d hd_odd z).mp hz with ⟨hx, hy⟩
  have hfirst : gamma.dpow n z.fst ∈ positiveEvenPart Aᵢ :=
    gamma.dpow_mem hn hx
  have hsecond : gamma.dpow (n - 1) z.fst * (show A from z.snd) ∈ oddPart Aᵢ := by
    by_cases hn1 : n = 1
    · subst n
      simpa [gamma.dpow_zero hx] using hy
    · have hnsub : n - 1 ≠ 0 := by omega
      have hpos : gamma.dpow (n - 1) z.fst ∈ positiveEvenPart Aᵢ :=
        gamma.dpow_mem hnsub hx
      have heven : gamma.dpow (n - 1) z.fst ∈ evenPart Aᵢ :=
        positiveEvenPart_le_evenPart Aᵢ hpos
      exact evenPart_mul_oddPart_mem Aᵢ heven hy
  rw [canonicalOddDpow_of_mem Aᵢ gamma d hz n]
  simp only [ite_eq_right hn]
  exact (positiveEvenPart_coeff_iff Aᵢ d hd_odd _).2
    ⟨by simpa [inclusion] using hfirst, by simpa [inclusion] using hsecond⟩

private theorem canonicalOddDpow_zero
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ]
    (gamma : DividedPowerStructure Aᵢ) (d : ℕ) {z : OddVariableExtension Aᵢ d}
    (hz : z ∈ positiveEvenPart (OddVariableExtension.grade Aᵢ d)) :
    canonicalOddDpow Aᵢ gamma d 0 z = 1 := by
  simp [canonicalOddDpow_of_mem Aᵢ gamma d hz 0]

private theorem canonicalOddDpow_one
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ]
    (gamma : DividedPowerStructure Aᵢ) (d : ℕ) (hd_odd : Odd d)
    {z : OddVariableExtension Aᵢ d}
    (hz : z ∈ positiveEvenPart (OddVariableExtension.grade Aᵢ d)) :
    canonicalOddDpow Aᵢ gamma d 1 z = z := by
  rcases (positiveEvenPart_coeff_iff Aᵢ d hd_odd z).mp hz with ⟨hx, hy⟩
  rw [canonicalOddDpow_of_mem Aᵢ gamma d hz 1]
  simp only [Nat.sub_self, gamma.dpow_one hx, gamma.dpow_zero hx, one_mul]
  exact TrivSqZeroExt.inl_fst_add_inr_snd_eq z

private theorem canonicalOddDpow_inclusion
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ]
    (gamma : DividedPowerStructure Aᵢ) (d : ℕ) {x : A}
    (hx : x ∈ positiveEvenPart Aᵢ) (n : ℕ) :
    canonicalOddDpow Aᵢ gamma d n (inclusion Aᵢ d x) =
      inclusion Aᵢ d (gamma.dpow n x) := by
  have hz : inclusion Aᵢ d x ∈ positiveEvenPart (OddVariableExtension.grade Aᵢ d) :=
    inclusion_mem_positiveEvenPart Aᵢ d hx
  by_cases hn : n = 0
  · subst n
    rw [canonicalOddDpow_zero Aᵢ gamma d hz, gamma.dpow_zero hx]
    simp [inclusion, TrivSqZeroExt.inlHom_apply]
  · rw [canonicalOddDpow_of_mem Aᵢ gamma d hz n]
    simp only [ite_eq_right hn]
    apply TrivSqZeroExt.ext
    · simp [inclusion, TrivSqZeroExt.inlHom_apply]
    · simp only [inclusion, TrivSqZeroExt.inlHom_apply,
        TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl,
        TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inr, zero_add]
      exact (mul_zero (gamma.dpow (n - 1) x) : gamma.dpow (n - 1) x * (0 : A) = 0)

private theorem canonicalOddDpow_mem_grade
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ]
    (gamma : DividedPowerStructure Aᵢ) (d : ℕ) (hd_odd : Odd d)
    {z : OddVariableExtension Aᵢ d} (hz : z ∈ positiveEvenPart (OddVariableExtension.grade Aᵢ d))
    {n e : ℕ} (hn : n ≠ 0) (he : z ∈ OddVariableExtension.grade Aᵢ d (2 * e)) :
    canonicalOddDpow Aᵢ gamma d n z ∈
      OddVariableExtension.grade Aᵢ d (2 * n * e) := by
  have hcoef := (OddVariableExtension.mem_grade_iff Aᵢ d (2 * e) z).mp he
  have hpos := (positiveEvenPart_coeff_iff Aᵢ d hd_odd z).mp hz |>.1
  have hfirst : gamma.dpow n z.fst ∈ Aᵢ (2 * n * e) := by
    simpa using gamma.dpow_mem_grade hn hpos hcoef.1
  have hsecond : gamma.dpow (n - 1) z.fst * (show A from z.snd) ∈
      (if d ≤ 2 * n * e then Aᵢ (2 * n * e - d) else ⊥) := by
    by_cases hdle : d ≤ 2 * e
    · have hy : (show A from z.snd) ∈ Aᵢ (2 * e - d) := by
        simpa [hdle] using hcoef.2
      have hnel : e ≤ n * e := by
        have hmul := Nat.mul_le_mul_right e (show 1 ≤ n by omega)
        simpa using hmul
      have hdle' : d ≤ 2 * n * e := by
        have hmul2 := Nat.mul_le_mul_left 2 hnel
        exact le_trans hdle (by simpa [Nat.mul_assoc] using hmul2)
      by_cases hn1 : n = 1
      · subst n
        simpa [hdle, hdle', gamma.dpow_zero hpos] using hy
      · have hnsub : n - 1 ≠ 0 := by omega
        have hgamma : gamma.dpow (n - 1) z.fst ∈ Aᵢ (2 * (n - 1) * e) :=
          gamma.dpow_mem_grade hnsub hpos hcoef.1
        have hmulmem : gamma.dpow (n - 1) z.fst * (show A from z.snd) ∈
            Aᵢ (2 * (n - 1) * e + (2 * e - d)) :=
          SetLike.mul_mem_graded hgamma hy
        have hidx : 2 * (n - 1) * e + (2 * e - d) = 2 * n * e - d := by
          have hdecomp : n - 1 + 1 = n := by omega
          have hnmul : (n - 1) * e + e = n * e := by
            calc
              (n - 1) * e + e = ((n - 1) + 1) * e := by ring
              _ = n * e := by rw [hdecomp]
          have hnmul2 : 2 * ((n - 1) * e) + 2 * e = 2 * (n * e) := by
            nlinarith [hnmul]
          have hsub : 2 * e - d + d = 2 * e := Nat.sub_add_cancel hdle
          have hsum : 2 * ((n - 1) * e) + (2 * e - d) + d = 2 * (n * e) := by
            nlinarith [hnmul2, hsub]
          have hbound : d ≤ 2 * (n * e) := by omega
          have hidx' : 2 * ((n - 1) * e) + (2 * e - d) = 2 * (n * e) - d := by
            omega
          calc
            2 * (n - 1) * e + (2 * e - d) =
                2 * ((n - 1) * e) + (2 * e - d) := by ring
            _ = 2 * (n * e) - d := hidx'
            _ = 2 * n * e - d := by rw [Nat.mul_assoc]
        simpa [hdle', hidx] using hmulmem
    · have hy : (show A from z.snd) = 0 := by simpa [hdle] using hcoef.2
      by_cases hdle' : d ≤ 2 * n * e <;> simp [hdle', hy]
  rw [canonicalOddDpow_of_mem Aᵢ gamma d hz n]
  simp only [ite_eq_right hn]
  rw [OddVariableExtension.mem_grade_iff]
  exact ⟨by simpa [inclusion] using hfirst, by simpa [inclusion] using hsecond⟩

private theorem oddHomogeneousProduct_fst_mul_snd_eq_zero
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ]
    [IsStrictlyGradedComm Aᵢ] (d : ℕ) (hd_odd : Odd d)
    {e f : ℕ} {x y : OddVariableExtension Aᵢ d}
    (hx : x ∈ OddVariableExtension.grade Aᵢ d (2 * e + 1))
    (hy : y ∈ OddVariableExtension.grade Aᵢ d (2 * f + 1)) :
    (x * y).fst * (show A from (x * y).snd) = 0 := by
  rcases hd_odd with ⟨q, hq⟩
  have hxcoord := (OddVariableExtension.mem_grade_iff Aᵢ d (2 * e + 1) x).mp hx
  have hycoord := (OddVariableExtension.mem_grade_iff Aᵢ d (2 * f + 1) y).mp hy
  have hxeven : (show A from x.snd) ∈ evenPart Aᵢ := by
    by_cases hle : d ≤ 2 * e + 1
    · have hmem : (show A from x.snd) ∈ Aᵢ (2 * e + 1 - d) := by
        simpa [hle] using hxcoord.2
      have hidx : 2 * e + 1 - d = 2 * (e - q) := by omega
      apply Submodule.mem_iSup_of_mem (e - q)
      simpa [hidx] using hmem
    · have hzero : (show A from x.snd) = 0 := by simpa [hle] using hxcoord.2
      simp [hzero]
  have hpowOdd : Odd ((2 * f + 1) * (2 * e + 1)) := by
    refine ⟨2 * f * e + f + e, ?_⟩
    ring
  have hyx : y.fst * x.fst = -(x.fst * y.fst) := by
    have h := IsStrictlyGradedComm.graded_comm hycoord.1 hxcoord.1
    simpa [smul_eq_mul, hpowOdd.neg_one_pow] using h
  have hsignPow : Odd (d * (2 * f + 1)) := by
    refine ⟨q * (2 * f + 1) + f, ?_⟩
    rw [hq]
    ring
  have hsignY : signRingEquiv Aᵢ d y.fst = -y.fst := by
    rw [signRingEquiv_of_mem Aᵢ d (2 * f + 1) hycoord.1]
    simp [hsignPow.neg_one_pow]
  have hySq : y.fst ^ 2 = 0 :=
    IsStrictlyGradedComm.odd_sq_zero hycoord.1
  have hxSq : x.fst ^ 2 = 0 :=
    IsStrictlyGradedComm.odd_sq_zero hxcoord.1
  have hyOddPart : y.fst ∈ oddPart Aᵢ :=
    Submodule.mem_iSup_of_mem f hycoord.1
  have hcommXY : y.fst * (show A from x.snd) =
      (show A from x.snd) * y.fst :=
    (evenPart_comm_oddPart Aᵢ hxeven hyOddPart).symm
  have hxSq' : x.fst * x.fst = 0 := by simpa [pow_two] using hxSq
  have hySq' : y.fst * y.fst = 0 := by simpa [pow_two] using hySq
  rw [TrivSqZeroExt.fst_mul, OddVariableExtension.mul_snd, hsignY]
  rw [mul_add]
  have hterm₁ : x.fst * y.fst * x.fst * (show A from y.snd) = 0 := by
    calc
      x.fst * y.fst * x.fst * (show A from y.snd) =
      x.fst * (y.fst * x.fst) * (show A from y.snd) := by simp only [mul_assoc]
      _ = x.fst * (-(x.fst * y.fst)) * (show A from y.snd) := by rw [hyx]
      _ = 0 := by
        rw [mul_neg, ← mul_assoc, hxSq']
        simp
  have hterm₂ : x.fst * y.fst * (show A from x.snd) * (-y.fst) = 0 := by
    calc
      x.fst * y.fst * (show A from x.snd) * (-y.fst) =
      x.fst * (y.fst * (show A from x.snd)) * (-y.fst) := by simp only [mul_assoc]
      _ = x.fst * ((show A from x.snd) * y.fst) * (-y.fst) := by rw [hcommXY]
      _ = 0 := by
        rw [← mul_assoc, mul_assoc, mul_neg, hySq']
        simp
  simp only [← mul_assoc, hterm₁, hterm₂]
  simp


end OddDividedPowers

end DividedPowers.TateResolution
