module

import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.FieldTheory.PurelyInseparable.Basic
import StacksCore.FieldTheory.IntermediateField.Adjoin.Basic
import StacksCore.FieldTheory.IntermediateField.Basic
import StacksCore.Tactic.StacksAttribute

/-! # Purely inseparable extension -/

@[expose] public section

add_to_stacks 030M "Second part of 1" separableClosure.isPurelyInseparable
add_to_stacks 09HG IsPurelyInseparable.trans
add_to_stacks 030K "uniqueness" eq_separableClosure
add_to_stacks 030J "algebraic" Algebra.IsAlgebraic
add_to_stacks 030J "separable" Algebra.IsSeparable
add_to_stacks 030J "purely inseparable" IsPurelyInseparable
add_to_stacks 030J "normal" Normal
add_to_stacks 030J "Galois" IsGalois

open IntermediateField

/-- **Stacks 09HI**.
A finite purely inseparable extension `E/F` of characteristic exponent `p` admits a tower of
generators: there exist `x₀, …, x_{n-1} ∈ E` whose `F`-adjunction is all of `E`, and at each
step `xᵢ` lies outside `F(x₀, …, x_{i-1})` while `xᵢ ^ p` lies inside it. -/
@[stacks 09HI]
theorem IsPurelyInseparable.exists_tower
    (F E : Type*) [Field F] [Field E] [Algebra F E] (p : ℕ) [ExpChar F p]
    [FiniteDimensional F E] [IsPurelyInseparable F E] :
    ∃ (n : ℕ) (x : Fin n → E), adjoin F (Set.range x) = ⊤ ∧
      ∀ i, x i ∉ adjoin F (x '' Set.Iio i) ∧ x i ^ p ∈ adjoin F (x '' Set.Iio i) := by
  -- strong induction on `[E : F]` generalizing `F`
  -- but instead of `F`, we use `(⊥ : IntermediateField F E)` to deal with universe issues
  generalize hf : (⊥ : IntermediateField F E) = F'
  suffices ∃ (n : ℕ) (x : Fin n → E), F' ⊔ adjoin F (Set.range x) = ⊤ ∧
      ∀ i, x i ∉ F' ⊔ adjoin F (x '' Set.Iio i) ∧ x i ^ p ∈ F' ⊔ adjoin F (x '' Set.Iio i) by
    obtain ⟨n, x, hx1, hx2⟩ := this
    refine ⟨n, x, ?_, ?_⟩
    · simpa [← hf] using congr(($hx1).restrictScalars F)
    · simpa [← mem_restrictScalars (K := F) (L' := F'), ← hf] using hx2
  clear hf
  generalize hn : Module.finrank F' E = n
  induction n using Nat.strong_induction_on generalizing F' with | h n ih =>
  have hn0 : 0 < n := hn ▸ Module.finrank_pos (R := F') (M := E)
  by_cases hf : F' = ⊤
  · subst hf
    exact ⟨0, Fin.elim0, by simp, fun i ↦ i.elim0⟩
  replace hf : ∃ x, x ∉ F' ∧ x ^ p ∈ F' := by
    simp_rw [eq_top_iff, IsConcreteLE.le_iff, mem_top, true_implies, not_forall] at hf
    obtain ⟨x, hx⟩ := hf
    obtain ⟨n, hn⟩ := IsPurelyInseparable.pow_mem F' p x
    rw [range_algebraMap, Subalgebra.mem_toSubring, mem_toSubalgebra] at hn
    classical
    let m := Nat.find (p := fun m ↦ x ^ p ^ m ∈ F') ⟨n, hn⟩
    have hm : x ^ p ^ m ∈ F' := Nat.find_spec (p := fun m ↦ x ^ p ^ m ∈ F') _
    have hm' (k) : x ^ p ^ k ∈ F' → m ≤ k := Nat.find_min' (p := fun m ↦ x ^ p ^ m ∈ F') _
    have hm0 : m ≠ 0 := fun hm0 ↦ by simp [hm0, hx] at hm
    exact ⟨x ^ p ^ (m - 1), by grind, by rw [← pow_mul, ← pow_succ]; grind⟩
  obtain ⟨x, hx, hxp⟩ := hf
  let K := F'⟮x⟯
  have hfk : Module.finrank F' K ≠ 1 := bot_eq_top_iff_finrank_eq_one.not.mp <| by
    simpa [K, eq_top_iff, IsConcreteLE.le_iff, mem_bot, Subtype.ext_iff]
      using ⟨x, subset_adjoin _ _ (by simp), hx⟩
  rw [← Module.finrank_mul_finrank _ K] at hn
  have hke : Module.finrank K E < n := hn ▸ (lt_mul_iff_one_lt_left Module.finrank_pos).mpr <| by
    grind [Module.finrank_pos (R := F') (M := K)]
  obtain ⟨n, y, hy1, hy2⟩ := ih _ hke (K.restrictScalars F) rfl
  simp_rw [K, restrictScalars_adjoin_eq_sup, sup_assoc, ← adjoin_union,
    Set.singleton_union] at hy1 hy2
  refine ⟨n + 1, Fin.cons x y, ?_, fun i ↦ ?_⟩
  · simpa using hy1
  · refine i.cases (by simp [Set.Iio, hx, hxp]) fun i ↦ ?_
    have h : Fin.cons x y '' Set.Iio i.succ = insert x (y '' Set.Iio i) := by
      ext; simp [Fin.exists_fin_succ]; grind
    simpa [h] using hy2 i

/-- If `x ∉ A` and `x ^ p ∈ A`, where `p` is the exponential characteristic, then
`[A⟮x⟯ : A] = p`. -/
theorem IntermediateField.finrank_adjoin_simple_eq_of_pow_mem {F E : Type*} [Field F] [Field E]
    [Algebra F E] (p : ℕ) [ExpChar E p] {A : IntermediateField F E} {x : E} (hx : x ∉ A)
    (hxp : x ^ p ∈ A) : Module.finrank A A⟮x⟯ = p := by
  obtain rfl | hp := (expChar_is_prime_or_one E p).symm
  · exact absurd (pow_one x ▸ hxp) hx
  have hirr : Irreducible (Polynomial.X ^ p - Polynomial.C (⟨x ^ p, hxp⟩ : A)) :=
    X_pow_sub_C_irreducible_of_prime hp fun b hb ↦ hx <| by
      rw [← frobenius_inj E p (congr_arg ((↑) : A → E) hb)]
      exact b.2
  rw [finrank_adjoin, ← minpoly.eq_of_irreducible_of_monic hirr (by simp)
    (Polynomial.monic_X_pow_sub_C _ hp.ne_zero), Polynomial.natDegree_X_pow_sub_C]

/-- **Stacks 09HI** (each step has degree `p`).
The tower of `IsPurelyInseparable.exists_tower` can be chosen so that, in addition, each step
`F(x₀, …, x_{i-1}) ⊆ F(x₀, …, x_i)` has degree `p`. -/
@[stacks 09HI "each step has degree p"]
theorem IsPurelyInseparable.exists_tower_finrank_eq
    (F E : Type*) [Field F] [Field E] [Algebra F E] (p : ℕ) [ExpChar F p]
    [FiniteDimensional F E] [IsPurelyInseparable F E] :
    ∃ (n : ℕ) (x : Fin n → E), adjoin F (Set.range x) = ⊤ ∧
      ∀ i, x i ∉ adjoin F (x '' Set.Iio i) ∧ x i ^ p ∈ adjoin F (x '' Set.Iio i) ∧
        Module.finrank (adjoin F (x '' Set.Iio i)) (adjoin F (x '' Set.Iio i))⟮x i⟯ = p := by
  have := expChar_of_injective_algebraMap (algebraMap F E).injective p
  obtain ⟨n, x, hx, hxp⟩ := exists_tower F E p
  exact ⟨n, x, hx, fun i ↦ ⟨(hxp i).1, (hxp i).2,
    finrank_adjoin_simple_eq_of_pow_mem p (hxp i).1 (hxp i).2⟩⟩
