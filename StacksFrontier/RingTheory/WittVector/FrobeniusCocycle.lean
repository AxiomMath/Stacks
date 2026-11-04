module

public import StacksFrontier.RingTheory.WittVector.Approximation

/-!
# Artin–Schreier–Witt cocycles with coefficients in subrings

Let `Ω` be a commutative ring of characteristic `p` and let `O₁, O₂ ≤ O₁₂` be subrings of `Ω`.
Think of `O₁` and `O₂` as the functions on two opens of a scheme and of `O₁₂` as the functions on
their intersection, all embedded in a common ring `Ω`. This file solves the equation
`a₂ - a₁ = F c - c` in the Witt vectors `𝕎 Ω`, with `a₁`, `a₂` and `c` having their coefficients
in `O₁`, `O₂` and `O₁₂` respectively, and with prescribed zeroth coefficients, under the
hypothesis that the corresponding equation on elements is always solvable: every `ε ∈ O₁₂` has
the form `β - α - (μ ^ p - μ)` with `α ∈ O₁`, `β ∈ O₂` and `μ ∈ O₁₂`.

## Main results

* `WittVector.exists_sub_eq_frobenius_sub_self_of_truncate`: a solution of `a₂ - a₁ = F c - c`
  on the coefficients of index `< n` extends to a solution, without changing those
  coefficients.
* `WittVector.exists_sub_eq_frobenius_sub_self`: given `α₀ ∈ O₁`, `β₀ ∈ O₂` and `c₀ ∈ O₁₂` with
  `β₀ - α₀ = c₀ ^ p - c₀`, there is a solution with zeroth coefficients `α₀`, `β₀` and `c₀`.
* `WittVector.exists_sub_eq_add_pow_sub_self_of_eq_add_smul`: the hypothesis on elements holds
  when `O₁₂ = O₁ + O₂ + k e` for a ring `k` on which `μ ↦ μ ^ p - μ` is surjective, provided
  `e ^ p - e ∈ O₁ + O₂`.

## Implementation notes

The solution is built by successive approximation along the coefficient index. If the error
`F c - c - (a₂ - a₁)` vanishes in the coefficients of index `< n`, it is `verschiebung^[n] u`,
and the hypothesis writes `u.coeff 0 = β - α - (μ ^ p - μ)`. Adding `verschiebung^[n]` of the
Teichmüller representatives of `μ`, `α` and `β` to `c`, `a₁` and `a₂` kills the coefficient of
index `n` of the error, because in characteristic `p` the Frobenius commutes with the
Verschiebung and the zeroth coefficient is additive. The limit is `WittVector.truncLimit`.
-/

@[expose] public section

namespace WittVector

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type*} [CommRing Ω]

local notation "𝕎" => WittVector p

section Cocycle

variable [CharP Ω p] {O₁ O₂ O₁₂ : Subring Ω}

/-- One step of the successive approximation: a solution of `a₂ - a₁ = F c - c` on the
coefficients of index `< n` is corrected by `verschiebung^[n]` of Teichmüller representatives into
a solution on the coefficients of index `< n + 1`. -/
private theorem exists_sub_eq_frobenius_sub_self_step (h₁ : O₁ ≤ O₁₂) (h₂ : O₂ ≤ O₁₂)
    (hH : ∀ ε ∈ O₁₂, ∃ α ∈ O₁, ∃ β ∈ O₂, ∃ μ ∈ O₁₂, β - α = ε + (μ ^ p - μ))
    {n : ℕ} {a₁ a₂ c : 𝕎 Ω} (ha₁ : a₁ ∈ coeffSubring p O₁) (ha₂ : a₂ ∈ coeffSubring p O₂)
    (hc : c ∈ coeffSubring p O₁₂) (h : truncate n (frobenius c - c - (a₂ - a₁)) = 0) :
    ∃ α ∈ O₁, ∃ β ∈ O₂, ∃ μ ∈ O₁₂,
      truncate (n + 1) (frobenius (c + verschiebung^[n] (teichmuller p μ)) -
        (c + verschiebung^[n] (teichmuller p μ)) - ((a₂ + verschiebung^[n] (teichmuller p β)) -
          (a₁ + verschiebung^[n] (teichmuller p α)))) = 0 := by
  set E := frobenius c - c - (a₂ - a₁) with hE
  have hEmem : E ∈ coeffSubring p O₁₂ :=
    sub_mem (sub_mem (frobenius_mem_coeffSubring hc) hc)
      (sub_mem (coeffSubring_mono h₂ ha₂) (coeffSubring_mono h₁ ha₁))
  have hEv := eq_iterate_verschiebung_shift_of_truncate_eq_zero h
  obtain ⟨α, hα, β, hβ, μ, hμ, hrel⟩ := hH (E.coeff n) (mem_coeffSubring_iff.1 hEmem n)
  refine ⟨α, hα, β, hβ, μ, hμ, ?_⟩
  have hcomm : frobenius (verschiebung^[n] (teichmuller p μ)) =
      verschiebung^[n] (frobenius (teichmuller p μ)) :=
    ((verschiebung_frobenius_comm (p := p) (R := Ω)).iterate_left n _).symm
  set u := E.shift n + (frobenius (teichmuller p μ) - teichmuller p μ) -
    (teichmuller p β - teichmuller p α) with hu
  have key : frobenius (c + verschiebung^[n] (teichmuller p μ)) -
      (c + verschiebung^[n] (teichmuller p μ)) - ((a₂ + verschiebung^[n] (teichmuller p β)) -
        (a₁ + verschiebung^[n] (teichmuller p α))) = verschiebung^[n] u := by
    rw [hu, iterate_map_sub, iterate_map_add, iterate_map_sub, iterate_map_sub, ← hEv, ← hcomm,
      hE, map_add]
    ring
  rw [key]
  refine (mem_ker_truncate (n + 1) _).2 fun k hk => ?_
  rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
  · exact iterate_verschiebung_coeff_eq_zero _ hk
  · have := iterate_verschiebung_coeff (p := p) u k 0
    rw [zero_add] at this
    rw [this, ← constantCoeff_apply, hu]
    simp only [map_add, map_sub, constantCoeff_apply, coeff_frobenius_charP,
      teichmuller_coeff_zero, shift_coeff, add_zero]
    linear_combination -hrel

/-- **Successive approximation for Artin–Schreier–Witt cocycles.** Let `O₁, O₂ ≤ O₁₂` be
subrings of a ring `Ω` of characteristic `p` such that every `ε ∈ O₁₂` has the form
`β - α - (μ ^ p - μ)` with `α ∈ O₁`, `β ∈ O₂` and `μ ∈ O₁₂`. If Witt vectors `a₁`, `a₂` and `c`
with coefficients in `O₁`, `O₂` and `O₁₂` solve `a₂ - a₁ = F c - c` on the coefficients of index
`< n₀`, then there are Witt vectors with coefficients in the same subrings, agreeing with them on
the coefficients of index `< n₀`, which solve `a₂ - a₁ = F c - c`. -/
theorem exists_sub_eq_frobenius_sub_self_of_truncate (h₁ : O₁ ≤ O₁₂) (h₂ : O₂ ≤ O₁₂)
    (hH : ∀ ε ∈ O₁₂, ∃ α ∈ O₁, ∃ β ∈ O₂, ∃ μ ∈ O₁₂, β - α = ε + (μ ^ p - μ))
    {n₀ : ℕ} {a₁ a₂ c : 𝕎 Ω} (ha₁ : a₁ ∈ coeffSubring p O₁) (ha₂ : a₂ ∈ coeffSubring p O₂)
    (hc : c ∈ coeffSubring p O₁₂) (h : truncate n₀ (frobenius c - c - (a₂ - a₁)) = 0) :
    ∃ a₁' ∈ coeffSubring p O₁, ∃ a₂' ∈ coeffSubring p O₂, ∃ c' ∈ coeffSubring p O₁₂,
      truncate n₀ a₁' = truncate n₀ a₁ ∧ truncate n₀ a₂' = truncate n₀ a₂ ∧
        truncate n₀ c' = truncate n₀ c ∧ a₂' - a₁' = frobenius c' - c' := by
  classical
  have mono : ∀ {m N : ℕ}, m ≤ N → ∀ {x y : 𝕎 Ω}, truncate N x = truncate N y →
      truncate m x = truncate m y := fun hmN x y hxy => by
    rw [← TruncatedWittVector.truncate_wittVector_truncate hmN x,
      ← TruncatedWittVector.truncate_wittVector_truncate hmN y, hxy]
  let T := 𝕎 Ω × 𝕎 Ω × 𝕎 Ω
  let err : T → 𝕎 Ω := fun t => frobenius t.2.2 - t.2.2 - (t.2.1 - t.1)
  let P : ℕ → T → Prop := fun n t => t.1 ∈ coeffSubring p O₁ ∧ t.2.1 ∈ coeffSubring p O₂ ∧
    t.2.2 ∈ coeffSubring p O₁₂ ∧ truncate n (err t) = 0
  let agree : ℕ → T → T → Prop := fun n t t' => truncate n t'.1 = truncate n t.1 ∧
    truncate n t'.2.1 = truncate n t.2.1 ∧ truncate n t'.2.2 = truncate n t.2.2
  have step : ∀ n t, ∃ t' : T, P n t → P (n + 1) t' ∧ agree n t t' := fun n t => by
    by_cases ht : P n t
    · obtain ⟨α, hα, β, hβ, μ, hμ, hsol⟩ :=
        exists_sub_eq_frobenius_sub_self_step h₁ h₂ hH ht.1 ht.2.1 ht.2.2.1 ht.2.2.2
      refine ⟨(t.1 + verschiebung^[n] (teichmuller p α), t.2.1 + verschiebung^[n]
        (teichmuller p β), t.2.2 + verschiebung^[n] (teichmuller p μ)), fun _ => ⟨⟨?_, ?_, ?_,
        hsol⟩, ?_, ?_, ?_⟩⟩
      · exact add_mem ht.1 (iterate_verschiebung_mem_coeffSubring
          (teichmuller_mem_coeffSubring hα) n)
      · exact add_mem ht.2.1 (iterate_verschiebung_mem_coeffSubring
          (teichmuller_mem_coeffSubring hβ) n)
      · exact add_mem ht.2.2.1 (iterate_verschiebung_mem_coeffSubring
          (teichmuller_mem_coeffSubring hμ) n)
      all_goals rw [map_add, truncate_iterate_verschiebung, add_zero]
    · exact ⟨t, fun h' => absurd h' ht⟩
  choose g hg using step
  let seq : ℕ → T := fun m => Nat.rec (motive := fun _ => T) (a₁, a₂, c)
    (fun m t => g (n₀ + m) t) m
  have hseq : ∀ m, P (n₀ + m) (seq m) := by
    intro m
    induction m with
    | zero => exact ⟨ha₁, ha₂, hc, h⟩
    | succ m ih => exact (hg (n₀ + m) (seq m) ih).1
  have hagree : ∀ m, agree (n₀ + m) (seq m) (seq (m + 1)) := fun m =>
    (hg (n₀ + m) (seq m) (hseq m)).2
  have hle : ∀ m, m ≤ n₀ + m := fun m => Nat.le_add_left m n₀
  set A₁ := truncLimit p fun m => (seq m).1
  set A₂ := truncLimit p fun m => (seq m).2.1
  set C := truncLimit p fun m => (seq m).2.2
  have lim : ∀ (f : ℕ → 𝕎 Ω) (A : 𝕎 Ω), A = truncLimit p f →
      (∀ m, truncate (n₀ + m) (f (m + 1)) = truncate (n₀ + m) (f m)) →
      (∀ m, truncate m A = truncate m (f m)) ∧ truncate n₀ A = truncate n₀ (f 0) :=
    fun f A hA hf => by
    have hA' := hA ▸ truncate_truncLimit fun m => mono (hle m) (hf m)
    have hinit : ∀ m, truncate n₀ (f m) = truncate n₀ (f 0) := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih => exact (mono (Nat.le_add_right n₀ m) (hf m)).trans ih
    exact ⟨hA', (mono (Nat.le_add_left n₀ n₀) (hA' (n₀ + n₀))).trans (hinit _)⟩
  obtain ⟨hA₁, i₁⟩ := lim _ A₁ rfl fun m => (hagree m).1
  obtain ⟨hA₂, i₂⟩ := lim _ A₂ rfl fun m => (hagree m).2.1
  obtain ⟨hC, i₃⟩ := lim _ C rfl fun m => (hagree m).2.2
  refine ⟨A₁, mem_coeffSubring_iff.2 fun k => ?_, A₂, mem_coeffSubring_iff.2 fun k => ?_, C,
    mem_coeffSubring_iff.2 fun k => ?_, ?_, ?_, ?_, ?_⟩
  · exact mem_coeffSubring_iff.1 (hseq (k + 1)).1 k
  · exact mem_coeffSubring_iff.1 (hseq (k + 1)).2.1 k
  · exact mem_coeffSubring_iff.1 (hseq (k + 1)).2.2.1 k
  · exact i₁
  · exact i₂
  · exact i₃
  · refine (sub_eq_zero.1 ?_).symm
    ext k
    have hk : truncate (k + 1) (err (A₁, A₂, C)) = 0 := by
      have e : truncate (k + 1) (err (A₁, A₂, C)) = truncate (k + 1) (err (seq (k + 1))) := by
        simp only [err, map_sub, truncate_frobenius_eq_of_truncate_eq (hC (k + 1)), hA₁ (k + 1),
          hA₂ (k + 1), hC (k + 1)]
      rw [e]
      exact mono (hle (k + 1)) ((hseq (k + 1)).2.2.2.trans (map_zero _).symm) |>.trans
        (map_zero _)
    simpa only [err, zero_coeff] using (mem_ker_truncate (k + 1) _).1 hk k (Nat.lt_succ_self k)

/-- **Artin–Schreier–Witt cocycles with coefficients in subrings.** Let `O₁, O₂ ≤ O₁₂` be
subrings of a ring `Ω` of characteristic `p` such that every `ε ∈ O₁₂` has the form
`β - α - (μ ^ p - μ)` with `α ∈ O₁`, `β ∈ O₂` and `μ ∈ O₁₂`. Given `α₀ ∈ O₁`, `β₀ ∈ O₂` and
`c₀ ∈ O₁₂` with `β₀ - α₀ = c₀ ^ p - c₀`, there are Witt vectors `a₁`, `a₂` and `c` with
coefficients in `O₁`, `O₂` and `O₁₂` respectively, with zeroth coefficients `α₀`, `β₀` and `c₀`,
such that `a₂ - a₁ = F c - c`. -/
theorem exists_sub_eq_frobenius_sub_self (h₁ : O₁ ≤ O₁₂) (h₂ : O₂ ≤ O₁₂)
    (hH : ∀ ε ∈ O₁₂, ∃ α ∈ O₁, ∃ β ∈ O₂, ∃ μ ∈ O₁₂, β - α = ε + (μ ^ p - μ))
    {α₀ β₀ c₀ : Ω} (hα₀ : α₀ ∈ O₁) (hβ₀ : β₀ ∈ O₂) (hc₀ : c₀ ∈ O₁₂)
    (h₀ : β₀ - α₀ = c₀ ^ p - c₀) :
    ∃ a₁ ∈ coeffSubring p O₁, ∃ a₂ ∈ coeffSubring p O₂, ∃ c ∈ coeffSubring p O₁₂,
      a₁.coeff 0 = α₀ ∧ a₂.coeff 0 = β₀ ∧ c.coeff 0 = c₀ ∧ a₂ - a₁ = frobenius c - c := by
  have h : truncate 1 (frobenius (teichmuller p c₀) - teichmuller p c₀ -
      (teichmuller p β₀ - teichmuller p α₀)) = 0 := by
    refine (mem_ker_truncate 1 _).2 fun k hk => ?_
    obtain rfl : k = 0 := Nat.lt_one_iff.1 hk
    rw [← constantCoeff_apply]
    simp only [map_sub, constantCoeff_apply, coeff_frobenius_charP, teichmuller_coeff_zero]
    linear_combination -h₀
  obtain ⟨a₁, ha₁, a₂, ha₂, c, hc, e₁, e₂, e₃, hsol⟩ :=
    exists_sub_eq_frobenius_sub_self_of_truncate h₁ h₂ hH (teichmuller_mem_coeffSubring hα₀)
      (teichmuller_mem_coeffSubring hβ₀) (teichmuller_mem_coeffSubring hc₀) h
  have coeff0 : ∀ {x y : 𝕎 Ω}, truncate 1 x = truncate 1 y → x.coeff 0 = y.coeff 0 :=
    fun hxy => truncate_eq_truncate_iff.1 hxy 0 Nat.one_pos
  refine ⟨a₁, ha₁, a₂, ha₂, c, hc, ?_, ?_, ?_, hsol⟩
  · rw [coeff0 e₁, teichmuller_coeff_zero]
  · rw [coeff0 e₂, teichmuller_coeff_zero]
  · rw [coeff0 e₃, teichmuller_coeff_zero]

end Cocycle

/-- Let `O₁, O₂ ≤ O₁₂` be subalgebras of an algebra `Ω` of characteristic `p` over a commutative
ring `k` on which `μ ↦ μ ^ p - μ` is surjective. If `O₁₂ = O₁ + O₂ + k e` and
`e ^ p - e ∈ O₁ + O₂`, then every `ε ∈ O₁₂` has the form `β - α - (μ ^ p - μ)` with `α ∈ O₁`,
`β ∈ O₂` and `μ ∈ O₁₂`. -/
theorem exists_sub_eq_add_pow_sub_self_of_eq_add_smul [CharP Ω p] {k : Type*} [CommRing k]
    [Algebra k Ω] {O₁ O₂ O₁₂ : Subalgebra k Ω} {e : Ω} (he : e ∈ O₁₂)
    (hk : ∀ l : k, ∃ μ : k, μ ^ p - μ = l)
    (hdec : ∀ ε ∈ O₁₂, ∃ α ∈ O₁, ∃ β ∈ O₂, ∃ l : k, ε = β - α + l • e)
    (hep : ∃ α ∈ O₁, ∃ β ∈ O₂, e ^ p - e = β - α) :
    ∀ ε ∈ O₁₂, ∃ α ∈ O₁, ∃ β ∈ O₂, ∃ μ ∈ O₁₂, β - α = ε + (μ ^ p - μ) := by
  intro ε hε
  obtain ⟨α, hα, β, hβ, l, rfl⟩ := hdec ε hε
  obtain ⟨α', hα', β', hβ', hαβ'⟩ := hep
  obtain ⟨μ, rfl⟩ := hk l
  refine ⟨α - μ ^ p • α', sub_mem hα (Subalgebra.smul_mem _ hα' _), β - μ ^ p • β',
    sub_mem hβ (Subalgebra.smul_mem _ hβ' _), -(μ • e), neg_mem (Subalgebra.smul_mem _ he _), ?_⟩
  have hneg : (-(μ • e)) ^ p = -(μ • e) ^ p := by
    rw [neg_pow, neg_one_pow_char Ω p, neg_one_mul]
  rw [hneg, smul_pow]
  simp only [Algebra.smul_def, map_pow, map_sub] at hαβ' ⊢
  linear_combination (algebraMap k Ω μ) ^ p * hαβ'

end WittVector
