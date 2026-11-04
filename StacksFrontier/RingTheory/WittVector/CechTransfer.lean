module

public import StacksFrontier.RingTheory.WittVector.Approximation

/-!
# Čech vanishing for Witt vectors with coefficients in subrings

Let `Ω` be a commutative ring, let `A i` (for `i` in an index type `ι`) and `B i j` (for
`i j : ι`) be subrings of `Ω` with `A i ≤ B i j` and `A j ≤ B i j`, and let `A` be a further
subring. Think of `Ω` as the ring of functions on an intersection of opens, of `A i` as the
functions on the `i`-th open and of `B i j` as the functions on the intersection of the `i`-th
and `j`-th opens, all embedded in `Ω`. A Witt vector `x : 𝕎 Ω` *has coefficients in* a subring
`S` if `x.coeff n ∈ S` for every `n`; these are the Witt vectors of `S`, embedded in `𝕎 Ω`.

This file shows that additive Čech vanishing in degrees `0` and `1` for this system of subrings
implies the same vanishing for the Witt vectors.

## Main results

* `WittVector.coeff_mem_of_forall_coeff_mem`: if every element of `Ω` lying in all the `A i`
  lies in `A`, then every Witt vector with coefficients in all the `A i` has coefficients in `A`.
* `WittVector.exists_cech_coboundary`: if every additive Čech `1`-cocycle `b i j ∈ B i j`
  (`b i j + b j k = b i k`) is a coboundary `b i j = c i - c j` with `c i ∈ A i`, then every
  Witt vector `1`-cocycle with coefficients in the `B i j` is a coboundary of Witt vectors with
  coefficients in the `A i`.

## Implementation notes

The degree-one statement is proved by successive approximation along the coefficient index. If a
cochain `c` solves the cocycle condition modulo the coefficients of index `≥ n`, the error
`b i j - (c i - c j)` is a cocycle of the form `verschiebung^[n] (f i j)`; the zeroth coefficients
of the `f i j` form an additive cocycle, which the hypothesis splits as `a i - a j`, and
`c i + verschiebung^[n] (teichmuller p (a i))` solves the condition modulo the coefficients of
index `≥ n + 1` without changing the coefficients of `c i` of index `< n`. The solution is the
Witt vector whose `n`-th coefficient is that of the `(n + 1)`-st approximation
(`WittVector.truncLimit`). Coefficients in a subring `S` are handled through the subring
`WittVector.coeffSubring p S` of `𝕎 Ω`.
-/

@[expose] public section

namespace WittVector

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type*} [CommRing Ω]

local notation "𝕎" => WittVector p

variable {ι : Type*}

omit hp in
/-- **Čech `H⁰` for Witt vectors.** If every element of `Ω` lying in all the subrings `A i`
lies in `A`, then every Witt vector over `Ω` whose coefficients lie in all the `A i` has its
coefficients in `A`. -/
theorem coeff_mem_of_forall_coeff_mem {A : Subring Ω} {Aᵢ : ι → Subring Ω}
    (hH0 : ∀ c : Ω, (∀ i, c ∈ Aᵢ i) → c ∈ A) {x : 𝕎 Ω} (hx : ∀ i n, x.coeff n ∈ Aᵢ i) (n : ℕ) :
    x.coeff n ∈ A :=
  hH0 _ fun i => hx i n

/-- A Witt vector with vanishing zeroth coefficient, shifted by `verschiebung^[n]`, vanishes
modulo the coefficients of index `≥ n + 1`. -/
theorem truncate_succ_iterate_verschiebung_eq_zero {x : 𝕎 Ω} (hx : x.coeff 0 = 0) (n : ℕ) :
    truncate (n + 1) (verschiebung^[n] x) = 0 := by
  refine (mem_ker_truncate (n + 1) _).2 fun k hk => ?_
  rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
  · exact iterate_verschiebung_coeff_eq_zero _ hk
  · have := iterate_verschiebung_coeff (p := p) x k 0
    rw [zero_add] at this
    rw [this, hx]

/-- One step of the successive approximation: a cochain solving the cocycle condition on the
coefficients of index `< n` is corrected, without changing those coefficients, into one solving
it on the coefficients of index `< n + 1`. -/
private theorem exists_cech_coboundary_step {Aᵢ : ι → Subring Ω} {B : ι → ι → Subring Ω}
    (hA₁ : ∀ i j, Aᵢ i ≤ B i j) (hA₂ : ∀ i j, Aᵢ j ≤ B i j)
    (hH1 : ∀ b : ι → ι → Ω, (∀ i j, b i j ∈ B i j) → (∀ i j k, b i j + b j k = b i k) →
      ∃ c : ι → Ω, (∀ i, c i ∈ Aᵢ i) ∧ ∀ i j, b i j = c i - c j)
    {b : ι → ι → 𝕎 Ω} (hb : ∀ i j, b i j ∈ coeffSubring p (B i j))
    (hcoc : ∀ i j k, b i j + b j k = b i k) (n : ℕ) {c : ι → 𝕎 Ω}
    (hc : ∀ i, c i ∈ coeffSubring p (Aᵢ i))
    (hbc : ∀ i j, truncate n (b i j - (c i - c j)) = 0) :
    ∃ c' : ι → 𝕎 Ω, (∀ i, c' i ∈ coeffSubring p (Aᵢ i)) ∧
      (∀ i, truncate n (c' i) = truncate n (c i)) ∧
      ∀ i j, truncate (n + 1) (b i j - (c' i - c' j)) = 0 := by
  set e : ι → ι → 𝕎 Ω := fun i j => b i j - (c i - c j) with he
  have he_eq : ∀ i j, e i j = verschiebung^[n] ((e i j).shift n) := fun i j =>
    eq_iterate_verschiebung_shift_of_truncate_eq_zero (hbc i j)
  have he_mem : ∀ i j, e i j ∈ coeffSubring p (B i j) := fun i j =>
    sub_mem (hb i j) (sub_mem (coeffSubring_mono (hA₁ i j) (hc i))
      (coeffSubring_mono (hA₂ i j) (hc j)))
  have hecoc : ∀ i j k, e i j + e j k = e i k := fun i j k => by
    simp only [he, ← hcoc i j k]
    ring
  set f : ι → ι → 𝕎 Ω := fun i j => (e i j).shift n with hf
  have hfcoc : ∀ i j k, f i j + f j k = f i k := fun i j k =>
    Function.Injective.iterate (verschiebung_injective (p := p) (R := Ω)) n <| by
      rw [iterate_map_add, hf]
      simpa only [← he_eq] using hecoc i j k
  obtain ⟨a, ha, hab⟩ := hH1 (fun i j => (f i j).coeff 0)
    (fun i j => by
      simpa [hf, shift_coeff] using mem_coeffSubring_iff.1 (he_mem i j) (n + 0))
    (fun i j k => by rw [← add_coeff_zero, hfcoc])
  refine ⟨fun i => c i + verschiebung^[n] (teichmuller p (a i)), fun i => add_mem (hc i)
    (iterate_verschiebung_mem_coeffSubring (teichmuller_mem_coeffSubring (ha i)) n),
    fun i => by rw [map_add, truncate_iterate_verschiebung, add_zero], fun i j => ?_⟩
  have key : b i j - ((c i + verschiebung^[n] (teichmuller p (a i))) -
      (c j + verschiebung^[n] (teichmuller p (a j)))) =
      verschiebung^[n] (f i j - (teichmuller p (a i) - teichmuller p (a j))) := by
    have hfe : verschiebung^[n] (f i j) = e i j := (he_eq i j).symm
    rw [iterate_map_sub, iterate_map_sub, hfe, he]
    ring
  rw [key]
  refine truncate_succ_iterate_verschiebung_eq_zero ?_ n
  rw [← constantCoeff_apply, map_sub, map_sub]
  simp only [constantCoeff_apply, teichmuller_coeff_zero, hab, sub_self]

/-- **Čech `H¹` for Witt vectors.** Let `Aᵢ i` and `B i j` be subrings of `Ω` with
`Aᵢ i ≤ B i j` and `Aᵢ j ≤ B i j`. If every additive Čech `1`-cocycle `b i j ∈ B i j` (that is,
`b i j + b j k = b i k`) is a coboundary `b i j = c i - c j` with `c i ∈ Aᵢ i`, then every Witt
vector `1`-cocycle `b i j : 𝕎 Ω` with coefficients in `B i j` is a coboundary `b i j = c i - c j`
of Witt vectors `c i : 𝕎 Ω` with coefficients in `Aᵢ i`. -/
theorem exists_cech_coboundary {Aᵢ : ι → Subring Ω} {B : ι → ι → Subring Ω}
    (hA₁ : ∀ i j, Aᵢ i ≤ B i j) (hA₂ : ∀ i j, Aᵢ j ≤ B i j)
    (hH1 : ∀ b : ι → ι → Ω, (∀ i j, b i j ∈ B i j) → (∀ i j k, b i j + b j k = b i k) →
      ∃ c : ι → Ω, (∀ i, c i ∈ Aᵢ i) ∧ ∀ i j, b i j = c i - c j)
    (b : ι → ι → 𝕎 Ω) (hb : ∀ i j n, (b i j).coeff n ∈ B i j)
    (hcoc : ∀ i j k, b i j + b j k = b i k) :
    ∃ c : ι → 𝕎 Ω, (∀ i n, (c i).coeff n ∈ Aᵢ i) ∧ ∀ i j, b i j = c i - c j := by
  classical
  -- `P n c`: the cochain `c` has coefficients in the `Aᵢ i` and solves the cocycle condition on
  -- the coefficients of index `< n`.
  let P : ℕ → (ι → 𝕎 Ω) → Prop := fun n c =>
    (∀ i, c i ∈ coeffSubring p (Aᵢ i)) ∧
      ∀ i j, truncate n (b i j - (c i - c j)) = 0
  have step : ∀ n c, ∃ c' : ι → 𝕎 Ω, P n c →
      P (n + 1) c' ∧ ∀ i, truncate n (c' i) = truncate n (c i) := fun n c => by
    by_cases h : P n c
    · obtain ⟨c', hc', hagree, hsol⟩ :=
        exists_cech_coboundary_step hA₁ hA₂ hH1 (fun i j => mem_coeffSubring_iff.2 (hb i j)) hcoc n
          h.1 h.2
      exact ⟨c', fun _ => ⟨⟨hc', hsol⟩, hagree⟩⟩
    · exact ⟨c, fun h' => absurd h' h⟩
  choose g hg using step
  let seq : ℕ → ι → 𝕎 Ω := fun n => Nat.rec (motive := fun _ => ι → 𝕎 Ω) 0 g n
  have hseq (n : ℕ) : P n (seq n) := by
    induction n with
    | zero => exact ⟨fun _ => zero_mem _, fun _ _ =>
        (mem_ker_truncate 0 _).2 fun k hk => absurd hk (Nat.not_lt_zero k)⟩
    | succ n ih => exact (hg n (seq n) ih).1
  have hagree : ∀ n i, truncate n (seq (n + 1) i) = truncate n (seq n i) := fun n =>
    (hg n (seq n) (hseq n)).2
  let c : ι → 𝕎 Ω := fun i => truncLimit p fun n => seq n i
  have hc_trunc : ∀ m i, truncate m (c i) = truncate m (seq m i) := fun m i =>
    truncate_truncLimit (fun n => hagree n i) m
  refine ⟨c, fun i k => ?_, fun i j => ?_⟩
  · rw [coeff_truncLimit]
    exact mem_coeffSubring_iff.1 ((hseq (k + 1)).1 i) k
  · rw [← sub_eq_zero]
    ext k
    have h := (hseq (k + 1)).2 i j
    rw [map_sub, map_sub, ← hc_trunc, ← hc_trunc, ← map_sub, ← map_sub] at h
    simpa using (mem_ker_truncate (k + 1) _).1 h k (Nat.lt_succ_self k)

end WittVector
