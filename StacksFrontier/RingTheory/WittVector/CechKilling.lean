module

public import StacksFrontier.RingTheory.WittVector.CechTransfer

/-!
# Killing an Artin–Schreier–Witt Čech class

Let `Ω` be a ring of characteristic `p` and let `A ≤ Aᵢ i ≤ B i j` be subrings of `Ω` for which
the additive Čech complex has no `H⁰` beyond `A` and no `H¹`. An Artin–Schreier–Witt Čech
cocycle, that is Witt vectors `a i` and `b i j` with coefficients in `Aᵢ i` and `B i j`, with
`b i j + b j k = b i k` and `F (b i j) - b i j = a i - a j`, then becomes trivial locally as soon
as `F - 1` is surjective on the Witt vectors with coefficients in `A`: every `a i` has the form
`F θ - θ` for a Witt vector `θ` with coefficients in `Aᵢ i`.

## Main results

* `WittVector.exists_frobenius_sub_self_eq_of_cech`: the statement above.
-/

@[expose] public section

namespace WittVector

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type*} [CommRing Ω] [CharP Ω p]

local notation "𝕎" => WittVector p

variable {ι : Type*}

omit [CharP Ω p] in
/-- **Killing an Artin–Schreier–Witt Čech class.** If the additive Čech complex of the subrings
`A ≤ Aᵢ i ≤ B i j` of `Ω` is exact in degrees `0` and `1` and `F - 1` is surjective on the Witt
vectors with coefficients in `A`, then for every Artin–Schreier–Witt Čech cocycle `(a, b)` each
`a i` has the form `F θ - θ` with `θ` a Witt vector with coefficients in `Aᵢ i`. -/
theorem exists_frobenius_sub_self_eq_of_cech {A : Subring Ω} {Aᵢ : ι → Subring Ω}
    {B : ι → ι → Subring Ω} (hA₁ : ∀ i j, Aᵢ i ≤ B i j) (hA₂ : ∀ i j, Aᵢ j ≤ B i j)
    (hH0 : ∀ c : Ω, (∀ i, c ∈ Aᵢ i) → c ∈ A)
    (hH1 : ∀ b : ι → ι → Ω, (∀ i j, b i j ∈ B i j) → (∀ i j k, b i j + b j k = b i k) →
      ∃ c : ι → Ω, (∀ i, c i ∈ Aᵢ i) ∧ ∀ i j, b i j = c i - c j)
    (hsurj : ∀ x ∈ coeffSubring p A, ∃ e ∈ coeffSubring p A, frobenius e - e = x)
    (hAA : ∀ i, A ≤ Aᵢ i)
    (a : ι → 𝕎 Ω) (b : ι → ι → 𝕎 Ω) (ha : ∀ i n, (a i).coeff n ∈ Aᵢ i)
    (hb : ∀ i j n, (b i j).coeff n ∈ B i j) (hcoc : ∀ i j k, b i j + b j k = b i k)
    (hab : ∀ i j, frobenius (b i j) - b i j = a i - a j) (i : ι) :
    ∃ θ : 𝕎 Ω, (∀ n, θ.coeff n ∈ Aᵢ i) ∧ frobenius θ - θ = a i := by
  obtain ⟨c, hc, hbc⟩ := exists_cech_coboundary hA₁ hA₂ hH1 b hb hcoc
  have hc' : ∀ j, c j ∈ coeffSubring p (Aᵢ j) := fun j => mem_coeffSubring_iff.2 (hc j)
  have ha' : ∀ j, a j ∈ coeffSubring p (Aᵢ j) := fun j => mem_coeffSubring_iff.2 (ha j)
  have hd : ∀ j, a j - (frobenius (c j) - c j) = a i - (frobenius (c i) - c i) := by
    intro j
    have h := hab i j
    rw [hbc i j, map_sub] at h
    linear_combination h
  have hdA : a i - (frobenius (c i) - c i) ∈ coeffSubring p A := by
    refine mem_coeffSubring_iff.2 fun n => hH0 _ fun j => ?_
    rw [← hd j]
    exact mem_coeffSubring_iff.1 (sub_mem (ha' j)
      (sub_mem (frobenius_mem_coeffSubring (hc' j)) (hc' j))) n
  obtain ⟨e, he, hee⟩ := hsurj _ hdA
  refine ⟨c i + e, fun n => mem_coeffSubring_iff.1
    (add_mem (hc' i) (coeffSubring_mono (hAA i) he)) n, ?_⟩
  rw [map_add]
  linear_combination hee

end WittVector
