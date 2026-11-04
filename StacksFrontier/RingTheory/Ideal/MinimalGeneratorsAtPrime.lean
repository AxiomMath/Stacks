module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Finiteness.Ideal

/-!
# Minimal generators of a finitely generated ideal at a prime

Let `I` be a finitely generated ideal of `Q` and `𝔮` a prime of `Q`. There are `f₁, …, fᵣ ∈ I`
and `g ∉ 𝔮` with `g I ⊆ (f₁, …, fᵣ)`, such that every relation `∑ aᵢ fᵢ = 0` in `Q` has all its
coefficients in `𝔮`.
-/

@[expose] public section

namespace Ideal

variable {Q : Type*} [CommRing Q]

/-- **Minimal generators at a prime.** Let `I` be a finitely generated ideal of `Q` and `q` a
prime of `Q`. There are `f₁, …, fᵣ ∈ I` and `g ∉ q` with `g I ⊆ (f₁, …, fᵣ)`, such that every
relation `∑ aᵢ fᵢ = 0` in `Q` has all its coefficients in `q`. -/
theorem exists_minimal_generators_at_prime (I : Ideal Q) (hI : I.FG) (q : Ideal Q) [q.IsPrime] :
    ∃ (r : ℕ) (f : Fin r → Q), (∀ i, f i ∈ I) ∧
      (∃ g ∉ q, ∀ x ∈ I, g * x ∈ Ideal.span (Set.range f)) ∧
      ∀ a : Fin r → Q, ∑ i, a i * f i = 0 → ∀ i, a i ∈ q := by
  classical
  obtain ⟨s, hs⟩ := hI
  let L := Localization.AtPrime q
  let Pσ : Finset Q → Prop := fun σ =>
    I.map (algebraMap Q L) ≤ Ideal.span (algebraMap Q L '' (σ : Set Q))
  have hPs : Pσ s := by
    simp only [Pσ, ← hs, Ideal.map_span]
    exact le_rfl
  obtain ⟨σ, hσmem, hσmin⟩ := (s.powerset.filter Pσ).exists_min_image Finset.card
    ⟨s, Finset.mem_filter.2 ⟨Finset.mem_powerset_self s, hPs⟩⟩
  rw [Finset.mem_filter, Finset.mem_powerset] at hσmem
  obtain ⟨hσs, hPσ⟩ := hσmem
  let e := σ.equivFin
  let f : Fin σ.card → Q := fun i => (e.symm i : Q)
  have hrange : Set.range f = (σ : Set Q) :=
    (e.symm.surjective.range_comp _).trans Subtype.range_coe
  have hsI : (s : Set Q) ⊆ I := hs ▸ Ideal.subset_span
  refine ⟨σ.card, f, fun i => hsI (hσs (e.symm i).2), ?_, ?_⟩
  · -- clearing denominators
    have hx : ∀ x ∈ s, ∃ c ∉ q, c * x ∈ Ideal.span (σ : Set Q) := by
      intro x hxs
      have h1 : algebraMap Q L x ∈ (Ideal.span (σ : Set Q)).map (algebraMap Q L) := by
        rw [Ideal.map_span]
        exact hPσ (Ideal.mem_map_of_mem _ (hsI hxs))
      obtain ⟨⟨⟨y, hy⟩, ⟨c, hc⟩⟩, hyc⟩ :=
        (IsLocalization.mem_map_algebraMap_iff q.primeCompl L).1 h1
      simp only at hyc
      rw [← map_mul] at hyc
      obtain ⟨⟨d, hd⟩, hdeq⟩ := (IsLocalization.eq_iff_exists q.primeCompl L).1 hyc
      refine ⟨d * c, fun hmem => ?_, ?_⟩
      · rcases Ideal.IsPrime.mem_or_mem ‹_› hmem with h | h
        · exact hd h
        · exact hc h
      · simp only at hdeq
        rw [mul_assoc, mul_comm c x, hdeq]
        exact Ideal.mul_mem_left _ _ hy
    choose! c hcq hcx using hx
    refine ⟨∏ x ∈ s, c x, fun hmem => ?_, ?_⟩
    · obtain ⟨x, hxs, hx⟩ := (Ideal.IsPrime.prod_mem_iff (p := q)).1 hmem
      exact hcq x hxs hx
    · intro y hy
      rw [hrange]
      rw [← hs] at hy
      refine Submodule.span_induction
        (p := fun y _ => (∏ x ∈ s, c x) * y ∈ Ideal.span (σ : Set Q))
        (fun x hxs => ?_) (by simp)
        (fun _ _ _ _ h1 h2 => by rw [mul_add]; exact Ideal.add_mem _ h1 h2)
        (fun a _ _ h => by rw [smul_eq_mul, mul_left_comm]; exact Ideal.mul_mem_left _ _ h) hy
      rw [← Finset.mul_prod_erase s c hxs, mul_comm (c x), mul_assoc]
      exact Ideal.mul_mem_left _ _ (hcx x hxs)
  · -- minimality forces the coefficients of every relation into `q`
    intro a ha j
    by_contra hj
    have hunit : IsUnit (algebraMap Q L (a j)) :=
      IsLocalization.map_units L (⟨a j, hj⟩ : q.primeCompl)
    set x₀ := f j
    have hx₀σ : x₀ ∈ σ := (e.symm j).2
    have hfinj : Function.Injective f := fun i i' h => e.symm.injective (Subtype.ext h)
    let J := Ideal.span (algebraMap Q L '' ((σ.erase x₀ : Finset Q) : Set Q))
    have hother : ∀ y ∈ σ, y ≠ x₀ → algebraMap Q L y ∈ J := fun y hy hyx =>
      Ideal.subset_span ⟨y, Finset.mem_erase.2 ⟨hyx, hy⟩, rfl⟩
    have hx₀ : algebraMap Q L x₀ ∈ J := by
      have hsum : algebraMap Q L (a j) * algebraMap Q L x₀ =
          -∑ i ∈ Finset.univ.erase j, algebraMap Q L (a i) * algebraMap Q L (f i) := by
        have := congrArg (algebraMap Q L) ha
        rw [map_sum, map_zero, ← Finset.add_sum_erase _ _ (Finset.mem_univ j)] at this
        simp only [map_mul] at this
        exact eq_neg_of_add_eq_zero_left this
      have hmem : algebraMap Q L (a j) * algebraMap Q L x₀ ∈ J := by
        rw [hsum]
        exact J.neg_mem (J.sum_mem fun i hi =>
          J.mul_mem_left _ (hother _ (e.symm i).2 fun h =>
            Finset.ne_of_mem_erase hi (hfinj h)))
      obtain ⟨u, hu⟩ := hunit
      have := J.mul_mem_left (↑u⁻¹ : L) hmem
      rwa [← mul_assoc, ← hu, Units.inv_mul, one_mul] at this
    have hP' : Pσ (σ.erase x₀) := by
      refine le_trans hPσ (Ideal.span_le.2 ?_)
      rintro _ ⟨y, hy, rfl⟩
      by_cases hyx : y = x₀
      · subst hyx; exact hx₀
      · exact hother y hy hyx
    have hmin := hσmin (σ.erase x₀) (Finset.mem_filter.2
      ⟨Finset.mem_powerset.2 ((Finset.erase_subset _ _).trans hσs), hP'⟩)
    have := Finset.card_erase_lt_of_mem hx₀σ
    omega

end Ideal
