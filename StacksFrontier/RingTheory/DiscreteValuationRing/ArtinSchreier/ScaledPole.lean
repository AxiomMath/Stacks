module

public import StacksFrontier.RingTheory.DiscreteValuationRing.ArtinSchreier.LaurentCoefficients

/-!
# Eliminating degree-prime ramification: Laurent presentations and scaled poles

The residually-inseparable branch of the degree-`p` endgame is solved over an orbit extension
whose depth and rank are read off the pole data being solved. Four results decouple those two
parameters from any single data set, so that one extension can be prescribed in advance and
several data sets run over it:

* `IsDiscreteValuationRing.exists_unique_max_scaled_pole_of_le`: the scaled-pole maximum at any
  rank above an explicit bound, rather than at the one rank the data determines.
* `IsDiscreteValuationRing.exists_forall_unique_max_scaled_pole` and
  `IsDiscreteValuationRing.exists_shared_orbit_parameters`: one rank, and one depth, serving a
  whole finite family of pole data at once.
* `IsDiscreteValuationRing.exists_isGalois_totallyRamified_orbitExtension_forall_depth`: the orbit
  extension built from a prescribed depth and rank, with its translation subgroup certified at
  every smaller depth.

These fix parameters only. None of them transfers a solution between data sets, and none asserts
that a solution survives enlarging the extension it was obtained over.

They also reach one branch only. The *constant*-parameter branch — every Laurent coefficient in
the image of `κ_A`, pole order prime to `p` — is not an orbit extension at all: it is solved by
adjoining a root of `X ^ p - X - π ^ (-n) a`, and nothing here bears on it. Neither does pole
reduction: `ξ = π⁻¹` over a perfect residue field has constant coefficient `1` and pole order `1`,
which no Artin--Schreier translation lowers, and a constant coefficient stays constant under a
separable residue extension, so that branch cannot be pushed into the orbit branch either. A
shared extension for a family of constant parameters is a separate construction and is not
supplied by these four results.

This part also contains the Laurent presentations without related poles and the localization
lemmas for integral closures used by the weak-solution criteria.
-/

@[expose] public section

open Polynomial
open nonZeroDivisors
open WithZero

open scoped TensorProduct

attribute [local instance] FractionRing.liftAlgebra
attribute [local instance] Ideal.Quotient.field

universe uA uB uC uK uL uM uK₁

namespace IsDiscreteValuationRing

private theorem artinSchreier_sum_pow {R : Type*} [CommRing R]
    (p : ℕ) [Fact p.Prime] [CharP R p] (x : R) (r : ℕ) :
    (∑ k ∈ Finset.range r, x ^ (p ^ k)) ^ p -
      (∑ k ∈ Finset.range r, x ^ (p ^ k)) = x ^ (p ^ r) - x := by
  induction r with
  | zero => simp [(Fact.out : p.Prime).ne_zero]
  | succ r ih =>
    rw [Finset.sum_range_succ, add_pow_char]
    rw [← pow_mul, ← pow_succ]
    linear_combination ih

private theorem artinSchreier_add_sum_pow {L M : Type*} [Field L] [Field M]
    [Algebra L M] (p : ℕ) [Fact p.Prime] [CharP L p]
    (ξ : L) (z : M) (hz : z ^ p - z = algebraMap L M ξ) (x : L) (r : ℕ) :
    (z + algebraMap L M (∑ k ∈ Finset.range r, x ^ (p ^ k))) ^ p -
      (z + algebraMap L M (∑ k ∈ Finset.range r, x ^ (p ^ k))) =
        algebraMap L M (ξ - x + x ^ (p ^ r)) := by
  have : CharP M p := charP_of_injective_algebraMap (algebraMap L M).injective p
  have h := congrArg (algebraMap L M) (artinSchreier_sum_pow p x r)
  simp only [map_sub, map_pow] at h
  rw [add_pow_char]
  simp only [map_add, map_sub, map_pow]
  linear_combination hz + h


private theorem mul_inv_pow_mem_range_of_mem_span_pow
    {B L : Type*} [CommRing B] [Field L] [Algebra B L]
    (π : B) (ht : algebraMap B L π ≠ 0) (N i : ℕ) (hi : i ≤ N)
    (x : B) (hx : x ∈ Ideal.span {π ^ N}) :
    algebraMap B L x * (algebraMap B L π)⁻¹ ^ i ∈ (Algebra.linearMap B L).range := by
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp hx
  refine ⟨π ^ (N - i) * b, ?_⟩
  simp only [Algebra.linearMap_apply, map_mul, map_pow]
  rw [pow_sub₀ _ ht hi, inv_pow]
  ring

private theorem principalPart_eq_of_sub_mem
    {B L : Type*} [CommRing B] [Field L] [Algebra B L]
    (π : B) (ht : algebraMap B L π ≠ 0) (N i : ℕ) (hi : i ≤ N)
    (x y : B) (hxy : x - y ∈ Ideal.span {π ^ N}) :
    (Submodule.Quotient.mk (algebraMap B L x * (algebraMap B L π)⁻¹ ^ i) :
      L ⧸ (Algebra.linearMap B L).range) =
    Submodule.Quotient.mk (algebraMap B L y * (algebraMap B L π)⁻¹ ^ i) := by
  apply (Submodule.Quotient.eq _).mpr
  rw [← sub_mul, ← map_sub]
  exact mul_inv_pow_mem_range_of_mem_span_pow π ht N i hi _ hxy

private noncomputable def laurentCoefficientHom
    {B L k : Type*} [CommRing B] [Field L] [Algebra B L] [CommRing k]
    (π : B) (ht : algebraMap B L π ≠ 0) (N i : ℕ) (hi : i ≤ N)
    (I : Ideal B) (hI : I ≤ Ideal.span {π ^ N})
    (σ : k → B) (s : k →+* B ⧸ I) (hs : ∀ x, Ideal.Quotient.mk I (σ x) = s x) :
    k →+ L ⧸ (Algebra.linearMap B L).range :=
  AddMonoidHom.mk'
    (fun x => Submodule.Quotient.mk (algebraMap B L (σ x) * (algebraMap B L π)⁻¹ ^ i))
    fun x y => by
      have hadd : σ (x + y) - (σ x + σ y) ∈ I :=
        (Ideal.Quotient.eq).mp (by simp only [map_add, hs])
      calc
        _ = Submodule.Quotient.mk
            (algebraMap B L (σ x + σ y) * (algebraMap B L π)⁻¹ ^ i) :=
          principalPart_eq_of_sub_mem π ht N i hi _ _ (hI hadd)
        _ = _ := by rw [map_add, add_mul, Submodule.Quotient.mk_add]

private theorem laurentCoefficientHom_apply
    {B L k : Type*} [CommRing B] [Field L] [Algebra B L] [CommRing k]
    (π : B) (ht : algebraMap B L π ≠ 0) (N i : ℕ) (hi : i ≤ N)
    (I : Ideal B) (hI : I ≤ Ideal.span {π ^ N})
    (σ : k → B) (s : k →+* B ⧸ I) (hs : ∀ x, Ideal.Quotient.mk I (σ x) = s x) (x : k) :
    laurentCoefficientHom π ht N i hi I hI σ s hs x =
      Submodule.Quotient.mk (algebraMap B L (σ x) * (algebraMap B L π)⁻¹ ^ i) := rfl


private theorem laurentCoefficientHom_pow
    {B L k : Type*} [CommRing B] [Field L] [Algebra B L] [CommRing k]
    (π : B) (ht : algebraMap B L π ≠ 0) (N j e : ℕ) (hje : j * e ≤ N)
    (I : Ideal B) (hI : I ≤ Ideal.span {π ^ N})
    (σ : k → B) (s : k →+* B ⧸ I) (hs : ∀ x, Ideal.Quotient.mk I (σ x) = s x) (x : k) :
    (Submodule.Quotient.mk ((algebraMap B L (σ x) * (algebraMap B L π)⁻¹ ^ j) ^ e) :
      L ⧸ (Algebra.linearMap B L).range) =
    laurentCoefficientHom π ht N (j * e) hje I hI σ s hs (x ^ e) := by
  have hpow : (σ x) ^ e - σ (x ^ e) ∈ I :=
    (Ideal.Quotient.eq).mp (by simp only [map_pow, hs])
  have h := principalPart_eq_of_sub_mem π ht N (j * e) hje ((σ x) ^ e) (σ (x ^ e)) (hI hpow)
  simpa only [laurentCoefficientHom_apply, map_pow, mul_pow, ← pow_mul] using h


private theorem sum_apply_update_of_mem
    {ι k Q : Type*} [DecidableEq ι] [AddCommGroup k] [AddCommGroup Q]
    (s : Finset ι) (H : ι → k →+ Q) (c : ι → k) (j : ι) (hj : j ∈ s) (a : k) :
    (∑ i ∈ s, H i (Function.update c j a i)) =
      (∑ i ∈ s, H i (c i)) - H j (c j) + H j a := by
  have he : (fun i => H i (Function.update c j a i)) =
      Function.update (fun i => H i (c i)) j (H j a) := by
    funext i
    by_cases hi : i = j
    · subst i; simp
    · simp [Function.update_of_ne hi]
  rw [he, Finset.sum_update_of_mem hj]
  have hs := Finset.sum_erase_add s (fun i => H i (c i)) hj
  rw [← hs, Finset.sdiff_singleton_eq_erase]
  abel

private theorem card_filter_update_update_lt
    {ι k : Type*} [DecidableEq ι] [Zero k]
    (s : Finset ι) (P : k → Prop) [DecidablePred P] (hP : P 0)
    (c : ι → k) (j j' : ι) (hj : j ∈ s) (hne : j ≠ j')
    (hcj : ¬P (c j)) (hcj' : ¬P (c j')) (a : k) :
    (s.filter fun i => ¬P (Function.update (Function.update c j 0) j' a i)).card <
      (s.filter fun i => ¬P (c i)).card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro i hi
    obtain ⟨his, hiP⟩ := Finset.mem_filter.mp hi
    refine Finset.mem_filter.mpr ⟨his, ?_⟩
    by_cases hij : i = j
    · subst i
      simp [Function.update_of_ne hne, hP] at hiP
    by_cases hij' : i = j'
    · subst i; exact hcj'
    · simpa [Function.update_of_ne hij, Function.update_of_ne hij'] using hiP
  · intro heq
    have hjmem : j ∈ s.filter fun i => ¬P (c i) := Finset.mem_filter.mpr ⟨hj, hcj⟩
    rw [← heq] at hjmem
    simp [Function.update_of_ne hne, hP] at hjmem


/-- Removing a lower coefficient and adding its Frobenius power to a second coefficient
strictly decreases the nonconstant support. -/
theorem exists_artinSchreier_presentation_with_smaller_support
    {L M k Q : Type*} [Field L] [Field M] [Algebra L M]
    [CommRing k] [AddCommGroup Q]
    (p : ℕ) [Fact p.Prime] [CharP L p]
    (q : L →+ Q) (H : ℕ → k →+ Q) (S : Finset ℕ)
    (P : k → Prop) [DecidablePred P] (hP : P 0)
    (ξ : L) (z : M) (coeff : ℕ → k)
    (hz : z ^ p - z = algebraMap L M ξ) (hgen : Algebra.adjoin L {z} = ⊤)
    (hexp : q ξ = ∑ i ∈ S, H i (coeff i))
    (j j' r : ℕ) (hj : j ∈ S) (hj' : j' ∈ S) (hne : j ≠ j')
    (hcj : ¬P (coeff j)) (hcj' : ¬P (coeff j'))
    (x : L) (hx : q x = H j (coeff j))
    (hxp : q (x ^ (p ^ r)) = H j' (coeff j ^ (p ^ r))) :
    ∃ (ξ' : L) (z' : M) (coeff' : ℕ → k),
      z' ^ p - z' = algebraMap L M ξ' ∧ Algebra.adjoin L {z'} = ⊤ ∧
      q ξ' = ∑ i ∈ S, H i (coeff' i) ∧
      (S.filter fun i => ¬P (coeff' i)).card < (S.filter fun i => ¬P (coeff i)).card := by
  let coeff' := Function.update (Function.update coeff j 0) j' (coeff j' + coeff j ^ (p ^ r))
  have hsum : (∑ i ∈ S, H i (coeff' i)) =
      (∑ i ∈ S, H i (coeff i)) - H j (coeff j) + H j' (coeff j ^ (p ^ r)) := by
    dsimp only [coeff']
    rw [sum_apply_update_of_mem S H _ j' hj', Function.update_of_ne hne.symm,
      sum_apply_update_of_mem S H coeff j hj, map_zero, map_add]
    abel
  refine ⟨ξ - x + x ^ (p ^ r),
    z + algebraMap L M (∑ k ∈ Finset.range r, x ^ (p ^ k)), coeff',
    artinSchreier_add_sum_pow p ξ z hz x r, ?_, ?_, ?_⟩
  · rw [← sub_neg_eq_add z, ← map_neg, adjoin_singleton_sub_algebraMap, hgen]
  · rw [map_add, map_sub, hexp, hx, hxp, hsum]
  · exact card_filter_update_update_lt S P hP coeff j j' hj hne hcj hcj' _

/-- A Laurent presentation can be chosen so that no two nonconstant pole indices
are related by a power of the characteristic. -/
theorem exists_artinSchreier_laurent_presentation_without_related_poles
    {B L M k : Type*} [CommRing B] [Field L] [Field M] [CommRing k]
    [Algebra B L] [Algebra L M]
    (p : ℕ) [Fact p.Prime] [CharP L p]
    (π : B) (ht : algebraMap B L π ≠ 0) (n : ℕ)
    (I : Ideal B) (hI : I ≤ Ideal.span {π ^ n})
    (σ : k → B) (s : k →+* B ⧸ I) (hs : ∀ x, Ideal.Quotient.mk I (σ x) = s x)
    (P : k → Prop) (hP : P 0)
    (ξ : L) (z : M) (coeff : ℕ → k) (b : B)
    (hz : z ^ p - z = algebraMap L M ξ) (hgen : Algebra.adjoin L {z} = ⊤)
    (hexp : ξ = (∑ i ∈ Finset.range n,
      algebraMap B L (σ (coeff i)) * (algebraMap B L π)⁻¹ ^ (n - i)) + algebraMap B L b) :
    ∃ (ξ' : L) (z' : M) (coeff' : ℕ → k) (b' : B),
      z' ^ p - z' = algebraMap L M ξ' ∧ Algebra.adjoin L {z'} = ⊤ ∧
      ξ' = (∑ i ∈ Finset.range n,
        algebraMap B L (σ (coeff' i)) * (algebraMap B L π)⁻¹ ^ (n - i)) + algebraMap B L b' ∧
      ∀ j ∈ Finset.range n, ¬P (coeff' j) →
        ∀ j' ∈ Finset.range n, ¬P (coeff' j') → j ≠ j' →
          ∀ r : ℕ, n - j' ≠ (n - j) * p ^ r := by
  classical
  let U := (Algebra.linearMap B L).range
  let q : L →+ L ⧸ U := U.mkQ.toAddMonoidHom
  let H : ℕ → k →+ L ⧸ U := fun i =>
    laurentCoefficientHom π ht n (n - i) (Nat.sub_le n i) I hI σ s hs
  have hqmap (a : B) : q (algebraMap B L a) = 0 :=
    (Submodule.Quotient.mk_eq_zero U).mpr ⟨a, rfl⟩
  have hexpq : q ξ = ∑ i ∈ Finset.range n, H i (coeff i) := by
    rw [hexp, map_add, hqmap, add_zero, map_sum]
    rfl
  let T : ℕ → Prop := fun m => ∃ (η : L) (w : M) (c : ℕ → k),
    w ^ p - w = algebraMap L M η ∧ Algebra.adjoin L {w} = ⊤ ∧
    q η = ∑ i ∈ Finset.range n, H i (c i) ∧
    (Finset.filter (fun i => ¬P (c i)) (Finset.range n)).card = m
  have hT : ∃ m, T m := ⟨_, ξ, z, coeff, hz, hgen, hexpq, rfl⟩
  obtain ⟨η, w, c, hη, hw, hc, hcard⟩ := Nat.find_spec hT
  have hLaurent : ∃ b' : B, η = (∑ i ∈ Finset.range n,
      algebraMap B L (σ (c i)) * (algebraMap B L π)⁻¹ ^ (n - i)) + algebraMap B L b' := by
    have he : q η = q (∑ i ∈ Finset.range n,
        algebraMap B L (σ (c i)) * (algebraMap B L π)⁻¹ ^ (n - i)) := by
      rw [hc, map_sum]
      rfl
    obtain ⟨b', hb'⟩ := (Submodule.Quotient.eq U).mp he
    exact ⟨b', by change algebraMap B L b' = _ at hb'; linear_combination -hb'⟩
  obtain ⟨b', hb'⟩ := hLaurent
  refine ⟨η, w, c, b', hη, hw, hb', ?_⟩
  intro j hj hcj j' hj' hcj' hne r hrel
  let x := algebraMap B L (σ (c j)) * (algebraMap B L π)⁻¹ ^ (n - j)
  have hx : q x = H j (c j) := rfl
  have hxp : q (x ^ (p ^ r)) = H j' (c j ^ (p ^ r)) := by
    have hbound : (n - j) * p ^ r ≤ n := by rw [← hrel]; exact Nat.sub_le n j'
    have h := laurentCoefficientHom_pow π ht n (n - j) (p ^ r) hbound I hI σ s hs (c j)
    simpa only [← hrel, H, x, q, U, Submodule.mkQ_apply, LinearMap.toAddMonoidHom_coe] using h
  obtain ⟨η', w', c', hη', hw', hc', hlt⟩ :=
    exists_artinSchreier_presentation_with_smaller_support p q H (Finset.range n) P hP
      η w c hη hw hc j j' r hj hj' hne hcj hcj' x hx hxp
  have hle : Nat.find hT ≤ (Finset.filter (fun i => ¬P (c' i)) (Finset.range n)).card :=
    Nat.find_min' hT ⟨η', w', c', hη', hw', hc', rfl⟩
  omega
/-- **The scaled-pole maximum, at any prescribed scaling exponent above an explicit bound.**

`exists_unique_max_scaled_pole` chooses the exponent `R` itself, as `∑_{i ∈ J} depth i + n + 2`.
That choice is a function of the data `(n, J, depth)`, and for the Artin--Schreier endgame that
data is read off one extension: the exponent produced is the rank of the orbit extension used to
solve it, so it is inseparable from the extension it solves.

Here `R` is an input, constrained only from below: for **every** exponent past the bound the four
clauses hold, so the exponent can be fixed *before* the data is examined and shared by several
data sets at once.

What varies with the exponent is which position attains the maximum, and the statement says so —
`j` is existentially quantified inside, after `R`.  The claim is not that a package established at
one exponent persists at another; it is that each admissible exponent has a package of its own.

That is the whole difference and it is what a shared extension needs.  `Module.finrank K K₁`
of an orbit extension is exactly `p ^ rank`, so one extension realises one rank; consumers cannot
each pick their own rank and reconcile afterwards.  With the exponent free above a bound, a finite
family of data sets can agree on `R` in advance — take any `R` past all their bounds, as
`exists_forall_unique_max_scaled_pole` does — and each member then reruns over the single
extension of that rank, rather than over an extension built from its own pole data.

The bound is not tight and is not meant to be; only that it is explicit and depends on the data
solely through `∑_{i ∈ J} depth i` and `n`, both of which a finite family can bound uniformly. -/
theorem exists_unique_max_scaled_pole_of_le
    (p n : ℕ) (hp : p.Prime) (J : Finset ℕ) (hJ : J.Nonempty)
    (hJn : ∀ j ∈ J, j < n) (depth : ℕ → ℕ)
    (hsep : ∀ j ∈ J, ∀ j' ∈ J, j ≠ j' → ∀ r : ℕ,
      n - j' ≠ (n - j) * p ^ r)
    (R : ℕ) (hR : (∑ i ∈ J, depth i) + n + 2 ≤ R) :
    ∃ j : ℕ, j ∈ J ∧ (∀ i ∈ J, depth i + 1 < R) ∧
      (∀ i ∈ J, n < (n - i) * p ^ (R - depth i)) ∧
      (∀ i ∈ J, i ≠ j → (n - i) * p ^ (R - depth i) < (n - j) * p ^ (R - depth j)) ∧
      p ∣ (n - j) * p ^ (R - depth j) := by
  have hd : ∀ i ∈ J, depth i ≤ ∑ k ∈ J, depth k := fun i hi =>
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
  have hdR : ∀ i ∈ J, depth i + 1 < R := by
    intro i hi
    have := hd i hi
    omega
  let f : ℕ → ℕ := fun i => (n - i) * p ^ (R - depth i)
  have hinj : ∀ i ∈ J, ∀ j ∈ J, f i = f j → i = j := by
    suffices H : ∀ i ∈ J, ∀ j ∈ J, depth i ≤ depth j → f i = f j → i = j by
      intro i hi j hj he
      rcases le_total (depth i) (depth j) with hij | hji
      · exact H i hi j hj hij he
      · exact (H j hj i hi hji he.symm).symm
    intro i hi j hj hij he
    by_contra hne
    have hjR := hdR j hj
    have hexp : R - depth i = (depth j - depth i) + (R - depth j) := by omega
    have he' : (n - i) * p ^ (depth j - depth i) = n - j := by
      apply Nat.mul_right_cancel (pow_pos hp.pos (R - depth j))
      simpa only [f, hexp, pow_add, mul_assoc] using he
    exact hsep i hi j hj hne (depth j - depth i) he'.symm
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image J f hJ
  refine ⟨j, hj, hdR, ?_, ?_, ?_⟩
  · intro i hi
    have hiN := hJn i hi
    have hiD := hd i hi
    have hNr : n ≤ R - depth i := by omega
    have hbig : n < p ^ (R - depth i) :=
      Nat.lt_two_pow_self.trans_le
        ((Nat.pow_le_pow_left hp.two_le n).trans (Nat.pow_le_pow_right hp.pos hNr))
    exact hbig.trans_le (by
      simpa only [one_mul] using Nat.mul_le_mul_right (p ^ (R - depth i))
        (show 1 ≤ n - i by omega))
  · intro i hi hne
    exact lt_of_le_of_ne (hmax i hi) (fun he => hne (hinj i hi j hj he))
  · apply dvd_mul_of_dvd_right
    exact dvd_pow_self p (by have := hdR j hj; omega)

/-- Let `J` be a nonempty finite set of indices `j < n` such that no pole order `n - j'` equals
`(n - j) * p ^ r` for distinct `j, j' ∈ J`, and let `depth : ℕ → ℕ`. Then there are `R` and
`j ∈ J` such that `depth i + 1 < R` for all `i ∈ J`, every scaled pole order
`(n - i) * p ^ (R - depth i)` with `i ∈ J` exceeds `n`, the one at `j` is strictly larger than
all others, and it is divisible by `p`. -/
theorem exists_unique_max_scaled_pole
    (p n : ℕ) (hp : p.Prime) (J : Finset ℕ) (hJ : J.Nonempty)
    (hJn : ∀ j ∈ J, j < n) (depth : ℕ → ℕ)
    (hsep : ∀ j ∈ J, ∀ j' ∈ J, j ≠ j' → ∀ r : ℕ,
      n - j' ≠ (n - j) * p ^ r) :
    ∃ R j : ℕ, j ∈ J ∧ (∀ i ∈ J, depth i + 1 < R) ∧
      (∀ i ∈ J, n < (n - i) * p ^ (R - depth i)) ∧
      (∀ i ∈ J, i ≠ j → (n - i) * p ^ (R - depth i) < (n - j) * p ^ (R - depth j)) ∧
      p ∣ (n - j) * p ^ (R - depth j) :=
  ⟨(∑ i ∈ J, depth i) + n + 2,
    exists_unique_max_scaled_pole_of_le p n hp J hJ hJn depth hsep
      ((∑ i ∈ J, depth i) + n + 2) le_rfl⟩

/-- **One scaling exponent for a whole finite family of pole data.**

Each member `c` of a finite family carries its own pole order `n c`, its own set `J c` of
non-descending coefficient positions and its own Frobenius depths `depth c`.  Read separately,
each would produce its own exponent and hence its own orbit extension.  Here a single `R` is
produced at which **every** member's unique-maximum package holds at once: take any exponent past
all of their bounds, which `exists_unique_max_scaled_pole_of_le` permits.

This is the arithmetic half of what a shared extension requires, and it is worth being precise
about what it does and does not give.

It does give a rank that no member determines: `R` is chosen from the family as a whole, so a
single orbit extension of rank `R` can be built once and each member rerun over it.  Every member
keeps its own maximising position `j`, its own pole order and its own depths, all of which stay
member-specific — the exponent is what is shared, not the data.

It does not give any stability statement.  Nothing here says a package established at one exponent
survives enlargement of an extension, and nothing here compares members: no member is
distinguished, and a package for one member is never used to obtain a package for another.  The
`∀ c` is discharged member by member, each from its own hypotheses. -/
theorem exists_forall_unique_max_scaled_pole
    (p : ℕ) (hp : p.Prime) {ι : Type*} [Finite ι]
    (n : ι → ℕ) (J : ι → Finset ℕ) (hJ : ∀ c, (J c).Nonempty)
    (hJn : ∀ c, ∀ j ∈ J c, j < n c) (depth : ι → ℕ → ℕ)
    (hsep : ∀ c, ∀ j ∈ J c, ∀ j' ∈ J c, j ≠ j' → ∀ r : ℕ,
      n c - j' ≠ (n c - j) * p ^ r) :
    ∃ R : ℕ, ∀ c : ι, ∃ j : ℕ, j ∈ J c ∧ (∀ i ∈ J c, depth c i + 1 < R) ∧
      (∀ i ∈ J c, n c < (n c - i) * p ^ (R - depth c i)) ∧
      (∀ i ∈ J c, i ≠ j →
        (n c - i) * p ^ (R - depth c i) < (n c - j) * p ^ (R - depth c j)) ∧
      p ∣ (n c - j) * p ^ (R - depth c j) := by
  let : Fintype ι := Fintype.ofFinite ι
  refine ⟨Finset.univ.sup fun c => (∑ i ∈ J c, depth c i) + n c + 2, fun c => ?_⟩
  have hle : (∑ i ∈ J c, depth c i) + n c + 2 ≤
      Finset.univ.sup fun c => (∑ i ∈ J c, depth c i) + n c + 2 :=
    Finset.le_sup (f := fun c => (∑ i ∈ J c, depth c i) + n c + 2) (Finset.mem_univ c)
  exact exists_unique_max_scaled_pole_of_le p (n c) hp (J c) (hJ c) (hJn c) (depth c) (hsep c)
    _ hle

/-- **One depth and one rank for a whole finite family of pole data.**

The pair of parameters `exists_isGalois_totallyRamified_orbitExtension` consumes, produced for a
finite family at once: a depth `N` clearing every member's pole order (`n c + 1 ≤ N`, which is
what that member's uniformiser approximation `α ^ (p ^ R) ≡ π mod π ^ (n c + 1)` needs) and a rank
`R` at which every member's unique-maximum package holds.

Feeding this pair to `exists_isGalois_totallyRamified_orbitExtension_forall_depth` yields a single
finite Galois extension, totally ramified with respect to `A`, of degree exactly `p ^ R`, whose
translation subgroup is certified at every depth `N' ≤ N` and so at each member's own `n c + 1`.
One extension, prescribed before any member is examined, carrying the orbit data every member
needs.

What still has to be supplied per member, and is not supplied here, is that member's own
Artin--Schreier and Laurent data over that extension.  This lemma fixes the parameters; it makes
no claim that a weak solution for one member transfers to another or survives enlargement. -/
theorem exists_shared_orbit_parameters
    (p : ℕ) (hp : p.Prime) {ι : Type*} [Finite ι]
    (n : ι → ℕ) (J : ι → Finset ℕ) (hJ : ∀ c, (J c).Nonempty)
    (hJn : ∀ c, ∀ j ∈ J c, j < n c) (depth : ι → ℕ → ℕ)
    (hsep : ∀ c, ∀ j ∈ J c, ∀ j' ∈ J c, j ≠ j' → ∀ r : ℕ,
      n c - j' ≠ (n c - j) * p ^ r) :
    ∃ N R : ℕ, 1 ≤ N ∧ (∀ c : ι, n c + 1 ≤ N) ∧
      ∀ c : ι, ∃ j : ℕ, j ∈ J c ∧ (∀ i ∈ J c, depth c i + 1 < R) ∧
        (∀ i ∈ J c, n c < (n c - i) * p ^ (R - depth c i)) ∧
        (∀ i ∈ J c, i ≠ j →
          (n c - i) * p ^ (R - depth c i) < (n c - j) * p ^ (R - depth c j)) ∧
        p ∣ (n c - j) * p ^ (R - depth c j) := by
  let : Fintype ι := Fintype.ofFinite ι
  obtain ⟨R, hRpkg⟩ := exists_forall_unique_max_scaled_pole p hp n J hJ hJn depth hsep
  refine ⟨(Finset.univ.sup n) + 1, R, Nat.le_add_left 1 _, fun c => ?_, hRpkg⟩
  have hc : n c ≤ Finset.univ.sup n := Finset.le_sup (f := n) (Finset.mem_univ c)
  omega

/-- If `ξ = ∑ i < n, cᵢ * π⁻¹ ^ (n - i) + b` with `cᵢ, b ∈ B`, then
`π ^ n * ξ = ∑ i < n, cᵢ * π ^ i + π ^ n * b`, the image of an element of `B`. -/
theorem pow_mul_laurent_expansion
    {B L : Type*} [CommRing B] [Field L] [Algebra B L]
    (π : B) (ht : algebraMap B L π ≠ 0) (n : ℕ) (coeff : ℕ → B) (b : B) (ξ : L)
    (hexp : ξ = (∑ i ∈ Finset.range n,
      algebraMap B L (coeff i) * (algebraMap B L π)⁻¹ ^ (n - i)) + algebraMap B L b) :
    algebraMap B L π ^ n * ξ =
      algebraMap B L ((∑ i ∈ Finset.range n, coeff i * π ^ i) + π ^ n * b) := by
  rw [hexp, mul_add, Finset.mul_sum, map_add, map_sum, map_mul, map_pow]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_mul, map_pow, inv_pow_sub₀ ht (Nat.le_of_lt (Finset.mem_range.mp hi))]
  field_simp

/-- A Laurent parameter whose coefficient lifts agree modulo the pole depth with elements of the
base DVR is a base-field parameter plus an integral term.

This is the presentation needed by the split-class solver after a weakly unramified residue
base change.  It deliberately assumes only coefficient congruences in the post-base-change DVR:
no section of that DVR's whole residue field, and no minimality of the transported Laurent
presentation, is required. -/
theorem exists_base_parameter_add_integral_of_coefficients_lift
    {A B K L : Type*} [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    (pi : A) (ht : algebraMap A L pi ≠ 0) (n : ℕ)
    (coeff : ℕ → B) (b : B) (xi : L) (lift : ℕ → A)
    (hexp : xi = (∑ i ∈ Finset.range n, algebraMap B L (coeff i) *
      (algebraMap B L (algebraMap A B pi))⁻¹ ^ (n - i)) + algebraMap B L b)
    (hlift : ∀ i ∈ Finset.range n,
      coeff i - algebraMap A B (lift i) ∈ Ideal.span {algebraMap A B pi ^ n}) :
    ∃ (xi0 : K) (b' : B), xi = algebraMap K L xi0 + algebraMap B L b' := by
  have htB : algebraMap B L (algebraMap A B pi) ≠ 0 := by
    simpa only [← IsScalarTower.algebraMap_apply] using ht
  have hexp' := pow_mul_laurent_expansion (algebraMap A B pi) htB n coeff b xi hexp
  obtain ⟨b', hxi⟩ := eq_constant_numerator_of_coefficients_lift pi ht n coeff b xi lift
    (by simpa only [← IsScalarTower.algebraMap_apply] using hexp') hlift
  refine ⟨(algebraMap A K pi)⁻¹ ^ n *
      algebraMap A K (∑ i ∈ Finset.range n, lift i * pi ^ i), b', ?_⟩
  calc
    xi = (algebraMap A L pi)⁻¹ ^ n *
        algebraMap A L (∑ i ∈ Finset.range n, lift i * pi ^ i) +
          algebraMap B L b' := hxi
    _ = (algebraMap K L (algebraMap A K pi))⁻¹ ^ n *
        algebraMap K L (algebraMap A K
          (∑ i ∈ Finset.range n, lift i * pi ^ i)) + algebraMap B L b' := by
      rw [← IsScalarTower.algebraMap_apply A K L,
        show algebraMap A L (∑ i ∈ Finset.range n, lift i * pi ^ i) =
          algebraMap K L (algebraMap A K
            (∑ i ∈ Finset.range n, lift i * pi ^ i)) from
          IsScalarTower.algebraMap_apply A K L _]
    _ = algebraMap K L ((algebraMap A K pi)⁻¹ ^ n *
        algebraMap A K (∑ i ∈ Finset.range n, lift i * pi ^ i)) +
          algebraMap B L b' := by rw [map_mul, map_pow, map_inv₀]


open scoped nonZeroDivisors in
private theorem exists_lift_integralClosure_to_field
    (R K T S F : Type*) [CommRing R] [IsDomain R] [Field K] [CommRing T] [CommRing S]
    [Field F] [Algebra R K] [IsFractionRing R K] [Algebra K T] [Algebra R T]
    [IsScalarTower R K T] [Algebra.IsIntegral K T]
    [Algebra R S] [Algebra S T] [IsScalarTower R S T] [IsIntegralClosure S R T]
    [Algebra R F] (hRF : Function.Injective (algebraMap R F)) (g : S →ₐ[R] F) :
    ∃ f : T →ₐ[R] F, ∀ s : S, f (algebraMap S T s) = g s := by
  let := Stacks.DiscreteValuationRing.Ramification.isLocalization_integralClosure_of_isIntegral
    R K T S R⁰
  have hu : ∀ s : Algebra.algebraMapSubmonoid S R⁰, IsUnit (g s) := by
    rintro ⟨_, r, hr, rfl⟩
    rw [AlgHom.commutes, isUnit_iff_ne_zero]
    simpa only [map_zero] using hRF.ne (mem_nonZeroDivisors_iff_ne_zero.mp hr)
  exact ⟨IsLocalization.liftAlgHom hu, fun _ => IsLocalization.lift_eq _ _⟩

open scoped nonZeroDivisors in
private theorem surjective_of_localization_fractionRing
    (K T S Q F : Type*) [Field K] [CommRing T] [CommRing S]
    [CommRing Q] [IsDomain Q] [Field F]
    [Algebra K T] [Algebra.IsIntegral K T] [Algebra K F]
    [Algebra S T] [Algebra S Q] [Algebra Q F] [Algebra S F]
    [IsScalarTower S Q F] [IsFractionRing Q F]
    (P : Submonoid S) [IsLocalization P Q]
    (f : T →ₐ[K] F) (hs : ∀ s : S, algebraMap S F s = f (algebraMap S T s)) :
    Function.Surjective f := by
  have hinv : ∀ x ∈ f.range, x⁻¹ ∈ f.range := by
    rintro x ⟨t, rfl⟩
    exact ((Algebra.IsIntegral.isIntegral (R := K) t).map f).inv_mem ⟨t, rfl⟩
  have hQ : ∀ q : Q, algebraMap Q F q ∈ f.range := by
    intro q
    obtain ⟨s, t, he⟩ := IsLocalization.exists_mk'_eq P q
    have heq : algebraMap Q F q = algebraMap S F s / algebraMap S F t := by
      have he' := IsLocalization.mk'_spec Q s t
      rw [he] at he'
      have ht : algebraMap S F t ≠ 0 := by
        rw [IsScalarTower.algebraMap_apply S Q F]
        exact ((IsLocalization.map_units Q t).map (algebraMap Q F)).ne_zero
      apply (eq_div_iff ht).mpr
      simpa only [map_mul, ← IsScalarTower.algebraMap_apply] using congrArg (algebraMap Q F) he'
    rw [heq, div_eq_mul_inv]
    exact f.range.mul_mem (hs s ▸ ⟨_, rfl⟩) (hinv _ (hs t ▸ ⟨_, rfl⟩))
  intro x
  obtain ⟨a, b, hb, h⟩ := IsFractionRing.div_surjective Q x
  rw [← h, div_eq_mul_inv]
  exact f.range.mul_mem (hQ a) (hinv _ (hQ b))

open scoped nonZeroDivisors in
private theorem exists_fieldFactor_of_integralClosure_localization
    (R K T S Q : Type*) [CommRing R] [IsDomain R] [Field K]
    [CommRing T] [CommRing S] [CommRing Q] [IsDomain Q]
    [Algebra R K] [IsFractionRing R K] [Algebra K T] [Algebra R T]
    [IsScalarTower R K T] [Module.Finite K T]
    [Algebra R S] [Algebra S T] [IsScalarTower R S T] [IsIntegralClosure S R T]
    [Algebra S Q] [Algebra R Q] [IsScalarTower R S Q]
    (P : Submonoid S) [IsLocalization P Q]
    (hRQ : Function.Injective (algebraMap R Q)) :
    ∃ (_ : Algebra K (FractionRing Q)) (_ : IsScalarTower R K (FractionRing Q)),
      ∃ f : T →ₐ[K] FractionRing Q,
        Function.Surjective f ∧
          (∀ s : S, f (algebraMap S T s) = algebraMap S (FractionRing Q) s) ∧
            Module.Finite K (FractionRing Q) := by
  let F := FractionRing Q
  have hRF : Function.Injective (algebraMap R F) := by
    rw [IsScalarTower.algebraMap_eq R Q F]
    exact (IsFractionRing.injective Q F).comp hRQ
  let k : K →ₐ[R] F := IsFractionRing.liftAlgHom (g := Algebra.ofId R F) hRF
  let : Algebra K F := k.toRingHom.toAlgebra
  let : IsScalarTower R K F := IsScalarTower.of_algebraMap_eq fun x => (k.commutes x).symm
  obtain ⟨f, hf⟩ := exists_lift_integralClosure_to_field R K T S F hRF
    (IsScalarTower.toAlgHom R S F)
  have hK : f.toRingHom.comp (algebraMap K T) = algebraMap K F := by
    apply IsLocalization.ringHom_ext R⁰
    ext r
    simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]
    exact f.commutes r
  let fK : T →ₐ[K] F := { f.toRingHom with commutes' := DFunLike.congr_fun hK }
  have hsurj : Function.Surjective fK := surjective_of_localization_fractionRing K T S Q F P
    fK (fun s => (hf s).symm)
  refine ⟨inferInstance, inferInstance, fK, hsurj, hf, ?_⟩
  exact Module.Finite.of_surjective fK.toLinearMap hsurj

private theorem ramificationIdx_localization_atPrime
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (q : Ideal S) [q.IsPrime] :
    (IsLocalRing.maximalIdeal (Localization.AtPrime q)).ramificationIdx R =
      q.ramificationIdx R := by
  let Q := Localization.AtPrime q
  let m := IsLocalRing.maximalIdeal Q
  let : m.LiesOver q := ⟨(IsLocalization.AtPrime.under_maximalIdeal Q q).symm⟩
  let : Module.Flat S Q := IsLocalization.flat Q q.primeCompl
  let : Algebra.FormallyUnramified S Q := Algebra.FormallyUnramified.of_isLocalization q.primeCompl
  let : Algebra.EssFiniteType S Q := Algebra.EssFiniteType.of_isLocalization Q q.primeCompl
  let : Algebra.IsUnramifiedAt S m := Algebra.FormallyUnramified.comp S Q (Localization.AtPrime m)
  rw [Ideal.ramificationIdx_tower (R := R) q m, Ideal.ramificationIdx_eq_one m S, mul_one]

end IsDiscreteValuationRing
