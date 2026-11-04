module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import StacksFrontier.RingTheory.CohenMacaulay.AssociatedPrimes
public import StacksFrontier.RingTheory.CohenMacaulay.Dimension
public import StacksFrontier.RingTheory.CohenMacaulay.RegularSequence

/-!
# Choosing a parameter in the source of a map to a Cohen-Macaulay local ring

Let `t : A →+* C` be a ring map into a Noetherian local Cohen-Macaulay ring `C` and let `I` be
an ideal of `A` whose extension `t(I)C` cuts the dimension of `C` down strictly, that is
`dim(C/t(I)C) < dim(C)`. Then some `f ∈ I` has `t(f)` outside every minimal prime of `C`.

This is the step Stacks 0461 performs between choosing the affine charts and cutting
`U' = Spec(A/fA)`. There `C = B_𝔮/s(𝔪)B_𝔮` is the local ring of the fibre `F_u` at `e(u)`, the
map is `t : A_𝔪 → C`, the ideal is `I = 𝔪`, and the two dimensions are
`dim(C/t(𝔪)C) = d₁ < d₂ = dim(C)`. Avoiding the minimal primes is what makes `t(f)` a
nonzerodivisor on `C`, which is how the slicing argument there continues.

## Shape of the argument

Only two inputs are used. A Noetherian ring has finitely many minimal primes, and a
Cohen-Macaulay local ring is equidimensional: the dimension formula of Stacks 00NA,
`dim(C) = height(𝔭) + dim(C/𝔭)`, reads `dim(C) = dim(C/𝔫)` at a minimal prime `𝔫`, whose height
is zero. So if `t(I)C` were contained in some minimal prime `𝔫` then `C/t(I)C` would surject
onto `C/𝔫`, giving `dim(C) = dim(C/𝔫) ≤ dim(C/t(I)C) < dim(C)`. Hence `I` is contained in none
of the finitely many primes `t⁻¹(𝔫)`, and prime avoidance (Stacks 00DS, available as
`Ideal.subset_union_prime_finite`) produces an `f ∈ I` lying outside all of them.

## Main definitions

No new definitions are introduced.

## Main results

* `ringKrullDim_quotient_eq_of_mem_minimalPrimes`: a Cohen-Macaulay local ring is
  equidimensional.
* `exists_mem_notMem_minimalPrimes_map`: the statement above, for an arbitrary ideal `I` of `A`.
* `exists_mem_maximalIdeal_notMem_minimalPrimes_map`: its reading at the maximal ideal of a local
  source, with the source's two bounds `dim(C/t(𝔪)C) ≤ d₁` and `d₁ < d₂ = dim(C)` in place of
  the single strict inequality.
* `exists_mem_isSMulRegular_map`: the same `f`, with `t(f)` a nonzerodivisor on `C`, which is the
  form the slicing argument consumes.

## Implementation notes

`t` is a bare ring homomorphism: neither locality of `t` nor Noetherianness of `A` is assumed,
and `I` is an arbitrary ideal rather than a maximal one, since prime avoidance needs none of
those. This matches `exists_mem_maximalIdeal_isSMulRegular_map` in
`CohenMacaulay/RegularSequence.lean`, which is the case `d₁ = 0` of the same argument run against
the associated primes instead, the hypothesis there being
`𝔪_C = √(t(𝔪_A)C)` rather than a dimension inequality.

Cohen-Macaulayness is `Module.IsMaximalCohenMacaulay C C`, the hypothesis under which the draft
states Stacks 00NA. Krull dimensions take values in `WithBot ℕ∞`, so the hypothesis is the
strict inequality `dim(C/t(I)C) < dim(C)` with no truncated subtraction; the source's chain
`dim(C/t(𝔪)C) ≤ d₁ < d₂ = dim(C)` is that inequality by transitivity, and is recorded in that
shape as `exists_mem_maximalIdeal_notMem_minimalPrimes_map`.

## References

* [Stacks Project, Tag 0461](https://stacks.math.columbia.edu/tag/0461)
* [Stacks Project, Tag 00NA](https://stacks.math.columbia.edu/tag/00NA)
* [Stacks Project, Tag 00DS](https://stacks.math.columbia.edu/tag/00DS)
-/

@[expose] public section

namespace Stacks.CohenMacaulay.ParameterChoice

/-- **A Cohen-Macaulay local ring is equidimensional.** If `C` is a Noetherian local
Cohen-Macaulay ring and `q` is a minimal prime of `C`, then `dim(C/q) = dim(C)`. This is the
dimension formula of Stacks 00NA read at a prime of height zero. -/
theorem ringKrullDim_quotient_eq_of_mem_minimalPrimes {C : Type*} [CommRing C]
    [IsNoetherianRing C] [IsLocalRing C] (hC : Module.IsMaximalCohenMacaulay C C) {q : Ideal C}
    (hq : q ∈ minimalPrimes C) : ringKrullDim (C ⧸ q) = ringKrullDim C := by
  have : q.IsPrime := Ideal.IsMinimalPrime.isPrime hq
  have h := hC.ringKrullDim_eq_height_add_ringKrullDim_quotient q
  rw [Ideal.height_eq_zero_iff.mpr hq] at h
  simpa using h.symm

/-- **The extension of `I` lies in no minimal prime.** With `C` a Noetherian local
Cohen-Macaulay ring and `t : A →+* C` a ring map whose extension of `I` cuts the dimension of
`C` down strictly, no minimal prime `q` of `C` contains `t(I)C`: if one did, then `C/t(I)C` would
surject onto `C/q`, whose dimension is all of `dim(C)` by equidimensionality. -/
theorem not_map_le_of_mem_minimalPrimes {A C : Type*} [CommRing A] [CommRing C]
    [IsNoetherianRing C] [IsLocalRing C] (hC : Module.IsMaximalCohenMacaulay C C) {t : A →+* C}
    {I : Ideal A} (hdim : ringKrullDim (C ⧸ Ideal.map t I) < ringKrullDim C) {q : Ideal C}
    (hq : q ∈ minimalPrimes C) : ¬ Ideal.map t I ≤ q := by
  intro hle
  have hsurj : ringKrullDim (C ⧸ q) ≤ ringKrullDim (C ⧸ Ideal.map t I) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.factor hle)
      (Ideal.Quotient.factor_surjective hle)
  rw [ringKrullDim_quotient_eq_of_mem_minimalPrimes hC hq] at hsurj
  exact absurd hdim (not_lt.mpr hsurj)

/-- **Choosing a parameter avoiding the minimal primes.** Let `C` be a Noetherian local
Cohen-Macaulay ring, let `t : A →+* C` be a ring map and let `I` be an ideal of `A` with
`dim(C/t(I)C) < dim(C)`. Then there is an `f ∈ I` whose image `t(f)` lies outside every minimal
prime of `C`. -/
theorem exists_mem_notMem_minimalPrimes_map {A C : Type*} [CommRing A] [CommRing C]
    [IsNoetherianRing C] [IsLocalRing C] (hC : Module.IsMaximalCohenMacaulay C C) (t : A →+* C)
    (I : Ideal A) (hdim : ringKrullDim (C ⧸ Ideal.map t I) < ringKrullDim C) :
    ∃ f ∈ I, ∀ q ∈ minimalPrimes C, t f ∉ q := by
  have hcover : ¬ ((I : Set A) ⊆ ⋃ q ∈ minimalPrimes C, (Ideal.comap t q : Set A)) := by
    intro hsub
    obtain ⟨q, hq, hle⟩ := (Ideal.subset_union_prime_finite
      (minimalPrimes.finite_of_isNoetherianRing C) (a := (⊥ : Ideal C)) (b := ⊥)
      (f := Ideal.comap t) (fun q hq _ _ => by
        have := Ideal.IsMinimalPrime.isPrime hq
        exact Ideal.comap_isPrime t q)).mp hsub
    exact not_map_le_of_mem_minimalPrimes hC hdim hq (Ideal.map_le_iff_le_comap.mpr hle)
  obtain ⟨f, hfI, hf⟩ := Set.not_subset.mp hcover
  exact ⟨f, hfI, by simpa [Ideal.mem_comap] using hf⟩

/-- **The source's form of the choice.** Let `C` be a Noetherian local Cohen-Macaulay ring of
dimension `d₂`, let `t : A →+* C` be a ring map out of a local ring `A` with maximal ideal `𝔪`,
and suppose `dim(C/t(𝔪)C) ≤ d₁` with `d₁ < d₂`. Then there is an `f ∈ 𝔪` whose image `t(f)` lies
outside every minimal prime of `C`. -/
theorem exists_mem_maximalIdeal_notMem_minimalPrimes_map {A C : Type*} [CommRing A] [CommRing C]
    [IsLocalRing A] [IsNoetherianRing C] [IsLocalRing C]
    (hC : Module.IsMaximalCohenMacaulay C C) (t : A →+* C) {d₁ d₂ : ℕ}
    (hd₁ : ringKrullDim (C ⧸ Ideal.map t (IsLocalRing.maximalIdeal A)) ≤ (d₁ : WithBot ℕ∞))
    (hd₂ : ringKrullDim C = (d₂ : WithBot ℕ∞)) (hlt : d₁ < d₂) :
    ∃ f ∈ IsLocalRing.maximalIdeal A, ∀ q ∈ minimalPrimes C, t f ∉ q :=
  exists_mem_notMem_minimalPrimes_map hC t _
    (hd₁.trans_lt (by rw [hd₂]; exact_mod_cast hlt))

/-- **The chosen parameter is a nonzerodivisor.** In the situation of
`exists_mem_notMem_minimalPrimes_map` the element `f ∈ I` can be chosen so that `t(f)` is a
nonzerodivisor on `C`, which is the form in which Stacks 0461 uses it. A Cohen-Macaulay local
ring has no embedded associated primes (Stacks 02M5), so its zerodivisors are exactly the
elements of its minimal primes and avoiding those is enough. -/
theorem exists_mem_isSMulRegular_map {A C : Type*} [CommRing A] [CommRing C]
    [IsNoetherianRing C] [IsLocalRing C] (hC : Module.IsMaximalCohenMacaulay C C) (t : A →+* C)
    (I : Ideal A) (hdim : ringKrullDim (C ⧸ Ideal.map t I) < ringKrullDim C) :
    ∃ f ∈ I, IsSMulRegular C (t f) := by
  have hC' : (Module.depth C (IsLocalRing.maximalIdeal C) C : WithBot ℕ∞) = ringKrullDim C := hC
  have hne : IsLocalRing.maximalIdeal C • (⊤ : Submodule C C) ≠ ⊤ := by
    simpa using (IsLocalRing.maximalIdeal.isMaximal C).ne_top
  have hdepth : depthM C C = Module.depth C (IsLocalRing.maximalIdeal C) C := by
    rw [Module.depth, ite_eq_right_of_eq_false _ _ (eq_false hne)]
    rfl
  have hCM : IsCM C C := by
    unfold IsCM
    rw [hdepth, hC', Module.supportDim_self_eq_ringKrullDim]
  have hann : Module.annihilator C C = ⊥ :=
    Module.annihilator_eq_bot.mpr (inferInstance : FaithfulSMul C C)
  obtain ⟨f, hfI, hf⟩ := exists_mem_notMem_minimalPrimes_map hC t I hdim
  refine ⟨f, hfI, isSMulRegular_of_avoiding fun p hp => hf p ?_⟩
  have h := ((CM_ass_minimal_support C C hCM).1 p hp).2
  rwa [hann] at h

end Stacks.CohenMacaulay.ParameterChoice

end


