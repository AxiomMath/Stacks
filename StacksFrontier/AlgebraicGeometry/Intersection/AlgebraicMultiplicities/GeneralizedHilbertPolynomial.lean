module

public import StacksFrontier.AlgebraicGeometry.Intersection.ComputingIntersectionMultiplicities.HilbertPolynomialMultiplicity
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The generalized Hilbert polynomial and the asymptotics of `χ_{I, M}`

Let `M` be a finite module over a Noetherian local ring and let `I` be an ideal with
`M / IM` of finite length, so that `I` need not be an ideal of definition. The generalized
Hilbert function `χ_{I, M}(n) = length(M / I ^ n M)` is then eventually given by a rational
polynomial of degree at most any `d ≥ dim(Supp(M))`, and

  `χ_{I, M}(n) = e_I(M, d) * n ^ d / d ! + (lower order terms)`,

exactly as for an ideal of definition. This is the last clause of Tag 0B00.

## Main results

* `Ideal.exists_computesGeneralizedHilbertPoly_degree_le`: the eventual polynomiality of
  `χ_{I, M}`, with a polynomial of degree at most `d`.
* `Ideal.exists_degree_lt_generalizedHilbertFunction_eq`: the asymptotic expansion of
  `χ_{I, M}` with leading term `e_I(M, d) * n ^ d / d !`.

## Implementation notes

"Lower order terms" is read as a rational polynomial of degree `< d`, which is what the
difference of the computing polynomial and its degree-`d` part is; together with the eventual
equality of `χ_{I, M}` and the computing polynomial this is the displayed asymptotic. The
finite-length hypothesis is the fifth of the equivalent conditions of
`Ideal.idealOfDefinition_support_length_tfae`; the degenerate case `M = IM`, in which the
hypothesis holds and `χ_{I, M}` vanishes identically, is covered by the zero polynomial.

The transport from the ideal-of-definition case is the one already carried out in
`Ideal.exists_computesGeneralizedHilbertPoly`, which lives downstream in the file on
intersection multiplicities computed from a Hilbert polynomial; what is added here is the
degree bound in the form the source states it and the asymptotic expansion.

## References

* [Stacks Project, Tag 0B00](https://stacks.math.columbia.edu/tag/0B00)
-/

@[expose] public section

universe u

open Filter Polynomial

namespace Ideal

/-- If `IM = M` then `I ^ n M = M` for every `n`. -/
private lemma pow_smul_top_eq_top_of_smul_top_eq_top
    {A M : Type*} [CommSemiring A] [AddCommMonoid M] [Module A M] {I : Ideal A}
    (h : I • (⊤ : Submodule A M) = ⊤) (n : ℕ) :
    I ^ n • (⊤ : Submodule A M) = ⊤ := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, Submodule.mul_smul, h, ih]

/-- If `IM = M` then the generalized Hilbert function of `M` for `I` vanishes identically, so
the zero polynomial computes it. -/
private lemma computesGeneralizedHilbertPoly_zero_of_smul_top_eq_top
    {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M] {I : Ideal A}
    (h : I • (⊤ : Submodule A M) = ⊤) : I.ComputesGeneralizedHilbertPoly M 0 :=
  Filter.Eventually.of_forall fun n => by
    have : Subsingleton (M ⧸ (I ^ n • (⊤ : Submodule A M))) :=
      Submodule.Quotient.subsingleton_iff.mpr (pow_smul_top_eq_top_of_smul_top_eq_top h n)
    have hlen : Module.length A (M ⧸ (I ^ n • (⊤ : Submodule A M))) = ((0 : ℕ) : ℕ∞) := by
      simp
    exact ⟨0, hlen, by simp⟩

/-- **Stacks Project, Tag 0B00, eventual polynomiality.** Let `M` be a finite module over a
Noetherian local ring and let `I` be an ideal with `M / IM` of finite length. For every
`d ≥ dim(Supp(M))` there is a rational polynomial of degree at most `d` which computes
`χ_{I, M}(n) = length(M / I ^ n M)` for all large `n`. -/
@[stacks 0B00 "eventual_polynomiality", ega "0 16.2.1" "partial"]
theorem exists_computesGeneralizedHilbertPoly_degree_le
    {A M : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M] (I : Ideal A)
    (hI : Module.length A (M ⧸ I • (⊤ : Submodule A M)) < ⊤)
    {d : ℕ} (hd : Module.supportDim A M ≤ (d : WithBot ℕ∞)) :
    ∃ P : ℚ[X], I.ComputesGeneralizedHilbertPoly M P ∧ P.degree ≤ (d : WithBot ℕ) := by
  rcases subsingleton_or_nontrivial (M ⧸ I • (⊤ : Submodule A M)) with hs | hn
  · exact ⟨0, computesGeneralizedHilbertPoly_zero_of_smul_top_eq_top
      (Submodule.Quotient.subsingleton_iff.mp hs), by simp⟩
  · have hle : Module.supportDim A (M ⧸ I • (⊤ : Submodule A M)) ≤ 0 :=
      ((Ideal.idealOfDefinition_support_length_tfae I hn).out 5 4).mp hI
    have hge : (0 : WithBot ℕ∞) ≤ Module.supportDim A (M ⧸ I • (⊤ : Submodule A M)) := by
      have : Nonempty (Module.support A (M ⧸ I • (⊤ : Submodule A M))) :=
        Module.nonempty_support_of_nontrivial.to_subtype
      unfold Module.supportDim
      exact Order.krullDim_nonneg
    have h0 : Module.supportDim A (M ⧸ I • (⊤ : Submodule A M)) = 0 := le_antisymm hle hge
    obtain ⟨P, hP⟩ := Ideal.exists_computesGeneralizedHilbertPoly I h0
    refine ⟨P, hP, ?_⟩
    have hmap : P.degree.map (Nat.cast : ℕ → ℕ∞) ≤
        ((d : WithBot ℕ).map (Nat.cast : ℕ → ℕ∞)) := by
      rw [Ideal.degree_eq_supportDim_of_computesGeneralizedHilbertPoly I h0 hP]
      simpa using hd
    exact (WithBot.map_le_iff _ (fun {_ _} => Nat.cast_le)).mp hmap

/-- **Stacks Project, Tag 0B00, asymptotics of the generalized Hilbert function.** Let `M` be
a finite module over a Noetherian local ring and let `I` be an ideal with `M / IM` of finite
length. For every `d ≥ dim(Supp(M))` there are lower order terms, a rational polynomial of
degree `< d`, such that for all large `n` the length `χ_{I, M}(n) = length(M / I ^ n M)` is
finite and equals `e_I(M, d) * n ^ d / d !` plus those terms. -/
@[stacks 0B00 "asymptotics"]
theorem exists_degree_lt_generalizedHilbertFunction_eq
    {A M : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M] (I : Ideal A)
    (hI : Module.length A (M ⧸ I • (⊤ : Submodule A M)) < ⊤)
    {d : ℕ} (hd : Module.supportDim A M ≤ (d : WithBot ℕ∞)) :
    ∃ Q : ℚ[X], Q.degree < (d : WithBot ℕ) ∧
      ∀ᶠ n : ℕ in atTop, ∃ p : ℕ,
        I.generalizedHilbertFunction M n = (p : ℕ∞) ∧
          (p : ℚ) = I.generalizedHilbertSamuelMultiplicity M d * (n : ℚ) ^ d
            / (d.factorial : ℚ) + Q.eval (n : ℚ) := by
  obtain ⟨P, hP, hdeg⟩ := exists_computesGeneralizedHilbertPoly_degree_le I hI hd
  refine ⟨P - C (P.coeff d) * X ^ d, ?_, ?_⟩
  · refine (Polynomial.degree_lt_iff_coeff_zero _ _).mpr fun m hm => ?_
    have hdm : d ≤ m := by exact_mod_cast hm
    rcases eq_or_lt_of_le hdm with rfl | hlt
    · simp
    · have hzero : P.coeff m = 0 :=
        Polynomial.coeff_eq_zero_of_degree_lt (hdeg.trans_lt (by exact_mod_cast hlt))
      simp [hzero, (Nat.ne_of_lt hlt).symm]
  · filter_upwards [hP] with n hn
    obtain ⟨p, hp1, hp2⟩ := hn
    refine ⟨p, by rw [Ideal.generalizedHilbertFunction]; exact hp1, ?_⟩
    have hfac : (d.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr d.factorial_ne_zero
    rw [Ideal.generalizedHilbertSamuelMultiplicity_eq_factorial_mul_coeff I M hP d, ← hp2]
    simp only [eval_sub, eval_mul, eval_C, eval_pow, eval_X]
    field_simp
    ring

end Ideal
