module

public import StacksFrontier.AlgebraicGeometry.Intersection.AlgebraicMultiplicities.ComputingPolynomial
public import Mathlib.RingTheory.KrullDimension.Module
public import StacksFrontier.RingTheory.HilbertSamuel.Dimension
public import StacksFrontier.RingTheory.HilbertSamuel.DegreeInvariance
public import StacksFrontier.RingTheory.HilbertSamuel.ShortExact
public import StacksFrontier.RingTheory.Length.Defs

/-!
# Additivity of Hilbert–Samuel multiplicity

Hilbert–Samuel multiplicity in any degree at least the dimension of the support is additive
along short exact sequences of finite modules over a Noetherian local ring. The two cases of
the argument are separated by whether the submodule has finite length: if it does, the three
computing polynomials satisfy `P = P' + P''` exactly; if not, the error term has degree below
the degree of the polynomial of the submodule, which the dimension bound keeps below `d`.

## Main results

* `Ideal.hilbertSamuelMultiplicity_additive_of_exact` proves additivity of multiplicity along
  a short exact sequence.

## Implementation notes

The condition that `d` is at least the dimension of the support is expressed in `WithBot ℕ∞`,
the codomain of `Module.supportDim`. A short exact sequence is represented by linear maps
together with injectivity, exactness, and surjectivity.

## References

* [Stacks Project, Tag 0AZW](https://stacks.math.columbia.edu/tag/0AZW)
-/

@[expose] public section

open Filter IsLocalRing Polynomial

namespace Ideal

/-- The degree of a polynomial computing the Hilbert–Samuel function of `N`, read in `ℕ∞`, is
the dimension of the support of `N`: the degree does not depend on the ideal of definition,
so it may be compared with the one for the maximal ideal. -/
private lemma degree_map_eq_supportDim
    {R N : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup N] [Module R N] [Module.Finite R N]
    {I : Ideal R} (hI : I.radical = maximalIdeal R) {P : ℚ[X]}
    (hP : ComputesHilbertSamuelPoly I N P) :
    P.degree.map (Nat.cast : ℕ → ℕ∞) = Module.supportDim R N := by
  obtain ⟨Q, hQ⟩ := exists_computesHilbertSamuelPoly (maximalIdeal R)
    ((maximalIdeal.isMaximal R).isPrime.radical) N
  obtain ⟨_de, e, he⟩ :=
    Ideal.exists_degree_eq_of_eventually_eval_eq_length_quotient_smul_pow (R := R) N
  have hPI : P.degree = e := (he I hI P).2 hP
  have hQm : Q.degree = e := (he (maximalIdeal R)
    ((maximalIdeal.isMaximal R).isPrime.radical) Q).2 hQ
  rw [hPI, ← hQm, ← hilbertSamuelDegree_eq_degree_of_computes hQ]
  exact Module.hilbertSamuelDegree_eq_supportDim R N

/-- Powers of an ideal of definition eventually annihilate a module of finite length: the
descending chain of submodules `I ^ n N` stabilizes and its intersection is zero. -/
private lemma exists_pow_smul_top_eq_bot_of_isFiniteLength
    {R N : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup N] [Module R N] [Module.Finite R N]
    (I : Ideal R) (hI : I.radical = maximalIdeal R) (hN : IsFiniteLength R N) :
    ∃ n : ℕ, I ^ n • (⊤ : Submodule R N) = ⊥ := by
  have : IsArtinian R N := (isFiniteLength_iff_isNoetherian_isArtinian.mp hN).2
  let F : ℕ →o (Submodule R N)ᵒᵈ :=
    { toFun := fun n => OrderDual.toDual (I ^ n • (⊤ : Submodule R N))
      monotone' := fun _ _ hab =>
        Submodule.smul_mono_left (Ideal.pow_le_pow_right hab) }
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes F
  refine ⟨n, ?_⟩
  have hIne : I ≠ ⊤ := by
    intro h
    rw [h, Ideal.radical_top] at hI
    exact (maximalIdeal.isMaximal R).ne_top hI.symm
  have hle : I ^ n • (⊤ : Submodule R N) ≤ ⨅ k : ℕ, I ^ k • (⊤ : Submodule R N) := by
    refine le_iInf fun k => ?_
    by_cases hnk : n ≤ k
    · exact (congrArg OrderDual.ofDual (hn k hnk)).le
    · exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (le_of_not_ge hnk))
  exact le_bot_iff.mp (hle.trans (Ideal.iInf_pow_smul_eq_bot_of_isLocalRing I hIne).le)

/-- If `I ^ k` annihilates `N`, then every quotient `N ⧸ I ^ m • ⊤` with `k ≤ m` has the length
of `N`. -/
private lemma length_quotient_pow_smul_top_eq
    {R N : Type*} [CommRing R] [AddCommGroup N] [Module R N]
    {I : Ideal R} {k m : ℕ} (hk : I ^ k • (⊤ : Submodule R N) = ⊥) (hkm : k ≤ m) :
    Module.length R (N ⧸ I ^ m • (⊤ : Submodule R N)) = Module.length R N := by
  have hm : I ^ m • (⊤ : Submodule R N) = ⊥ :=
    le_bot_iff.mp ((Submodule.smul_mono_left (Ideal.pow_le_pow_right hkm)).trans hk.le)
  rw [hm]
  exact (Submodule.quotEquivOfEqBot (⊥ : Submodule R N) rfl).length_eq

/-- The polynomial computing the Hilbert–Samuel function of a module of finite length is the
constant equal to that length. -/
private lemma computes_eq_C_length_of_isFiniteLength
    {R N : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup N] [Module R N] [Module.Finite R N]
    {I : Ideal R} (hI : I.radical = maximalIdeal R) {P : ℚ[X]}
    (hP : ComputesHilbertSamuelPoly I N P) (hN : IsFiniteLength R N) :
    P = C ((Module.length R N).toNat : ℚ) := by
  obtain ⟨k, hk⟩ := exists_pow_smul_top_eq_bot_of_isFiniteLength I hI hN
  apply Polynomial.eq_of_eventually_eval_natCast_eq
  filter_upwards [hP, eventually_ge_atTop k] with n hn hkn
  obtain ⟨q, hq, heval⟩ := hn
  rw [length_quotient_pow_smul_top_eq hk (by omega)] at hq
  have hq' : q = (Module.length R N).toNat := by
    exact_mod_cast hq.symm.trans (ENat.natCast_toNat (Module.length_ne_top_iff.mpr hN)).symm
  simp [heval, hq']

/-- When the submodule of a short exact sequence has finite length, the computing polynomial
of the middle term is exactly the sum of the other two: the additivity of the characteristic
functions has no error term, because the shifted contribution is constant. -/
private lemma computes_add_of_exact_of_isFiniteLength
    {R M' M M'' : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup M'] [Module R M'] [Module.Finite R M']
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup M''] [Module R M''] [Module.Finite R M'']
    {I : Ideal R} (hI : I.radical = maximalIdeal R)
    {P' P P'' : ℚ[X]} (hP' : ComputesHilbertSamuelPoly I M' P')
    (hP : ComputesHilbertSamuelPoly I M P) (hP'' : ComputesHilbertSamuelPoly I M'' P'')
    {f : M' →ₗ[R] M} {g : M →ₗ[R] M''}
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g)
    (hfin : IsFiniteLength R M') : P = P' + P'' := by
  obtain ⟨N, c, l, hl, hchar, -⟩ :=
    additivity_of_characteristic_and_hilbert_functions R I hI M' M M'' f g hf hg hfg
  have hN : IsFiniteLength R N := hfin.of_injective N.injective_subtype
  obtain ⟨k, hk⟩ := exists_pow_smul_top_eq_bot_of_isFiniteLength I hI hN
  have hPC := computes_eq_C_length_of_isFiniteLength hI hP' hfin
  have hadd := Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype
    N.mkQ_surjective (LinearMap.exact_subtype_mkQ N)
  have hnat : (Module.length R M').toNat = (Module.length R N).toNat + l := by
    rw [hl] at hadd
    rw [hadd, ENat.toNat_add (Module.length_ne_top_iff.mpr hN) (by simp)]
    simp
  rw [hPC]
  apply Polynomial.eq_of_eventually_eval_natCast_eq
  filter_upwards [hP, hP'', eventually_ge_atTop (c + k)] with n hn hn'' hnck
  obtain ⟨p, hp, hp'⟩ := hn
  obtain ⟨p'', hp'', hp'''⟩ := hn''
  have hc := hchar n (by omega)
  simp only [charFn] at hc
  rw [hp, hp''] at hc
  rw [length_quotient_pow_smul_top_eq hk (by omega : k ≤ n - c + 1)] at hc
  rw [hp', eval_add, eval_C, hp''', hnat]
  rw [← ENat.natCast_toNat (Module.length_ne_top_iff.mpr hN)] at hc
  have hcNat : p = p'' + (Module.length R N).toNat + l := by exact_mod_cast hc
  exact_mod_cast (by omega : p = (Module.length R N).toNat + l + p'')

/-- Hilbert–Samuel multiplicity in degree `d` is additive in a short exact sequence of
finite modules, provided `d` is at least the dimension of the support of the middle term. -/
@[stacks 0AZW]
theorem hilbertSamuelMultiplicity_additive_of_exact
    {R M' M M'' : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup M'] [Module R M'] [Module.Finite R M']
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup M''] [Module R M''] [Module.Finite R M'']
    (I : Ideal R) (hI : IsIdealOfDefinition I) (d : ℕ)
    {f : M' →ₗ[R] M} {g : M →ₗ[R] M''}
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g)
    (hd : Module.supportDim R M ≤ (d : WithBot ℕ∞)) :
    I.hilbertSamuelMultiplicity M d =
      I.hilbertSamuelMultiplicity M' d + I.hilbertSamuelMultiplicity M'' d := by
  obtain ⟨P', hP'⟩ := exists_computesHilbertSamuelPoly I hI M'
  obtain ⟨P, hP⟩ := exists_computesHilbertSamuelPoly I hI M
  obtain ⟨P'', hP''⟩ := exists_computesHilbertSamuelPoly I hI M''
  have hcoeff : P.coeff d = P'.coeff d + P''.coeff d := by
    by_cases hfin : IsFiniteLength R M'
    · rw [computes_add_of_exact_of_isFiniteLength hI hP' hP hP'' hf hfg hg hfin, coeff_add]
    · have herr := ((Ideal.max_degree_eq_degree_of_exact I hI hfg hf hg).1
          P' P P'' hP' hP hP'').1 hfin
      have hdegMap : P'.degree.map (Nat.cast : ℕ → ℕ∞) ≤ (d : WithBot ℕ∞) := by
        rw [degree_map_eq_supportDim hI hP']
        exact (Module.supportDim_le_of_injective f hf).trans hd
      have hdeg : P'.degree ≤ (d : WithBot ℕ) := by
        change P'.degree.map (Nat.cast : ℕ → ℕ∞) ≤
          ((d : WithBot ℕ).map (Nat.cast : ℕ → ℕ∞)) at hdegMap
        exact (WithBot.map_le_iff _ (fun {_ _} => Nat.cast_le)).mp hdegMap
      have hz := Polynomial.coeff_eq_zero_of_degree_lt (herr.trans_le hdeg)
      simp only [coeff_sub] at hz
      linarith
  rw [hilbertSamuelMultiplicity_eq_factorial_mul_coeff I M hP d,
    hilbertSamuelMultiplicity_eq_factorial_mul_coeff I M' hP' d,
    hilbertSamuelMultiplicity_eq_factorial_mul_coeff I M'' hP'' d, hcoeff]
  ring

end Ideal
