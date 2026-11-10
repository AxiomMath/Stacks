module

public import StacksFrontier.NumberTheory.DifferentAnnihilatorConductor

/-!
# The different of an extension of number rings is the annihilator of the differentials

Let `L/K` be an extension of number fields. Then

  `differentIdeal 𝒪_K 𝒪_L = Module.annihilator 𝒪_L Ω[𝒪_L⁄𝒪_K]`,

the assertion of Tag 024Z, with no monogenicity hypothesis and no hypothesis on `K`.

## Main results

* `NumberField.exists_not_conductor_le`: every maximal ideal `P` of `𝒪_L` is coprime to the
  conductor of `𝒪_K[x]` for some `x : 𝒪_L`.
* `NumberField.differentIdeal_eq_annihilator_kaehlerDifferential_general`: the different is the
  annihilator of `Ω[𝒪_L⁄𝒪_K]`.

## Implementation notes

The extension `𝒪_L/𝒪_K` need not be monogenic, nor need it become monogenic after localising the
base at a prime, so the identity is proved one maximal ideal `P` of `𝒪_L` at a time: there the
conductor of a suitable `𝒪_K[x]` is coprime to `P`, which is enough by
`NumberField.differentIdeal_eq_annihilator_of_forall_exists_conductor_not_le`.

The generator `x` is Serre's, *Local Fields* III §6 Proposition 12, chosen globally by the Chinese
remainder theorem rather than in a completion. Writing `p = P ∩ 𝒪_K` and `𝔭𝒪_L = P ^ n 𝔮` with
`𝔮` coprime to `P`, take `β` a nonzero primitive element of the residue extension
`(𝒪_L/P) / (𝒪_K/p)` and `g` a monic lift of its minimal polynomial; a lift `b` of `β`, adjusted by
a uniformizer if necessary, has `g(b) ∈ P \ P²`, and `x ≡ b` modulo `P²` with `x ∈ 𝔮` keeps that
while putting `x` in every other prime above `p`. The three hypotheses of
`NumberField.not_conductor_le_of_residue_surjective` are then satisfied: `𝒪_K[x]` surjects onto
`𝒪_L/P` because the residue of `x` is `β`; it contains `g(x) ∈ P \ P²`; and every other nonzero
prime of `𝒪_L` contains either `x` (if it lies over `p`, since it then divides `𝔮`) or an element
of `p' \ p` for `p'` the prime of `𝒪_K` below it.

## References

* [Stacks Project, Tag 024Z](https://stacks.math.columbia.edu/tag/024Z)
-/

@[expose] public section

open NumberField Polynomial

universe u

noncomputable section

/-- A prime of a Dedekind domain is not contained in its own square. -/
theorem Ideal.exists_mem_notMem_sq {B : Type*} [CommRing B] [IsDedekindDomain B] (P : Ideal B)
    [hP : P.IsPrime] (hPbot : P ≠ ⊥) : ∃ π ∈ P, π ∉ P ^ 2 := by
  have hPprime : Prime P := Ideal.prime_of_isPrime hPbot hP
  have hsq : P ^ 2 ≠ P := by
    intro h
    have hmul : P * P = P * 1 := by rw [← sq, h, mul_one]
    exact hPprime.not_isUnit ((mul_left_cancel₀ hPbot hmul) ▸ isUnit_one)
  by_contra hcon
  push Not at hcon
  exact hsq (le_antisymm (Ideal.pow_le_self two_ne_zero) hcon)

/-- Multiplying an element of a maximal ideal `P` outside `P²` by a unit modulo `P` keeps it
outside `P²`. -/
theorem Ideal.mul_notMem_sq {B : Type*} [CommRing B] {P : Ideal B} [hP : P.IsMaximal] {a c : B}
    (ha : a ∉ P) (hc : c ∉ P ^ 2) (hcP : c ∈ P) : a * c ∉ P ^ 2 := by
  intro hmem
  obtain ⟨y, e, he, hye⟩ := hP.exists_inv ha
  refine hc ?_
  have hrw : c = y * (a * c) + e * c := by
    rw [← one_mul c]
    nth_rewrite 1 [← hye]
    ring
  rw [hrw]
  refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ hmem) ?_
  rw [sq]
  exact Ideal.mul_mem_mul he hcP

/-- If a positive power of `I` is contained in a prime, so is `I`. -/
theorem Ideal.le_of_pow_succ_le_prime {B : Type*} [CommSemiring B] {I J : Ideal B}
    [hJ : J.IsPrime] (n : ℕ) (h : I ^ (n + 1) ≤ J) : I ≤ J := by
  induction n with
  | zero => simpa using h
  | succ m ih =>
    rw [pow_succ] at h
    rcases (hJ.mul_le).mp h with h' | h'
    · exact ih h'
    · exact h'

namespace NumberField

attribute [local instance] FractionRing.liftAlgebra

variable (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

/-- **Every prime of `𝒪_L` has a monogenic subring agreeing with `𝒪_L` there.** For each maximal
ideal `P` of `𝒪_L` there is an `x : 𝒪_L` whose conductor is not contained in `P`. -/
theorem exists_not_conductor_le (P : Ideal (𝓞 L)) [hPmax : P.IsMaximal] :
    ∃ x : 𝓞 L, ¬ conductor (𝓞 K) x ≤ P := by
  classical
  have hPprime : P.IsPrime := hPmax.isPrime
  have hPbot : P ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField hPmax (RingOfIntegers.not_isField L)
  set p : Ideal (𝓞 K) := P.comap (algebraMap (𝓞 K) (𝓞 L)) with hpdef
  have : p.IsPrime := Ideal.IsPrime.comap (algebraMap (𝓞 K) (𝓞 L))
  have hpbot : p ≠ ⊥ := Ideal.under_ne_bot _ hPbot
  have hpmax : p.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hpbot
  have : Finite ((𝓞 K) ⧸ p) := Ring.HasFiniteQuotients.finiteQuotient hpbot
  have : Finite ((𝓞 L) ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hPbot
  let : Field ((𝓞 K) ⧸ p) := Ideal.Quotient.field p
  let : Field ((𝓞 L) ⧸ P) := Ideal.Quotient.field P
  let : Algebra ((𝓞 K) ⧸ p) ((𝓞 L) ⧸ P) :=
    Ideal.Quotient.algebraQuotientOfLEComap (le_of_eq hpdef)
  have hcomp : (algebraMap ((𝓞 K) ⧸ p) ((𝓞 L) ⧸ P)).comp (Ideal.Quotient.mk p)
      = (Ideal.Quotient.mk P).comp (algebraMap (𝓞 K) (𝓞 L)) := by
    ext a
    simp
  -- a nonzero primitive element of the residue field extension
  obtain ⟨β, hβ0, hβgen⟩ : ∃ β : (𝓞 L) ⧸ P, β ≠ 0 ∧
      Algebra.adjoin ((𝓞 K) ⧸ p) ({β} : Set ((𝓞 L) ⧸ P)) = ⊤ := by
    obtain ⟨β₀, hβ₀⟩ := Field.exists_primitive_element ((𝓞 K) ⧸ p) ((𝓞 L) ⧸ P)
    have hβ₀' : Algebra.adjoin ((𝓞 K) ⧸ p) ({β₀} : Set ((𝓞 L) ⧸ P)) = ⊤ := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
        (IsAlgebraic.of_finite _ _), hβ₀, IntermediateField.top_toSubalgebra]
    rcases eq_or_ne β₀ 0 with rfl | hne
    · refine ⟨1, one_ne_zero, le_antisymm le_top ?_⟩
      rw [← hβ₀']
      exact Algebra.adjoin_le (Set.singleton_subset_iff.mpr (Subalgebra.zero_mem _))
    · exact ⟨β₀, hne, hβ₀'⟩
  obtain ⟨b₀, hb₀⟩ := Ideal.Quotient.mk_surjective (I := P) β
  -- a monic lift of the minimal polynomial of `β`
  obtain ⟨g, hgmap, -, -⟩ := Polynomial.lifts_and_degree_eq_and_monic
    (Polynomial.mem_lifts_of_surjective (f := Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
      (minpoly ((𝓞 K) ⧸ p) β))
    (minpoly.monic (Algebra.IsIntegral.isIntegral (R := (𝓞 K) ⧸ p) β))
  have hgval : ∀ c : 𝓞 L, Ideal.Quotient.mk P (aeval c g)
      = aeval (Ideal.Quotient.mk P c) (minpoly ((𝓞 K) ⧸ p) β) := by
    intro c
    rw [map_aeval_eq_aeval_map hcomp, hgmap]
  have hgderiv : aeval b₀ (derivative g) ∉ P := by
    intro hmem
    have h0 : (Ideal.Quotient.mk P) (aeval b₀ (derivative g)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    rw [map_aeval_eq_aeval_map hcomp, hb₀, ← derivative_map, hgmap] at h0
    exact (Algebra.IsSeparable.isSeparable _ β).aeval_derivative_ne_zero (minpoly.aeval _ _) h0
  obtain ⟨π, hπP, hπ2⟩ := Ideal.exists_mem_notMem_sq P hPbot
  -- a lift of `β` at which `g` has valuation exactly one
  set b : 𝓞 L := if aeval b₀ g ∈ P ^ 2 then b₀ + π else b₀ with hbdef
  have hbres : Ideal.Quotient.mk P b = β := by
    rw [hbdef]
    split_ifs with h
    · rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hπP, add_zero, hb₀]
    · exact hb₀
  have hgb : aeval b g ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, hgval, hbres]
    exact minpoly.aeval _ _
  have hgb2 : aeval b g ∉ P ^ 2 := by
    rw [hbdef]
    split_ifs with h
    · intro hmem
      obtain ⟨k, hk⟩ := (g.map (algebraMap (𝓞 K) (𝓞 L))).binomExpansion b₀ π
      simp only [derivative_map, eval_map_algebraMap] at hk
      have hkey : aeval b₀ (derivative g) * π ∈ P ^ 2 := by
        have hrw : aeval b₀ (derivative g) * π
            = aeval (b₀ + π) g - aeval b₀ g - k * π ^ 2 := by rw [hk]; ring
        rw [hrw]
        exact Ideal.sub_mem _ (Ideal.sub_mem _ hmem h)
          (Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hπP 2))
      exact Ideal.mul_notMem_sq hgderiv hπ2 hπP hkey
    · exact h
  -- the `P`-free part of `p 𝒪_L`
  have hIbot : p.map (algebraMap (𝓞 K) (𝓞 L)) ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective
      (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L))).not.mpr hpbot
  obtain ⟨Q, hPQ, hIQ⟩ := Ideal.eq_prime_pow_mul_coprime hIbot P
  obtain ⟨n, hn⟩ : ∃ n : ℕ, p.map (algebraMap (𝓞 K) (𝓞 L)) = P ^ n * Q := ⟨_, hIQ⟩
  have hP2Q : P ^ 2 ⊔ Q = ⊤ :=
    Ideal.isCoprime_iff_sup_eq.mp (Ideal.isCoprime_iff_sup_eq.mpr hPQ).pow_left
  obtain ⟨i, hi, j, hj, hij⟩ :=
    Submodule.mem_sup.mp (hP2Q ▸ Submodule.mem_top (x := (1 : 𝓞 L)))
  -- the generator
  set x : 𝓞 L := b * j with hxdef
  have hj1 : j = 1 - i := by rw [← hij]; ring
  have hxb : x - b ∈ P ^ 2 := by
    have hrw : x - b = b * i * (-1) := by
      rw [hxdef, hj1]
      ring
    rw [hrw]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hi)
  have hxQ : x ∈ Q := Ideal.mul_mem_left _ _ hj
  have hxres : Ideal.Quotient.mk P x = β := by
    have := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_le_self two_ne_zero hxb)
    rw [map_sub, sub_eq_zero] at this
    rw [this, hbres]
  have hxP : x ∉ P := by
    intro hmem
    exact hβ0 (hxres ▸ Ideal.Quotient.eq_zero_iff_mem.mpr hmem)
  -- the three hypotheses
  have h1 : ∀ c : 𝓞 L, ∃ r ∈ Algebra.adjoin (𝓞 K) ({x} : Set (𝓞 L)), c - r ∈ P := by
    intro c
    have hmem : Ideal.Quotient.mk P c ∈
        Algebra.adjoin ((𝓞 K) ⧸ p) ({β} : Set ((𝓞 L) ⧸ P)) := by
      rw [hβgen]; exact Algebra.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range] at hmem
    obtain ⟨q₀, hq₀⟩ := hmem
    obtain ⟨q₁, rfl⟩ :=
      Polynomial.map_surjective (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective q₀
    refine ⟨aeval x q₁, ?_, ?_⟩
    · exact aeval_mem_adjoin_singleton _ _
    · rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero,
        map_aeval_eq_aeval_map hcomp, hxres]
      exact hq₀.symm
  have hgx : aeval x g - aeval b g ∈ P ^ 2 := by
    obtain ⟨t, ht⟩ : (x - b) ∣ (aeval x g - aeval b g) := by
      have h := Polynomial.sub_dvd_eval_sub x b (g.map (algebraMap (𝓞 K) (𝓞 L)))
      simpa only [Polynomial.eval_map_algebraMap] using h
    rw [ht]
    exact Ideal.mul_mem_right _ _ hxb
  have h2 : ∃ u ∈ Algebra.adjoin (𝓞 K) ({x} : Set (𝓞 L)), u ∈ P ∧ u ∉ P ^ 2 := by
    refine ⟨aeval x g, ?_, ?_, ?_⟩
    · exact aeval_mem_adjoin_singleton _ _
    · have h' : aeval x g - aeval b g ∈ P := Ideal.pow_le_self two_ne_zero hgx
      simpa using Ideal.add_mem P h' hgb
    · intro hmem
      exact hgb2 (by simpa using Ideal.sub_mem (P ^ 2) hmem hgx)
  have h3 : ∀ P' : Ideal (𝓞 L), P'.IsPrime → P' ≠ ⊥ → P' ≠ P →
      ∃ w ∈ Algebra.adjoin (𝓞 K) ({x} : Set (𝓞 L)), w ∉ P ∧ w ∈ P' := by
    intro P' hP' hP'bot hP'ne
    have := hP'
    by_cases hover : P'.comap (algebraMap (𝓞 K) (𝓞 L)) = p
    · refine ⟨x, Algebra.self_mem_adjoin_singleton _ _, hxP, ?_⟩
      have hIle : p.map (algebraMap (𝓞 K) (𝓞 L)) ≤ P' := by
        rw [Ideal.map_le_iff_le_comap, ← hover]
      rw [hn] at hIle
      rcases (hP'.mul_le).mp hIle with hle | hle
      · exfalso
        rcases Nat.eq_zero_or_eq_succ_pred n with hn0 | hn0
        · rw [hn0, pow_zero, Ideal.one_eq_top] at hle
          exact hP'.ne_top (top_le_iff.mp hle)
        · rw [hn0] at hle
          exact hP'ne (hPmax.eq_of_le hP'.ne_top (Ideal.le_of_pow_succ_le_prime _ hle)).symm
      · exact hle hxQ
    · have : (P'.comap (algebraMap (𝓞 K) (𝓞 L))).IsPrime :=
        Ideal.IsPrime.comap (algebraMap (𝓞 K) (𝓞 L))
      have hp'bot : P'.comap (algebraMap (𝓞 K) (𝓞 L)) ≠ ⊥ := Ideal.under_ne_bot _ hP'bot
      have hp'max : (P'.comap (algebraMap (𝓞 K) (𝓞 L))).IsMaximal :=
        Ideal.IsPrime.isMaximal inferInstance hp'bot
      have hnle : ¬ P'.comap (algebraMap (𝓞 K) (𝓞 L)) ≤ p := fun hle ↦
        hover (hp'max.eq_of_le hpmax.ne_top hle)
      obtain ⟨a, ha, ha'⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
      exact ⟨algebraMap (𝓞 K) (𝓞 L) a, Subalgebra.algebraMap_mem _ a,
        fun h ↦ ha' (Ideal.mem_comap.mpr h), Ideal.mem_comap.mp ha⟩
  exact ⟨x, not_conductor_le_of_residue_surjective K L P h1 h2 h3⟩

/-- **The different of an extension of number rings is the annihilator of the module of
differentials.** For an arbitrary extension of number fields `L/K`,

  `differentIdeal 𝒪_K 𝒪_L = Module.annihilator 𝒪_L Ω[𝒪_L⁄𝒪_K]`. -/
@[stacks 024Z "the different is the annihilator of the module of differentials"]
theorem differentIdeal_eq_annihilator_kaehlerDifferential_general :
    differentIdeal (𝓞 K) (𝓞 L) = Module.annihilator (𝓞 L) Ω[(𝓞 L)⁄(𝓞 K)] :=
  differentIdeal_eq_annihilator_of_forall_exists_conductor_not_le K L fun P hP ↦ by
    have := hP
    exact exists_not_conductor_le K L P

end NumberField

end

end
