module

public import StacksFrontier.RingTheory.CohenMacaulay.Dimension
public import StacksFrontier.RingTheory.RegularLocalRing.Basic
public import StacksFrontier.RingTheory.RegularRing.GlobalDimension
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Regular local rings: supporting lemmas for the approximation property

This file collects facts about Noetherian local rings and regular local rings used in the proof
that a Noetherian local ring with the approximation property is a G-ring (Rotthaus). They
concern dimensions of quotients, systems of parameters, unmixedness, and a test for the
regularity of a localization of a quotient of a regular local ring in terms of explicit relations
among generators of the kernel.

## Main results

Throughout, `(R, 𝔪)` is a Noetherian local ring.

* `isDomain_of_isRegularLocalRing`: a regular local ring is a domain.
* `ringKrullDim_eq_height_add_ringKrullDim_quotient_of_isRegularLocalRing`: in a regular local
  ring, `dim R = ht P + dim R/P` for every prime `P`.
* `ringKrullDim_quotient_lt_of_lt`, `eq_of_le_of_ringKrullDim_quotient_eq`: the coheight
  `dim R/P` is strictly antitone on primes.
* `mem_of_forall_mem_sup_pow`, `mem_of_frequently_mem_sup_pow`: Krull's intersection theorem for
  `R ⧸ I`: if `x ∈ I + 𝔪ⁿ` for all (or for infinitely many) `n`, then `x ∈ I`.
* `ringKrullDim_quotient_le_of_pow_le_sup_span`: if `L₁, …, L_k ∈ 𝔪` and `𝔪ᴺ ≤ P + (L)` for a
  prime `P`, then `dim R/P ≤ k`.
* `exists_pow_le_sup_span_singleton_sup_span`: if `dim R/P = k + 1` and `t ∉ P`, there are
  `L₁, …, L_k ∈ 𝔪` with `𝔪ᴺ ≤ P + (t) + (L)`.
* `ringKrullDim_quotient_eq_of_mem_associatedPrimes` (unmixedness): if `z₁, …, z_l, w₁, …, w_k`
  is a system of parameters of a regular local ring `R`, every associated prime `P` of
  `R/(z₁, …, z_l)` has `dim R/P = k`.
* `exists_fin_mem_and_mul_mem_span_and_pow_le`: if `P` is a prime of height `l` of a regular
  local ring of dimension `l + k`, there are `v₁, …, v_l ∈ P` and `s ∉ P` with `s P ⊆ (v)`,
  and `w₁, …, w_k ∈ 𝔪` with `𝔪ᴺ ≤ (v, w)`.
* `not_isRegularLocalRing_localization_of_forall_exists_mul_mem` and its converse
  `exists_mul_mem_of_not_isRegularLocalRing_localization`, the singularity test: let `R` be a
  regular local ring, `ρ : R → T` a surjection with prime kernel `𝔮 = (q₁, …, q_a)` and `P ⊇ 𝔮` a
  prime. Then `T_{ρ(P)}` is not regular iff there is `t ∉ P` such that every set `J` of `ht 𝔮`
  indices contains some `j` with `t q_j ∈ P² + (q_i : i ∈ J ∖ {j})`; for the first implication
  `t` may depend on `J`.

## Implementation notes

The singularity test is proved in `S = R_P`, a regular local ring of dimension `h = ht P` since
the localizations of a regular local ring are regular (Stacks 0AFS), with `I = 𝔮 S`. One has
`T_{ρ(P)} ≅ S ⧸ I`; `dim S/I = h - ht 𝔮` by the dimension formula (Stacks 00NA) in `S`, as
`ht(𝔮 S) = ht 𝔮`; and the embedding dimension of `S ⧸ I` is `h - δ`, where `δ` is the
dimension of the span of the classes of the `q_i` in `𝔪_S/𝔪_S²`. So `S ⧸ I` is regular iff some
`ht 𝔮` of these classes are linearly independent, and a relation
`t q_j ∈ P² + (q_i : i ∈ J ∖ {j})` with `t ∉ P` says exactly that the class of `q_j` lies in the
span of the classes of the `q_i, i ∈ J ∖ {j}`.

The parameters adapted to a prime `P` are built by prime avoidance: each `v_i ∈ P` avoids the
minimal primes of `(v₁, …, v_{i-1})`, which have height `< ht P` by Krull's height theorem, and
the ideal of elements whose class in `P R_P/P² R_P` lies in the span of the classes of
`v₁, …, v_{i-1}`; then each `w_j ∈ 𝔪` avoids the minimal primes of `(v, w₁, …, w_{j-1})`. All
minimal primes of `(v, w)` then have height `≥ dim R`, so `(v, w)` is `𝔪`-primary, and the
classes of the `v_i` form a basis of `P R_P/P² R_P`, so that `(v) R_P = P R_P` by Nakayama.

## References

* C. Rotthaus, *Rings with approximation property*, Math. Ann. 287 (1990), 455–466.
* H. Matsumura, *Commutative Ring Theory*, §8 (Krull's intersection theorem), §§13–14 (Krull's
  height theorem, systems of parameters), §17 (Cohen–Macaulay rings) and §19 (regular rings).
* [Stacks Project, Tag 00NA](https://stacks.math.columbia.edu/tag/00NA) (dimension formula),
  [Tag 00NQ](https://stacks.math.columbia.edu/tag/00NQ) (regular implies Cohen–Macaulay),
  [Tag 00NP](https://stacks.math.columbia.edu/tag/00NP),
  [Tag 0AFS](https://stacks.math.columbia.edu/tag/0AFS),
  [Tag 00N4](https://stacks.math.columbia.edu/tag/00N4),
  [Tag 00N6](https://stacks.math.columbia.edu/tag/00N6),
  [Tag 0BUS](https://stacks.math.columbia.edu/tag/0BUS) (associated primes of a Cohen–Macaulay
  module), [Tag 00DS](https://stacks.math.columbia.edu/tag/00DS) (prime avoidance).
-/

@[expose] public section

universe u v

open IsLocalRing

namespace Stacks.ApproximationProperty

section Basic

/-! ### Dimension of quotients of Noetherian local rings -/

variable {R : Type u} [CommRing R]

/-- A regular local ring is a domain. -/
theorem isDomain_of_isRegularLocalRing [IsRegularLocalRing R] : IsDomain R :=
  IsRegularLocalRing.isDomain R

/-- The dimension formula in a regular local ring. -/
theorem ringKrullDim_eq_height_add_ringKrullDim_quotient_of_isRegularLocalRing
    [IsRegularLocalRing R] (P : Ideal R) [P.IsPrime] :
    ringKrullDim R = P.height + ringKrullDim (R ⧸ P) :=
  Module.IsMaximalCohenMacaulay.ringKrullDim_eq_height_add_ringKrullDim_quotient
    (IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay R).2 P

/-- The quotient of a local ring by a proper ideal is local. -/
private theorem isLocalRing_quotient [IsLocalRing R] {I : Ideal R} (hI : I ≠ ⊤) :
    IsLocalRing (R ⧸ I) :=
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

/-- A Noetherian local ring has finite Krull dimension, a natural number. -/
private theorem exists_natCast_eq_ringKrullDim (A : Type*) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] : ∃ n : ℕ, ringKrullDim A = (n : WithBot ℕ∞) := by
  rw [← maximalIdeal_height_eq_ringKrullDim]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp
    (Ideal.height_ne_top (maximalIdeal.isMaximal A).ne_top)
  exact ⟨n, by rw [← hn]; rfl⟩

/-- Modulo a prime `P ≤ P'`, any `t ∈ P' ∖ P` lowers the dimension: `dim R/P' + 1 ≤ dim R/P`. -/
private theorem ringKrullDim_quotient_succ_le {P P' : Ideal R} [P.IsPrime] (h : P ≤ P') {t : R}
    (ht : t ∉ P) (htP' : t ∈ P') : ringKrullDim (R ⧸ P') + 1 ≤ ringKrullDim (R ⧸ P) :=
  ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor h) (Ideal.Quotient.factor_surjective h)
    (r := Ideal.Quotient.mk P t)
    (mem_nonZeroDivisors_of_ne_zero fun h0 => ht (Ideal.Quotient.eq_zero_iff_mem.mp h0))
    (by rw [Ideal.Quotient.factor_mk]; exact Ideal.Quotient.eq_zero_iff_mem.mpr htP')

/-- In a Noetherian local ring, a strictly larger prime has strictly smaller coheight. -/
theorem ringKrullDim_quotient_lt_of_lt [IsLocalRing R] [IsNoetherianRing R] {P P' : Ideal R}
    [P.IsPrime] [P'.IsPrime] (h : P < P') : ringKrullDim (R ⧸ P') < ringKrullDim (R ⧸ P) := by
  obtain ⟨x, hxP', hxP⟩ := IsConcreteLE.exists_of_lt h
  have hle := ringKrullDim_quotient_succ_le h.le hxP hxP'
  have := isLocalRing_quotient (Ideal.IsPrime.ne_top (inferInstance : P'.IsPrime))
  obtain ⟨n, hn⟩ := exists_natCast_eq_ringKrullDim (R ⧸ P')
  rw [hn] at hle ⊢
  refine lt_of_lt_of_le ?_ hle
  exact_mod_cast (show ((n : ℕ∞) : WithBot ℕ∞) < ((n : ℕ∞) : WithBot ℕ∞) + 1 by
    exact_mod_cast Nat.lt_succ_self n)

/-- In a Noetherian local ring, two nested primes with the same coheight are equal. -/
theorem eq_of_le_of_ringKrullDim_quotient_eq [IsLocalRing R] [IsNoetherianRing R]
    {P P' : Ideal R} [P.IsPrime] [P'.IsPrime] (h : P ≤ P')
    (hdim : ringKrullDim (R ⧸ P) = ringKrullDim (R ⧸ P')) : P = P' := by
  by_contra hne
  exact (ringKrullDim_quotient_lt_of_lt (lt_of_le_of_ne h hne)).ne hdim.symm

/-! ### Krull's intersection theorem for quotients -/

/-- Krull's intersection theorem for the quotient `R ⧸ I` of a Noetherian local ring: an
element lying in `I + 𝔪ⁿ` for all `n` lies in `I`. -/
theorem mem_of_forall_mem_sup_pow [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R) {x : R}
    (hx : ∀ n : ℕ, x ∈ I ⊔ maximalIdeal R ^ n) : x ∈ I := by
  have key := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := R ⧸ I) (maximalIdeal R)
    (maximalIdeal.isMaximal R).ne_top
  have hmem : (Ideal.Quotient.mk I x : R ⧸ I) ∈
      (⨅ i : ℕ, (maximalIdeal R) ^ i • ⊤ : Submodule R (R ⧸ I)) := by
    rw [Submodule.mem_iInf]
    intro n
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp (hx n)
    have hy0 : Ideal.Quotient.mk I y = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hy
    rw [map_add, hy0, zero_add]
    have he : z • (1 : R ⧸ I) = Ideal.Quotient.mk I z := by
      rw [Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq]
    rw [← he]
    exact Submodule.smul_mem_smul hz Submodule.mem_top
  rw [key, Submodule.mem_bot] at hmem
  exact Ideal.Quotient.eq_zero_iff_mem.mp hmem

/-- Krull's intersection theorem for quotients, for infinitely many exponents. -/
theorem mem_of_frequently_mem_sup_pow [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R) {x : R}
    (hx : ∀ N : ℕ, ∃ n ≥ N, x ∈ I ⊔ maximalIdeal R ^ n) : x ∈ I := by
  refine mem_of_forall_mem_sup_pow I fun n => ?_
  obtain ⟨m, hm, hxm⟩ := hx n
  exact sup_le_sup_left (Ideal.pow_le_pow_right hm) I hxm

/-! ### Systems of parameters modulo a prime -/

/-- A family indexed by `Fin k` has at most `k` distinct values. -/
private theorem ncard_range_fin_le {A : Type*} {k : ℕ} (f : Fin k → A) :
    (Set.range f).ncard ≤ k := by
  rw [← Set.image_univ]
  refine (Set.ncard_image_le (Set.toFinite _)).trans ?_
  simp [Set.ncard_univ]

/-- In a local ring, the maximal ideal is a minimal prime of every ideal `J ≤ 𝔪` containing a
power of `𝔪`. -/
private theorem maximalIdeal_mem_minimalPrimes_of_pow_le {A : Type*} [CommRing A]
    [IsLocalRing A] {J : Ideal A} (hJ : J ≤ maximalIdeal A) {N : ℕ}
    (hN : maximalIdeal A ^ N ≤ J) : maximalIdeal A ∈ J.minimalPrimes := by
  refine ⟨⟨inferInstance, hJ⟩, fun Q hQ _ => ?_⟩
  have := hQ.1
  exact Ideal.IsPrime.le_of_pow_le (hN.trans hQ.2)

/-- The dimension bound of `ringKrullDim_quotient_le_of_pow_le_sup_span` for an arbitrary
ideal `I` in place of the prime `P`. -/
private theorem ringKrullDim_quotient_le_of_pow_le_sup_span' [IsLocalRing R] [IsNoetherianRing R]
    (I : Ideal R) {k : ℕ} (L : Fin k → R) (hL : ∀ i, L i ∈ maximalIdeal R)
    (hN : ∃ N, maximalIdeal R ^ N ≤ I ⊔ Ideal.span (Set.range L)) :
    ringKrullDim (R ⧸ I) ≤ k := by
  by_cases hI : I = ⊤
  · have : Subsingleton (R ⧸ I) := Ideal.Quotient.subsingleton_iff.mpr hI
    rw [ringKrullDim_eq_bot_of_subsingleton]
    exact bot_le
  obtain ⟨N, hN⟩ := hN
  have := isLocalRing_quotient hI
  set f := Ideal.Quotient.mk I with hf
  have hmax : (maximalIdeal R).map f = maximalIdeal (R ⧸ I) :=
    map_maximalIdeal_of_surjective f Ideal.Quotient.mk_surjective
  have hspan : Ideal.span (Set.range (f ∘ L)) = (Ideal.span (Set.range L)).map f := by
    rw [Ideal.map_span, ← Set.range_comp]
  have hle : Ideal.span (Set.range (f ∘ L)) ≤ maximalIdeal (R ⧸ I) := by
    rw [hspan, ← hmax]
    exact Ideal.map_mono (Ideal.span_le.mpr (Set.range_subset_iff.mpr hL))
  have hpow : maximalIdeal (R ⧸ I) ^ N ≤ Ideal.span (Set.range (f ∘ L)) := by
    rw [← hmax, ← Ideal.map_pow, hspan]
    calc (maximalIdeal R ^ N).map f ≤ (I ⊔ Ideal.span (Set.range L)).map f := Ideal.map_mono hN
      _ = (Ideal.span (Set.range L)).map f := by
        rw [Ideal.map_sup, hf, Ideal.map_quotient_self, bot_sup_eq]
  have hht := Ideal.height_le_ncard_of_mem_minimalPrimes_span (Set.finite_range _)
    (maximalIdeal_mem_minimalPrimes_of_pow_le hle hpow)
  rw [← maximalIdeal_height_eq_ringKrullDim]
  have hcard : ((Set.range (f ∘ L)).ncard : ℕ∞) ≤ k := by exact_mod_cast ncard_range_fin_le _
  exact_mod_cast hht.trans hcard

/-- **Dimension bound.** In a Noetherian local ring, if `P` is a prime and `L₁, …, L_k ∈ 𝔪`
generate an ideal of definition modulo `P`, then `dim R/P ≤ k`. -/
@[ega "IV 5.1.6" "lower bound"]
theorem ringKrullDim_quotient_le_of_pow_le_sup_span [IsLocalRing R] [IsNoetherianRing R]
    (P : Ideal R) {k : ℕ} (L : Fin k → R) (hL : ∀ i, L i ∈ maximalIdeal R)
    (hN : ∃ N, maximalIdeal R ^ N ≤ P ⊔ Ideal.span (Set.range L)) :
    ringKrullDim (R ⧸ P) ≤ k :=
  ringKrullDim_quotient_le_of_pow_le_sup_span' P L hL hN

/-- An element of a local ring whose class modulo `I` is in the maximal ideal of `R ⧸ I` lies in
the maximal ideal. -/
private theorem mem_maximalIdeal_of_mk_mem [IsLocalRing R] {I : Ideal R} [IsLocalRing (R ⧸ I)]
    {x : R} (hx : Ideal.Quotient.mk I x ∈ maximalIdeal (R ⧸ I)) : x ∈ maximalIdeal R :=
  (mem_maximalIdeal _).mpr fun hu => (mem_maximalIdeal _).mp hx (hu.map _)

/-- Containment of ideals can be checked after passing to the quotient by `I`. -/
private theorem le_sup_of_map_mk_le {I J K : Ideal R}
    (h : J.map (Ideal.Quotient.mk I) ≤ K.map (Ideal.Quotient.mk I)) : J ≤ K ⊔ I := by
  have := Ideal.map_le_iff_le_comap.mp h
  rwa [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
    Ideal.mk_ker] at this

/-- A finset of at most `k` elements, padded with zeros to a family indexed by `Fin k`. -/
private theorem exists_fin_span_eq_span_finset (s : Finset R) {k : ℕ} (hk : s.card ≤ k) :
    ∃ L : Fin k → R, Ideal.span (Set.range L) = Ideal.span (s : Set R) ∧
      ∀ i, L i ∈ s ∨ L i = 0 := by
  classical
  refine ⟨fun i => if h : (i : ℕ) < s.card then (s.equivFin.symm ⟨i, h⟩ : R) else 0, ?_, ?_⟩
  · apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      dsimp only
      split_ifs with h
      · exact Ideal.subset_span (s.equivFin.symm ⟨i, h⟩).2
      · exact zero_mem _
    · rw [Ideal.span_le]
      intro x hx
      apply Ideal.subset_span
      refine ⟨⟨s.equivFin ⟨x, hx⟩, lt_of_lt_of_le (s.equivFin ⟨x, hx⟩).2 hk⟩, ?_⟩
      simp
  · intro i
    dsimp only
    split_ifs with h
    · exact Or.inl (s.equivFin.symm ⟨i, h⟩).2
    · exact Or.inr rfl

/-- **Systems of parameters modulo an ideal.** If `I` is an ideal of a Noetherian local ring
with `dim R/I ≤ k`, there are `L₁, …, L_k ∈ 𝔪` with `𝔪ᴺ ≤ I + (L₁, …, L_k)` for some `N`. -/
private theorem exists_fin_pow_le_sup_span [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R)
    {k : ℕ} (hk : ringKrullDim (R ⧸ I) ≤ k) :
    ∃ L : Fin k → R, (∀ i, L i ∈ maximalIdeal R) ∧
      ∃ N, maximalIdeal R ^ N ≤ I ⊔ Ideal.span (Set.range L) := by
  classical
  by_cases hI : I = ⊤
  · exact ⟨0, fun _ => zero_mem _, 0, by simp [hI]⟩
  have := isLocalRing_quotient hI
  set f := Ideal.Quotient.mk I with hf
  obtain ⟨s, hs, hcard⟩ :=
    Ideal.exists_finset_card_eq_height_of_isNoetherianRing (maximalIdeal (R ⧸ I))
  have hsk : s.card ≤ k := by
    have h1 : ((s.card : ℕ∞) : WithBot ℕ∞) ≤ k := by
      rwa [hcard, maximalIdeal_height_eq_ringKrullDim]
    exact_mod_cast h1
  set g : R ⧸ I → R := Function.surjInv Ideal.Quotient.mk_surjective
  have hg : ∀ a, f (g a) = a := Function.surjInv_eq Ideal.Quotient.mk_surjective
  obtain ⟨L, hLspan, hLmem⟩ :=
    exists_fin_span_eq_span_finset (s.image g) (Finset.card_image_le.trans hsk)
  refine ⟨L, fun i => ?_, ?_⟩
  · rcases hLmem i with h | h
    · obtain ⟨a, ha, hga⟩ := Finset.mem_image.mp h
      rw [← hga]
      exact mem_maximalIdeal_of_mk_mem (by rw [hg]; exact hs.1.2 (Ideal.subset_span ha))
    · exact h ▸ zero_mem _
  · have hrad : maximalIdeal (R ⧸ I) ≤ (Ideal.span (s : Set (R ⧸ I))).radical := by
      rw [Ideal.radical_eq_sInf]
      refine le_sInf fun Q hQ => ?_
      exact hs.2 ⟨hQ.2, hQ.1⟩ (le_maximalIdeal hQ.2.ne_top)
    obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
    refine ⟨N, ?_⟩
    have hmapL : (Ideal.span (Set.range L)).map f = Ideal.span (s : Set (R ⧸ I)) := by
      rw [hLspan, Ideal.map_span, Finset.coe_image, ← Set.image_comp]
      congr 1
      ext a
      simp [hg]
    have hmax : (maximalIdeal R).map f = maximalIdeal (R ⧸ I) :=
      map_maximalIdeal_of_surjective f Ideal.Quotient.mk_surjective
    have h1 : (maximalIdeal R ^ N).map f ≤ (Ideal.span (Set.range L)).map f := by
      rwa [Ideal.map_pow, hmax, hmapL]
    rw [sup_comm]
    exact le_sup_of_map_mk_le h1

/-- **Parameters through a prime and an element outside it.** If `P` is a prime of a Noetherian
local ring with `dim R/P = k + 1` and `t ∉ P`, there are `L₁, …, L_k ∈ 𝔪` such that
`P + (t) + (L₁, …, L_k)` contains a power of `𝔪`. -/
theorem exists_pow_le_sup_span_singleton_sup_span [IsLocalRing R] [IsNoetherianRing R]
    (P : Ideal R) [P.IsPrime] {k : ℕ} (hP : ringKrullDim (R ⧸ P) = (k + 1 : ℕ)) {t : R}
    (ht : t ∉ P) :
    ∃ L : Fin k → R, (∀ i, L i ∈ maximalIdeal R) ∧
      ∃ N, maximalIdeal R ^ N ≤ P ⊔ Ideal.span {t} ⊔ Ideal.span (Set.range L) := by
  apply exists_fin_pow_le_sup_span
  have h := ringKrullDim_quotient_succ_le (le_sup_left : P ≤ P ⊔ Ideal.span {t}) ht
    (Ideal.mem_sup_right (Ideal.mem_span_singleton_self t))
  rw [hP] at h
  generalize ringKrullDim (R ⧸ (P ⊔ Ideal.span {t})) = D at h ⊢
  induction D using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe D =>
    induction D using ENat.recTopCoe with
    | top =>
      exfalso
      have h' : ((⊤ : ℕ∞) + 1 : ℕ∞) ≤ ((k + 1 : ℕ) : ℕ∞) := by exact_mod_cast h
      simp at h'
    | coe D =>
      have h' : D + 1 ≤ k + 1 := by exact_mod_cast h
      exact_mod_cast (show D ≤ k by omega)

/-! ### Unmixedness -/

/-- A regular local ring is Cohen–Macaulay as a module over itself, in the spelling
`IsCohenMacaulayModule` of `StacksFrontier.RingTheory.CohenMacaulay.Defs` (Stacks 00NQ). -/
@[ega "0 17.1.3"]
private theorem isCohenMacaulayModule_self [IsRegularLocalRing R] :
    IsCohenMacaulayModule R R := by
  have hmcm :=
    (IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay R).2
  rw [Module.IsMaximalCohenMacaulay] at hmcm
  have hne : maximalIdeal R • (⊤ : Submodule R R) ≠ ⊤ := by
    simpa using (maximalIdeal.isMaximal R).ne_top
  have hdepth : Module.depthSup R (maximalIdeal R) R = Module.depth R (maximalIdeal R) R := by
    rw [Module.depth, Module.depthSup_eq_iSup]
    split_ifs with hc
    · exact absurd hc hne
    · rfl
  rw [isCohenMacaulayModule_iff_supportDim_eq_depth, Module.supportDim_self_eq_ringKrullDim,
    hdepth, hmcm]

/-- The ideal generated by the list of values of a family is the span of its range. -/
private theorem ofList_ofFn {n : ℕ} (z : Fin n → R) :
    Ideal.ofList (List.ofFn z) = Ideal.span (Set.range z) := by
  unfold Ideal.ofList
  congr 1
  ext x
  simp [List.mem_ofFn]

/-- **Unmixedness.** Let `R` be a regular local ring and let `z₁, …, z_l, w₁, …, w_k ∈ 𝔪` be a
system of parameters, i.e. `dim R = l + k` and `(z, w)` contains a power of `𝔪`. Then every
associated prime `P` of `R/(z₁, …, z_l)` satisfies `dim R/P = k`. -/
theorem ringKrullDim_quotient_eq_of_mem_associatedPrimes [IsRegularLocalRing R] {l k : ℕ}
    (z : Fin l → R) (w : Fin k → R) (hz : ∀ i, z i ∈ maximalIdeal R)
    (hw : ∀ i, w i ∈ maximalIdeal R) (hdim : ringKrullDim R = (l + k : ℕ))
    (hN : ∃ N, maximalIdeal R ^ N ≤ Ideal.span (Set.range z) ⊔ Ideal.span (Set.range w))
    {P : Ideal R} (hP : P ∈ associatedPrimes R (R ⧸ Ideal.span (Set.range z))) :
    ringKrullDim (R ⧸ P) = k := by
  set I := Ideal.span (Set.range z) with hIdef
  have hIm : I ≤ maximalIdeal R := Ideal.span_le.mpr (Set.range_subset_iff.mpr hz)
  have hItop : I ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hIm
  -- `dim R/(z) = k`
  have hdimI : ringKrullDim (R ⧸ I) = k := by
    have := isLocalRing_quotient hItop
    obtain ⟨n, hn⟩ := exists_natCast_eq_ringKrullDim (R ⧸ I)
    have hle : ringKrullDim (R ⧸ I) ≤ k := ringKrullDim_quotient_le_of_pow_le_sup_span' I w hw hN
    have hge := ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank I
      (by rw [ringJacobson_eq_maximalIdeal]; exact hIm)
    have hsf : I.spanFinrank ≤ l :=
      (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range z)).trans
        (ncard_range_fin_le z)
    rw [hn] at hle hge ⊢
    rw [hdim] at hge
    have hle' : n ≤ k := by exact_mod_cast hle
    have hge' : l + k ≤ n + I.spanFinrank := by exact_mod_cast hge
    exact_mod_cast (show n = k by omega)
  -- `z` is a regular sequence, by Cohen–Macaulayness of `R`
  have hCM : IsCohenMacaulayModule R R := isCohenMacaulayModule_self
  have hsmul : Ideal.ofList (List.ofFn z) • (⊤ : Submodule R R) = I := by
    rw [ofList_ofFn]; simp [hIdef]
  have hmem : ∀ g ∈ List.ofFn z, g ∈ maximalIdeal R := by
    intro g hg
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
    exact hz i
  have hreg : RingTheory.Sequence.IsRegular R (List.ofFn z) := by
    refine cohenMacaulay_dimDrop_isRegular (l + k) l (by omega)
      (by rw [Module.supportDim_self_eq_ringKrullDim, hdim]) hCM.isCohenMacaulay
      (List.ofFn z) (List.length_ofFn) hmem ?_
    rw [hsmul, Module.supportDim_quotient_eq_ringKrullDim, hdimI]
    congr 1
    omega
  -- `R/(z)` is Cohen–Macaulay of dimension `k`, so its associated primes have coheight `k`
  have hCMq := isCohenMacaulay_quotient_ofList (List.ofFn z) hCM hreg hmem
  have hCMI : IsCohenMacaulayModule R (R ⧸ I) :=
    isCohenMacaulay_of_linearEquiv (Submodule.quotEquivOfEq _ _ hsmul) hCMq
  have hcoh := (coheight_eq_supportDim_of_mem_associatedPrimes_of_isCohenMacaulayModule hCMI hP).1
  have : P.IsPrime := hP.isPrime
  rw [Module.supportDim_quotient_eq_ringKrullDim, hdimI] at hcoh
  rw [ringKrullDim_quotient, Order.krullDim_eq_of_orderIso (OrderIso.refl _)]
  rw [← hcoh, Order.coheight_eq_krullDim_Ici]
  rfl

end Basic

section Cotangent

/-! ### Cotangent space computations -/

variable {S : Type*} [CommRing S] [IsLocalRing S]

/-- Membership in the span of a family of cotangent vectors, read off in the ring: the class of
`x ∈ 𝔪` lies in the span of the classes of `y i, i ∈ J`, iff `x ∈ 𝔪² + (y i : i ∈ J)`. -/
private theorem toCotangent_mem_span_image_iff {ι : Type*} (y : ι → maximalIdeal S) (J : Set ι)
    (x : maximalIdeal S) :
    (maximalIdeal S).toCotangent x ∈
        Submodule.span (ResidueField S) ((maximalIdeal S).toCotangent ∘ y '' J) ↔
      (x : S) ∈ maximalIdeal S ^ 2 ⊔ Ideal.span ((fun i => (y i : S)) '' J) := by
  have hsurj : Function.Surjective (algebraMap S (ResidueField S)) := residue_surjective
  have hmap : Submodule.map (maximalIdeal S).subtype (Submodule.span S (y '' J)) =
      Ideal.span ((fun i => (y i : S)) '' J) := by
    rw [Submodule.map_span, Set.image_image]; rfl
  rw [← Submodule.restrictScalars_mem S, Submodule.restrictScalars_span S (ResidueField S) hsurj,
    Set.image_comp, ← Submodule.map_span]
  constructor
  · rintro ⟨t, ht, hteq⟩
    have h2 : (x : S) - t ∈ maximalIdeal S ^ 2 := (Ideal.toCotangent_eq _).mp hteq.symm
    have ht' : (t : S) ∈ Ideal.span ((fun i => (y i : S)) '' J) := by
      rw [← hmap]; exact Submodule.mem_map_of_mem ht
    rw [← sub_add_cancel (x : S) t]
    exact Ideal.add_mem _ (Ideal.mem_sup_left h2) (Ideal.mem_sup_right ht')
  · intro hx
    obtain ⟨m, hm, u, hu, hmu⟩ := Submodule.mem_sup.mp hx
    rw [← hmap] at hu
    obtain ⟨t, ht, rfl⟩ := hu
    refine ⟨t, ht, (Ideal.toCotangent_eq _).mpr ?_⟩
    have : (t : S) - x = -m := by rw [← hmu]; simp
    exact this ▸ neg_mem hm

/-- A family in `𝔪` spans `𝔪` as a module iff the ideal it generates contains `𝔪`. -/
private theorem span_eq_top_iff_le_span_coe {s : Set (maximalIdeal S)} :
    Submodule.span S s = ⊤ ↔ maximalIdeal S ≤ Ideal.span (((↑) : maximalIdeal S → S) '' s) := by
  have hmap : Submodule.map (maximalIdeal S).subtype (Submodule.span S s) =
      Ideal.span (((↑) : maximalIdeal S → S) '' s) := by
    rw [Submodule.map_span]; rfl
  constructor
  · intro h
    rw [← hmap, h, Submodule.map_subtype_top]
  · intro h
    rw [eq_top_iff]
    intro m _
    have hm : (m : S) ∈ Submodule.map (maximalIdeal S).subtype (Submodule.span S s) :=
      hmap ▸ h m.2
    obtain ⟨t, ht, hteq⟩ := hm
    rwa [show t = m from Subtype.ext hteq] at ht

/-- Over a division ring, a finite-dimensional space is spanned by a subspace `W` together with
`dim (V ⧸ W)` further vectors. -/
private theorem exists_span_range_sup_eq_top {K V : Type*} [DivisionRing K] [AddCommGroup V]
    [Module K V] [Module.Finite K V] (W : Submodule K V) :
    ∃ z : Fin (Module.finrank K (V ⧸ W)) → V, Submodule.span K (Set.range z) ⊔ W = ⊤ := by
  classical
  set b := Module.finBasis K (V ⧸ W)
  refine ⟨fun j => Function.surjInv W.mkQ_surjective (b j), ?_⟩
  have hz : ∀ j, W.mkQ (Function.surjInv W.mkQ_surjective (b j)) = b j :=
    fun j => Function.surjInv_eq W.mkQ_surjective (b j)
  have hmap : Submodule.map W.mkQ (Submodule.span K
      (Set.range fun j => Function.surjInv W.mkQ_surjective (b j))) = ⊤ := by
    rw [Submodule.map_span]
    have himg : (W.mkQ '' Set.range fun j => Function.surjInv W.mkQ_surjective (b j))
        = Set.range b := by
      rw [← Set.range_comp]
      exact congrArg Set.range (funext hz)
    rw [himg, b.span_eq]
  have h := Submodule.comap_map_eq W.mkQ (Submodule.span K
    (Set.range fun j => Function.surjInv W.mkQ_surjective (b j)))
  rw [hmap, Submodule.comap_top, Submodule.ker_mkQ] at h
  exact h.symm

/-- The span of a linearly independent finite subfamily has dimension its cardinality. -/
private theorem finrank_span_image_finset {K V ι : Type*} [DivisionRing K] [AddCommGroup V]
    [Module K V] {f : ι → V} {J : Finset ι} (hJ : LinearIndepOn K f (J : Set ι)) :
    Module.finrank K (Submodule.span K (f '' (J : Set ι))) = J.card := by
  rw [Set.image_eq_range, finrank_span_eq_card hJ]
  simp

/-- **Upper bound for the embedding dimension of a quotient.** If `y_j, j ∈ J`, lie in an
ideal `I ≤ 𝔪` and have linearly independent classes in `𝔪/𝔪²`, then the maximal ideal of
`S ⧸ I` needs at most `dim 𝔪/𝔪² - |J|` generators. -/
private theorem spanFinrank_quotient_add_card_le [IsNoetherianRing S] {ι : Type*}
    (y : ι → maximalIdeal S) (I : Ideal S) [IsLocalRing (S ⧸ I)] (J : Finset ι)
    (hyI : ∀ i ∈ J, (y i : S) ∈ I)
    (hJ : LinearIndepOn (ResidueField S) ((maximalIdeal S).toCotangent ∘ y) (J : Set ι)) :
    (maximalIdeal (S ⧸ I)).spanFinrank + J.card ≤
      Module.finrank (ResidueField S) (CotangentSpace S) := by
  classical
  set K := ResidueField S
  set W := Submodule.span K ((maximalIdeal S).toCotangent ∘ y '' (J : Set ι))
  have hWrank : Module.finrank K W = J.card := finrank_span_image_finset hJ
  obtain ⟨z, hz⟩ := exists_span_range_sup_eq_top W
  have hsum := Submodule.finrank_quotient_add_finrank W
  set z' := fun j => Function.surjInv (maximalIdeal S).toCotangent_surjective (z j)
  have hz'eq : (maximalIdeal S).toCotangent ∘ z' = z :=
    funext fun j => Function.surjInv_eq (maximalIdeal S).toCotangent_surjective (z j)
  have hspanK : Submodule.span K
      ((maximalIdeal S).toCotangent '' (Set.range z' ∪ y '' (J : Set ι))) = ⊤ := by
    rw [Set.image_union, Submodule.span_union, ← Set.range_comp, hz'eq, Set.image_image]
    exact hz
  rw [CotangentSpace.span_image_eq_top_iff, span_eq_top_iff_le_span_coe, Set.image_union,
    Ideal.span_union, ← Set.range_comp, Set.image_image] at hspanK
  have hle : maximalIdeal S ≤ Ideal.span (Set.range (((↑) : maximalIdeal S → S) ∘ z')) ⊔ I := by
    refine hspanK.trans (sup_le_sup_left ?_ _)
    rw [Ideal.span_le]
    rintro _ ⟨i, hi, rfl⟩
    exact hyI i hi
  set mk := Ideal.Quotient.mk I with hmk
  have hmax : (maximalIdeal S).map mk = maximalIdeal (S ⧸ I) :=
    map_maximalIdeal_of_surjective mk Ideal.Quotient.mk_surjective
  have heq : maximalIdeal (S ⧸ I) =
      Ideal.span (Set.range (mk ∘ ((↑) : maximalIdeal S → S) ∘ z')) := by
    apply le_antisymm
    · rw [← hmax]
      calc (maximalIdeal S).map mk
          ≤ (Ideal.span (Set.range (((↑) : maximalIdeal S → S) ∘ z')) ⊔ I).map mk :=
            Ideal.map_mono hle
        _ = Ideal.span (Set.range (mk ∘ ((↑) : maximalIdeal S → S) ∘ z')) := by
          rw [Ideal.map_sup, hmk, Ideal.map_quotient_self, sup_bot_eq, Ideal.map_span,
            ← Set.range_comp]
    · rw [Ideal.span_le, ← hmax]
      rintro _ ⟨j, rfl⟩
      exact Ideal.mem_map_of_mem _ (z' j).2
  rw [heq]
  calc (Ideal.span (Set.range (mk ∘ ((↑) : maximalIdeal S → S) ∘ z'))).spanFinrank + J.card
      ≤ Module.finrank K (CotangentSpace S ⧸ W) + J.card := by
        gcongr
        exact (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range _)).trans
          (ncard_range_fin_le _)
    _ = Module.finrank K (CotangentSpace S) := by rw [← hWrank]; exact hsum

/-- **Lower bound for the embedding dimension of a quotient.** If an ideal `I ≤ 𝔪` is contained
in the ideal generated by `y_i ∈ 𝔪`, there is a finite set `b` of indices whose classes in
`𝔪/𝔪²` are linearly independent and such that `dim 𝔪/𝔪² ≤ edim(S ⧸ I) + |b|`. -/
private theorem exists_linearIndepOn_finrank_le [IsNoetherianRing S] {ι : Type*} [Finite ι]
    (y : ι → maximalIdeal S) (I : Ideal S) [IsLocalRing (S ⧸ I)]
    (hIy : I ≤ Ideal.span (Set.range fun i => (y i : S))) :
    ∃ b : Finset ι,
      LinearIndepOn (ResidueField S) ((maximalIdeal S).toCotangent ∘ y) (b : Set ι) ∧
      Module.finrank (ResidueField S) (CotangentSpace S) ≤
        (maximalIdeal (S ⧸ I)).spanFinrank + b.card := by
  classical
  set K := ResidueField S
  set f := (maximalIdeal S).toCotangent ∘ y
  obtain ⟨b, -, -, hbspan, hbli⟩ := exists_linearIndepOn_extension (K := K) (v := f)
    (linearIndepOn_empty K f) (Set.empty_subset Set.univ)
  set bF := (Set.toFinite b).toFinset
  have hbcoe : (bF : Set ι) = b := Set.Finite.coe_toFinset _
  have hbli' : LinearIndepOn K f (bF : Set ι) := by rwa [hbcoe]
  refine ⟨bF, hbli', ?_⟩
  set mk := Ideal.Quotient.mk I with hmk
  obtain ⟨G, hGcard, hGspan⟩ :=
    (IsNoetherian.noetherian (maximalIdeal (S ⧸ I))).exists_span_finset_card_eq_spanFinrank
  set g : S ⧸ I → S := Function.surjInv Ideal.Quotient.mk_surjective
  have hg : ∀ a, mk (g a) = a := Function.surjInv_eq Ideal.Quotient.mk_surjective
  have hgmem : ∀ a ∈ G, g a ∈ maximalIdeal S := fun a ha =>
    mem_maximalIdeal_of_mk_mem (by rw [hg]; exact hGspan ▸ Submodule.subset_span ha)
  let φ : G → maximalIdeal S := fun a => ⟨g a, hgmem a a.2⟩
  have hmax : (maximalIdeal S).map mk = maximalIdeal (S ⧸ I) :=
    map_maximalIdeal_of_surjective mk Ideal.Quotient.mk_surjective
  have hrange : Set.range (mk ∘ fun a => (φ a : S)) = (G : Set (S ⧸ I)) := by
    ext c
    simp [φ, hg]
  have hle : maximalIdeal S ≤ Ideal.span (Set.range fun a => (φ a : S)) ⊔ I := by
    apply le_sup_of_map_mk_le
    rw [hmax, Ideal.map_span, ← Set.range_comp, hrange]
    exact hGspan.ge
  have hle' : maximalIdeal S ≤
      Ideal.span (((↑) : maximalIdeal S → S) '' (Set.range φ ∪ Set.range y)) := by
    rw [Set.image_union, Ideal.span_union, ← Set.range_comp, ← Set.range_comp]
    exact hle.trans (sup_le_sup_left hIy _)
  have htop := span_eq_top_iff_le_span_coe.mpr hle'
  rw [← CotangentSpace.span_image_eq_top_iff, Set.image_union, Submodule.span_union,
    ← Set.range_comp, ← Set.range_comp] at htop
  have h1 : Module.finrank K
      (Submodule.span K (Set.range ((maximalIdeal S).toCotangent ∘ φ))) ≤ G.card := by
    simpa [Set.finrank] using finrank_range_le_card (R := K) ((maximalIdeal S).toCotangent ∘ φ)
  have h2 : Module.finrank K (Submodule.span K (Set.range f)) ≤ bF.card := by
    have hle2 : Submodule.span K (Set.range f) ≤ Submodule.span K (f '' (bF : Set ι)) := by
      rwa [Submodule.span_le, ← Set.image_univ, hbcoe]
    exact (Submodule.finrank_mono hle2).trans (finrank_span_image_finset hbli').le
  calc Module.finrank K (CotangentSpace S)
      = Module.finrank K (⊤ : Submodule K (CotangentSpace S)) := (finrank_top _ _).symm
    _ = Module.finrank K ↥(Submodule.span K (Set.range ((maximalIdeal S).toCotangent ∘ φ)) ⊔
          Submodule.span K (Set.range f)) := by rw [htop]
    _ ≤ Module.finrank K (Submodule.span K (Set.range ((maximalIdeal S).toCotangent ∘ φ))) +
          Module.finrank K (Submodule.span K (Set.range f)) :=
        Submodule.finrank_add_le_finrank_add_finrank _ _
    _ ≤ G.card + bF.card := add_le_add h1 h2
    _ = (maximalIdeal (S ⧸ I)).spanFinrank + bF.card := by rw [hGcard]

end Cotangent

section RegularQuotient

variable {S : Type*} [CommRing S]

/-- **The regularity criterion for a quotient of a regular local ring by a prime.** Let `S`
be a regular local ring and `I` a prime generated by `y₁, …, y_a ∈ 𝔪`. Then `S ⧸ I` is regular
iff some `ht(I)` of the classes of the `y_i` in `𝔪/𝔪²` are linearly independent. -/
private theorem isRegularLocalRing_quotient_iff [IsRegularLocalRing S] {a : ℕ}
    (y : Fin a → maximalIdeal S) (I : Ideal S) [I.IsPrime]
    (hI : I = Ideal.span (Set.range fun i => (y i : S))) :
    IsRegularLocalRing (S ⧸ I) ↔ ∃ J : Finset (Fin a), (J.card : ℕ∞) = I.height ∧
      LinearIndepOn (ResidueField S) ((maximalIdeal S).toCotangent ∘ y) (J : Set (Fin a)) := by
  have hItop : I ≠ ⊤ := Ideal.IsPrime.ne_top inferInstance
  have := isLocalRing_quotient hItop
  set h := Module.finrank (ResidueField S) (CotangentSpace S) with hhdef
  have hh : (h : WithBot ℕ∞) = ringKrullDim S := by
    rw [hhdef, ← spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
    exact IsRegularLocalRing.spanFinrank_maximalIdeal
  have hformula := ringKrullDim_eq_height_add_ringKrullDim_quotient_of_isRegularLocalRing I
  obtain ⟨d, hd⟩ := exists_natCast_eq_ringKrullDim (S ⧸ I)
  obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.mp (Ideal.height_ne_top hItop)
  have hcd : c + d = h := by
    rw [hd, ← hc, ← hh] at hformula
    exact_mod_cast hformula.symm
  rw [← hc]
  constructor
  · intro hreg
    have he : (maximalIdeal (S ⧸ I)).spanFinrank = d := by
      have := IsRegularLocalRing.spanFinrank_maximalIdeal (R := S ⧸ I)
      rw [hd] at this
      exact_mod_cast this
    obtain ⟨b, hbli, hb⟩ := exists_linearIndepOn_finrank_le y I hI.le
    have hcb : c ≤ b.card := by omega
    obtain ⟨J, hJb, hJcard⟩ := Finset.exists_subset_card_eq hcb
    exact ⟨J, by rw [hJcard], hbli.mono (Finset.coe_subset.mpr hJb)⟩
  · rintro ⟨J, hJcard, hJli⟩
    have hJc : J.card = c := by exact_mod_cast hJcard
    have hyI : ∀ i ∈ J, (y i : S) ∈ I := fun i _ => hI ▸ Ideal.subset_span ⟨i, rfl⟩
    have hle := spanFinrank_quotient_add_card_le y I J hyI hJli
    apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
    rw [hd]
    exact_mod_cast (show (maximalIdeal (S ⧸ I)).spanFinrank ≤ d by omega)

end RegularQuotient

section SingularityTest

/-! ### The singularity test -/

variable {R : Type u} [CommRing R]

/-- The local ring of `T` at `ρ(P)` is the quotient of `R_P` by the extension of `ker ρ`. -/
private noncomputable def localizationQuotientEquiv {T : Type v} [CommRing T] (ρ : R →+* T)
    (hρ : Function.Surjective ρ) (P : Ideal R) [P.IsPrime] (hP : RingHom.ker ρ ≤ P)
    [(P.map ρ).IsPrime] :
    (Localization.AtPrime P ⧸ (RingHom.ker ρ).map (algebraMap R (Localization.AtPrime P))) ≃+*
      Localization.AtPrime (P.map ρ) := by
  let Pb : Ideal (R ⧸ RingHom.ker ρ) := P.map (Ideal.Quotient.mk (RingHom.ker ρ))
  haveI : Pb.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hP
  have hPb : Pb.comap (Ideal.Quotient.mk (RingHom.ker ρ)) = P := Ideal.comap_map_mk hP
  have hm : Algebra.algebraMapSubmonoid (R ⧸ RingHom.ker ρ) P.primeCompl = Pb.primeCompl := by
    ext z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    simp only [Algebra.algebraMapSubmonoid, Submonoid.mem_map, Ideal.mem_primeCompl_iff]
    constructor
    · rintro ⟨b, hb, hab⟩
      have hbp : b ∉ P := hb
      have hbq : (Ideal.Quotient.mk (RingHom.ker ρ) b) ∉ Pb := by
        simpa [← hPb] using hbp
      exact hab ▸ hbq
    · intro ha
      exact ⟨a, by simpa [← hPb] using ha, rfl⟩
  haveI : IsLocalization Pb.primeCompl (Localization.AtPrime P ⧸
      (RingHom.ker ρ).map (algebraMap R (Localization.AtPrime P))) := by
    rw [← hm]
    infer_instance
  let e₀ := RingHom.quotientKerEquivOfSurjective hρ
  have hcomp : (e₀ : R ⧸ RingHom.ker ρ →+* T).comp (Ideal.Quotient.mk (RingHom.ker ρ)) = ρ := by
    ext x
    simp [e₀]
  have he : Pb = (P.map ρ).comap e₀ := by
    apply Ideal.comap_injective_of_surjective (Ideal.Quotient.mk (RingHom.ker ρ))
      Ideal.Quotient.mk_surjective
    rw [hPb]
    change P = Ideal.comap (Ideal.Quotient.mk (RingHom.ker ρ))
      (Ideal.comap (e₀ : R ⧸ RingHom.ker ρ →+* T) (P.map ρ))
    rw [Ideal.comap_comap, hcomp, Ideal.comap_map_of_surjective ρ hρ, ← RingHom.ker_eq_comap_bot,
      sup_eq_left.mpr hP]
  exact (IsLocalization.algEquiv Pb.primeCompl _ (Localization.AtPrime Pb)).toRingEquiv.trans
    (Localization.localRingEquiv Pb (P.map ρ) e₀ he)

/-- The images in the maximal ideal of `R_P` of a family of elements of `P`. -/
private noncomputable def locFamily (P : Ideal R) [P.IsPrime] {ι : Type*} (q : ι → R)
    (hq : ∀ i, q i ∈ P) : ι → maximalIdeal (Localization.AtPrime P) :=
  fun i => ⟨algebraMap R (Localization.AtPrime P) (q i),
    (IsLocalization.AtPrime.to_map_mem_maximal_iff _ P _).mpr (hq i)⟩

/-- An element becomes a member of the extension of `A` to `R_P` iff a multiple of it by an
element outside `P` lies in `A`. -/
private theorem exists_mul_mem_iff_mem_map (P : Ideal R) [P.IsPrime] (A : Ideal R) (x : R) :
    (∃ t ∉ P, t * x ∈ A) ↔
      algebraMap R (Localization.AtPrime P) x ∈ A.map (algebraMap R (Localization.AtPrime P)) := by
  constructor
  · rintro ⟨t, ht, htx⟩
    have hu : IsUnit (algebraMap R (Localization.AtPrime P) t) :=
      IsLocalization.map_units _ (⟨t, ht⟩ : P.primeCompl)
    have hmem := Ideal.mem_map_of_mem (algebraMap R (Localization.AtPrime P)) htx
    rw [map_mul] at hmem
    exact (Ideal.unit_mul_mem_iff_mem _ hu).mp hmem
  · intro hx
    obtain ⟨⟨a, s⟩, hs⟩ := (IsLocalization.mem_map_algebraMap_iff P.primeCompl _).mp hx
    rw [← map_mul] at hs
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists P.primeCompl _).mp hs
    refine ⟨c * s, (P.primeCompl.mul_mem c.2 s.2 : (c * s : R) ∈ P.primeCompl), ?_⟩
    have : (c * s : R) * x = c * a := by
      rw [← hc]
      ring
    exact this ▸ Ideal.mul_mem_left _ _ a.2

/-- A relation `t q_j ∈ P² + (q_i : i ∈ J)` with `t ∉ P` says exactly that the class of `q_j` in
the cotangent space of `R_P` lies in the span of the classes of the `q_i, i ∈ J`. -/
private theorem exists_mul_mem_iff_toCotangent_mem_span (P : Ideal R) [P.IsPrime] {ι : Type*}
    (q : ι → R) (hqP : ∀ i, q i ∈ P) (j : ι) (J : Set ι) :
    (∃ t ∉ P, t * q j ∈ P ^ 2 ⊔ Ideal.span (q '' J)) ↔
      ((maximalIdeal (Localization.AtPrime P)).toCotangent ∘ locFamily P q hqP) j ∈
        Submodule.span (ResidueField (Localization.AtPrime P))
          ((maximalIdeal (Localization.AtPrime P)).toCotangent ∘ locFamily P q hqP '' J) := by
  rw [Function.comp_apply, toCotangent_mem_span_image_iff, exists_mul_mem_iff_mem_map,
    Ideal.map_sup, Ideal.map_pow, Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_span,
    Set.image_image]
  rfl

/-- Finitely many conditions, each satisfied by some element outside a prime `P` and stable
under multiplication, are simultaneously satisfied by one element outside `P`. -/
private theorem exists_notMem_forall_of_mul_closed (P : Ideal R) [P.IsPrime] {ι : Type*}
    (s : Finset ι) (Φ : ι → R → Prop) (hΦ : ∀ i t u, Φ i t → Φ i (u * t))
    (h : ∀ i ∈ s, ∃ t ∉ P, Φ i t) : ∃ t ∉ P, ∀ i ∈ s, Φ i t := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨1, fun h1 => (Ideal.IsPrime.ne_top inferInstance) ((Ideal.eq_top_iff_one P).mpr h1),
      by simp⟩
  | insert i s hi ih =>
    obtain ⟨t', ht', hΦ'⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    obtain ⟨t, ht, hΦt⟩ := h i (Finset.mem_insert_self i s)
    refine ⟨t' * t, fun hmem => ?_, ?_⟩
    · rcases (Ideal.IsPrime.mem_or_mem inferInstance) hmem with h1 | h1
      exacts [ht' h1, ht h1]
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hΦ _ _ _ hΦt
      · rw [mul_comm]
        exact hΦ _ _ _ (hΦ' j hj)

/-- The common setting of the singularity test: `R_P` is regular, the extension `I` of `ker ρ`
to `R_P` is a prime of the same height generated by the images of the `q_i`, and
`T_{ρ(P)}` is regular iff `R_P ⧸ I` is. -/
private theorem singularityTest_aux [IsRegularLocalRing R] {T : Type v} [CommRing T]
    (ρ : R →+* T) (hρ : Function.Surjective ρ) [(RingHom.ker ρ).IsPrime] {a : ℕ} (q : Fin a → R)
    (hq : RingHom.ker ρ = Ideal.span (Set.range q)) (P : Ideal R) [P.IsPrime]
    (hP : RingHom.ker ρ ≤ P) [(P.map ρ).IsPrime] (hqP : ∀ i, q i ∈ P) :
    IsRegularLocalRing (Localization.AtPrime (P.map ρ)) ↔
      ∃ J : Finset (Fin a), (J.card : ℕ∞) = (RingHom.ker ρ).height ∧
        LinearIndepOn (ResidueField (Localization.AtPrime P))
          ((maximalIdeal (Localization.AtPrime P)).toCotangent ∘ locFamily P q hqP)
          (J : Set (Fin a)) := by
  have hR : IsRegularLocalRing R := inferInstance
  have : IsRegularRing R := ((IsLocalRing.isRegularRing_tfae (R := R)).out 1 3).mp hR
  have hdisj : Disjoint (P.primeCompl : Set R) (RingHom.ker ρ : Set R) :=
    Set.disjoint_left.mpr fun x hx1 hx2 => hx1 (hP hx2)
  set I := (RingHom.ker ρ).map (algebraMap R (Localization.AtPrime P)) with hIdef
  have : I.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint P.primeCompl _ _
    inferInstance hdisj
  have hIy :
      I = Ideal.span (Set.range fun i => (locFamily P q hqP i : Localization.AtPrime P)) := by
    rw [hIdef, hq, Ideal.map_span, ← Set.range_comp]
    rfl
  have hht : I.height = (RingHom.ker ρ).height :=
    IsLocalization.height_map_of_disjoint P.primeCompl _ hdisj
  rw [← hht, ← isRegularLocalRing_quotient_iff (locFamily P q hqP) I hIy]
  exact ⟨fun h => IsRegularLocalRing.of_ringEquiv (localizationQuotientEquiv ρ hρ P hP).symm,
    fun h => IsRegularLocalRing.of_ringEquiv (localizationQuotientEquiv ρ hρ P hP)⟩

/-- **Singularity test.** Let `R` be a regular local ring, `ρ : R → T` a surjection whose kernel
`𝔮 = (q₁, …, q_a)` is prime, and `P ⊇ 𝔮` a prime with `ρ(P)` prime. If every set `J` of
`ht(𝔮)` indices contains some `j` satisfying a relation `t q_j ∈ P² + (q_i : i ∈ J ∖ {j})` with
`t ∉ P`, then the local ring of `T` at `ρ(P)` is not regular. -/
theorem not_isRegularLocalRing_localization_of_forall_exists_mul_mem [IsRegularLocalRing R]
    {T : Type v} [CommRing T] (ρ : R →+* T) (hρ : Function.Surjective ρ)
    [(RingHom.ker ρ).IsPrime] {a : ℕ} (q : Fin a → R)
    (hq : RingHom.ker ρ = Ideal.span (Set.range q)) (P : Ideal R) [P.IsPrime]
    (hP : RingHom.ker ρ ≤ P) [(P.map ρ).IsPrime]
    (h : ∀ J : Finset (Fin a), (J.card : ℕ∞) = (RingHom.ker ρ).height →
      ∃ j ∈ J, ∃ t ∉ P, t * q j ∈ P ^ 2 ⊔ Ideal.span (q '' ↑(J.erase j))) :
    ¬ IsRegularLocalRing (Localization.AtPrime (P.map ρ)) := by
  classical
  have hqP : ∀ i, q i ∈ P := fun i => hP (hq ▸ Ideal.subset_span ⟨i, rfl⟩)
  intro hreg
  obtain ⟨J, hJcard, hJli⟩ := (singularityTest_aux ρ hρ q hq P hP hqP).mp hreg
  obtain ⟨j, hj, t, ht, hmem⟩ := h J hJcard
  have hspan := (exists_mul_mem_iff_toCotangent_mem_span P q hqP j ↑(J.erase j)).mp ⟨t, ht, hmem⟩
  rw [Finset.coe_erase] at hspan
  exact hJli.notMem_span (Finset.mem_coe.mpr hj) hspan

/-- **Singularity test, converse.** In the setting of
`not_isRegularLocalRing_localization_of_forall_exists_mul_mem`, if the local ring of `T` at `ρ(P)`
is not regular, then a single `t ∉ P` works for all sets `J` of `ht(𝔮)` indices: each such `J`
contains some `j` with `t q_j ∈ P² + (q_i : i ∈ J ∖ {j})`. -/
theorem exists_mul_mem_of_not_isRegularLocalRing_localization [IsRegularLocalRing R]
    {T : Type v} [CommRing T] (ρ : R →+* T) (hρ : Function.Surjective ρ)
    [(RingHom.ker ρ).IsPrime] {a : ℕ} (q : Fin a → R)
    (hq : RingHom.ker ρ = Ideal.span (Set.range q)) (P : Ideal R) [P.IsPrime]
    (hP : RingHom.ker ρ ≤ P) [(P.map ρ).IsPrime]
    (h : ¬ IsRegularLocalRing (Localization.AtPrime (P.map ρ))) :
    ∃ t ∉ P, ∀ J : Finset (Fin a), (J.card : ℕ∞) = (RingHom.ker ρ).height →
      ∃ j ∈ J, t * q j ∈ P ^ 2 ⊔ Ideal.span (q '' ↑(J.erase j)) := by
  classical
  have hqP : ∀ i, q i ∈ P := fun i => hP (hq ▸ Ideal.subset_span ⟨i, rfl⟩)
  set 𝒥 := (Finset.univ : Finset (Finset (Fin a))).filter
    (fun J => (J.card : ℕ∞) = (RingHom.ker ρ).height) with h𝒥
  have key : ∀ J ∈ 𝒥, ∃ t ∉ P, ∃ j ∈ J, t * q j ∈ P ^ 2 ⊔ Ideal.span (q '' ↑(J.erase j)) := by
    intro J hJ
    have hJcard := (Finset.mem_filter.mp hJ).2
    have hnli : ¬ LinearIndepOn (ResidueField (Localization.AtPrime P))
        ((maximalIdeal (Localization.AtPrime P)).toCotangent ∘ locFamily P q hqP)
        (J : Set (Fin a)) :=
      fun hli => h ((singularityTest_aux ρ hρ q hq P hP hqP).mpr ⟨J, hJcard, hli⟩)
    rw [linearIndepOn_iff_notMem_span] at hnli
    push Not at hnli
    obtain ⟨j, hj, hjspan⟩ := hnli
    rw [← Finset.coe_erase] at hjspan
    obtain ⟨t, ht, htm⟩ := (exists_mul_mem_iff_toCotangent_mem_span P q hqP j _).mpr hjspan
    exact ⟨t, ht, j, Finset.mem_coe.mp hj, htm⟩
  obtain ⟨t, ht, hall⟩ := exists_notMem_forall_of_mul_closed P 𝒥
    (fun J t => ∃ j ∈ J, t * q j ∈ P ^ 2 ⊔ Ideal.span (q '' ↑(J.erase j)))
    (fun J t u ⟨j, hj, hmem⟩ => ⟨j, hj, by rw [mul_assoc]; exact Ideal.mul_mem_left _ u hmem⟩)
    key
  exact ⟨t, ht, fun J hJ => hall J (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hJ⟩)⟩

end SingularityTest

section Parameters

/-! ### Parameters adapted to a prime -/

variable {R : Type u} [CommRing R]

/-- **Prime avoidance step.** Let `I, B` be ideals of a Noetherian ring with `I ⊄ B`, and let `s`
be a set of at most `n` elements all of whose minimal primes have height `≥ n`, where
`n < ht(I)`. Then some `x ∈ I ∖ B` is such that all minimal primes of `(s, x)` have height
`≥ n + 1`. -/
private theorem exists_mem_notMem_forall_height_le [IsNoetherianRing R] (I B : Ideal R)
    (hIB : ¬ I ≤ B) (s : Set R) (hs : s.Finite) {n : ℕ} (hsn : s.ncard ≤ n)
    (hht : (n : ℕ∞) < I.height)
    (hmin : ∀ Q ∈ (Ideal.span s).minimalPrimes, (n : ℕ∞) ≤ Q.height) :
    ∃ x ∈ I, x ∉ B ∧ ∀ Q ∈ (Ideal.span (insert x s)).minimalPrimes,
      ((n + 1 : ℕ) : ℕ∞) ≤ Q.height := by
  classical
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing R (Ideal.span s)
  set F : Finset (Ideal R) := insert B hfin.toFinset with hF
  have hnot : ¬ (I : Set R) ⊆ ⋃ J ∈ (F : Set (Ideal R)), ((fun J : Ideal R => J) J : Set R) := by
    rw [Ideal.subset_union_prime (f := fun J : Ideal R => J) B B]
    · rintro ⟨J, hJ, hIJ⟩
      rcases Finset.mem_insert.mp hJ with rfl | hJ
      · exact hIB hIJ
      · rw [Set.Finite.mem_toFinset] at hJ
        have := hJ.1.1
        have hle : J.height ≤ s.ncard := Ideal.height_le_ncard_of_mem_minimalPrimes_span hs hJ
        have hsn' : (s.ncard : ℕ∞) ≤ n := by exact_mod_cast hsn
        exact absurd (hht.trans_le ((Ideal.height_mono hIJ).trans (hle.trans hsn')))
          (lt_irrefl _)
    · intro J hJ hJB _
      rcases Finset.mem_insert.mp hJ with rfl | hJ
      · exact absurd rfl hJB
      · rw [Set.Finite.mem_toFinset] at hJ
        exact hJ.1.1
  obtain ⟨x, hxI, hxU⟩ := Set.not_subset.mp hnot
  have hxF : ∀ J ∈ F, x ∉ J := fun J hJ hxJ => hxU (Set.mem_iUnion₂.mpr ⟨J, hJ, hxJ⟩)
  refine ⟨x, hxI, hxF B (Finset.mem_insert_self _ _), ?_⟩
  intro Q' hQ'
  have := hQ'.1.1
  have hsQ' : Ideal.span s ≤ Q' := (Ideal.span_mono (Set.subset_insert x s)).trans hQ'.1.2
  have hxQ' : x ∈ Q' := hQ'.1.2 (Ideal.subset_span (Set.mem_insert x s))
  obtain ⟨Q, hQ, hQQ'⟩ := Ideal.exists_minimalPrimes_le hsQ'
  have := hQ.1.1
  have hxQ : x ∉ Q :=
    hxF Q (Finset.mem_insert_of_mem ((Set.Finite.mem_toFinset hfin).mpr hQ))
  have hlt : Q < Q' := lt_of_le_of_ne hQQ' fun h => hxQ (h ▸ hxQ')
  calc ((n + 1 : ℕ) : ℕ∞) = (n : ℕ∞) + 1 := by push_cast; rfl
    _ ≤ Q.height + 1 := by gcongr; exact hmin Q hQ
    _ ≤ Q'.height := Ideal.height_add_one_le_of_lt_of_isPrime hlt

/-- The classes in the cotangent space of `R_P` of the images of the elements of `P` span it. -/
private theorem span_toCotangent_algebraMap_eq_top [IsNoetherianRing R] (P : Ideal R)
    [P.IsPrime] :
    Submodule.span (ResidueField (Localization.AtPrime P))
      ((maximalIdeal (Localization.AtPrime P)).toCotangent ''
        {m | ∃ p ∈ P, (m : Localization.AtPrime P) = algebraMap R _ p}) = ⊤ := by
  rw [CotangentSpace.span_image_eq_top_iff, span_eq_top_iff_le_span_coe]
  have himg : ((↑) : maximalIdeal (Localization.AtPrime P) → Localization.AtPrime P) ''
      {m | ∃ p ∈ P, (m : Localization.AtPrime P) = algebraMap R _ p} =
      algebraMap R (Localization.AtPrime P) '' P := by
    ext z
    constructor
    · rintro ⟨m, ⟨p, hp, hmp⟩, rfl⟩
      exact ⟨p, hp, hmp.symm⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨algebraMap R _ p, (IsLocalization.AtPrime.to_map_mem_maximal_iff _ P _).mpr hp⟩,
        ⟨p, hp, rfl⟩, rfl⟩
  rw [himg, ← Localization.AtPrime.map_eq_maximalIdeal]
  exact le_rfl

/-- **Elements of `P` with independent cotangent classes, avoiding small primes.** If `R_P` has
cotangent space of dimension `ht(P) = l`, then for each `i ≤ l` there are `v₁, …, v_i ∈ P` with
linearly independent classes in the cotangent space of `R_P`, all of whose minimal primes have
height `≥ i`. -/
private theorem exists_cotangent_family [IsNoetherianRing R] (P : Ideal R) [P.IsPrime] {l : ℕ}
    (hP : P.height = l)
    (hcot : Module.finrank (ResidueField (Localization.AtPrime P))
      (CotangentSpace (Localization.AtPrime P)) = l) :
    ∀ i ≤ l, ∃ v : Fin i → R, ∃ y : Fin i → maximalIdeal (Localization.AtPrime P),
      (∀ j, v j ∈ P) ∧ (∀ j, (y j : Localization.AtPrime P) = algebraMap R _ (v j)) ∧
      LinearIndependent (ResidueField (Localization.AtPrime P))
        ((maximalIdeal (Localization.AtPrime P)).toCotangent ∘ y) ∧
      ∀ Q ∈ (Ideal.span (Set.range v)).minimalPrimes, (i : ℕ∞) ≤ Q.height := by
  intro i
  induction i with
  | zero =>
    intro _
    exact ⟨Fin.elim0, Fin.elim0, fun j => j.elim0, fun j => j.elim0,
      linearIndependent_empty_type, fun Q _ => by simp⟩
  | succ i ih =>
    intro hi
    obtain ⟨v, y, hvP, hyv, hli, hmin⟩ := ih (by omega)
    set Sₚ := Localization.AtPrime P
    set B := Ideal.comap (algebraMap R Sₚ)
      (maximalIdeal Sₚ ^ 2 ⊔ Ideal.span (Set.range fun j => (y j : Sₚ))) with hB
    have hPB : ¬ P ≤ B := by
      intro hPB
      have hsub : (maximalIdeal Sₚ).toCotangent '' {m | ∃ p ∈ P, (m : Sₚ) = algebraMap R _ p} ⊆
          Submodule.span (ResidueField Sₚ) (Set.range ((maximalIdeal Sₚ).toCotangent ∘ y)) := by
        rintro _ ⟨m, ⟨p, hp, hmp⟩, rfl⟩
        have h1 := hPB hp
        rw [hB, Ideal.mem_comap, ← hmp] at h1
        have := (toCotangent_mem_span_image_iff y Set.univ m).mpr (by rwa [Set.image_univ])
        rwa [Set.image_univ] at this
      have htop : Submodule.span (ResidueField Sₚ)
          (Set.range ((maximalIdeal Sₚ).toCotangent ∘ y)) = ⊤ := by
        rw [eq_top_iff, ← span_toCotangent_algebraMap_eq_top P]
        exact Submodule.span_le.mpr hsub
      have hrank := finrank_span_eq_card hli
      rw [htop, finrank_top, hcot, Fintype.card_fin] at hrank
      omega
    obtain ⟨x, hxP, hxB, hxmin⟩ := exists_mem_notMem_forall_height_le P B hPB (Set.range v)
      (Set.finite_range v) (ncard_range_fin_le v)
      (by rw [hP]; exact_mod_cast (show i < l by omega)) hmin
    have hxm : algebraMap R Sₚ x ∈ maximalIdeal Sₚ :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff _ P _).mpr hxP
    refine ⟨Fin.cons x v, Fin.cons ⟨algebraMap R Sₚ x, hxm⟩ y, ?_, ?_, ?_, ?_⟩
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · simpa using hxP
      · simpa using hvP j
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · rfl
      · simpa using hyv j
    · rw [Fin.comp_cons, linearIndependent_finCons]
      refine ⟨hli, fun hmem => hxB ?_⟩
      rw [hB, Ideal.mem_comap]
      have := (toCotangent_mem_span_image_iff y Set.univ ⟨algebraMap R Sₚ x, hxm⟩).mp
        (by rwa [Set.image_univ])
      rwa [Set.image_univ] at this
    · rw [Fin.range_cons]
      exact hxmin

/-- **Parameters adapted to a prime of a regular local ring.** Let `R` be a regular local ring of
dimension `l + k` and `P` a prime of height `l`. There are `v₁, …, v_l ∈ P` generating `P` after
localization at `P` (i.e. `s P ⊆ (v)` for some `s ∉ P`), and `w₁, …, w_k ∈ 𝔪` such that
`(v, w)` contains a power of `𝔪`. -/
theorem exists_fin_mem_and_mul_mem_span_and_pow_le [IsRegularLocalRing R] (P : Ideal R)
    [P.IsPrime] {l k : ℕ} (hP : P.height = l) (hdim : ringKrullDim R = (l + k : ℕ)) :
    ∃ v : Fin l → R, (∀ i, v i ∈ P) ∧ (∃ s ∉ P, ∀ x ∈ P, s * x ∈ Ideal.span (Set.range v)) ∧
      ∃ w : Fin k → R, (∀ i, w i ∈ maximalIdeal R) ∧
        ∃ N, maximalIdeal R ^ N ≤ Ideal.span (Set.range v) ⊔ Ideal.span (Set.range w) := by
  classical
  have hR : IsRegularLocalRing R := inferInstance
  have : IsRegularRing R := ((IsLocalRing.isRegularRing_tfae (R := R)).out 1 3).mp hR
  set Sₚ := Localization.AtPrime P
  have hcot : Module.finrank (ResidueField Sₚ) (CotangentSpace Sₚ) = l := by
    have h1 : ((maximalIdeal Sₚ).spanFinrank : WithBot ℕ∞) = ringKrullDim Sₚ :=
      IsRegularLocalRing.spanFinrank_maximalIdeal
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height P Sₚ, hP,
      spanFinrank_maximalIdeal_eq_finrank_cotangentSpace] at h1
    exact_mod_cast h1
  obtain ⟨v, y, hvP, hyv, hli, hmin⟩ := exists_cotangent_family P hP hcot l le_rfl
  refine ⟨v, hvP, ?_, ?_⟩
  · have hspan : Submodule.span (ResidueField Sₚ)
        (Set.range ((maximalIdeal Sₚ).toCotangent ∘ y)) = ⊤ :=
      hli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, hcot])
    rw [Set.range_comp, CotangentSpace.span_image_eq_top_iff, span_eq_top_iff_le_span_coe]
      at hspan
    have hmap : Ideal.span (((↑) : maximalIdeal Sₚ → Sₚ) '' Set.range y) =
        (Ideal.span (Set.range v)).map (algebraMap R Sₚ) := by
      rw [Ideal.map_span, ← Set.range_comp, ← Set.range_comp]
      congr 1
      exact congrArg Set.range (funext hyv)
    rw [hmap] at hspan
    have hloc : ∀ x ∈ P, ∃ t ∉ P, t * x ∈ Ideal.span (Set.range v) := fun x hx =>
      (exists_mul_mem_iff_mem_map P _ x).mpr
        (hspan ((IsLocalization.AtPrime.to_map_mem_maximal_iff _ P _).mpr hx))
    obtain ⟨G, hG⟩ := (IsNoetherian.noetherian P : P.FG)
    obtain ⟨s, hs, hsG⟩ := exists_notMem_forall_of_mul_closed P G
      (fun g t => t * g ∈ Ideal.span (Set.range v))
      (fun g t u h => by rw [mul_assoc]; exact Ideal.mul_mem_left _ u h)
      (fun g hg => hloc g (hG ▸ Submodule.subset_span hg))
    refine ⟨s, hs, fun x hx => ?_⟩
    have hle : P ≤ Submodule.comap (LinearMap.mulLeft R s) (Ideal.span (Set.range v)) := by
      rw [← hG, Submodule.span_le]
      intro g hg
      exact hsG g hg
    exact hle hx
  · have hm : (maximalIdeal R).height = (l + k : ℕ) := by
      have := maximalIdeal_height_eq_ringKrullDim (R := R)
      rw [hdim] at this
      exact_mod_cast this
    have key : ∀ j ≤ k, ∃ w : Fin j → R, (∀ i, w i ∈ maximalIdeal R) ∧
        ∀ Q ∈ (Ideal.span (Set.range v ∪ Set.range w)).minimalPrimes,
          ((l + j : ℕ) : ℕ∞) ≤ Q.height := by
      intro j
      induction j with
      | zero =>
        intro _
        refine ⟨Fin.elim0, fun i => i.elim0, ?_⟩
        simpa using hmin
      | succ j ih =>
        intro hj
        obtain ⟨w, hw, hwmin⟩ := ih (by omega)
        have hbot : ¬ maximalIdeal R ≤ ⊥ := by
          intro h
          have h1 := Ideal.height_mono h
          rw [Ideal.height_bot, hm] at h1
          have h2 : l + k = 0 := by exact_mod_cast nonpos_iff_eq_zero.mp h1
          omega
        obtain ⟨x, hxm, -, hxmin⟩ := exists_mem_notMem_forall_height_le (maximalIdeal R) ⊥ hbot
          (Set.range v ∪ Set.range w) ((Set.finite_range v).union (Set.finite_range w))
          ((Set.ncard_union_le _ _).trans
            (add_le_add (ncard_range_fin_le v) (ncard_range_fin_le w)))
          (by rw [hm]; exact_mod_cast (show l + j < l + k by omega)) hwmin
        refine ⟨Fin.cons x w, fun i => Fin.cases hxm hw i, ?_⟩
        rw [Fin.range_cons, Set.union_insert]
        exact hxmin
    obtain ⟨w, hw, hwmin⟩ := key k le_rfl
    refine ⟨w, hw, ?_⟩
    rw [← Ideal.span_union]
    have hrad : maximalIdeal R ≤ (Ideal.span (Set.range v ∪ Set.range w)).radical := by
      rw [← Ideal.sInf_minimalPrimes]
      refine le_sInf fun Q hQ => ?_
      have := hQ.1.1
      have hQm : Q ≤ maximalIdeal R := le_maximalIdeal this.ne_top
      rw [Ideal.eq_of_le_of_height_le Q hQm (by rw [hm]; exact hwmin Q hQ)]
    exact Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)

end Parameters

end Stacks.ApproximationProperty

end
