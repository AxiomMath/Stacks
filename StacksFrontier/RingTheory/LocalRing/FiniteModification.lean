module

import StacksFrontier.RingTheory.Depth.Nakayama
import StacksFrontier.RingTheory.Depth.ShortExact
import StacksFrontier.RingTheory.Depth.Dimension
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.PicardGroup

public import StacksFrontier.RingTheory.Depth.Criteria
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Basic
public import StacksFrontier.RingTheory.RegularLocalRing.MaximalCohenMacaulay
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

universe u

/-!
# Kollár's four cases for a Noetherian local ring

Let `(R, 𝔪)` be a Noetherian local ring. Exactly one of the following holds: `R` is Artinian;
`R` is regular of dimension `1`; `depth_𝔪(R) ≥ 2`; or there is a finite ring map `R → R'` to a
nonzero ring which is not an isomorphism, whose kernel and cokernel are annihilated by a power
of `𝔪`, and for which `𝔪` is not an associated prime of `R'`.

## Main results

* `Stacks.LocalRing.KollarCases.solution`: the proof of [StackProject 0BHZ].

## Implementation notes

The source produces the ring `R'` of the fourth case, in the hardest branch, as `R[y/x]` inside
`R_x`, its finiteness coming from the determinantal trick applied to `f ↦ yf/x : 𝔪 → 𝔪`. Here it
is produced instead as the full stabiliser

`R' = {z ∈ R_x | z · 𝔪 ⊆ 𝔪}`

of the image of `𝔪` in `R_x`, a subalgebra of `R_x` because the stabiliser of a submodule is
closed under multiplication. This ring contains `R[y/x]`, and all five conditions of the fourth
case are immediate for it: it is finite over `R` because `z · x ∈ 𝔪 ⊆ R` puts it inside the
cyclic module `x⁻¹ R`, so no integrality argument is needed; its cokernel is annihilated by `𝔪`
itself, so the exponent `n` can be taken to be `1`; and `𝔪` is not an associated prime of it
because `x` is invertible in `R_x`.

The exclusions the source leaves to the reader are proved by the same two invariants it uses for
the two it does prove: cases (1) and (2) are separated from case (3) as in the source, and the
remaining four combinations follow from `depth_𝔪(R) ≤ dim R` (Lemma 00LK) together with the
observation that a nonzero finite module over an Artinian local ring always has `𝔪` as an
associated prime.

That case (2) excludes case (4) is, after Lemma 00NT has made `R'` free, the statement that two
distinct vectors of a basis cannot both be carried into one cyclic submodule without the two
scalars used multiplying to zero; the scalars here range over `𝔪 ^ n`, so `𝔪 ^ (2 n) = 0` and `R`
is Artinian after all.

## References

* [StackProject 0BHZ](https://stacks.math.columbia.edu/tag/0BHZ)
-/



namespace Stacks.LocalRing

section Shared

open IsLocalRing Pointwise RingTheory.Sequence

/-- **Depth is at most the dimension** (Lemma 00LK for `M = R`): for a local ring `R`, the
`𝔪`-depth of `R` is at most the Krull dimension of `R`. -/
public lemma depth_le_ringKrullDim (R : Type u) [CommRing R] [IsLocalRing R] :
    (Module.depth R (maximalIdeal R) R : WithBot ℕ∞) ≤ ringKrullDim R := by
  have h := Module.depth_le_supportDim R (maximalIdeal R) R
    (by rw [Ideal.smul_eq_mul, Ideal.mul_top]; exact (maximalIdeal.isMaximal R).ne_top)
  rwa [Module.supportDim_self_eq_ringKrullDim] at h

/-- The Krull dimension of an Artinian Noetherian ring is at most `0`. -/
private lemma ringKrullDim_le_zero_of_artinian (R : Type u) [CommRing R]
    [IsNoetherianRing R] (h : IsArtinianRing R) : ringKrullDim R ≤ 0 :=
  Ring.krullDimLE_iff.1 (isArtinianRing_iff_krullDimLE_zero.1 h)

/-- A local ring of dimension at most `1` does not have depth `≥ 2`. -/
private lemma not_two_le_depth_of_ringKrullDim_le_one (R : Type u) [CommRing R] [IsLocalRing R]
    (hdim : ringKrullDim R ≤ 1) : ¬ 2 ≤ Module.depth R (maximalIdeal R) R := by
  intro hd
  have h2 : ((2 : ℕ∞) : WithBot ℕ∞) ≤ 1 :=
    le_trans (WithBot.coe_le_coe.2 hd) ((depth_le_ringKrullDim R).trans hdim)
  norm_num at h2

end Shared

end Stacks.LocalRing

namespace Stacks.LocalRing.KollarCases

open IsLocalRing Pointwise RingTheory.Sequence

/-- Case (4) of Kollár's list: a finite ring map `R → R'` to a nonzero ring, not an isomorphism,
whose kernel and cokernel are annihilated by a power of `𝔪`, and for which `𝔪` is not an
associated prime of `R'`. -/
private def HasSmallFiniteExtension (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R'), Nontrivial R' ∧
    Module.Finite R R' ∧ ¬ Function.Bijective (algebraMap R R') ∧
    maximalIdeal R ∉ associatedPrimes R R' ∧
    ∃ n : ℕ, maximalIdeal R ^ n * RingHom.ker (algebraMap R R') = ⊥ ∧
      maximalIdeal R ^ n • (⊤ : Submodule R R') ≤
        LinearMap.range (Algebra.linearMap R R')

/-! ### Generalities -/

/-- An `M`-regular sequence inside `I` is a lower bound for `depth_I(M)`. -/
private lemma le_depth_of_isRegular {R : Type u} [CommRing R] (I : Ideal R)
    (M : Type*) [AddCommGroup M] [Module R M] (rs : List R)
    (hmem : ∀ r ∈ rs, r ∈ I) (hreg : IsRegular M rs) :
    (rs.length : ℕ∞) ≤ Module.depth R I M := by
  rw [Module.depth]
  split
  · exact le_top
  · exact le_iSup_of_le rs (le_iSup_of_le ⟨hmem, hreg⟩ le_rfl)

/-- The only use made below of the hypothesis that `𝔪` is an associated prime of `M`: some
nonzero element of `M` is killed by the whole of `𝔪`. -/
private lemma exists_ne_zero_smul_eq_zero (R : Type u) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (M : Type*) [AddCommGroup M] [Module R M]
    (h : maximalIdeal R ∈ associatedPrimes R M) :
    ∃ w : M, w ≠ 0 ∧ ∀ r ∈ maximalIdeal R, r • w = 0 := by
  obtain ⟨-, w, hw⟩ := isAssociatedPrime_iff.1 h
  refine ⟨w, ?_, fun r hr =>
    (Submodule.mem_bot R).1 (Submodule.mem_colon_singleton.1 (hw ▸ hr))⟩
  rintro rfl
  have h1 : (1 : R) ∈ maximalIdeal R := by rw [hw]; simp [Submodule.mem_colon_singleton]
  exact (maximalIdeal.isMaximal R).ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)

/-- Lemma 00LL over a local ring: if `𝔪` is not an associated prime of the finite module `M`,
then some element of `𝔪` is a nonzerodivisor on `M`. -/
private lemma exists_isSMulRegular (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (h : maximalIdeal R ∉ associatedPrimes R M) : ∃ x ∈ maximalIdeal R, IsSMulRegular M x :=
  (Ideal.exists_mem_isSMulRegular_iff_forall_associatedPrimes_not_le (maximalIdeal R) M
    (associatedPrimes.finite R M)).2 fun _q hq hle =>
      h (((maximalIdeal.isMaximal R).eq_of_le hq.1.ne_top hle) ▸ hq)

/-- Over a Noetherian local ring, if `𝔪` is not an associated prime of the nonzero finite module
`M` then `𝔪` contains a one-term `M`-regular sequence. -/
private lemma exists_isRegular_singleton (R : Type u) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (h : maximalIdeal R ∉ associatedPrimes R M) : ∃ x ∈ maximalIdeal R, IsRegular M [x] := by
  obtain ⟨x, hx, hxreg⟩ := exists_isSMulRegular R M h
  refine ⟨x, hx, (isRegular_cons_iff M x []).2 ⟨hxreg, ?_⟩⟩
  have : Nontrivial (QuotSMulTop x M) := nontrivial_quotSMulTop_of_mem_maximalIdeal M hx
  exact IsRegular.nil R _

/-- A module without `𝔪` as an associated prime has positive depth. -/
private lemma one_le_depth_of_notMem_associatedPrimes (R : Type u) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] (h : maximalIdeal R ∉ associatedPrimes R M) :
    1 ≤ Module.depth R (maximalIdeal R) M := by
  obtain ⟨x, hxm, hx⟩ := exists_isRegular_singleton R M h
  simpa using Module.le_depth_of_isRegular (maximalIdeal R) (M := M) (rs := [x])
    (by simpa using hxm) hx

/-- A module on which no element of `𝔪` acts regularly has depth zero. -/
private lemma depth_eq_zero_of_forall_not_isSMulRegular (R : Type u) [CommRing R] [IsLocalRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (h : ∀ x ∈ maximalIdeal R, ¬ IsSMulRegular M x) :
    Module.depth R (maximalIdeal R) M = 0 := by
  rw [Module.depth]
  split
  · rename_i hc
    exact absurd hc (Module.maximalIdeal_smul_top_ne_top (R := R) M)
  · refine le_antisymm (iSup₂_le ?_) zero_le
    rintro rs ⟨hmem, hreg⟩
    match rs with
    | [] => simp
    | a :: l =>
      exact absurd ((isRegular_cons_iff M a l).1 hreg).1 (h a (hmem a (by simp)))

/-- Positive depth produces a nonzerodivisor in `𝔪`; the converse of
`one_le_depth_of_notMem_associatedPrimes` up to the associated prime. -/
private lemma exists_isSMulRegular_of_one_le_depth (R : Type u) [CommRing R] [IsLocalRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (h : 1 ≤ Module.depth R (maximalIdeal R) M) : ∃ x ∈ maximalIdeal R, IsSMulRegular M x := by
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  rw [depth_eq_zero_of_forall_not_isSMulRegular R M hcon] at h
  norm_num at h

/-- A nonzero finite module annihilated by a power of `𝔪` has depth zero. -/
private lemma depth_eq_zero_of_pow_smul_eq_bot (R : Type u) [CommRing R] [IsLocalRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M] (n : ℕ)
    (h : maximalIdeal R ^ n • (⊤ : Submodule R M) = ⊥) :
    Module.depth R (maximalIdeal R) M = 0 := by
  refine depth_eq_zero_of_forall_not_isSMulRegular R M fun a ha hareg => ?_
  obtain ⟨c, hc⟩ := exists_ne (0 : M)
  refine hc ((hareg.pow n) ?_)
  have hmem : a ^ n • c ∈ maximalIdeal R ^ n • (⊤ : Submodule R M) :=
    Submodule.smul_mem_smul (Ideal.pow_mem_pow ha n) Submodule.mem_top
  rw [h] at hmem
  simpa using hmem

/-- An ideal annihilated by an ideal that contains a nonzerodivisor is zero. -/
private lemma eq_bot_of_mul_eq_bot {R : Type u} [CommRing R] {I J : Ideal R} {x : R}
    (hxI : x ∈ I) (hxreg : IsSMulRegular R x) (h : I * J = ⊥) : J = ⊥ := by
  refine eq_bot_iff.2 fun q hq => Ideal.mem_bot.2 (hxreg (a₁ := q) (a₂ := 0) ?_)
  have hx : x * q ∈ I * J := Ideal.mul_mem_mul hxI hq
  rw [h, Ideal.mem_bot] at hx
  simpa [smul_eq_mul] using hx

/-- Membership in the annihilator of an ideal, written multiplicatively. -/
private lemma mem_annihilator_iff {R : Type u} [CommRing R] {I : Ideal R} {a : R} :
    a ∈ Submodule.annihilator I ↔ ∀ i ∈ I, a * i = 0 := by
  simp [Submodule.mem_annihilator, smul_eq_mul]

/-- If `r a` kills `J` for every `r ∈ I`, then `a` kills `J I`. -/
private lemma mem_annihilator_mul {R : Type u} [CommRing R] {I J : Ideal R} {a : R}
    (h : ∀ r ∈ I, r * a ∈ Submodule.annihilator J) : a ∈ Submodule.annihilator (J * I) := by
  rw [mem_annihilator_iff]
  intro z hz
  refine Submodule.mul_induction_on hz (fun i hi r hr => ?_) fun p q hp hq => by
    rw [mul_add, hp, hq, add_zero]
  calc a * (i * r) = r * a * i := by ring
    _ = 0 := mem_annihilator_iff.1 (h r hr) i hi

/-- Two distinct vectors of a basis cannot both be carried into the cyclic submodule generated by
`v` unless the two scalars used multiply to zero. -/
private lemma mul_eq_zero_of_smul_basis_eq_smul {R : Type u} {M ι : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (b : Module.Basis ι R M) {i j : ι} (hij : i ≠ j) {v : M}
    {p q a c : R} (hp : p • b i = a • v) (hq : q • b j = c • v) : p * q = 0 := by
  have key : (a * q) • b j = (c * p) • b i := by
    rw [mul_smul, hq, mul_smul, hp, smul_comm]
  have haq : a * q = 0 := by
    by_contra hne
    exact hij (b.linearIndependent.eq_of_smul_apply_eq_smul_apply _ _ j i hne key).symm
  have hz : (q * p) • b i = 0 := by
    rw [mul_smul, hp, smul_smul, mul_comm q a, haq, zero_smul]
  rw [mul_comm]
  exact b.linearIndependent.eq_zero_of_smul_mem_span i (q * p) (by simp [hz])

/-! ### The exclusions -/

private lemma not_two_le_depth_of_isArtinianRing (R : Type u) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (h : IsArtinianRing R) : ¬ 2 ≤ Module.depth R (maximalIdeal R) R :=
  not_two_le_depth_of_ringKrullDim_le_one R
    ((ringKrullDim_le_zero_of_artinian R h).trans zero_le_one)

/-- An Artinian local ring has dimension zero, so it is not of dimension one. -/
private lemma not_isArtinianRing_of_ringKrullDim_eq_one (R : Type u) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (hdim : ringKrullDim R = 1) : ¬ IsArtinianRing R := by
  intro h
  have h0 := ringKrullDim_le_zero_of_artinian R h
  rw [hdim] at h0
  norm_num at h0

/-- Over an Artinian local ring `𝔪` is an associated prime of every nonzero module: the only
prime available is `𝔪` itself. -/
private lemma maximalIdeal_mem_associatedPrimes (R : Type u) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] [IsArtinianRing R] (M : Type*) [AddCommGroup M] [Module R M] [Nontrivial M] :
    maximalIdeal R ∈ associatedPrimes R M := by
  obtain ⟨q, hq⟩ := associatedPrimes.nonempty R M
  have : q.IsPrime := hq.1
  exact IsLocalRing.eq_maximalIdeal (IsArtinianRing.isMaximal_of_isPrime q) ▸ hq

private lemma not_hasSmallFiniteExtension_of_isArtinianRing (R : Type u) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (h : IsArtinianRing R) :
    ¬ HasSmallFiniteExtension R := by
  rintro ⟨R', _, _, hnt, -, -, hass, -⟩
  have := h
  exact hass (maximalIdeal_mem_associatedPrimes R R')

/-! ### Case (3) excludes case (4) -/

/-- With `depth_𝔪(R) ≥ 2` an algebra `R'` as in case (4) is already all of `R`: the quotient
`R'/R` is a finite module killed by `𝔪 ^ n`, hence of depth `0`, while the depth estimate for the
exact sequence `0 → R → R' → R'/R → 0` (Lemma 00LX) forces its depth to be at least `1`. -/
private lemma range_algebraMap_eq_top_of_two_le_depth (R : Type u) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (R' : Type u) [CommRing R'] [Algebra R R']
    [Nontrivial R'] [Module.Finite R R'] (hinj : Function.Injective (algebraMap R R'))
    (hass : maximalIdeal R ∉ associatedPrimes R R')
    (hd : 2 ≤ Module.depth R (maximalIdeal R) R) {n : ℕ}
    (hcok : maximalIdeal R ^ n • (⊤ : Submodule R R') ≤
      LinearMap.range (Algebra.linearMap R R')) :
    LinearMap.range (Algebra.linearMap R R') = ⊤ := by
  set N := LinearMap.range (Algebra.linearMap R R') with hN
  by_contra hne
  obtain ⟨z₀, hz₀⟩ : ∃ z : R', z ∉ N := by
    by_contra hcc
    exact hne (Submodule.eq_top_iff'.2 (by simpa using hcc))
  have : Nontrivial (R' ⧸ N) :=
    nontrivial_of_ne (N.mkQ z₀) 0 (by
      simpa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using hz₀)
  have hexact : Function.Exact (Algebra.linearMap R R') N.mkQ := fun b => by
    simp [hN, Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
  have hquot := (Module.min_depth_le_depth_of_exact (maximalIdeal R) hexact hinj
    N.mkQ_surjective).2.1
  have hlow : (1 : ℕ∞) ≤ Module.depth R (maximalIdeal R) (R' ⧸ N) := by
    refine le_trans (le_min (one_le_depth_of_notMem_associatedPrimes R R' hass) ?_) hquot
    exact ((by decide : (1 : ℕ∞) ≤ 2 - 1)).trans (tsub_le_tsub_right hd 1)
  have hzero : Module.depth R (maximalIdeal R) (R' ⧸ N) = 0 := by
    refine depth_eq_zero_of_pow_smul_eq_bot R (R' ⧸ N) n
      (eq_bot_iff.2 (Submodule.smul_le.2 fun p hp z _ => ?_))
    obtain ⟨w, rfl⟩ := N.mkQ_surjective z
    rw [Submodule.mem_bot, ← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hcok (Submodule.smul_mem_smul hp Submodule.mem_top)
  rw [hzero] at hlow
  norm_num at hlow

private lemma not_hasSmallFiniteExtension_of_two_le_depth (R : Type u) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (hd : 2 ≤ Module.depth R (maximalIdeal R) R) :
    ¬ HasSmallFiniteExtension R := by
  rintro ⟨R', _, _, hnt, hfin, hnb, hass, n, hker, hcok⟩
  obtain ⟨x, hxm, hxreg⟩ :=
    exists_isSMulRegular_of_one_le_depth R R (le_trans (by norm_num) hd)
  have hinj : Function.Injective (algebraMap R R') :=
    (RingHom.injective_iff_ker_eq_bot _).2
      (eq_bot_of_mul_eq_bot (Ideal.pow_mem_pow hxm n) (hxreg.pow n) hker)
  refine hnb ⟨hinj, fun z => ?_⟩
  obtain ⟨r, hr⟩ := Submodule.eq_top_iff'.1
    (range_algebraMap_eq_top_of_two_le_depth R R' hinj hass hd hcok) z
  exact ⟨r, hr⟩

/-! ### Case (2) excludes case (4) -/

private lemma not_hasSmallFiniteExtension_of_isRegularLocalRing (R : Type u) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (hreg : IsRegularLocalRing R)
    (hdim : ringKrullDim R = 1) : ¬ HasSmallFiniteExtension R := by
  classical
  rintro ⟨R', _, _, hnt, hfin, hnb, hass, n, -, hcok⟩
  obtain ⟨x, hxm, hxseq⟩ := exists_isRegular_singleton R R' hass
  -- `R'` is a maximal Cohen-Macaulay module over the regular local ring `R`, hence free.
  have : Module.Free R R' :=
    regular_mcm_free R R' ⟨[x], by simpa using hxm, hxseq, by simp [hdim]⟩
  set ι := Module.Free.ChooseBasisIndex R R'
  set b : Module.Basis ι R R' := Module.Free.chooseBasis R R'
  have hone : ∀ (p : R) (i : ι), p ∈ maximalIdeal R ^ n → ∃ a : R, p • b i = a • (1 : R') := by
    intro p i hp
    obtain ⟨a, ha⟩ := hcok (Submodule.smul_mem_smul hp (Submodule.mem_top (x := b i)))
    exact ⟨a, by rw [← ha, Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one]⟩
  -- Two distinct basis vectors would force `𝔪 ^ (2 n) = ⊥`, hence `R` Artinian of dimension one.
  have : Subsingleton ι := by
    by_contra hcon
    obtain ⟨i, j, hij⟩ := not_subsingleton_iff_nontrivial.1 hcon
    refine not_isArtinianRing_of_ringKrullDim_eq_one R hdim
      ((isArtinianRing_iff_isNilpotent_maximalIdeal R).2 ⟨2 * n, ?_⟩)
    rw [Ideal.zero_eq_bot, two_mul, pow_add, eq_bot_iff]
    refine Ideal.mul_le.2 fun p hp q hq => Ideal.mem_bot.2 ?_
    obtain ⟨a, ha⟩ := hone p i hp
    obtain ⟨c, hc⟩ := hone q j hq
    exact mul_eq_zero_of_smul_basis_eq_smul b hij ha hc
  -- So `R'` is free of rank one, and the structure map is an isomorphism.
  have : Nonempty ι := b.index_nonempty
  have : Unique ι := uniqueOfSubsingleton (Classical.arbitrary ι)
  exact hnb (Module.Free.bijective_algebraMap_of_finrank_eq_one
    (by rw [Module.finrank_eq_card_basis b, Fintype.card_unique]))

/-! ### Existence -/

/-- A Noetherian local ring which is not Artinian has dimension at least one. -/
private lemma one_le_ringKrullDim_of_not_isArtinianRing (R : Type u) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (h : ¬ IsArtinianRing R) : 1 ≤ ringKrullDim R := by
  rw [isArtinianRing_iff_krullDimLE_zero, Ring.krullDimLE_iff] at h
  exact (WithBot.one_le_iff_pos _).2 (lt_of_not_ge h)

/-- A Noetherian local ring which is not Artinian and whose maximal ideal is principal, generated
by a nonzero element, is regular of dimension one. -/
@[ega "0 16.1.1" "local Dedekind domains", ega "0 17.1.4" "more general"]
private lemma isRegularLocalRing_and_ringKrullDim_eq_one (R : Type u) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (hart : ¬ IsArtinianRing R) {t : R} (htne : t ≠ 0)
    (hmt : maximalIdeal R = Ideal.span {t}) :
    IsRegularLocalRing R ∧ ringKrullDim R = 1 := by
  have hsf : (maximalIdeal R).spanFinrank = 1 := by
    rw [hmt, Submodule.spanFinrank_singleton htne]
  have hle : ringKrullDim R ≤ 1 := by
    have h := ringKrullDim_le_spanFinrank_maximalIdeal R
    rwa [hsf, Nat.cast_one] at h
  have hdim : ringKrullDim R = 1 :=
    le_antisymm hle (one_le_ringKrullDim_of_not_isArtinianRing R hart)
  refine ⟨IsRegularLocalRing.of_spanFinrank_maximalIdeal_le R ?_, hdim⟩
  rw [hsf, hdim, Nat.cast_one]

/-- If `x = y t` with `x` a nonzerodivisor and `x ∣ y m` for every `m ∈ 𝔪`, then `𝔪 = (t)`. -/
private lemma maximalIdeal_eq_span_singleton (R : Type u) [CommRing R] [IsLocalRing R]
    {x y t : R} (hxreg : IsSMulRegular R x) (ht : y * t = x) (htm : t ∈ maximalIdeal R)
    (hyx : ∀ m ∈ maximalIdeal R, x ∣ y * m) :
    maximalIdeal R = Ideal.span {t} := by
  have hyreg : IsSMulRegular R y :=
    IsSMulRegular.of_mul (a := t) (by rwa [mul_comm t y, ht])
  refine le_antisymm (fun t' ht' => ?_) (Ideal.span_le.2 (by simpa using htm))
  obtain ⟨s, hs⟩ := hyx t' ht'
  refine Ideal.mem_span_singleton.2 ⟨s, hyreg ?_⟩
  simp only [smul_eq_mul]
  rw [hs, ← ht]
  ring

/-- The chain of ideals killed by the powers of `𝔪` stabilises: there is an `n ≥ 1` with
`(0 :_R 𝔪 ^ n) = (0 :_R 𝔪 ^ (n + 1))`. -/
private lemma exists_annihilator_pow_stabilizes (R : Type u) [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) : ∃ n : ℕ, 1 ≤ n ∧
      Submodule.annihilator (I ^ n) = Submodule.annihilator (I ^ (n + 1)) := by
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance
    (⟨fun k => Submodule.annihilator (I ^ k),
      fun a b hab => Submodule.annihilator_mono (Ideal.pow_le_pow_right hab)⟩ : ℕ →o Ideal R)
  exact ⟨max n 1, le_max_right _ _,
    (hn _ (le_max_left _ _)).symm.trans (hn _ (le_trans (le_max_left _ _) (Nat.le_succ _)))⟩

/-- If the ideal `J = (0 :_R 𝔪 ^ n)` of elements killed by `𝔪 ^ n` is nonzero, and the chain of
annihilators has stabilised at `n`, then `R → R / J` is a map as in case (4): its cokernel
vanishes, its kernel `J` is killed by `𝔪 ^ n`, and `𝔪` is not an associated prime of `R / J`
because `𝔪 a ⊆ J` forces `𝔪 ^ (n + 1) a = 0`, that is `a ∈ J`. -/
private lemma hasSmallFiniteExtension_of_annihilator_ne_bot (R : Type u) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (hart : ¬ IsArtinianRing R) {n : ℕ}
    (hstab : Submodule.annihilator (maximalIdeal R ^ n) =
      Submodule.annihilator (maximalIdeal R ^ (n + 1)))
    (hne : Submodule.annihilator (maximalIdeal R ^ n) ≠ ⊥) :
    HasSmallFiniteExtension R := by
  set J : Ideal R := Submodule.annihilator (maximalIdeal R ^ n) with hJ
  have hsm : ∀ r b : R, r • (Ideal.Quotient.mk J b) = Ideal.Quotient.mk J (r * b) :=
    fun r b => (map_mul (Ideal.Quotient.mk J) r b).symm
  have hJtop : J ≠ ⊤ := by
    intro htop
    refine hart ((isArtinianRing_iff_isNilpotent_maximalIdeal R).2 ⟨n, ?_⟩)
    rw [Ideal.zero_eq_bot, eq_bot_iff]
    intro i hi
    have h1 : (1 : R) ∈ J := htop ▸ Submodule.mem_top
    exact Ideal.mem_bot.2 (by rw [← one_mul i]; exact mem_annihilator_iff.1 (hJ ▸ h1) i hi)
  have := Submodule.Quotient.nontrivial_iff.mpr hJtop
  refine ⟨R ⧸ J, inferInstance, inferInstance, inferInstance,
    Module.Finite.of_surjective (Algebra.linearMap R (R ⧸ J)) Ideal.Quotient.mk_surjective,
    ?_, ?_, n, ?_, ?_⟩
  · -- not bijective: the kernel is `J ≠ ⊥`
    rintro ⟨hinj, -⟩
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    exact ha0 (hinj (a₂ := 0) (by simpa [Ideal.Quotient.eq_zero_iff_mem] using ha))
  · -- `𝔪` is not an associated prime of `R / J`
    intro hass
    obtain ⟨w, hw0, hw⟩ := exists_ne_zero_smul_eq_zero R (R ⧸ J) hass
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective w
    refine hw0 ?_
    rw [Ideal.Quotient.eq_zero_iff_mem, hstab, pow_succ]
    refine mem_annihilator_mul fun r hr => ?_
    rw [← hJ, ← Ideal.Quotient.eq_zero_iff_mem, ← hsm]
    exact hw r hr
  · -- the kernel is killed by `𝔪 ^ n`
    rw [eq_bot_iff]
    refine Ideal.mul_le.2 fun i hi q hq => Ideal.mem_bot.2 ?_
    have hqJ : q ∈ Submodule.annihilator (maximalIdeal R ^ n) := by
      rw [← hJ]
      simpa [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem] using hq
    rw [mul_comm]
    exact mem_annihilator_iff.1 hqJ i hi
  · -- the cokernel is zero
    rw [LinearMap.range_eq_top.2 Ideal.Quotient.mk_surjective]
    exact le_top

/-- The stabiliser of a submodule `N` of an `R`-algebra `A`: the `R`-subalgebra of those `w : A`
with `w N ⊆ N`. It is a subalgebra because `w (w' N) ⊆ w N ⊆ N`. -/
private def mulStabilizer {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (N : Submodule R A) : Subalgebra R A where
  carrier := {w | ∀ n ∈ N, w * n ∈ N}
  mul_mem' ha hb n hn := by rw [mul_assoc]; exact ha _ (hb n hn)
  one_mem' n hn := by simpa using hn
  add_mem' ha hb n hn := by simpa [add_mul] using N.add_mem (ha n hn) (hb n hn)
  zero_mem' n _ := by simp
  algebraMap_mem' c n hn := by simpa [Algebra.smul_def] using N.smul_mem c hn

private lemma mem_mulStabilizer_iff {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {N : Submodule R A} {w : A} : w ∈ mulStabilizer N ↔ ∀ n ∈ N, w * n ∈ N := Iff.rfl

/-- The hard case: `x ∈ 𝔪` a nonzerodivisor and `y` with `x ∤ y` but `y 𝔪 ⊆ x 𝔪`. Then the
stabiliser `R' = {w ∈ R_x | w · 𝔪 R_x ⊆ 𝔪 R_x}` of the image of `𝔪` in `R_x` is a map as in
case (4): it contains `y / x`, which is not in the image of `R`, and `x R' ⊆ 𝔪` puts it inside
the cyclic module `x⁻¹ R`. -/
private lemma hasSmallFiniteExtension_of_mul_maximalIdeal_le (R : Type u) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] {x y : R} (hx : x ∈ maximalIdeal R)
    (hxreg : IsSMulRegular R x) (hy : ¬ x ∣ y)
    (hyx : ∀ m ∈ maximalIdeal R, ∃ m' ∈ maximalIdeal R, y * m = x * m') :
    HasSmallFiniteExtension R := by
  classical
  set S := Localization.Away x
  set ι : R →+* S := algebraMap R S with hι
  have hAl : ∀ r : R, Algebra.linearMap R S r = ι r := fun _ => rfl
  have hinj : Function.Injective ι :=
    IsLocalization.injective S (by
      rw [Submonoid.powers_le]
      exact isRegular_iff_mem_nonZeroDivisors.1 (isLeftRegular_iff_isRegular.1 hxreg))
  obtain ⟨u, hu⟩ : IsUnit (ι x) := IsLocalization.map_units S ⟨x, Submonoid.mem_powers x⟩
  set N : Submodule R S := Submodule.map (Algebra.linearMap R S) (maximalIdeal R) with hN
  have hcancel : ∀ a : S, ↑u * a * ↑u⁻¹ = a := fun a => by
    rw [mul_comm (↑u : S) a, mul_assoc, Units.mul_inv, mul_one]
  have hmemN : ∀ w : S, w ∈ N ↔ ∃ m ∈ maximalIdeal R, ι m = w :=
    fun w => by simp [hN, Submodule.mem_map, hAl]
  have hxN : ι x ∈ N := (hmemN _).2 ⟨x, hx, rfl⟩
  -- `y / x` stabilises the image of `𝔪`, by hypothesis.
  set z : S := ι y * ↑u⁻¹ with hz
  have hzR' : z ∈ mulStabilizer N := by
    refine mem_mulStabilizer_iff.2 fun n hn => ?_
    obtain ⟨m, hm, rfl⟩ := (hmemN n).1 hn
    obtain ⟨m', hm', he⟩ := hyx m hm
    refine (hmemN _).2 ⟨m', hm', ?_⟩
    calc ι m' = ↑u * ι m' * ↑u⁻¹ := (hcancel _).symm
      _ = ι (x * m') * ↑u⁻¹ := by rw [map_mul, hu]
      _ = ι (y * m) * ↑u⁻¹ := by rw [he]
      _ = z * ι m := by rw [hz, map_mul]; ring
  set R' : Subalgebra R S := mulStabilizer N
  -- `R'` sits inside the cyclic module generated by `x⁻¹`, hence is finite over `R`.
  have hle : Subalgebra.toSubmodule R' ≤ Submodule.span R {(↑u⁻¹ : S)} := by
    intro w hw
    obtain ⟨m, hm, hme⟩ := (hmemN _).1 (mem_mulStabilizer_iff.1 hw _ hxN)
    have hwe : w = m • (↑u⁻¹ : S) := by
      rw [Algebra.smul_def, ← hι, hme, ← hu, mul_assoc, Units.mul_inv, mul_one]
    exact hwe ▸ Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hnoeth : IsNoetherian R (Submodule.span R {(↑u⁻¹ : S)}) :=
    isNoetherian_span_of_finite R (Set.finite_singleton _)
  have hSnt : Nontrivial S := ⟨⟨0, 1, fun h => one_ne_zero (hinj (by simp [← h]))⟩⟩
  refine ⟨R', inferInstance, inferInstance, inferInstance,
    Module.Finite.iff_fg.mpr (Submodule.FG.of_le_of_isNoetherian hle), ?_, ?_, 1, ?_, ?_⟩
  · -- not bijective: `y / x` is not in the image of `R`
    rintro ⟨-, hsurj⟩
    obtain ⟨r, hr⟩ := hsurj ⟨z, hzR'⟩
    have hrz : ι r = z := congrArg Subtype.val hr
    refine hy ⟨r, hinj ?_⟩
    rw [map_mul, hrz, hz, ← hu]
    rw [← mul_assoc]
    exact (hcancel _).symm
  · -- `𝔪` is not an associated prime of `R'`, because `x` is invertible in `R_x`
    intro hass
    obtain ⟨w, hw0, hw⟩ := exists_ne_zero_smul_eq_zero R R' hass
    refine hw0 (Subtype.ext ?_)
    have h1 : (↑u : S) * (w : S) = 0 := by
      rw [hu, ← Algebra.smul_def]
      exact congrArg Subtype.val (hw x hx)
    simpa using (Units.mul_right_eq_zero u).1 h1
  · -- `R → R'` is injective
    have hker : RingHom.ker (algebraMap R R') = ⊥ := by
      rw [RingHom.ker_eq_bot_iff_eq_zero]
      intro r hr
      exact hinj (by simpa using congrArg Subtype.val hr)
    rw [hker, Ideal.mul_bot]
  · -- `𝔪 R' ⊆ R`
    rw [pow_one]
    refine Submodule.smul_le.2 fun m hm w _ => ?_
    obtain ⟨m₁, hm₁, hme⟩ :=
      (hmemN _).1 (mem_mulStabilizer_iff.1 w.2 _ ((hmemN _).2 ⟨m, hm, rfl⟩))
    refine ⟨m₁, Subtype.ext ?_⟩
    show ι m₁ = ((m • w : R') : S)
    rw [hme, SetLike.val_smul, Algebra.smul_def, hι]
    ring

/-- If no nonzero element of `R` is killed by `𝔪 ^ n`, with `n ≥ 1`, then `𝔪` is not an
associated prime of `R`. -/
private lemma notMem_associatedPrimes_of_annihilator_pow_eq_bot (R : Type u) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] {n : ℕ} (hn : 1 ≤ n)
    (h : Submodule.annihilator (maximalIdeal R ^ n) = ⊥) :
    maximalIdeal R ∉ associatedPrimes R R := by
  intro hass
  obtain ⟨a, ha0, ha⟩ := exists_ne_zero_smul_eq_zero R R hass
  refine ha0 ?_
  rw [← Ideal.mem_bot, ← h, mem_annihilator_iff]
  intro i hi
  simpa [smul_eq_mul, mul_comm] using ha i (Ideal.pow_le_self (by omega) hi)

/-- If `𝔪` is an associated prime of `R / x R`, there is a `y` with `x ∤ y` and `x ∣ y m` for
every `m ∈ 𝔪`. -/
private lemma exists_not_dvd_of_maximalIdeal_mem_associatedPrimes_quotSMulTop (R : Type u)
    [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (x : R)
    (h : maximalIdeal R ∈ associatedPrimes R (QuotSMulTop x R)) :
    ∃ y : R, ¬ x ∣ y ∧ ∀ m ∈ maximalIdeal R, x ∣ y * m := by
  obtain ⟨w, hw0, hw⟩ := exists_ne_zero_smul_eq_zero R (QuotSMulTop x R) h
  obtain ⟨y, rfl⟩ := (x • (⊤ : Submodule R R)).mkQ_surjective w
  refine ⟨y, fun ⟨s, hs⟩ => hw0 ?_, fun m hm => ?_⟩
  · rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).2
      ⟨s, Submodule.mem_top, by simpa [smul_eq_mul] using hs.symm⟩
  · have h2 := hw m hm
    rw [← LinearMap.map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h2
    obtain ⟨s, -, hs⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 h2
    exact ⟨s, by rw [mul_comm]; simpa [smul_eq_mul] using hs.symm⟩

/-- Every Noetherian local ring falls into one of the four cases.

The argument, following the source: if `R` is not Artinian, let `J = (0 :_R 𝔪 ^ n)` be the
largest ideal killed by a power of `𝔪` (the chain `(0 :_R 𝔪 ^ k)` is increasing and `R` is
Noetherian, so it stabilises at some `n ≥ 1`). If `J ≠ 0` then `R → R / J` is a map as in case
(4). If `J = 0` then `𝔪` is not an associated prime of `R`, so Lemma 00LL gives a nonzerodivisor
`x ∈ 𝔪`. If `𝔪` is not an associated prime of `R / x R` the same lemma gives a second element and
`2 ≤ depth_𝔪(R)`, case (3). Otherwise there is `y` with `x ∤ y` and `y 𝔪 ⊆ x R`. If `y 𝔪 ⊆ x 𝔪`
then `y / x` lies in the stabiliser `R' = {w ∈ R_x | w · 𝔪 R_x ⊆ 𝔪 R_x}` of the image of `𝔪` in
`R_x` but not in `R`, and `R'` is a witness for case (4). Otherwise `y t = x` for some `t ∈ 𝔪`,
which makes `y` a nonzerodivisor and forces `𝔪 = (t)`, so `R` is regular of dimension one,
case (2). -/
private lemma exists_case (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
    IsArtinianRing R ∨ (IsRegularLocalRing R ∧ ringKrullDim R = 1) ∨
      2 ≤ Module.depth R (maximalIdeal R) R ∨ HasSmallFiniteExtension R := by
  classical
  by_cases hart : IsArtinianRing R
  · exact Or.inl hart
  obtain ⟨n, hn1, hstab⟩ := exists_annihilator_pow_stabilizes R (maximalIdeal R)
  by_cases hJ : Submodule.annihilator (maximalIdeal R ^ n) = ⊥
  swap
  · exact Or.inr (Or.inr (Or.inr
      (hasSmallFiniteExtension_of_annihilator_ne_bot R hart hstab hJ)))
  -- `J = 0`, so `𝔪` is not an associated prime of `R` and contains a nonzerodivisor `x`.
  obtain ⟨x, hxm, hxreg⟩ := exists_isSMulRegular R R
    (notMem_associatedPrimes_of_annihilator_pow_eq_bot R hn1 hJ)
  have hntq : Nontrivial (QuotSMulTop x R) := nontrivial_quotSMulTop_of_mem_maximalIdeal R hxm
  by_cases hass2 : maximalIdeal R ∈ associatedPrimes R (QuotSMulTop x R)
  swap
  · -- `depth ≥ 2`
    obtain ⟨y, hym, hyseq⟩ := exists_isRegular_singleton R (QuotSMulTop x R) hass2
    refine Or.inr (Or.inr (Or.inl ?_))
    have hseq : IsRegular R [x, y] := (isRegular_cons_iff R x [y]).2 ⟨hxreg, hyseq⟩
    simpa using Module.le_depth_of_isRegular (maximalIdeal R) (M := R) (rs := [x, y])
      (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr;
          rcases hr with rfl | rfl; exacts [hxm, hym]) hseq
  -- `𝔪` is an associated prime of `R / x R`: there is `y` with `x ∤ y` and `y 𝔪 ⊆ x R`.
  obtain ⟨y, hyni, hym⟩ :=
    exists_not_dvd_of_maximalIdeal_mem_associatedPrimes_quotSMulTop R x hass2
  by_cases hA : ∀ m ∈ maximalIdeal R, ∃ m' ∈ maximalIdeal R, y * m = x * m'
  · exact Or.inr (Or.inr (Or.inr
      (hasSmallFiniteExtension_of_mul_maximalIdeal_le R hxm hxreg hyni hA)))
  -- otherwise `y (m v) = x` for some `m ∈ 𝔪` and some unit `v`, and `𝔪 = (m v)`
  push Not at hA
  obtain ⟨m, hm, hm2⟩ := hA
  obtain ⟨s, hs⟩ := hym m hm
  obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.1
    (notMem_maximalIdeal.mp (fun hsm => hm2 s hsm hs))
  have hmv : y * (m * v) = x := by rw [← mul_assoc, hs, mul_assoc, hv, mul_one]
  refine Or.inr (Or.inl
    (isRegularLocalRing_and_ringKrullDim_eq_one R hart (t := m * v) ?_ ?_))
  · exact fun h0 => IsLeftRegular.ne_zero hxreg (by rw [← hmv, h0, mul_zero])
  · exact maximalIdeal_eq_span_singleton R hxreg hmv (Ideal.mul_mem_right _ _ hm) hym

/-! ### Assembly -/

public theorem solution (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
    ∃! i : Fin 4,
      ![IsArtinianRing R,
        IsRegularLocalRing R ∧ ringKrullDim R = 1,
        2 ≤ Module.depth R (maximalIdeal R) R,
        ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R'), Nontrivial R' ∧
          Module.Finite R R' ∧ ¬ Function.Bijective (algebraMap R R') ∧
          maximalIdeal R ∉ associatedPrimes R R' ∧
          ∃ n : ℕ, maximalIdeal R ^ n * RingHom.ker (algebraMap R R') = ⊥ ∧
            maximalIdeal R ^ n • (⊤ : Submodule R R') ≤
              LinearMap.range (Algebra.linearMap R R')] i := by
  have e01 : (IsRegularLocalRing R ∧ ringKrullDim R = 1) → ¬ IsArtinianRing R :=
    fun h => not_isArtinianRing_of_ringKrullDim_eq_one R h.2
  have e02 := not_two_le_depth_of_isArtinianRing R
  have e03 := not_hasSmallFiniteExtension_of_isArtinianRing R
  have e12 : (IsRegularLocalRing R ∧ ringKrullDim R = 1) →
      ¬ 2 ≤ Module.depth R (maximalIdeal R) R :=
    fun h => not_two_le_depth_of_ringKrullDim_le_one R h.2.le
  have e13 : (IsRegularLocalRing R ∧ ringKrullDim R = 1) → ¬ HasSmallFiniteExtension R :=
    fun h => not_hasSmallFiniteExtension_of_isRegularLocalRing R h.1 h.2
  have e23 := not_hasSmallFiniteExtension_of_two_le_depth R
  have huniq : ∀ i j : Fin 4,
      ![IsArtinianRing R, IsRegularLocalRing R ∧ ringKrullDim R = 1,
        2 ≤ Module.depth R (maximalIdeal R) R, HasSmallFiniteExtension R] i →
      ![IsArtinianRing R, IsRegularLocalRing R ∧ ringKrullDim R = 1,
        2 ≤ Module.depth R (maximalIdeal R) R, HasSmallFiniteExtension R] j → i = j := by
    intro i j hi hj
    fin_cases i <;> fin_cases j <;>
      first
        | rfl
        | exact absurd hi (e01 hj) | exact absurd hj (e02 hi) | exact absurd hj (e03 hi)
        | exact absurd hj (e12 hi) | exact absurd hj (e13 hi) | exact absurd hj (e23 hi)
        | exact absurd hj (e01 hi) | exact absurd hi (e02 hj) | exact absurd hi (e03 hj)
        | exact absurd hi (e12 hj) | exact absurd hi (e13 hj) | exact absurd hi (e23 hj)
  rcases exists_case R with h | h | h | h
  · exact ⟨0, h, fun j hj => huniq j 0 hj h⟩
  · exact ⟨1, h, fun j hj => huniq j 1 hj h⟩
  · exact ⟨2, h, fun j hj => huniq j 2 hj h⟩
  · exact ⟨3, h, fun j hj => huniq j 3 hj h⟩

end Stacks.LocalRing.KollarCases

/-!
# Kollár's four cases for a Noetherian local ring

Let `(R, 𝔪)` be a Noetherian local ring. Then exactly one of the following four alternatives
holds:

0. `R` is Artinian;
1. `R` is regular of dimension `1`;
2. `depth_𝔪(R) ≥ 2`;
3. there is a finite ring map `R → R'` which is not an isomorphism, whose kernel and cokernel
   are annihilated by a power of `𝔪`, for which `𝔪` is not an associated prime of `R'`, and with
   `R' ≠ 0`.

That the four cases cover everything is proved by following the largest ideal `J ⊆ R` killed by a
power of `𝔪`: if `J ≠ 0` then `R → R/J` is a map as in case 3; if `J = 0` then `𝔪` is not an
associated prime of `R`, so `𝔪` contains a nonzerodivisor `x`, and either `𝔪` is not an associated
prime of `R/xR` — whence `depth_𝔪(R) ≥ 2` — or there is `y ∉ xR` with `y𝔪 ⊆ xR`. In the latter
case, if `y𝔪 ⊆ x𝔪` the determinantal trick applied to `f ↦ yf/x : 𝔪 → 𝔪` makes `y/x ∈ R_x`
integral over `R`, and `R' = R[y/x]` is a map as in case 3; otherwise `yt = x` for some `t ∈ 𝔪`,
which forces `𝔪 = (t)` and `R` regular of dimension `1`. That no two cases hold at once is
checked in the source for cases 1 and 2 against case 3, the remaining four combinations being
left to the reader: an `R'` as in case 3 has `depth_𝔪(R') ≥ 1`, so over a regular local ring of
dimension `1` it is a finite free `R`-module (Lemma 00NT), of rank `1` because `R → R'` is an
isomorphism at the generic point, whence `R → R'` is an isomorphism after all; and if
`depth_𝔪(R) ≥ 2` then `R → R'` is injective and its cokernel has depth `≥ 1` (Lemma 00LX), so
cannot be nonzero and supported on `{𝔪}`.

## Main results

* `IsLocalRing.existsUnique_isArtinianRing_or_isRegularLocalRing_or_two_le_depth_or_exists_finite`:
  exactly one of the four alternatives above holds for a Noetherian local ring.

## Implementation notes

The source's "exactly one of the following holds" is `∃! i : Fin 4, ![P₀, P₁, P₂, P₃] i`, with
the four propositions in the source's order. This carries both halves of the assertion — that
the cases cover (`∃`) and that they are pairwise exclusive (`∀ i j, … → i = j`, the six
combinations of the source) — while writing each `Pᵢ` exactly once, which a conjunction of a
fourfold disjunction with six negated conjunctions would not.

Case 1 is `IsRegularLocalRing R ∧ ringKrullDim R = 1`, the source's own wording (Definition
00KU); it is equivalent to `R` being a discrete valuation ring, but `IsDiscreteValuationRing R`
presupposes an `IsDomain R` instance and so cannot be written down before the case is known to
hold. Case 2 is `2 ≤ Module.depth R (maximalIdeal R) R`, the depth of Definition 00LI at the
maximal ideal, taken in `ℕ∞`.

Case 3 quantifies over a type in the universe of `R` carrying `CommRing` and `Algebra R`
instances: a ring map `R → R'` and an `R`-algebra structure on `R'` are the same datum, and the
algebra spelling is what supplies the `R`-module structure that "finite", "cokernel" and
"associated prime of `R'`" all refer to. The two annihilation conditions are stated with a single
exponent `n`, which is no restriction: powers of `𝔪` decrease, so a pair of exponents is replaced
by their maximum. The kernel condition is the ideal identity `𝔪 ^ n * ker (algebraMap R R') = ⊥`.
The cokernel condition is `𝔪 ^ n • (⊤ : Submodule R R') ≤ range (Algebra.linearMap R R')`: the
`R`-module `R'/R` is annihilated by `𝔪 ^ n` exactly when `𝔪 ^ n R'` lands in the image of `R`, so
the quotient module needs no name. The clause `R' ≠ 0` is `Nontrivial R'` and cannot be dropped:
the zero algebra has kernel `R` and zero cokernel, and `𝔪` is not an associated prime of it, so
for Artinian `R` (where `𝔪 ^ n = 0` for some `n`) it would satisfy every other clause of case 3
and the exclusivity of cases 0 and 3 would fail.

"`𝔪` is not an associated prime of `R'`" is read, as in the source, over `R`:
`maximalIdeal R ∉ associatedPrimes R R'`. Mathlib defines an associated prime by `I` being the
radical of the annihilator of some element; over the Noetherian `R` of this statement that is the
classical condition `I = Ann(x)`, because the primes minimal over `Ann(x)` are associated primes
of `R ∙ x`.

Faithfulness. (1) Both hypotheses are used: `[IsLocalRing R]` is what gives the `𝔪` occurring in
cases 2 and 3, and `[IsNoetherianRing R]` cannot be dropped — a valuation ring `V` with value
group `ℚ` is local with all four cases false (it has dimension `1` so is not Artinian, it is not
Noetherian so not regular, `depth_𝔪(V) = 1` since `𝔪 ^ 2 = 𝔪` makes every `y ∈ 𝔪` a zerodivisor
on `V/xV`, and `𝔪 ^ n = 𝔪` forces an `R'` as in case 3 to satisfy `𝔪 R' ⊆ V`, i.e. `R' = V`).
(2) The base is the source's throughout: the depth, the finiteness, the kernel, the cokernel and
the associated prime are all taken over `R` along `𝔪 ⊆ R`, with no localization intervening — the
ring `R_x` of the proof sketch does not appear in the statement. (3) Case 3 is existential in the
source as well, and its four conditions are pinned on the structure map `algebraMap R R'` of the
algebra produced, not on an unnamed map; "not an isomorphism" is `¬ Function.Bijective`, which for
a ring homomorphism is exactly the failure of invertibility. (4) The instantiation is not
degenerate and each case is attained: `k[X]/(X ^ 2)` for case 0, `k[[X]]` for case 1, `k[[X, Y]]`
for case 2, and `R = k[[X, Y]]/(Y ^ 2) ⊆ R' = k[[X, Z]]/(Z ^ 2)`, `Y ↦ XZ` for case 3
(Example 00PA).

## References

* [StackProject 0BHZ](https://stacks.math.columbia.edu/tag/0BHZ), taken there from a paper of
  J. Kollár, *Variants of normality for Noetherian schemes*.
-/



open IsLocalRing in
/-- **Kollár's four cases.** For a Noetherian local ring `(R, 𝔪)` exactly one of the following
holds: (0) `R` is Artinian; (1) `R` is regular of dimension `1`; (2) `depth_𝔪(R) ≥ 2`; (3) there
is a finite ring map `R → R'` to a nonzero ring, not an isomorphism, whose kernel and cokernel
are annihilated by a power of `𝔪` and for which `𝔪` is not an associated prime of `R'`. -/
@[stacks 0BHZ "The four alternatives are indexed by `Fin 4` in the order of the tag, so that
`∃!` states both that they cover and that they are pairwise exclusive. See the module docstring
for the spelling of each one, in particular for case (4)."]
public theorem
    IsLocalRing.existsUnique_isArtinianRing_or_isRegularLocalRing_or_two_le_depth_or_exists_finite
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
    ∃! i : Fin 4,
      ![IsArtinianRing R,
        IsRegularLocalRing R ∧ ringKrullDim R = 1,
        2 ≤ Module.depth R (maximalIdeal R) R,
        ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R'), Nontrivial R' ∧
          Module.Finite R R' ∧ ¬ Function.Bijective (algebraMap R R') ∧
          maximalIdeal R ∉ associatedPrimes R R' ∧
          ∃ n : ℕ, maximalIdeal R ^ n * RingHom.ker (algebraMap R R') = ⊥ ∧
            maximalIdeal R ^ n • (⊤ : Submodule R R') ≤
              LinearMap.range (Algebra.linearMap R R')] i :=
    Stacks.LocalRing.KollarCases.solution R


/-!
# A one-dimensional local ring with non-principal maximal ideal admits a finite modification

Let `(R, 𝔪)` be a Noetherian local ring with `dim R = 1` and `dim_κ(𝔪/𝔪²) > 1`. This file proves
Stacks 00P9: there is a ring map `R → R'` which is finite, is not an isomorphism, whose kernel
and cokernel are annihilated by a power of `𝔪`, and for which `𝔪` is not an associated prime of
`R'`.

The conclusion is case (4) of Kollár's dichotomy (Lemma 0BHZ): a Noetherian local ring is
Artinian, or regular of dimension `1`, or of depth `≥ 2`, or admits such an `R'`. So the whole
content here is that the three hypotheses rule out the first three alternatives:

* `dim R = 1` rules out the Artinian case, since an Artinian Noetherian ring has dimension `≤ 0`;
* `dim_κ(𝔪/𝔪²) > 1` rules out the regular case, since a regular local ring has
  `dim_κ(𝔪/𝔪²) = dim R`, which is `1` here;
* `dim R = 1` rules out the depth `≥ 2` case, since `depth_𝔪(R) ≤ dim(Supp(R)) = dim R`
  (Lemma 00LK).

## Main results

* `Stacks.LocalRing.FiniteModification.solution`: the proof of [StackProject 00P9].

## Implementation notes

The four alternatives of Lemma 0BHZ are indexed by `Fin 4`, so ruling out the first three is
`fin_cases` on the index it produces; the fourth alternative is character-for-character the
conclusion wanted here, so no reassembly is needed once the index is known to be `3`.

`Module.depth_le_ringKrullDim`, the specialisation of Lemma 00LK to `M = R` along
`Module.supportDim_self_eq_ringKrullDim`, is a lemma of the theory that neither Mathlib nor the
source names; it is proved here as a `private` helper (and again, privately, in the proof of
Lemma 0BHZ).

## References

* [StackProject 00P9](https://stacks.math.columbia.edu/tag/00P9)
-/



namespace Stacks.LocalRing.FiniteModification

open IsLocalRing

/-- The Krull dimension of an Artinian Noetherian ring is at most `0`. -/
@[ega "0 16.1.1" "partial"]
private lemma ringKrullDim_le_zero_of_isArtinianRing (R : Type u) [CommRing R]
    [IsNoetherianRing R] (h : IsArtinianRing R) : ringKrullDim R ≤ 0 :=
  Stacks.LocalRing.ringKrullDim_le_zero_of_artinian R h

/-- A local ring whose cotangent space has dimension `> dim R` is not regular, since a regular
local ring satisfies `dim_κ(𝔪/𝔪²) = dim R`. -/
private lemma not_isRegularLocalRing_of_ringKrullDim_lt_finrank_cotangentSpace (R : Type u)
    [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (h : ringKrullDim R < (Module.finrank (ResidueField R) (CotangentSpace R) : WithBot ℕ∞)) :
    ¬ IsRegularLocalRing R := fun hR =>
  absurd ((IsRegularLocalRing.iff_finrank_cotangentSpace R).1 hR).symm h.ne

/-- **A one-dimensional local ring with non-principal maximal ideal admits a finite
modification** (Stacks 00P9): for a Noetherian local ring `(R, 𝔪)` with `dim R = 1` and
`dim_κ(𝔪/𝔪²) > 1` there is a ring map `R → R'` which is finite, is not an isomorphism, whose
kernel and cokernel are annihilated by a power of `𝔪`, and for which `𝔪` is not an associated
prime of `R'`. -/
public theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (hdim : ringKrullDim R = 1)
    (hcotangent : 1 < Module.finrank (ResidueField R) (CotangentSpace R)) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R'), Nontrivial R' ∧
      Module.Finite R R' ∧ ¬ Function.Bijective (algebraMap R R') ∧
      maximalIdeal R ∉ associatedPrimes R R' ∧
      ∃ n : ℕ, maximalIdeal R ^ n * RingHom.ker (algebraMap R R') = ⊥ ∧
        maximalIdeal R ^ n • (⊤ : Submodule R R') ≤
          LinearMap.range (Algebra.linearMap R R') := by
  obtain ⟨i, hi, -⟩ :=
    IsLocalRing.existsUnique_isArtinianRing_or_isRegularLocalRing_or_two_le_depth_or_exists_finite R
  fin_cases i
  · -- `R` is not Artinian, since `dim R = 1`.
    have := ringKrullDim_le_zero_of_isArtinianRing R hi
    rw [hdim] at this
    norm_num at this
  · -- `R` is not regular, since `dim_κ(𝔪/𝔪²) > 1 = dim R`.
    refine absurd hi.1 (not_isRegularLocalRing_of_ringKrullDim_lt_finrank_cotangentSpace R ?_)
    rw [hdim]
    exact_mod_cast hcotangent
  · -- `R` does not have depth `≥ 2`, since `depth_𝔪(R) ≤ dim R = 1`.
    exact absurd hi (not_two_le_depth_of_ringKrullDim_le_one R hdim.le)
  · exact hi

end Stacks.LocalRing.FiniteModification

/-!
# A one-dimensional local ring with non-principal maximal ideal admits a finite modification

Let `(R, 𝔪)` be a Noetherian local ring of dimension `1` whose cotangent space `𝔪/𝔪²` has
dimension `> 1` over the residue field, i.e. whose maximal ideal is not principal. Then there is
a ring map `R → R'` which is finite, is not an isomorphism, whose kernel and cokernel are
annihilated by a power of `𝔪`, and for which `𝔪` is not an associated prime of `R'`.

Such an `R'` is one step of a normalization: `Spec(R') → Spec(R)` is an isomorphism away from
`𝔪` (the kernel and cokernel are supported on `{𝔪}`), and `R'` has no `𝔪`-torsion, so it is
strictly closer to being regular than `R` is. The example `R = k[[x, y]]/(y²) ⊆ k[[x, z]]/(z²)`,
`y ↦ xz`, obtained by adjoining `y/x`, is the typical case (Example 00PA).

The reason is Kollár's dichotomy (Lemma 0BHZ): a Noetherian local ring is Artinian, or regular
of dimension `1`, or of depth `≥ 2`, or admits such an `R'`, and exactly one of these holds. The
three hypotheses of this lemma rule out the first three alternatives: `dim R = 1` says `R` is
not Artinian, `dim_κ(𝔪/𝔪²) > 1` says `𝔪` is not principal so `R` is not regular of dimension
`1`, and `depth(R) ≤ dim R = 1` (Lemma 00LK) says the depth is not `≥ 2`.

## Main results

* `IsLocalRing.exists_finite_of_ringKrullDim_eq_one_of_one_lt_finrank_cotangentSpace`: the
  existence of the finite ring map `R → R'` described above.

## Implementation notes

The conclusion is spelled exactly as case (4) of the statement of Lemma 0BHZ
(`IsLocalRing.existsUnique_isArtinianRing_or_isRegularLocalRing_or_two_le_depth_or_exists_finite`),
so that the two are interchangeable. In particular: a ring map out of `R` is an `Algebra R`
instance, which is also what supplies the `R`-module structure that "finite", "cokernel" and
"associated prime of `R'`" refer to; "not an isomorphism" is `¬ Function.Bijective (algebraMap R
R')`, which for a ring homomorphism is exactly the failure of invertibility; the cokernel
condition is `𝔪 ^ n • (⊤ : Submodule R R') ≤ LinearMap.range (Algebra.linearMap R R')`, saying
that `𝔪 ^ n R'` lands in the image of `R`, which is what it means for `R'/R` to be annihilated
by `𝔪 ^ n`, so the quotient module needs no name; and a single exponent `n` serves both
annihilation clauses, which is no restriction since powers of `𝔪` decrease.

Two additions to the source's list, neither weakening it. The clause `Nontrivial R'` is
carried over from Lemma 0BHZ; here it is automatic, since the zero algebra has kernel `R` and
`𝔪 ^ n * R = 𝔪 ^ n ≠ ⊥` for all `n` because a Noetherian local ring with nilpotent maximal ideal
is Artinian, of dimension `0`. Stating it keeps the conclusion literally case (4) of Lemma 0BHZ.
The hypothesis `dim_κ(𝔪/𝔪²) > 1` is written with Mathlib's `IsLocalRing.CotangentSpace R`, an
abbreviation for `(maximalIdeal R).Cotangent = 𝔪/𝔪²`, as a module over the residue field; it is
equivalent to `¬ (maximalIdeal R).IsPrincipal` by
`IsLocalRing.finrank_cotangentSpace_le_one_iff`, and the source's `dim(𝔪/𝔪²) > 1` is kept
because it is the source's wording and is already Mathlib's spelling of `𝔪/𝔪²`.

Faithfulness. (1) No dead hypothesis: `ringKrullDim R = 1` excludes both the Artinian case and
the depth `≥ 2` case of Lemma 0BHZ, `1 < dim_κ(𝔪/𝔪²)` excludes the regular case, and
`IsNoetherianRing R` is what makes the dichotomy available at all — for a non-Noetherian local
ring of dimension `1` with non-principal maximal ideal, such as a valuation ring with value
group `ℚ ⊕ ℚ` ordered lexicographically, `𝔪 ^ n = 𝔪` forces any `R'` as in the conclusion to
satisfy `𝔪 R' ⊆ R`, hence `R' = R`. (2) The base is the source's: the finiteness, the kernel,
the cokernel and the associated prime are all taken over `R` along `𝔪 ⊆ R`, with no
localization intervening, and the cotangent space is a vector space over the residue field of
`R`. (3) The four conditions are pinned on the structure map `algebraMap R R'` of the algebra
produced, not on an unnamed map; the statement is existential in `R'` in the source as well, and
the content is exactly that the list of four conditions is simultaneously satisfiable. (4) Not
degenerate: `R = k[[x, y]]/(y²)` has dimension `1` and `dim_κ(𝔪/𝔪²) = 2`, and
`R' = k[[x, z]]/(z²)` with `y ↦ xz` satisfies the conclusion — the map is injective with
cokernel `R'/R` generated by the image of `z = y/x` and killed by `𝔪`, and `x` is a
nonzerodivisor on `R'`, so `𝔪` is not an associated prime of `R'` (Example 00PA).

## References

* [StackProject 00P9](https://stacks.math.columbia.edu/tag/00P9)
-/



open IsLocalRing in
/-- **A one-dimensional local ring with non-principal maximal ideal admits a finite
modification.** Let `(R, 𝔪)` be a Noetherian local ring of dimension `1` with
`dim_κ(𝔪/𝔪²) > 1`, i.e. with `𝔪` not principal. Then there is a ring map `R → R'` which is
finite, is not an isomorphism, whose kernel and cokernel are annihilated by a power of `𝔪`, and
for which `𝔪` is not an associated prime of `R'`. -/
@[stacks 00P9 "The conclusion is case (4) of Lemma 0BHZ, spelled the same way there; see the
module docstring for the reading of each of the four conditions. The hypothesis
`dim(𝔪/𝔪²) > 1` is `1 < finrank (ResidueField R) (CotangentSpace R)`."]
public theorem
    IsLocalRing.exists_finite_of_ringKrullDim_eq_one_of_one_lt_finrank_cotangentSpace
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (hdim : ringKrullDim R = 1)
    (hcotangent : 1 < Module.finrank (ResidueField R) (CotangentSpace R)) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R'), Nontrivial R' ∧
      Module.Finite R R' ∧ ¬ Function.Bijective (algebraMap R R') ∧
      maximalIdeal R ∉ associatedPrimes R R' ∧
      ∃ n : ℕ, maximalIdeal R ^ n * RingHom.ker (algebraMap R R') = ⊥ ∧
        maximalIdeal R ^ n • (⊤ : Submodule R R') ≤
          LinearMap.range (Algebra.linearMap R R') :=
    Stacks.LocalRing.FiniteModification.solution R hdim hcotangent
