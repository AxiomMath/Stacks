module

public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.Subalgebra
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.SpecialElement
public import StacksFrontier.RingTheory.Nilpotent.Ideal
public import StacksFrontier.RingTheory.UniversalHomeomorphism.Examples
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Morphisms.Constructors
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.RingTheory.Localization.Away.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Universal homeomorphisms after inverting a prime

When a ring map becomes an isomorphism after inverting a prime number, its map on spectra is
a universal homeomorphism exactly when its kernel is locally nilpotent and every element of
the target has a suitable prime-power multiple and prime-power power in the image.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.universalHomeomorphism_iff_locallyNilpotent_ker_and_pow_mem_range` is the
  characterization.

## Implementation notes

The isomorphism after inverting `p` is expressed by bijectivity of the canonical map between
the principal localizations. A `p`-power is written `p ^ n`; the same exponent is used for the
multiple and the power of each target element. The forward direction runs a maximality
argument over the subalgebra of elements admitting such an exponent; the reverse direction
checks integrality and universal injectivity directly, using that a `p`-th power map is
injective in characteristic `p`.

## References

* [Stacks Project, Tag 0CNF](https://stacks.math.columbia.edu/tag/0CNF)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

private abbrev pGoodSet (A B : Type u) [CommRing A] [CommRing B] (φ : A →+* B)
    (p : ℕ) : Set B :=
  {b | ∃ n > 0, b ^ p ^ n ∈ Set.range φ ∧ p ^ n • b ∈ Set.range φ}

private theorem pGood_of_arbitrary_exponent {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (p : ℕ) {b : B} {n : ℕ}
    (hpow : b ^ p ^ n ∈ Set.range φ) (hmul : p ^ n • b ∈ Set.range φ) :
    b ∈ pGoodSet A B φ p := by
  obtain ⟨a, ha⟩ := hpow
  obtain ⟨c, hc⟩ := hmul
  refine ⟨n + 1, Nat.succ_pos n, ⟨a ^ p, ?_⟩, ⟨p • c, ?_⟩⟩
  · rw [map_pow, ha, ← pow_mul, ← pow_succ]
  · rw [map_nsmul, hc, pow_succ, mul_comm (p ^ n) p, mul_smul]

private theorem pGood_algebraMap {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (p : ℕ) (a : A) : φ a ∈ pGoodSet A B φ p :=
  pGood_of_arbitrary_exponent φ p (n := 0) ⟨a, by simp⟩ ⟨a, by simp⟩

private theorem pGood_mul {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (p : ℕ) {x y : B}
    (hx : x ∈ pGoodSet A B φ p) (hy : y ∈ pGoodSet A B φ p) :
    x * y ∈ pGoodSet A B φ p := by
  obtain ⟨n, hn, ⟨a, ha⟩, ⟨b, hb⟩⟩ := hx
  obtain ⟨m, hm, ⟨c, hc⟩, ⟨d, hd⟩⟩ := hy
  apply pGood_of_arbitrary_exponent φ p (n := n + m)
  · refine ⟨a ^ p ^ m * c ^ p ^ n, ?_⟩
    rw [map_mul, map_pow, map_pow, ha, hc, ← pow_mul, ← pow_mul,
      ← pow_add, ← pow_add, add_comm m n, mul_pow]
  · refine ⟨b * d, ?_⟩
    rw [map_mul, hb, hd, smul_mul_smul_comm, ← pow_add]

private theorem pGood_add_mem_range {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (p : ℕ) (hp : Nat.Prime p) {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) {x y : B}
    (hx₁ : x ^ p ^ n ∈ Set.range φ) (hx₂ : p ^ n • x ∈ Set.range φ)
    (hy₁ : y ^ p ^ m ∈ Set.range φ) (hy₂ : p ^ m • y ∈ Set.range φ) :
    ∃ a : ℕ, (x + y) ^ p ^ a ∈ Set.range φ ∧ p ^ a • (x + y) ∈ Set.range φ := by
  obtain ⟨a, ha₁, ha₂⟩ :=
    Stacks.UniversalHomeomorphism.FrobeniusPowerSubring.exists_pow_mem p hp n m hn hm
  set F : MvPolynomial (Fin 2) ℤ →ₐ[ℤ] B := MvPolynomial.aeval ![x, y]
  have hkey (z : MvPolynomial (Fin 2) ℤ) (hz : z ∈
    Stacks.UniversalHomeomorphism.FrobeniusPowerSubring.subringR p n m) :
      F z ∈ Set.range φ := by
    rw [Stacks.UniversalHomeomorphism.FrobeniusPowerSubring.subringR] at hz
    induction hz using Algebra.adjoin_induction with
    | mem w hw =>
      rcases hw with rfl | rfl | rfl | rfl
      · simpa [F] using hx₁
      · simpa [F] using hx₂
      · simpa [F] using hy₁
      · simpa [F] using hy₂
    | algebraMap i => exact ⟨(i : A), by simp [F]⟩
    | add u v _ _ hu hv =>
      obtain ⟨a, ha⟩ := hu
      obtain ⟨b, hb⟩ := hv
      exact ⟨a + b, by simp only [map_add, ha, hb]⟩
    | mul u v _ _ hu hv =>
      obtain ⟨a, ha⟩ := hu
      obtain ⟨b, hb⟩ := hv
      exact ⟨a * b, by simp only [map_mul, ha, hb]⟩
  exact ⟨a, by simpa [F] using hkey _ ha₁, by simpa [F] using hkey _ ha₂⟩

private theorem pGood_add {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (p : ℕ) (hp : Nat.Prime p) {x y : B}
    (hx : x ∈ pGoodSet A B φ p) (hy : y ∈ pGoodSet A B φ p) :
    x + y ∈ pGoodSet A B φ p := by
  obtain ⟨n, hn, hx₁, hx₂⟩ := hx
  obtain ⟨m, hm, hy₁, hy₂⟩ := hy
  obtain ⟨a, ha₁, ha₂⟩ := pGood_add_mem_range φ p hp hn hm hx₁ hx₂ hy₁ hy₂
  exact pGood_of_arbitrary_exponent φ p ha₁ ha₂

private def pGoodSubalgebra {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (φ : A →+* B) (hφ : algebraMap A B = φ) (p : ℕ) (hp : Nat.Prime p) : Subalgebra A B where
  carrier := pGoodSet A B φ p
  mul_mem' := pGood_mul φ p
  one_mem' := by simpa [hφ] using pGood_algebraMap φ p 1
  add_mem' := pGood_add φ p hp
  zero_mem' := by simpa [hφ] using pGood_algebraMap φ p 0
  algebraMap_mem' := fun a => by simpa [hφ] using pGood_algebraMap φ p a

private theorem exists_p_power_mul_mem_range_of_localizedMap_bijective
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (p : ℕ)
    (hφ : Function.Bijective
      (IsLocalization.Away.map (Localization.Away (p : A))
        (Localization.Away (φ (p : A))) φ (p : A))) (b : B) :
    ∃ n : ℕ, (p : B) ^ n * b ∈ Set.range φ := by
  obtain ⟨a, m, h⟩ := (IsLocalization.Away.map_surjective_iff _ _ φ (p : A)).mp hφ.2 b
  exact ⟨m, a, by simpa using h⟩

private theorem subalgebra_pow_mem_of_sq_cube {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] (C : Subalgebra A B) {b : B}
    (h2 : b ^ 2 ∈ C) (h3 : b ^ 3 ∈ C)
    {n : ℕ} (hn : 2 ≤ n) : b ^ n ∈ C := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    obtain rfl | rfl | h4 : n = 2 ∨ n = 3 ∨ 4 ≤ n := by omega
    · exact h2
    · exact h3
    · rw [show n = n - 2 + 2 by omega, pow_add]
      exact C.mul_mem (ih _ (by omega) (by omega)) h2

private theorem primePower_coprime {p ℓ k : ℕ} (hp : Nat.Prime p)
    (hℓ : Nat.Prime ℓ) (hne : ℓ ≠ p) : Nat.Coprime ℓ (p ^ k) :=
  Nat.Coprime.pow_right k ((Nat.coprime_primes hℓ hp).mpr hne)

private theorem subring_mem_of_coprime_multiples {A B : Type u} [CommRing A]
    [CommRing B] [Algebra A B] (C : Subalgebra A B)
    {a b : ℕ} (hab : Nat.Coprime a b) {x : B}
    (ha : (a : B) * x ∈ C) (hb : (b : B) * x ∈ C) : x ∈ C := by
  have hx : x = (Nat.gcdA a b : B) * ((a : B) * x) + (Nat.gcdB a b : B) * ((b : B) * x) := by
    calc
      x = (((a : ℤ) * Nat.gcdA a b + b * Nat.gcdB a b : ℤ) : B) * x := by
        rw [← Nat.gcd_eq_gcd_ab, hab.gcd_eq_one, Nat.cast_one, Int.cast_one, one_mul]
      _ = _ := by
        push_cast
        ring
  rw [hx]
  exact C.add_mem (C.mul_mem (intCast_mem C _) ha) (C.mul_mem (intCast_mem C _) hb)

private theorem mem_pGoodSet_of_pow_mem_pGoodSet {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (p : ℕ) {b : B} {k : ℕ} (hqb : (p : B) ^ k * b ∈ Set.range φ)
    (hpow : b ^ p ^ k ∈ pGoodSet A B φ p) : b ∈ pGoodSet A B φ p := by
  obtain ⟨n, -, hpw, -⟩ := hpow
  obtain ⟨a, ha⟩ := hqb
  have hbigpow : b ^ (p ^ (k + n)) ∈ Set.range φ := by
    simpa [pow_mul, Nat.pow_add, mul_comm] using hpw
  refine pGood_of_arbitrary_exponent φ p hbigpow ⟨(p ^ n : A) * a, ?_⟩
  rw [map_mul, show φ (p ^ n : A) = (p ^ n : B) by simp, ha]
  simp only [nsmul_eq_mul]
  push_cast
  ring

private theorem pos_of_not_mem_pGoodSet {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (p : ℕ) {b : B} {k : ℕ} (hqb : (p : B) ^ k * b ∈ Set.range φ)
    (hb : b ∉ pGoodSet A B φ p) : 0 < k := by
  refine Nat.pos_of_ne_zero fun hk => hb ?_
  subst hk
  obtain ⟨a, ha⟩ := hqb
  exact (show φ a = b by simpa using ha) ▸ pGood_algebraMap φ p a

private theorem mem_pGoodSet_of_universalHomeomorphism
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (p : ℕ)
    (hp : Nat.Prime p)
    (hφ : Function.Bijective
      (IsLocalization.Away.map (Localization.Away (p : A))
        (Localization.Away (φ (p : A))) φ (p : A)))
    (hUH : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom φ).op)) (b : B) :
    b ∈ pGoodSet A B φ p := by
  let : Algebra A B := φ.toAlgebra
  have hAlg : algebraMap A B = φ := RingHom.algebraMap_toAlgebra φ
  let C := pGoodSubalgebra φ hAlg p hp
  suffices hCtop : C = ⊤ from Algebra.eq_top_iff.mp hCtop b
  by_contra hCtop
  obtain h | h := exists_special_element_over_subalgebra C
    (universalHomeomorphism_specMap_to_subalgebra hUH C) hCtop
  · obtain ⟨b, hbC, h2, h3⟩ := h
    obtain ⟨k, hqb⟩ := exists_p_power_mul_mem_range_of_localizedMap_bijective φ p hφ b
    exact hbC (mem_pGoodSet_of_pow_mem_pGoodSet φ p hqb (subalgebra_pow_mem_of_sq_cube C h2 h3
      (hp.two_le.trans (Nat.le_pow (pos_of_not_mem_pGoodSet φ p hqb hbC)))))
  · obtain ⟨ℓ, hℓ, b, hbC, hℓb, hbℓ⟩ := h
    obtain ⟨k, hqb⟩ := exists_p_power_mul_mem_range_of_localizedMap_bijective φ p hφ b
    have hqbC : (p ^ k : B) * b ∈ C := by
      obtain ⟨a, ha⟩ := hqb
      rw [← ha, ← hAlg]
      exact C.algebraMap_mem a
    by_cases hℓp : ℓ = p
    · rw [hℓp] at hbℓ
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (pos_of_not_mem_pGoodSet φ p hqb hbC).ne'
      refine hbC (mem_pGoodSet_of_pow_mem_pGoodSet φ p hqb ?_)
      change b ^ p ^ (j + 1) ∈ C
      rw [pow_succ', pow_mul]
      exact C.pow_mem hbℓ _
    · exact hbC (subring_mem_of_coprime_multiples C (primePower_coprime (k := k) hp hℓ hℓp) hℓb
        (by simpa only [Nat.cast_pow] using hqbC))

private theorem locallyNilpotentKer_and_pow_mem_range_of_universalHomeomorphism
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (p : ℕ)
    (hp : Nat.Prime p)
    (hφ : Function.Bijective
      (IsLocalization.Away.map (Localization.Away (p : A))
        (Localization.Away (φ (p : A))) φ (p : A)))
    (hUH : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom φ).op)) :
    (RingHom.ker φ).LocallyNilpotent ∧
      ∀ b : B, ∃ n : ℕ,
        (p : B) ^ n * b ∈ Set.range φ ∧ b ^ (p ^ n) ∈ Set.range φ := by
  have hhomeo : IsHomeomorph (PrimeSpectrum.comap φ) :=
    hUH.universally_isHomeomorph _ _ _ IsPullback.of_id_snd
  refine ⟨fun x hx => mem_nilradical.2
    ((PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical φ).mp
      hhomeo.surjective.denseRange hx), fun b => ?_⟩
  obtain ⟨n, -, hpw, hmul⟩ := mem_pGoodSet_of_universalHomeomorphism φ p hp hφ hUH b
  exact ⟨n, by simpa only [nsmul_eq_mul, Nat.cast_pow] using hmul, hpw⟩

private theorem injective_pow_prime_power_of_char {K : Type u} [Field K]
    {p n : ℕ} (hp : Nat.Prime p) [CharP K p] :
    Function.Injective (fun x : K => x ^ (p ^ n)) := by
  have : Fact p.Prime := ⟨hp⟩
  exact iterateFrobenius_inj K p n

private theorem specMap_comp_injective_of_pow_mem_range
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (p : ℕ)
    (hp : Nat.Prime p)
    (hpow : ∀ b : B, ∃ n : ℕ,
      (p : B) ^ n * b ∈ Set.range φ ∧ b ^ (p ^ n) ∈ Set.range φ) (K : Type u) [Field K] :
    Function.Injective (fun g : Spec (.of K) ⟶ Spec (.of B) =>
      g ≫ Scheme.Spec.map (CommRingCat.ofHom φ).op) := by
  intro g₁ g₂ h
  obtain ⟨α, rfl⟩ := Scheme.Spec.map_surjective g₁
  obtain ⟨β, rfl⟩ := Scheme.Spec.map_surjective g₂
  have hcat : α ≫ (CommRingCat.ofHom φ).op = β ≫ (CommRingCat.ofHom φ).op := by
    apply Scheme.Spec.map_injective
    simpa only [Scheme.Spec.map_comp] using h
  have hcomp : (α.unop.hom).comp φ = (β.unop.hom).comp φ := by
    simpa only [unop_comp, Quiver.Hom.unop_op, CommRingCat.hom_comp,
      CommRingCat.hom_ofHom] using congrArg (fun g => g.unop.hom) hcat
  have hαβ : α.unop.hom = β.unop.hom := by
    refine RingHom.ext fun b => ?_
    obtain ⟨n, ⟨a, ha⟩, ⟨c, hc⟩⟩ := hpow b
    have hmulK : (p : K) ^ n * α.unop.hom b = (p : K) ^ n * β.unop.hom b := by
      simpa only [RingHom.comp_apply, ha, map_mul, map_pow, map_natCast] using
        DFunLike.congr_fun hcomp a
    by_cases hpK : (p : K) = 0
    · have hpowK : (α.unop.hom b) ^ (p ^ n) = (β.unop.hom b) ^ (p ^ n) := by
        simpa only [RingHom.comp_apply, hc, map_pow] using DFunLike.congr_fun hcomp c
      have : CharP K p := (CharP.charP_iff_prime_eq_zero hp).2 hpK
      exact injective_pow_prime_power_of_char hp hpowK
    · exact mul_left_cancel₀ (pow_ne_zero n hpK) hmulK
  exact congrArg Scheme.Spec.map (congrArg Quiver.Hom.op (CommRingCat.hom_ext hαβ))

private theorem universalHomeomorphism_of_locallyNilpotentKer_and_pow_mem_range
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (p : ℕ)
    (hp : Nat.Prime p)
    (hker : (RingHom.ker φ).LocallyNilpotent)
    (hpow : ∀ b : B, ∃ n : ℕ,
      (p : B) ^ n * b ∈ Set.range φ ∧ b ^ (p ^ n) ∈ Set.range φ) :
    UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom φ).op) := by
  let : Algebra A B := φ.toAlgebra
  have hAlg : algebraMap A B = φ := RingHom.algebraMap_toAlgebra φ
  have hhomeo : IsHomeomorph (PrimeSpectrum.comap φ) :=
    PrimeSpectrum.isHomeomorph_comap φ
      (fun b => by
        obtain ⟨n, -, a, ha⟩ := hpow b
        exact ⟨p ^ n, pow_pos hp.pos n, a, ha⟩)
      (fun x hx => mem_nilradical.2 (by simpa [hAlg] using hker x (by simpa [hAlg] using hx)))
  have hφInt : φ.IsIntegral := by
    intro b
    obtain ⟨n, -, a, ha⟩ := hpow b
    refine IsIntegral.of_pow (pow_pos hp.pos n) ?_
    rw [← ha]
    exact φ.isIntegralElem_map
  have hint : IsIntegralHom (Scheme.Spec.map (CommRingCat.ofHom φ).op) := by
    change IsIntegralHom (Spec.map (CommRingCat.ofHom φ))
    exact IsIntegralHom.SpecMap_iff.mpr hφInt
  let f : Spec (.of B) ⟶ Spec (.of A) :=
    Scheme.Spec.map (CommRingCat.ofHom φ).op
  exact (universalHomeomorphism_iff_integral_universallyInjective_surjective f).mpr
    ⟨hint, ((tfae_universallyInjective f).out 2 1).mp
      (specMap_comp_injective_of_pow_mem_range φ p hp hpow),
      (surjective_iff f).mpr hhomeo.surjective⟩

/-- A ring map that is an isomorphism after inverting a prime induces a universal
homeomorphism on spectra precisely when its kernel is locally nilpotent and
every target element has a prime-power multiple and prime-power power in its
image. -/
@[stacks 0CNF]
theorem universalHomeomorphism_iff_locallyNilpotent_ker_and_pow_mem_range
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (p : ℕ) (hp : Nat.Prime p)
    (hφ : Function.Bijective
      (IsLocalization.Away.map (Localization.Away (p : A))
        (Localization.Away (φ (p : A))) φ (p : A))) :
    UniversalHomeomorphism
        (Scheme.Spec.map (CommRingCat.ofHom φ).op) ↔
      (RingHom.ker φ).LocallyNilpotent ∧
        ∀ b : B, ∃ n : ℕ,
          (p : B) ^ n * b ∈ Set.range φ ∧ b ^ (p ^ n) ∈ Set.range φ :=
  ⟨locallyNilpotentKer_and_pow_mem_range_of_universalHomeomorphism φ p hp hφ,
    fun ⟨hker, hpow⟩ => universalHomeomorphism_of_locallyNilpotentKer_and_pow_mem_range
      φ p hp hker hpow⟩

end AlgebraicGeometry

end
