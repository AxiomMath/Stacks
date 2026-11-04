module

public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DiscreteValuationRing.Existence

/-!
# Bounded divisibility in finite ring extensions

In a one-dimensional Noetherian local ring, a fixed nonzerodivisor cannot become divisible
by arbitrarily high powers of a nonunit nonzerodivisor in finite ring extensions.

## Main results

* `AlgebraicGeometry.exists_bound_factorization_exponent_of_finite_extension` gives a bound,
  uniform over finite ring extensions, on the exponent in such a factorization.

## Implementation notes

A finite ring extension `R ⊆ S` is represented by an `R`-algebra `S` whose structure map is
finite and injective. Nonzerodivisors are expressed by `IsSMulRegular R`. The exponents, called
integers in the source, are nonnegative and hence are represented by natural numbers.

The proof maps `b / a ^ m` into a discrete valuation ring dominating a minimal-prime quotient.
It is integral over the valuation ring, hence belongs to it. Krull intersection then bounds
the powers of `a` dividing `b`. The argument works for any Noetherian local ring with the
stated regularity conditions.

## References

* [Stacks Project, Tag 0EAF](https://stacks.math.columbia.edu/tag/0EAF)
-/

@[expose] public section

universe u v

namespace AlgebraicGeometry

/-- In a Noetherian local ring, the powers of an element of the maximal ideal that divide a
fixed nonzero element are bounded. -/
private theorem bound_pow_dvd_of_mem_maximalIdeal
    (A : Type*) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {a b : A} (ha : a ∈ IsLocalRing.maximalIdeal A) (hb : b ≠ 0) :
    ∃ n : ℕ, ∀ m : ℕ, a ^ m ∣ b → m ≤ n := by
  let I := IsLocalRing.maximalIdeal A
  have h : ¬ ∀ n : ℕ, b ≡ 0 [SMOD (I ^ n • ⊤ : Submodule A A)] :=
    fun h => hb (IsHausdorff.haus (I := I) (M := A) inferInstance b h)
  obtain ⟨n, hn⟩ := not_forall.mp h
  refine ⟨n, fun m hm => ?_⟩
  by_contra hmn
  have hle : n ≤ m := Nat.le_of_not_ge hmn
  obtain ⟨c, hc⟩ := hm
  apply hn
  rw [SModEq.zero]
  have hpow : a ^ m ∈ I ^ n := Ideal.pow_le_pow_right hle (Ideal.pow_mem_pow ha m)
  rw [hc]
  simpa using (Ideal.mul_mem_right c (I ^ n) hpow)

/-- A regular element does not lie in any minimal prime. -/
private theorem notMem_of_isSMulRegular_of_mem_minimalPrimes
    {R : Type*} [CommRing R] [IsNoetherianRing R] {a : R} (ha : IsSMulRegular R a)
    {q : Ideal R} (hq : q ∈ minimalPrimes R) : a ∉ q := by
  apply ha.notMem_of_mem_minimalPrimes
  rwa [Module.annihilator_eq_bot.mpr (inferInstance : FaithfulSMul R R)]

/-- If a regular element lies in the maximal ideal, some minimal prime has a quotient that is
not a field. -/
private theorem exists_minimalPrime_nonfield_quotient
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {a : R} (ha : IsSMulRegular R a) (ha_mem : a ∈ IsLocalRing.maximalIdeal R) :
    ∃ (q : Ideal R), q ∈ minimalPrimes R ∧ ¬ IsField (R ⧸ q) := by
  classical
  obtain ⟨q, hq, hqm⟩ :=
    Ideal.exists_minimalPrimes_le (I := ⊥) (J := IsLocalRing.maximalIdeal R) bot_le
  let : q.IsPrime := hq.isPrime
  have hnotmem := notMem_of_isSMulRegular_of_mem_minimalPrimes ha hq
  have hnonfield : ¬ IsField (R ⧸ q) := by
    intro hf
    have hm : q.IsMaximal := (Ideal.Quotient.maximal_ideal_iff_isField_quotient q).mpr hf
    exact hnotmem ((IsLocalRing.eq_maximalIdeal hm).symm ▸ ha_mem)
  exact ⟨q, hq, hnonfield⟩

/-- If the image of `b` in a finite extension factors as `a ^ m` times an element, then
`b / a ^ m` is integral over the base ring. -/
private theorem integral_localized_factorization
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    {a b : R} (hf : (algebraMap R S).Finite)
    (hinj : Function.Injective (algebraMap R S))
    (m : ℕ) (c : S)
    (hc : algebraMap R S b = (algebraMap R S a) ^ m * c) :
    IsIntegral R ((algebraMap R (Localization.Away a) b) *
      (IsLocalization.Away.invSelf a : Localization.Away a) ^ m) := by
  let Q := Localization.Away a
  let T := Localization.Away (algebraMap R S a)
  let f : Q →+* T := IsLocalization.Away.map Q T (algebraMap R S) a
  have hfi : Function.Injective f :=
    IsLocalization.map_injective_of_injective (Submonoid.powers a) Q T hinj
  have hcint : IsIntegral R c := hf.to_isIntegral c
  let x : Q := (algebraMap R Q b) * (IsLocalization.Away.invSelf a : Q) ^ m
  have hTint : IsIntegral R (algebraMap S T c) :=
    hcint.map (IsScalarTower.toAlgHom R S T)
  have heq : f x = algebraMap S T c := by
    have hmapb : f (algebraMap R Q b) = algebraMap S T (algebraMap R S b) := by
      simp [f, IsLocalization.Away.map]
    have hmapinv : f (IsLocalization.Away.invSelf a : Q) =
        (IsLocalization.Away.invSelf (algebraMap R S a) : T) := by
      simp [f, IsLocalization.Away.map, IsLocalization.Away.invSelf, IsLocalization.map_mk']
    dsimp [x]
    rw [map_mul, map_pow, hmapb, hmapinv, hc, map_mul, map_pow]
    calc
      _ = ((algebraMap S T (algebraMap R S a)) *
            (IsLocalization.Away.invSelf (algebraMap R S a) : T)) ^ m *
            algebraMap S T c := by rw [mul_pow]; ring
      _ = algebraMap S T c := by
        rw [IsLocalization.Away.mul_invSelf, one_pow, one_mul]
  have hQ : IsIntegral R x := by
    apply RingHom.IsIntegralElem.of_map hfi
    rw [heq]
    have hcomp : f.comp (algebraMap R Q) = algebraMap R T := by
      ext r
      simp [f, IsLocalization.Away.map, IsScalarTower.algebraMap_apply R S T]
    rw [hcomp]
    exact hTint
  exact hQ

/-- The bound on the exponent, obtained by mapping into a discrete valuation ring that
dominates a minimal-prime quotient. -/
private theorem bound_factorization_exponent_via_dvr
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {a b : R} (ha : IsSMulRegular R a) (hb : IsSMulRegular R b)
    (ha_mem : a ∈ IsLocalRing.maximalIdeal R) :
    ∃ n : ℕ, ∀ (S : Type*) [CommRing S] [Algebra R S],
      (algebraMap R S).Finite → Function.Injective (algebraMap R S) → ∀ m : ℕ,
        (∃ c : S, algebraMap R S b = (algebraMap R S a) ^ m * c) → m ≤ n := by
  classical
  obtain ⟨q, hq, hnonfield⟩ := exists_minimalPrime_nonfield_quotient R ha ha_mem
  let : q.IsPrime := hq.isPrime
  let D := R ⧸ q
  have : IsLocalRing D :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
  let K := FractionRing D
  have : Algebra.EssFiniteType K K := inferInstance
  obtain ⟨A, hA, hfrac, hlocal⟩ :=
    exists_isDiscreteValuationRing_isFractionRing_of_not_isField (L := K) K hnonfield
  let : IsDiscreteValuationRing A := hA
  let : IsFractionRing A K := hfrac
  let : IsLocalHom (algebraMap D A) := hlocal
  let : IsLocalHom (Ideal.Quotient.mk q) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
  let rA : R →+* A := (algebraMap D A).comp (Ideal.Quotient.mk q)
  have haD : (Ideal.Quotient.mk q) a ∈ IsLocalRing.maximalIdeal D :=
    map_nonunit (Ideal.Quotient.mk q) a ha_mem
  have haA : rA a ∈ IsLocalRing.maximalIdeal A :=
    map_nonunit (algebraMap D A) _ haD
  have hbnot := notMem_of_isSMulRegular_of_mem_minimalPrimes hb hq
  have hbD : (Ideal.Quotient.mk q) b ≠ 0 :=
    fun h => hbnot (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hDA : Function.Injective (algebraMap D A) := by
    intro x y h
    apply IsFractionRing.injective D K
    simpa using congrArg (A.val : A →+* K) h
  have hbA : rA b ≠ 0 := fun h => hbD (hDA (by simpa [rA] using h))
  obtain ⟨n, hn⟩ := bound_pow_dvd_of_mem_maximalIdeal A haA hbA
  let g : R →+* K := (algebraMap D K).comp (Ideal.Quotient.mk q)
  have haDne : (Ideal.Quotient.mk q) a ≠ 0 := by
    intro h
    exact notMem_of_isSMulRegular_of_mem_minimalPrimes ha hq (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hga : g a ≠ 0 :=
    fun h => haDne ((IsFractionRing.injective D K) (by simpa [g] using h))
  have hunit : IsUnit (g a) := isUnit_iff_ne_zero.mpr hga
  let Q := Localization.Away a
  let L : Q →+* K := IsLocalization.Away.lift (g := g) a hunit
  have hLinv : L (IsLocalization.Away.invSelf a : Q) = (g a)⁻¹ := by
    apply (mul_left_cancel₀ hga)
    calc
      g a * L (IsLocalization.Away.invSelf a : Q) =
          L ((algebraMap R Q a) * IsLocalization.Away.invSelf a) := by
            rw [map_mul, IsLocalization.Away.lift_eq]
      _ = 1 := by rw [IsLocalization.Away.mul_invSelf, map_one]
      _ = g a * (g a)⁻¹ := by rw [mul_inv_cancel₀ hga]
  have hcomp : (algebraMap A K).comp rA = g := by
    ext r
    simp [rA, g]
  refine ⟨n, ?_⟩
  intro S _ _ hf hinj m ⟨c, hc⟩
  let x : Q := algebraMap R Q b * (IsLocalization.Away.invSelf a : Q) ^ m
  have hIntQ : IsIntegral R x := integral_localized_factorization R S hf hinj m c hc
  have hIntR : g.IsIntegralElem (L x) := by
    have h := RingHom.IsIntegralElem.map hIntQ L
    rwa [IsLocalization.Away.lift_comp] at h
  have hIntA : IsIntegral A (L x) := by
    show (algebraMap A K).IsIntegralElem (L x)
    apply RingHom.IsIntegralElem.of_comp (f := rA)
    rwa [hcomp]
  obtain ⟨d, hd⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hIntA
  have hbK : g b = (g a) ^ m * L x := by
    dsimp [x]
    rw [map_mul, map_pow, IsLocalization.Away.lift_eq, hLinv]
    calc
      g b = g b * (g a * (g a)⁻¹) ^ m := by
        rw [mul_inv_cancel₀ hga, one_pow, mul_one]
      _ = (g a) ^ m * (g b * (g a)⁻¹ ^ m) := by rw [mul_pow]; ring
  have hbAeq : rA b = (rA a) ^ m * d := by
    apply IsFractionRing.injective A K
    simpa only [map_mul, map_pow, ← hd, ← hcomp, RingHom.comp_apply] using hbK
  exact hn m ⟨d, hbAeq⟩

/-- **Stacks Project, Tag 0EAF.** Let `R` be a one-dimensional Noetherian local ring and let
`a` and `b` be nonzerodivisors, with `a` in the maximal ideal. There is a uniform bound on an
exponent `m` for which the image of `b` in a finite ring extension is a multiple of `a ^ m`. -/
@[stacks 0EAF]
public theorem exists_bound_factorization_exponent_of_finite_extension
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (_hdim : ringKrullDim R = 1) {a b : R} (ha : IsSMulRegular R a)
    (hb : IsSMulRegular R b) (ha_mem : a ∈ IsLocalRing.maximalIdeal R) :
    ∃ n : ℕ, ∀ (S : Type v) [CommRing S] [Algebra R S],
      (algebraMap R S).Finite → Function.Injective (algebraMap R S) → ∀ m : ℕ,
        (∃ c : S, algebraMap R S b = (algebraMap R S a) ^ m * c) → m ≤ n :=
  bound_factorization_exponent_via_dvr R ha hb ha_mem

end AlgebraicGeometry
