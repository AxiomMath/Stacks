module

public import StacksFrontier.RingTheory.DiscreteValuationRing.ArtinSchreier.GaloisDegree
import all StacksFrontier.RingTheory.DiscreteValuationRing.ArtinSchreier.GaloisDegree

/-!
# Artin--Schreier extensions of a discrete valuation field: the ramification alternatives

The four ramification alternatives for an Artin--Schreier extension `z ^ p - z = ξ` of a discrete
valuation field, and the three criteria read off the valuation of `ξ`: an integral parameter
(unramified or trivial), a pole whose order is divisible by `p` with non-`p`-th-power leading
coefficient (residually inseparable), and a pole of order prime to `p` (totally ramified).

## Main results

* `IsDiscreteValuationRing.isGalois_and_ramification_cases_of_adjoin_root_artinSchreier`: the
  four ramification alternatives and the three criteria determined by a uniformizer.

## Implementation notes

The ramification alternatives are expressed using the integral closure, its maximal ideals and
their residue fields. The assertion that the extension is obtained by adjoining the given root
is represented by `Algebra.adjoin K {z} = ⊤`. Triviality means that the structure map is
surjective. Weak unramifiedness is ramification index one; unramifiedness additionally requires
separability of every induced residue-field extension.

## References

* [Stacks Project, Tag 09F0](https://stacks.math.columbia.edu/tag/09F0)
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

/-- If `B` is an `A`-algebra inside a field extension `L` of `Frac A`, then `B` is torsion free
over `A`. -/
private theorem isTorsionFree_of_isScalarTower
    (A K L B : Type*) [CommRing A] [IsDomain A] [Field K] [Field L] [CommRing B] [IsDomain B]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [Algebra A B] [Algebra B L] [IsScalarTower A B L] : Module.IsTorsionFree A B := by
  refine Module.isTorsionFree_iff_algebraMap_injective.mpr ?_
  apply Function.Injective.of_comp (f := algebraMap B L)
  rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq,
    IsScalarTower.algebraMap_eq A K L]
  exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)

/-- A maximal ideal of an integral extension of a local ring lies over the maximal ideal. -/
private theorem liesOver_maximalIdeal_of_isMaximal
    (A B : Type*) [CommRing A] [IsLocalRing A] [CommRing B] [Algebra A B]
    [Algebra.IsIntegral A B] (m : Ideal B) [m.IsMaximal] :
    m.LiesOver (IsLocalRing.maximalIdeal A) :=
  ⟨((IsLocalRing.isMaximal_iff A).mp
    (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m)).symm⟩

/-- A surjective algebra map between fields forces the extension to have degree one. -/
private theorem finrank_eq_one_of_surjective_algebraMap
    (F E : Type*) [Field F] [Field E] [Algebra F E] (h : Function.Surjective (algebraMap F E)) :
    Module.finrank F E = 1 :=
  Algebra.finrank_eq_one_iff_bijective_algebraMap.2 ⟨(algebraMap F E).injective, h⟩

/-- If `L` is generated over `K` by a single element `x` integral over `R` whose minimal
polynomial stays separable after reduction modulo the prime of `R` under `P`, then the integral
closure `S` of `R` in `L` is unramified over `R` at `P`. -/
theorem unramified_of_separable_minpoly
    (R K L S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [Field K] [Field L] [IsDedekindDomain R]
    [Algebra R K] [IsFractionRing R K] [Algebra S L]
    [Algebra K L] [Algebra R L] [IsScalarTower R S L] [IsScalarTower R K L]
    [IsIntegralClosure S R L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (P : Ideal S) [P.IsPrime] (hPbot : P ≠ ⊥) (x : L)
    (hx : IsIntegral R x) (hx' : Algebra.adjoin K {x} = ⊤)
    (h : Polynomial.Separable
      ((minpoly R x).map (Ideal.Quotient.mk (P.under R)))) :
    Algebra.IsUnramifiedAt R P := by
  classical
  let y : S := IsIntegralClosure.mk' S x hx
  have hy : Algebra.adjoin K {algebraMap S L y} = ⊤ := by
    simpa [y, IsIntegralClosure.algebraMap_mk'] using hx'
  have hysep : Polynomial.Separable
      ((minpoly R y).map (Ideal.Quotient.mk (P.under R))) := by
    rw [← IsIntegralClosure.algebraMap_mk' S x hx,
      minpoly.algebraMap_eq (IsIntegralClosure.algebraMap_injective S R L)] at h
    exact h
  have : IsDomain S :=
    (IsIntegralClosure.equiv R S L (integralClosure R L)).toMulEquiv.isDomain
      (integralClosure R L)
  have : Module.IsTorsionFree R S := isTorsionFree_of_isScalarTower R K L S
  have : IsNoetherianRing S := IsIntegralClosure.isNoetherianRing R K L S
  have : IsDedekindDomain S := IsIntegralClosure.isDedekindDomain R K L S
  have : IsFractionRing S L :=
    IsIntegralClosure.isFractionRing_of_finite_extension R K L S
  have : Algebra.IsIntegral R S := IsIntegralClosure.isIntegral_algebra R L
  have : Module.Finite R S := IsIntegralClosure.finite R K L S
  have hdiff := aeval_derivative_mem_differentIdeal R K L y hy
  have H : RingHom.comp (algebraMap (FractionRing R) (FractionRing S))
      (FractionRing.algEquiv R K).symm.toRingEquiv =
      RingHom.comp (FractionRing.algEquiv S L).symm.toRingEquiv
        (algebraMap K L) := by
    apply IsLocalization.ringHom_ext R⁰
    ext
    simp only [RingHom.coe_comp, RingHom.coe_coe, AlgEquiv.coe_ringEquiv,
      Function.comp_apply, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply R S L, AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply]
  have : Algebra.IsSeparable (FractionRing R) (FractionRing S) :=
    Algebra.IsSeparable.of_equiv_equiv _ _ H
  rw [← not_dvd_differentIdeal_iff (A := R) (B := S)]
  intro hPdiv
  have hxP : Polynomial.aeval y (Polynomial.derivative (minpoly R y)) ∈ P :=
    (Ideal.dvd_iff_le.mp hPdiv) hdiff
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.algebraMap_eq] at hxP
  let p : Ideal R := P.under R
  have : p.IsPrime := inferInstance
  have hpbot : p ≠ ⊥ := Ideal.under_ne_bot R hPbot
  have : p.IsMaximal := (show p.IsPrime from inferInstance).isMaximal hpbot
  have : P.IsMaximal := (show P.IsPrime from inferInstance).isMaximal hPbot
  let : IsScalarTower S (S ⧸ P) (S ⧸ P) := IsScalarTower.right
  have hle : p ≤ P.comap (algebraMap R S) := by
    change P.under R ≤ P.comap (algebraMap R S)
    rw [Ideal.under_def]
  have hsep' :=
    (Polynomial.separable_map (Ideal.quotientMap P (algebraMap R S) hle)).mpr hysep
  rw [Polynomial.map_map, Ideal.quotientMap_comp_mk] at hsep'
  obtain ⟨a, b, e⟩ := hsep'
  apply_fun (Polynomial.aeval (Ideal.Quotient.mk P y)) at e
  simp_rw [← Ideal.Quotient.algebraMap_eq, ← Polynomial.map_map,
    Polynomial.derivative_map, map_add, _root_.map_mul,
    Polynomial.aeval_map_algebraMap, Polynomial.aeval_algebraMap_apply,
    minpoly.aeval, hxP, map_zero, mul_zero, zero_add, map_one, zero_ne_one] at e

private theorem separable_reduction_minpoly_artin_schreier
    (A L : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Field L] [Algebra A L] [Module.IsTorsionFree A L]
    (p : ℕ) (hp : p.Prime) [CharP A p]
    (a : A) (z : L) (hz : z ^ p - z = algebraMap A L a)
    (T : Type*) [CommRing T] (f : A →+* T) :
    Polynomial.Separable ((minpoly A z).map f) := by
  let g : A[X] := X ^ p - X - C a
  have hgmonic : g.Monic := by
    dsimp [g]
    have hmono : (X ^ p - (X + C a) : A[X]).Monic := monic_X_pow_sub (by
      rw [degree_X_add_C]
      exact_mod_cast hp.one_lt)
    convert hmono using 1; ring
  have hgroot : Polynomial.aeval z g = 0 := by
    dsimp [g]
    simp [hz]
  have hint : IsIntegral A z := ⟨g, hgmonic, hgroot⟩
  have hdvd : minpoly A z ∣ g := minpoly.isIntegrallyClosed_dvd hint hgroot
  have hgsep : g.Separable := by
    have hpoly : g = C (1 : A) * X ^ p + C (-1) * X + C (-a) := by
      dsimp [g]
      simp
      ring
    rw [hpoly]
    exact separable_C_mul_X_pow_add_C_mul_X_add_C' p p 1 (-1) (-a)
      (dvd_refl p) isUnit_neg_one
  exact hgsep.map.of_dvd (Polynomial.map_dvd f hdvd)

private theorem unramified_or_trivial_of_integral_artin_schreier
    (A : Type uA) (K : Type uK) (L : Type uL)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    (p : ℕ) (hp : p.Prime) [CharP K p]
    (a : A) (z : L)
    (hz : z ^ p - z = algebraMap A L a)
    (hgen : Algebra.adjoin K {z} = ⊤)
    (hdegree : Module.finrank K L ∣ p) :
    Function.Surjective (algebraMap K L) ∨
      (Module.finrank K L = p ∧
        ∀ m : Ideal (integralClosure A L), m.IsMaximal →
          ∃ _ : m.LiesOver (IsLocalRing.maximalIdeal A),
            Ideal.ramificationIdx' (IsLocalRing.maximalIdeal A) m = 1 ∧
              @Algebra.IsSeparable
                (A ⧸ IsLocalRing.maximalIdeal A)
                ((integralClosure A L) ⧸ m) _ _
                (Ideal.Quotient.algebraOfLiesOver m (IsLocalRing.maximalIdeal A))) := by
  let B := integralClosure A L
  let mA := IsLocalRing.maximalIdeal A
  have hAK : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have hAL : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp hAK
  let : Module.IsTorsionFree A L :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hAL
  let : CharP A p := (algebraMap A K).charP hAK p
  have hsep : Algebra.IsSeparable K L := inferInstance
  let : Algebra.IsSeparable K L := hsep
  let : Module.Finite A B := IsIntegralClosure.finite A K L B
  let : IsDedekindDomain B := integralClosure.isDedekindDomain A K L
  let : Algebra.IsIntegral A B := IsIntegralClosure.isIntegral_algebra A L
  have hcase := hp.eq_one_or_self_of_dvd (Module.finrank K L) hdegree
  rcases hcase with htriv | hprime
  · left
    exact (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp htriv).2
  · right
    refine ⟨hprime, ?_⟩
    intro m hm
    let : m.IsMaximal := hm
    let : m.IsPrime := hm.isPrime
    have hOver : m.LiesOver mA := liesOver_maximalIdeal_of_isMaximal A B m
    let : m.LiesOver mA := hOver
    have hm0 : m ≠ ⊥ :=
      Ideal.ne_bot_of_liesOver_of_ne_bot (IsDiscreteValuationRing.not_a_field A) m
    have hzA : z ^ p - z = algebraMap A L a := hz
    have hint : IsIntegral A z := by
      let g : A[X] := X ^ p - X - C a
      have hgmonic : g.Monic := by
        dsimp [g]
        have hmono : (X ^ p - (X + C a) : A[X]).Monic := monic_X_pow_sub (by
          rw [degree_X_add_C]
          exact_mod_cast hp.one_lt)
        convert hmono using 1; ring
      have hroot : Polynomial.aeval z g = 0 := by
        dsimp [g]
        simp [hzA]
      exact ⟨g, hgmonic, hroot⟩
    have hsepmin : Polynomial.Separable
        ((minpoly A z).map (Ideal.Quotient.mk (m.under A))) :=
      separable_reduction_minpoly_artin_schreier A L p hp a z hzA
        (A ⧸ m.under A) (Ideal.Quotient.mk (m.under A))
    have hunr : Algebra.IsUnramifiedAt A m :=
      unramified_of_separable_minpoly A K L B m hm0 z hint hgen hsepmin
    refine ⟨hOver, ?_, ?_⟩
    · rw [Ideal.ramificationIdx'_eq_ramificationIdx mA m
        (IsDiscreteValuationRing.not_a_field A)]
      exact m.ramificationIdx_eq_one A
    · let : Algebra (Localization.AtPrime mA) (Localization.AtPrime m) :=
        Localization.AtPrime.algebraOfLiesOver mA m
      exact (Algebra.isSeparable_residueField_iff).mp inferInstance

private theorem purely_inseparable_of_prime_power_root
    (F : Type*) (E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] (p : ℕ) (hp : p.Prime) [CharP F p]
    (a : F) (x : E) (hx : x ^ p = algebraMap F E a)
    (ha : ¬∃ b : F, a = b ^ p)
    (hdegree : Module.finrank F E ≤ p) :
    Module.finrank F E = p ∧ IsPurelyInseparable F E := by
  let f : F[X] := X ^ p - C a
  have hf : Irreducible f := by
    dsimp [f]
    exact X_pow_sub_C_irreducible_of_prime hp (by
      intro b hb
      exact ha ⟨b, hb.symm⟩)
  have hroot : Polynomial.aeval x f = 0 := by
    dsimp [f]
    simp [hx]
  have hmonic : f.Monic := monic_X_pow_sub_C a hp.ne_zero
  have hmin : f = minpoly F x := minpoly.eq_of_irreducible_of_monic hf hroot hmonic
  have hle : p ≤ Module.finrank F E := by
    have hdim : f.natDegree ≤ Module.finrank F E := by
      rw [hmin]
      exact minpoly.natDegree_le x
    simpa [f, hp.ne_zero] using hdim
  have hfinrank : Module.finrank F E = p := Nat.le_antisymm hdegree hle
  refine ⟨hfinrank, ?_⟩
  have hadj : IntermediateField.adjoin F {x} = ⊤ := by
    apply (Field.primitive_element_iff_minpoly_natDegree_eq F x).2
    rw [← hmin, hfinrank]
    simp [f]
  let : Fact p.Prime := ⟨hp⟩
  have hpure : IsPurelyInseparable F (IntermediateField.adjoin F {x}) :=
    (IntermediateField.isPurelyInseparable_adjoin_simple_iff_pow_mem F E p).2
      ⟨1, by simpa using (show x ^ p ∈ (algebraMap F E).range from ⟨a, hx.symm⟩)⟩
  rw [hadj] at hpure
  exact IntermediateField.topEquiv.isPurelyInseparable

private theorem scaled_artin_schreier_root
    (L : Type*) [Field L] (p k : ℕ) (hp : 1 ≤ p)
    (π a z : L) (hπ : π ≠ 0)
    (hz : z ^ p - z = π⁻¹ ^ (p * k) * a) :
    (π ^ k * z) ^ p - π ^ ((p - 1) * k) * (π ^ k * z) = a := by
  have hpow : (p - 1) * k + k = p * k := by
    calc
      (p - 1) * k + k = ((p - 1) + 1) * k := by ring
      _ = p * k := by rw [Nat.sub_add_cancel hp]
  calc
    (π ^ k * z) ^ p - π ^ ((p - 1) * k) * (π ^ k * z) =
        π ^ (p * k) * (z ^ p - z) := by
          rw [mul_pow, ← pow_mul, Nat.mul_comm k p]
          have hterm : π ^ ((p - 1) * k) * (π ^ k * z) = π ^ (p * k) * z := by
            rw [← mul_assoc, ← pow_add, hpow]
          rw [hterm]
          ring
    _ = a := by
      rw [hz, ← mul_assoc, ← mul_pow]
      simp [hπ]

private theorem integral_of_scaled_artin_schreier_root
    (A L : Type*) [CommRing A] [Field L] [Algebra A L]
    (p : ℕ) (hp : p.Prime) (c a : A) (y : L)
    (hy : y ^ p - algebraMap A L c * y = algebraMap A L a) :
    IsIntegral A y := by
  let f : A[X] := X ^ p - C c * X - C a
  have hmonic : f.Monic := by
    dsimp [f]
    have hmono : (X ^ p - (C c * X + C a) : A[X]).Monic :=
      monic_X_pow_sub (degree_linear_le.trans_lt (by exact_mod_cast hp.one_lt))
    convert hmono using 1; ring
  have hroot : Polynomial.aeval y f = 0 := by
    dsimp [f]
    simp [hy]
  exact ⟨f, hmonic, hroot⟩

private theorem purely_inseparable_residue_of_scaled_artin_schreier
    (A : Type uA) (K : Type uK) (L : Type uL)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (p : ℕ) (hp : p.Prime) [CharP K p]
    (k : ℕ) (hk : 0 < k) (π a : A) (hπ : Irreducible π)
    (z : L)
    (hz : z ^ p - z = (algebraMap A L π)⁻¹ ^ (p * k) * algebraMap A L a)
    (ha : ¬∃ b : IsLocalRing.ResidueField A,
      IsLocalRing.residue A a = b ^ p)
    (hdegree : Module.finrank K L ≤ p)
    (m : Ideal (integralClosure A L)) (hm : m.IsMaximal)
    [hOver : m.LiesOver (IsLocalRing.maximalIdeal A)] :
    letI := Ideal.Quotient.algebraOfLiesOver m (IsLocalRing.maximalIdeal A)
    Module.finrank (A ⧸ IsLocalRing.maximalIdeal A)
        ((integralClosure A L) ⧸ m) = p ∧
      IsPurelyInseparable (A ⧸ IsLocalRing.maximalIdeal A)
        ((integralClosure A L) ⧸ m) := by
  let B := integralClosure A L
  let mA := IsLocalRing.maximalIdeal A
  let : m.IsMaximal := hm
  let : m.IsPrime := hm.isPrime
  let : m.LiesOver mA := hOver
  let : mA.IsMaximal := IsLocalRing.maximalIdeal.isMaximal A
  let : mA.IsPrime := (IsLocalRing.maximalIdeal.isMaximal A).isPrime
  let : Field (A ⧸ mA) := IsLocalRing.ResidueField.field A
  let : Field (B ⧸ m) := Ideal.Quotient.field m
  let : Algebra (A ⧸ mA) (B ⧸ m) :=
    Ideal.Quotient.algebraOfLiesOver m mA
  have hπ0 : algebraMap A L π ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply A K L π]
    simpa only [map_zero] using
      (algebraMap K L).injective.ne
        ((IsFractionRing.injective A K).ne hπ.ne_zero)
  let c : A := π ^ ((p - 1) * k)
  let y : L := (algebraMap A L π) ^ k * z
  have hy : y ^ p - algebraMap A L c * y = algebraMap A L a := by
    simpa [y, c, map_pow] using
      scaled_artin_schreier_root L p k hp.one_le
        (algebraMap A L π) (algebraMap A L a) z hπ0 hz
  have hint : IsIntegral A y :=
    integral_of_scaled_artin_schreier_root A L p hp c a y hy
  let yB : B := IsIntegralClosure.mk' B y hint
  have hyB : yB ^ p - algebraMap A B c * yB = algebraMap A B a := by
    apply IsIntegralClosure.algebraMap_injective B A L
    simp only [map_sub, map_pow, map_mul, ← IsScalarTower.algebraMap_apply]
    have hyMap : algebraMap B L yB = y := IsIntegralClosure.algebraMap_mk' B y hint
    rw [hyMap]
    exact hy
  have hπmem : π ∈ mA := by
    change π ∈ IsLocalRing.maximalIdeal A
    rw [hπ.maximalIdeal_eq]
    exact Ideal.mem_span_singleton_self π
  have hcpos : 0 < (p - 1) * k := Nat.mul_pos (Nat.sub_pos_of_lt hp.one_lt) hk
  have hcmem : c ∈ mA := mA.pow_mem_of_mem hπmem _ hcpos
  have hcm : algebraMap A B c ∈ m := by
    change c ∈ m.comap (algebraMap A B)
    rw [← Ideal.under_def, ← hOver.over]
    exact hcmem
  have hq := congrArg (Ideal.Quotient.mk m) hyB
  have hpow : (Ideal.Quotient.mk m yB) ^ p =
      algebraMap (A ⧸ mA) (B ⧸ m) (Ideal.Quotient.mk mA a) := by
    change (Ideal.Quotient.mk m yB) ^ p =
      (Ideal.Quotient.mk m) ((algebraMap A B) a)
    simpa [Ideal.Quotient.eq_zero_iff_mem.mpr hcm,
      Ideal.Quotient.mk_algebraMap] using hq
  let : Module.Finite A B := IsIntegralClosure.finite A K L B
  let : IsDedekindDomain B := integralClosure.isDedekindDomain A K L
  let : IsFractionRing B L :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  let : Module.IsTorsionFree A B := isTorsionFree_of_isScalarTower A K L B
  let : NoZeroSMulDivisors A B :=
    ⟨fun h => smul_eq_zero.mp h⟩
  have hmodfin : Module.Finite (A ⧸ mA) (B ⧸ m) :=
    module_finite_of_liesOver m mA
  have hle : Module.finrank (A ⧸ mA) (B ⧸ m) ≤ p := by
    have hbound := (ramificationIdx_and_inertiaDeg_le_finrank A K L m hm).2
    rw [Ideal.inertiaDeg_eq_of_isMaximal mA m] at hbound
    exact hbound.trans hdegree
  let : CharP A p := (algebraMap A K).charP (IsFractionRing.injective A K) p
  have hcharres : CharP (A ⧸ mA) p :=
    CharP.quotient' p mA (by
      intro n hn
      have hdiv : p ∣ n := by
        by_contra hnot
        have hunit : IsUnit (n : A) := (CharP.isUnit_natCast_iff hp).2 hnot
        exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top
          (Ideal.eq_top_of_isUnit_mem mA hn hunit)
      exact (CharP.cast_eq_zero_iff A p n).2 hdiv)
  let : CharP (A ⧸ mA) p := hcharres
  have hnot : ¬∃ b : A ⧸ mA, (Ideal.Quotient.mk mA a) = b ^ p := fun ⟨b, hb⟩ => ha ⟨b, hb⟩
  exact @purely_inseparable_of_prime_power_root (A ⧸ mA) (B ⧸ m)
    (IsLocalRing.ResidueField.field A) (Ideal.Quotient.field m)
    (Ideal.Quotient.algebraOfLiesOver m mA) hmodfin p hp
    hcharres (Ideal.Quotient.mk mA a) (Ideal.Quotient.mk m yB)
    hpow hnot hle

private theorem residually_inseparable_of_divisible_pole
    (A : Type uA) (K : Type uK) (L : Type uL)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    (p : ℕ) (hp : p.Prime) [CharP K p]
    (hdegree : Module.finrank K L ∣ p)
    (k : ℕ) (hk : 0 < k) (π a : A) (hπ : Irreducible π)
    (z : L)
    (hz : z ^ p - z = (algebraMap A L π)⁻¹ ^ (p * k) * algebraMap A L a)
    (ha : ¬∃ b : IsLocalRing.ResidueField A,
      IsLocalRing.residue A a = b ^ p) :
    let B := integralClosure A L
    let mA := IsLocalRing.maximalIdeal A
    ∃ hDVR : IsDiscreteValuationRing B,
      letI := hDVR
      let mB := IsLocalRing.maximalIdeal B
      ∃ _ : mB.LiesOver mA,
        Ideal.ramificationIdx' mA mB = 1 ∧
          letI := Ideal.Quotient.algebraOfLiesOver mB mA
          IsPurelyInseparable (A ⧸ mA) (B ⧸ mB) ∧
            Module.finrank (A ⧸ mA) (B ⧸ mB) = p := by
  let B := integralClosure A L
  let mA := IsLocalRing.maximalIdeal A
  let : Module.Finite A B := IsIntegralClosure.finite A K L B
  let : IsDedekindDomain B := integralClosure.isDedekindDomain A K L
  let : Algebra.IsIntegral A B := IsIntegralClosure.isIntegral_algebra A L
  let : IsFractionRing B L :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  let : Module.IsTorsionFree A B := isTorsionFree_of_isScalarTower A K L B
  let : NoZeroSMulDivisors A B := ⟨fun h => smul_eq_zero.mp h⟩
  have hle : Module.finrank K L ≤ p :=
    Nat.le_of_dvd hp.pos hdegree
  obtain ⟨m, hm⟩ := Ideal.exists_maximal B
  let : m.IsMaximal := hm
  let : m.IsPrime := hm.isPrime
  have hOver : m.LiesOver mA := liesOver_maximalIdeal_of_isMaximal A B m
  let : m.LiesOver mA := hOver
  have hres := purely_inseparable_residue_of_scaled_artin_schreier
    A K L p hp k hk π a hπ z hz ha hle m hm
  have hbound := (ramificationIdx_and_inertiaDeg_le_finrank A K L m hm).2
  rw [Ideal.inertiaDeg_eq_of_isMaximal mA m] at hbound
  have hdim : Module.finrank K L = p := Nat.le_antisymm hle (hres.1 ▸ hbound)
  have hcase := ramification_cases_of_isGalois_of_finrank_dvd_prime
    A K L p hp hdegree
  rcases hcase with htriv | hunram | htotal | hrescase
  · exact (hp.ne_one (hdim.symm.trans (finrank_eq_one_of_surjective_algebraMap K L htriv))).elim
  · obtain ⟨_, hsep⟩ := hunram
    obtain ⟨_, ⟨_, hs⟩⟩ := hsep m hm
    let : Algebra (A ⧸ mA) (B ⧸ m) :=
      Ideal.Quotient.algebraOfLiesOver m mA
    let : Algebra.IsSeparable (A ⧸ mA) (B ⧸ m) := hs
    let : IsPurelyInseparable (A ⧸ mA) (B ⧸ m) := hres.2
    exact (hp.ne_one (hres.1.symm.trans (finrank_eq_one_of_surjective_algebraMap _ _
      (IsPurelyInseparable.surjective_algebraMap_of_isSeparable _ _)))).elim
  · obtain ⟨m', hm', ho', _, hf'⟩ := htotal.1
    let : m'.LiesOver mA := ho'
    have hr' := purely_inseparable_residue_of_scaled_artin_schreier
      A K L p hp k hk π a hπ z hz ha hle m' hm'
    exact (hp.ne_one (hr'.1.symm.trans (by simpa using hf'))).elim
  · exact hrescase

/-- A polynomial with coefficients of valuation at most one, evaluated at an element of
valuation at most one, has valuation at most one. -/
theorem valuation_aeval_le_one
    {A L Γ : Type*} [CommRing A] [Field L] [Algebra A L]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation L Γ)
    (hA : ∀ a : A, v (algebraMap A L a) ≤ 1)
    (P : Polynomial A) (z : L) (hz : v z ≤ 1) :
    v (Polynomial.aeval z P) ≤ 1 := by
  classical
  rw [Polynomial.as_sum_range P, map_sum]
  apply v.map_sum_le
  intro i hi
  simp only [← Polynomial.C_mul_X_pow_eq_monomial, map_mul,
    Polynomial.aeval_C, map_pow, Polynomial.aeval_X]
  exact (mul_le_of_le_one_left zero_le (hA _)).trans (pow_le_one₀ zero_le hz)

/-- A monic polynomial with coefficients of valuation at most one, evaluated at an element of
valuation greater than one, has valuation the degree-th power of that element's valuation. -/
theorem valuation_aeval_eq_pow_of_one_lt
    {A L Γ : Type*} [CommRing A] [Field L] [Algebra A L]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation L Γ)
    (hA : ∀ a : A, v (algebraMap A L a) ≤ 1)
    (P : Polynomial A) (hP : P.Monic) (z : L) (hz : 1 < v z) :
    v (Polynomial.aeval z P) = v z ^ P.natDegree := by
  classical
  have hlead : v (Polynomial.aeval z (Polynomial.monomial P.natDegree P.leadingCoeff)) =
      v z ^ P.natDegree := by
    simp only [← Polynomial.C_mul_X_pow_eq_monomial, map_pow,
      Polynomial.aeval_X, hP.leadingCoeff, map_one, one_mul]
  rw [← hlead]
  nth_rw 1 [Polynomial.as_sum_range P, map_sum]
  apply Valuation.map_sum_eq_of_lt _ (by simp)
  intro i hi
  simp only [Finset.mem_sdiff, Finset.mem_range, Nat.lt_add_one_iff, Finset.mem_singleton,
    ← lt_iff_le_and_ne] at hi
  simp only [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, Polynomial.aeval_C,
    map_pow, Polynomial.aeval_X, Polynomial.coeff_natDegree, hP.leadingCoeff,
    map_one, one_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left zero_le (hA _))
    (pow_lt_pow_right₀ hz hi)

/-- If a monic polynomial with coefficients of valuation at most one takes a value of valuation
`exp N` at `z`, then its degree divides `N`. -/
theorem natDegree_dvd_of_valuation_aeval_eq_exp
    {A L : Type*} [CommRing A] [Field L] [Algebra A L]
    (v : Valuation L (WithZero (Multiplicative ℤ))) (hA : ∀ a : A, v (algebraMap A L a) ≤ 1)
    (P : Polynomial A) (hP : P.Monic) (z : L) (N : ℕ) (hN : 0 < N)
    (hval : v (Polynomial.aeval z P) = WithZero.exp (N : ℤ)) :
    P.natDegree ∣ N := by
  have hgt : 1 < v (Polynomial.aeval z P) := by
    rw [hval]
    exact WithZero.one_lt_exp_iff.mpr (by exact_mod_cast hN)
  have hzgt : 1 < v z := by
    by_contra h
    exact not_le.mpr hgt (valuation_aeval_le_one v hA P z (le_of_not_gt h))
  have hpow : v z ^ P.natDegree = WithZero.exp (N : ℤ) :=
    (valuation_aeval_eq_pow_of_one_lt v hA P hP z hzgt).symm.trans hval
  have hlog := congrArg WithZero.log hpow
  rw [WithZero.log_pow, WithZero.log_exp] at hlog
  simp only [nsmul_eq_mul] at hlog
  have hdiv : (P.natDegree : ℤ) ∣ (N : ℤ) := ⟨(v z).log, hlog.symm⟩
  exact_mod_cast hdiv

/-- If `P` is a monic polynomial over `A` with `P.natDegree = p` and `P z = ξ` for an element
`ξ` of `K` whose pole order `n` at the maximal ideal of `A` is positive and coprime to `p`,
then `p` divides the ramification index of every maximal ideal of `integralClosure A L`
lying over the maximal ideal of `A`. -/
theorem natDegree_dvd_ramificationIdx_of_coprime_pole
    (A : Type uA) (K : Type uK) (L : Type uL)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (p n : ℕ) (hn : 0 < n) (hnp : p.Coprime n)
    (π a : A) (hπ : Irreducible π) (ha : IsUnit a)
    (P : Polynomial A) (hPm : P.Monic) (hPd : P.natDegree = p)
    (ξ : K) (z : L) (hz : Polynomial.aeval z P = algebraMap K L ξ)
    (hξ : ξ = (algebraMap A K π)⁻¹ ^ n * algebraMap A K a)
    (m : Ideal (integralClosure A L)) (hm : m.IsMaximal)
    [hOver : m.LiesOver (IsLocalRing.maximalIdeal A)] :
    p ∣ Ideal.ramificationIdx' (IsLocalRing.maximalIdeal A) m := by
  let B := integralClosure A L
  let mA := IsLocalRing.maximalIdeal A
  let : m.IsPrime := hm.isPrime
  let : Module.IsTorsionFree A B := isTorsionFree_of_isScalarTower A K L B
  let : Module.Finite A B := IsIntegralClosure.finite A K L B
  let : IsDedekindDomain B := integralClosure.isDedekindDomain A K L
  let : IsFractionRing B L :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  let vA : IsDedekindDomain.HeightOneSpectrum A :=
    ⟨mA, (IsLocalRing.maximalIdeal.isMaximal A).isPrime,
      IsDiscreteValuationRing.not_a_field A⟩
  have hm0 : m ≠ ⊥ :=
    Ideal.ne_bot_of_liesOver_of_ne_bot (IsDiscreteValuationRing.not_a_field A) m
  let vB : IsDedekindDomain.HeightOneSpectrum B := ⟨m, hm.isPrime, hm0⟩
  let : vB.asIdeal.LiesOver vA.asIdeal := hOver
  have hvπ : vA.intValuation π = WithZero.exp (-1 : ℤ) :=
    vA.intValuation_singleton hπ.ne_zero hπ.maximalIdeal_eq
  have hva : vA.intValuation a = 1 :=
    vA.intValuation_eq_one_iff.mpr (IsLocalRing.notMem_maximalIdeal.mpr ha)
  have hvξ : vA.valuation K ξ = WithZero.exp (n : ℤ) := by
    rw [hξ]
    rw [map_mul, map_pow, Valuation.map_inv,
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      hvπ, hva, mul_one, ← WithZero.exp_neg, neg_neg,
      ← WithZero.exp_nsmul]
    simp
  have hvξB : vB.valuation L (algebraMap K L ξ) =
      WithZero.exp ((n * mA.ramificationIdx' m : ℕ) : ℤ) := by
    rw [← IsDedekindDomain.HeightOneSpectrum.valuation_liesOver L vA vB ξ,
      hvξ, ← WithZero.exp_nsmul]
    congr 1
    simp [Nat.cast_mul, mul_comm, vA, vB]
  have he : 0 < mA.ramificationIdx' m :=
    Nat.pos_iff_ne_zero.mpr
      (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver m
        (IsDiscreteValuationRing.not_a_field A))
  have hcoeff : ∀ a : A, vB.valuation L (algebraMap A L a) ≤ 1 := by
    intro a
    rw [IsScalarTower.algebraMap_apply A B L,
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact vB.intValuation_le_one _
  have hmul : p ∣ n * mA.ramificationIdx' m := by
    rw [← hPd]
    apply natDegree_dvd_of_valuation_aeval_eq_exp (vB.valuation L) hcoeff P hPm z _
      (Nat.mul_pos hn he)
    rw [hz]
    exact hvξB
  exact hnp.dvd_of_dvd_mul_left hmul

/-- Let `P` be a monic polynomial over `A` of prime degree `p` with `Module.finrank K L ∣ p`,
and let `P z = ξ` for an element `ξ` of `K` with a pole of positive order `n` not divisible by
`p` at the maximal ideal of `A`. Then `L / K` is totally ramified with respect to `A`, with
ramification index `p` at every maximal ideal lying over the maximal ideal of `A`. -/
theorem totally_ramified_of_coprime_pole
    (A : Type uA) (K : Type uK) (L : Type uL)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    (p n : ℕ) (hp : p.Prime) (hn : 0 < n) (hnp : ¬p ∣ n)
    (hdegree : Module.finrank K L ∣ p)
    (π a : A) (hπ : Irreducible π) (ha : IsUnit a)
    (P : Polynomial A) (hPm : P.Monic) (hPd : P.natDegree = p)
    (ξ : K) (z : L) (hz : Polynomial.aeval z P = algebraMap K L ξ)
    (hξ : ξ = (algebraMap A K π)⁻¹ ^ n * algebraMap A K a) :
    Stacks.KummerExtension.IsTotallyRamified A K L ∧
      ∀ m : Ideal (integralClosure A L), m.IsMaximal →
        m.LiesOver (IsLocalRing.maximalIdeal A) →
        Ideal.ramificationIdx' (IsLocalRing.maximalIdeal A) m = p := by
  let B := integralClosure A L
  let mA := IsLocalRing.maximalIdeal A
  let : Module.Finite A B := IsIntegralClosure.finite A K L B
  let : IsDedekindDomain B := integralClosure.isDedekindDomain A K L
  let : Algebra.IsIntegral A B := IsIntegralClosure.isIntegral_algebra A L
  let : IsFractionRing B L :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  let : Module.IsTorsionFree A B := isTorsionFree_of_isScalarTower A K L B
  let : NoZeroSMulDivisors A B := ⟨fun h => smul_eq_zero.mp h⟩
  have hcop : p.Coprime n := hp.coprime_iff_not_dvd.mpr hnp
  obtain ⟨m, hm⟩ := Ideal.exists_maximal B
  let : m.IsMaximal := hm
  let : m.IsPrime := hm.isPrime
  have hOver : m.LiesOver mA := liesOver_maximalIdeal_of_isMaximal A B m
  let : m.LiesOver mA := hOver
  have hdvd := natDegree_dvd_ramificationIdx_of_coprime_pole
    A K L p n hn hcop π a hπ ha P hPm hPd ξ z hz hξ m hm
  have he : 0 < mA.ramificationIdx' m :=
    Nat.pos_iff_ne_zero.mpr
      (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver m
        (IsDiscreteValuationRing.not_a_field A))
  have hge : p ≤ Module.finrank K L :=
    (Nat.le_of_dvd he hdvd).trans
      ((Ideal.ramificationIdx'_eq_ramificationIdx mA m
          (IsDiscreteValuationRing.not_a_field A)) ▸
        (ramificationIdx_and_inertiaDeg_le_finrank A K L m hm).1)
  rcases ramification_cases_of_isGalois_of_finrank_dvd_prime
      A K L p hp hdegree with htriv | hunram | htotal | hres
  · exact ((not_le.mpr hp.one_lt)
      (finrank_eq_one_of_surjective_algebraMap K L htriv ▸ hge)).elim
  · obtain ⟨_, h⟩ := hunram
    obtain ⟨_, heq, _⟩ := h m hm
    rw [heq] at hdvd
    exact (hp.not_dvd_one hdvd).elim
  · exact htotal
  · obtain ⟨hDVR, hres⟩ := hres
    let := hDVR
    obtain ⟨hOverB, heq, _⟩ := hres
    let := hOverB
    have hdvdB := natDegree_dvd_ramificationIdx_of_coprime_pole
      A K L p n hn hcop π a hπ ha P hPm hPd ξ z hz hξ
      (IsLocalRing.maximalIdeal B) (IsLocalRing.maximalIdeal.isMaximal B)
    rw [heq] at hdvdB
    exact (hp.not_dvd_one hdvdB).elim

/-- Let `A` be a discrete valuation ring with fraction field `K` of characteristic
`p > 0`. If `L = K[z]` and `z ^ p - z = ξ`, then `L / K` is Galois and is either
trivial, unramified of degree `p`, totally ramified of ramification index `p`, or
weakly unramified with purely inseparable residue extension of degree `p`.

Moreover, for a uniformizer `π` of `A`, an integral `ξ` gives one of the first two
cases; a pole of order prime to `p` gives the totally ramified case; and a pole whose
positive order is divisible by `p` and whose leading coefficient is not a `p`-th
power in the residue field gives the weakly unramified, residually inseparable case. -/
@[stacks 09F0]
theorem isGalois_and_ramification_cases_of_adjoin_root_artinSchreier
    (A : Type uA) (K : Type uK) (L : Type uL)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    (p : ℕ) (hp : p.Prime) [CharP K p]
    (ξ : K) (z : L)
    (hz : z ^ p - z = algebraMap K L ξ)
    (hgen : Algebra.adjoin K {z} = ⊤)
    (π : A) (hπ : Irreducible π) :
    ∃ hfin : Module.Finite K L,
      letI := hfin
      let B := integralClosure A L
      let mA := IsLocalRing.maximalIdeal A
      let trivial : Prop := Function.Surjective (algebraMap K L)
      let unramified : Prop :=
        Module.finrank K L = p ∧
          ∀ m : Ideal B, m.IsMaximal → ∃ _ : m.LiesOver mA,
            Ideal.ramificationIdx' mA m = 1 ∧
              @Algebra.IsSeparable (A ⧸ mA) (B ⧸ m) _ _
                (Ideal.Quotient.algebraOfLiesOver m mA)
      let totallyRamified : Prop :=
        Stacks.KummerExtension.IsTotallyRamified A K L ∧
          ∀ m : Ideal B, m.IsMaximal → m.LiesOver mA →
            Ideal.ramificationIdx' mA m = p
      let residuallyInseparable : Prop :=
        ∃ hDVR : IsDiscreteValuationRing B,
          letI := hDVR
          let mB := IsLocalRing.maximalIdeal B
          ∃ _ : mB.LiesOver mA,
            Ideal.ramificationIdx' mA mB = 1 ∧
              letI := Ideal.Quotient.algebraOfLiesOver mB mA
              IsPurelyInseparable (A ⧸ mA) (B ⧸ mB) ∧
                Module.finrank (A ⧸ mA) (B ⧸ mB) = p
      IsGalois K L ∧
        (trivial ∨ unramified ∨ totallyRamified ∨ residuallyInseparable) ∧
        ((∃ a : A, ξ = algebraMap A K a) → trivial ∨ unramified) ∧
        (∀ (n : ℕ) (a : A), 0 < n → ¬p ∣ n → IsUnit a →
          ξ = (algebraMap A K π)⁻¹ ^ n * algebraMap A K a → totallyRamified) ∧
        (∀ (n : ℕ) (a : A), 0 < n → p ∣ n →
          (¬∃ b : IsLocalRing.ResidueField A, IsLocalRing.residue A a = b ^ p) →
          ξ = (algebraMap A K π)⁻¹ ^ n * algebraMap A K a →
            residuallyInseparable) := by
  obtain ⟨hfin, hdegree⟩ := finrank_dvd_artin_schreier K L p hp ξ z hz hgen
  let := hfin
  let : IsGalois K L := isGalois_artin_schreier K L p hp ξ z hz hgen
  refine ⟨hfin, inferInstance,
    ramification_cases_of_isGalois_of_finrank_dvd_prime A K L p hp hdegree,
    ?_, ?_, ?_⟩
  · rintro ⟨a, rfl⟩
    apply unramified_or_trivial_of_integral_artin_schreier A K L p hp a z _ hgen hdegree
    simpa only [← IsScalarTower.algebraMap_apply] using hz
  · intro n a hn hnp ha hξ
    have hXdeg : (Polynomial.X : Polynomial A).degree < (p : WithBot ℕ) := by
      rw [Polynomial.degree_X]
      exact_mod_cast hp.one_lt
    have hXd : (Polynomial.X ^ p - Polynomial.X : Polynomial A).natDegree = p := by
      have hp1 : 1 < p := hp.one_lt
      rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt, Polynomial.natDegree_X_pow]
      simp only [Polynomial.natDegree_X, Polynomial.natDegree_X_pow]
      omega
    exact totally_ramified_of_coprime_pole
      A K L p n hp hn hnp hdegree π a hπ ha _ (Polynomial.monic_X_pow_sub hXdeg) hXd ξ z
      (by simpa only [map_sub, map_pow, Polynomial.aeval_X] using hz) hξ
  · intro n a hn hnp ha hξ
    obtain ⟨k, rfl⟩ := hnp
    have hk : 0 < k := Nat.pos_of_mul_pos_left hn
    apply residually_inseparable_of_divisible_pole
      A K L p hp hdegree k hk π a hπ z _ ha
    rw [hz, hξ, map_mul, map_pow, map_inv₀,
      ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

end IsDiscreteValuationRing
