module

public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
public import Mathlib.RingTheory.Localization.AtPrime.Extension
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import StacksFrontier.RingTheory.DiscreteValuationRing.Kummer
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tame ramification in towers of field extensions

Let `A` be a discrete valuation ring with fraction field `K` and let `M / L / K` be finite
separable field extensions. Tame ramification with respect to `A` is stable under composition:
if `L / K` is tamely ramified with respect to `A` and `M / L` is tamely ramified with respect to
the localization of the integral closure of `A` in `L` at each of its maximal ideals, then
`M / K` is tamely ramified with respect to `A`. Conversely, tame ramification of `M / K` descends
to the intermediate extension `L / K`.

## Main results

* `IsDiscreteValuationRing.isTamelyRamified_tower`: tame ramification composes in a tower of
  finite separable field extensions.
* `IsDiscreteValuationRing.isTamelyRamified_of_isTamelyRamified_tower`: every intermediate
  extension of a finite separable extension which is tamely ramified with respect to `A` is
  itself tamely ramified with respect to `A`.

## Implementation notes

Tame ramification is expressed by `Stacks.KummerExtension.IsTamelyRamified`. The integral closure
  of the base
discrete valuation ring in the intermediate field is represented by `integralClosure A L`, and its
localization at a maximal ideal `m` by `Localization.AtPrime m`. Finiteness and separability of
`M / K` are obtained by transitivity from `L / K` and `M / L`, so they appear as `letI`s in the
statements rather than as instance hypotheses.

## References

* [Stacks Project, Tag 0EXU](https://stacks.math.columbia.edu/tag/0EXU)
* [Stacks Project, Tag 0EXV](https://stacks.math.columbia.edu/tag/0EXV)
-/

@[expose] public section

namespace IsDiscreteValuationRing

universe u v w x

section

variable (A : Type u) (K : Type v) (L : Type w) (M : Type x)
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [Field K] [Field L] [Field M]
variable [Algebra A K] [IsFractionRing A K]
variable [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
variable [Algebra A L] [IsScalarTower A K L]
variable [Algebra A M] [IsScalarTower A K M] [IsScalarTower A L M]
variable [Module.Finite K L] [Algebra.IsSeparable K L]
variable [Module.Finite L M] [Algebra.IsSeparable L M]

/-- The map on integral closures induced by the inclusion `L → M`. -/
private noncomputable def closureMap :
    integralClosure A L →ₐ[A] integralClosure A M :=
  IsIntegralClosure.lift A (integralClosure A M) M

omit [IsDomain A] [IsDiscreteValuationRing A]
  [Module.Finite L M] [Algebra.IsSeparable L M] in
private lemma closureMap_commutes (z : integralClosure A L) :
    algebraMap L M z.1 = (closureMap A L M z : integralClosure A M).1 :=
  (IsIntegralClosure.algebraMap_lift A (integralClosure A M) M z).symm

set_option maxHeartbeats 1000000 in
-- The localization and integral closure comparison produces a large elaborated term.
/-- Tame ramification over a maximal localization gives separability of the
corresponding residue extension and a ramification index prime to its characteristic. -/
private lemma isSeparable_and_coprime_ramificationIdx_of_isTamelyRamified
    [Algebra (integralClosure A L) (integralClosure A M)]
    [IsScalarTower (integralClosure A L) (integralClosure A M) M]
    [Module.IsTorsionFree (integralClosure A L) (integralClosure A M)]
    (hML : ∀ (m : Ideal (integralClosure A L)) (hm : m.IsMaximal),
      letI : m.IsPrime := hm.isPrime
      letI : IsFractionRing (integralClosure A L) L :=
        integralClosure.isFractionRing_of_finite_extension K L
      letI : Algebra (Localization.AtPrime m) L :=
        IsLocalization.localizationAlgebraOfSubmonoidLe _ _ m.primeCompl
          (nonZeroDivisors (integralClosure A L)) m.primeCompl_le_nonZeroDivisors
      letI : Algebra (Localization.AtPrime m) M :=
        ((algebraMap L M).comp (algebraMap (Localization.AtPrime m) L)).toAlgebra
      letI : IsScalarTower (Localization.AtPrime m) L M :=
        IsScalarTower.of_algebraMap_eq fun _ => rfl
      Stacks.KummerExtension.IsTamelyRamified (Localization.AtPrime m) L M)
    (q : Ideal (integralClosure A M)) (hq : q.IsMaximal)
    (p : Ideal (integralClosure A L)) (hp : p.IsMaximal)
    (hp0 : p ≠ ⊥)
    [q.LiesOver p]
    (hpq : p = q.comap (algebraMap (integralClosure A L) (integralClosure A M))) :
    @Algebra.IsSeparable (integralClosure A L ⧸ p) (integralClosure A M ⧸ q) _ _
        (Ideal.Quotient.algebraOfLiesOver q p) ∧
      (ringChar (integralClosure A L ⧸ p) = 0 ∨
        Nat.Coprime (ringChar (integralClosure A L ⧸ p))
          (Ideal.ramificationIdx' p q)) := by
  subst p
  let p := q.comap (algebraMap (integralClosure A L) (integralClosure A M))
  let : p.IsMaximal := hp
  let : p.IsPrime := hp.isPrime
  let : IsFractionRing (integralClosure A L) L :=
    integralClosure.isFractionRing_of_finite_extension K L
  let : Algebra (Localization.AtPrime p) L :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ p.primeCompl
      (nonZeroDivisors (integralClosure A L)) p.primeCompl_le_nonZeroDivisors
  let : Algebra (Localization.AtPrime p) M :=
    ((algebraMap L M).comp (algebraMap (Localization.AtPrime p) L)).toAlgebra
  let : IsScalarTower (Localization.AtPrime p) L M :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have ht := hML p hp
  dsimp [Stacks.KummerExtension.IsTamelyRamified] at ht
  let R := Localization.AtPrime p
  let D := integralClosure R M
  let : IsDedekindDomain (integralClosure A L) :=
    IsIntegralClosure.isDedekindDomain A K L (integralClosure A L)
  let : IsScalarTower (integralClosure A L) R L :=
    IsLocalization.localization_isScalarTower_of_submonoid_le R L p.primeCompl
      (nonZeroDivisors (integralClosure A L)) p.primeCompl_le_nonZeroDivisors
  let : IsScalarTower A R M := IsScalarTower.of_algebraMap_eq fun a => by
    calc
      algebraMap A M a = algebraMap L M (algebraMap A L a) :=
        IsScalarTower.algebraMap_apply A L M a
      _ = algebraMap L M (algebraMap R L (algebraMap A R a)) := by
        congr 1
        calc
          algebraMap A L a =
              algebraMap (integralClosure A L) L
                (algebraMap A (integralClosure A L) a) :=
            (IsScalarTower.algebraMap_apply A (integralClosure A L) L a).symm
          _ = algebraMap R L
                (algebraMap (integralClosure A L) R
                  (algebraMap A (integralClosure A L) a)) :=
            IsScalarTower.algebraMap_apply (integralClosure A L) R L _
          _ = algebraMap R L (algebraMap A R a) := by
            rw [← IsScalarTower.algebraMap_apply A (integralClosure A L) R a]
      _ = algebraMap R M (algebraMap A R a) :=
        IsScalarTower.algebraMap_apply R L M _
  let : IsScalarTower (integralClosure A L) L M :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower (integralClosure A L) R M :=
    IsScalarTower.of_algebraMap_eq fun z => by
      calc
        algebraMap (integralClosure A L) M z =
            algebraMap L M (algebraMap (integralClosure A L) L z) :=
          IsScalarTower.algebraMap_apply (integralClosure A L) L M z
        _ = algebraMap L M (algebraMap R L
              (algebraMap (integralClosure A L) R z)) := by
          rw [IsScalarTower.algebraMap_apply (integralClosure A L) R L]
        _ = algebraMap R M (algebraMap (integralClosure A L) R z) :=
          IsScalarTower.algebraMap_apply R L M _
  let : IsFractionRing R L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.primeCompl R L
  let : IsDedekindDomain R := IsLocalization.AtPrime.isDedekindDomain _ p R
  let : IsDedekindDomain D := IsIntegralClosure.isDedekindDomain R L M D
  let : FaithfulSMul R L :=
    (faithfulSMul_iff_algebraMap_injective R L).mpr (IsFractionRing.injective R L)
  let : Module.IsTorsionFree R M := .trans_faithfulSMul R L M
  let : Module.IsTorsionFree R D := Subalgebra.instIsTorsionFree D
  let : IsDiscreteValuationRing R :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain _ hp0 R
  have hsub : integralClosure A M ≤ Subalgebra.restrictScalars A D := fun _ hz => hz.tower_top
  let : Algebra (integralClosure A M) D := (Subalgebra.inclusion hsub).toAlgebra
  let : IsScalarTower (integralClosure A M) D M :=
    IsScalarTower.of_algebraMap_eq fun z => by
      show z.1 = (algebraMap D M (algebraMap (integralClosure A M) D z))
      rfl
  let : IsScalarTower A (integralClosure A M) D :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let B := integralClosure A L
  let C := integralClosure A M
  let E := integralClosure B M
  let : Module.Finite K M := Module.Finite.trans L M
  let : Algebra.IsSeparable K M := Algebra.IsSeparable.trans K L M
  let : IsDedekindDomain C := IsIntegralClosure.isDedekindDomain A K M C
  let : IsScalarTower A B M := IsScalarTower.of_algebraMap_eq fun a => by
    calc
      algebraMap A M a = algebraMap L M (algebraMap A L a) :=
        IsScalarTower.algebraMap_apply A L M a
      _ = algebraMap L M (algebraMap B L (algebraMap A B a)) := by
        rw [IsScalarTower.algebraMap_apply A B L]
      _ = algebraMap B M (algebraMap A B a) :=
        IsScalarTower.algebraMap_apply B L M _
  let : IsIntegralClosure C B M :=
    IsIntegralClosure.tower_top (R := A) (A := B) (B := M) (C := C)
  let e : E ≃ₐ[B] C := IsIntegralClosure.equiv B E M C
  have hEsub : E ≤ Subalgebra.restrictScalars B D := fun _ hz => hz.tower_top
  let : Algebra E D := (Subalgebra.inclusion hEsub).toAlgebra
  let : IsScalarTower E D M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower B E D := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsLocalization (Algebra.algebraMapSubmonoid M p.primeCompl) M :=
    IsLocalization.self (by
      rintro z ⟨y, hy, rfl⟩
      apply isUnit_iff_ne_zero.mpr
      have hy0 : y ≠ 0 := by
        rintro rfl
        exact hy p.zero_mem
      simpa only [map_zero] using (FaithfulSMul.algebraMap_injective B M).ne hy0)
  let : IsLocalization
      (Algebra.algebraMapSubmonoid (integralClosure A M) p.primeCompl) D := by
    let : IsLocalization (Algebra.algebraMapSubmonoid E p.primeCompl) D :=
      IsLocalization.integralClosure (R := B) (S := M) (Rf := R) (Sf := M)
        p.primeCompl
    have hmap : (Algebra.algebraMapSubmonoid C p.primeCompl).map
        e.symm.toMonoidHom = Algebra.algebraMapSubmonoid E p.primeCompl := by
      have hhom : e.symm.toMonoidHom = e.symm.toAlgHom.toMonoidHom := by
        ext z
        simp
      rw [hhom]
      exact Algebra.algebraMapSubmonoid_map_eq p.primeCompl e.symm.toAlgHom
    have hcomp (z : C) : algebraMap C D z = algebraMap E D (e.symm z) := by
      apply FaithfulSMul.algebraMap_injective D M
      show z.1 = (e.symm z).1
      exact (IsIntegralClosure.algebraMap_equiv B C M E z).symm
    exact IsLocalization.of_ringEquiv_left e.symm.toRingEquiv hmap hcomp
  let n := q.map (algebraMap (integralClosure A M) D)
  have hdisj : Disjoint
      (Algebra.algebraMapSubmonoid (integralClosure A M) p.primeCompl :
        Set (integralClosure A M))
      (q : Set (integralClosure A M)) := by
    rw [Set.disjoint_left]
    rintro z ⟨y, hy, rfl⟩ hzq
    exact hy (show y ∈ p from hzq)
  have hn : n.IsMaximal :=
    IsLocalization.isMaximal_of_isMaximal_disjoint _ D q hdisj
  let : n.IsMaximal := hn
  let : n.IsPrime := hn.isPrime
  let : IsScalarTower B E M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower B D M := IsScalarTower.of_algebraMap_eq fun z => by
    calc
      algebraMap B M z = algebraMap E M (algebraMap B E z) :=
        IsScalarTower.algebraMap_apply B E M z
      _ = algebraMap D M (algebraMap E D (algebraMap B E z)) :=
        IsScalarTower.algebraMap_apply E D M _
      _ = algebraMap D M (algebraMap B D z) := by
        rw [IsScalarTower.algebraMap_apply B E D]
  let : IsScalarTower B C D := IsScalarTower.of_algebraMap_eq fun z => by
    apply FaithfulSMul.algebraMap_injective D M
    calc
      algebraMap D M (algebraMap B D z) = algebraMap B M z :=
        (IsScalarTower.algebraMap_apply B D M z).symm
      _ = algebraMap C M (algebraMap B C z) :=
        IsScalarTower.algebraMap_apply B C M z
      _ = algebraMap D M (algebraMap C D (algebraMap B C z)) :=
        IsScalarTower.algebraMap_apply C D M _
  let hnlo : n.LiesOver (IsLocalRing.maximalIdeal R) :=
    IsLocalization.AtPrime.liesOver_map_of_liesOver p R D q
  have htn := ht n hn hnlo
  have heq : Ideal.ramificationIdx' (IsLocalRing.maximalIdeal R) n =
      Ideal.ramificationIdx'
        (q.comap (algebraMap (integralClosure A L) (integralClosure A M))) q := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx (IsLocalRing.maximalIdeal R) n
      (IsDiscreteValuationRing.not_a_field R),
      Ideal.ramificationIdx'_eq_ramificationIdx p q hp0]
    exact IsLocalization.AtPrime.ramificationIdx_map_eq_ramificationIdx p R D q
  let ebase := IsLocalization.AtPrime.equivQuotMaximalIdeal p R
  let etop := IsLocalization.AtPrime.equivQuotientMapOfIsMaximal p D q
  have hcomm := IsLocalization.AtPrime.algebraMap_equivQuotMaximalIdeal_symm_apply
    p R D q
  let : Field (R ⧸ IsLocalRing.maximalIdeal R) :=
    Ideal.Quotient.field (IsLocalRing.maximalIdeal R)
  let : Field (B ⧸ p) := Ideal.Quotient.field p
  let : Field (C ⧸ q) := Ideal.Quotient.field q
  let : Field (D ⧸ n) := Ideal.Quotient.field n
  let : Algebra (B ⧸ p) (C ⧸ q) := Ideal.Quotient.algebraOfLiesOver q p
  let : Algebra (R ⧸ IsLocalRing.maximalIdeal R) (D ⧸ n) :=
    Ideal.Quotient.algebraOfLiesOver n (IsLocalRing.maximalIdeal R)
  constructor
  · let : Algebra.IsSeparable (R ⧸ IsLocalRing.maximalIdeal R) (D ⧸ n) := htn.1
    exact Algebra.IsSeparable.of_equiv_equiv
      (A₁ := R ⧸ IsLocalRing.maximalIdeal R) (B₁ := D ⧸ n)
      (A₂ := B ⧸ p) (B₂ := C ⧸ q) ebase.symm etop.symm (by
      ext z
      simpa only [RingHom.comp_apply, RingEquiv.coe_toRingHom,
        ebase, etop, n, B, C] using hcomm z)
  · have hchar : ringChar (R ⧸ IsLocalRing.maximalIdeal R) =
        ringChar (integralClosure A L ⧸ p) := by
      let : Algebra (R ⧸ IsLocalRing.maximalIdeal R) (integralClosure A L ⧸ p) :=
        ebase.symm.toRingHom.toAlgebra
      exact Algebra.ringChar_eq (R ⧸ IsLocalRing.maximalIdeal R)
        (integralClosure A L ⧸ p)
    rw [heq, hchar] at htn
    exact htn.2

end

/-- The residue fields of a tower of rings with compatible primes form a scalar tower. -/
private lemma isScalarTower_quotient_of_liesOver {A B C : Type*} [CommRing A] [CommRing B]
    [CommRing C] [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (m : Ideal A) (p : Ideal B) (q : Ideal C) [p.LiesOver m] [q.LiesOver p] [q.LiesOver m] :
    IsScalarTower (A ⧸ m) (B ⧸ p) (C ⧸ q) :=
  IsScalarTower.of_algebraMap_eq fun z => by
    induction z using Quotient.inductionOn with
    | _ a =>
      exact congrArg (Ideal.Quotient.mk q) (IsScalarTower.algebraMap_apply A B C a)

set_option synthInstance.maxHeartbeats 200000 in
-- The residue field tower requires several algebra structures on quotient rings.
/-- Tame ramification composes in a tower of finite separable extensions when
the upper extension is tamely ramified at every maximal localization of the
intermediate integral closure. -/
@[stacks 0EXU]
theorem isTamelyRamified_tower
    (A : Type u) (K : Type v) (L : Type w) (M : Type x)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Field M]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [Algebra A L] [IsScalarTower A K L]
    [Algebra A M] [IsScalarTower A K M] [IsScalarTower A L M]
    [Module.Finite K L] [Algebra.IsSeparable K L]
    [Module.Finite L M] [Algebra.IsSeparable L M]
    (hLK : Stacks.KummerExtension.IsTamelyRamified A K L)
    (hML : ∀ (m : Ideal (integralClosure A L)) (hm : m.IsMaximal),
      letI : m.IsPrime := hm.isPrime
      letI : IsFractionRing (integralClosure A L) L :=
        integralClosure.isFractionRing_of_finite_extension K L
      letI : Algebra (Localization.AtPrime m) L :=
        IsLocalization.localizationAlgebraOfSubmonoidLe _ _ m.primeCompl
          (nonZeroDivisors (integralClosure A L)) m.primeCompl_le_nonZeroDivisors
      letI : Algebra (Localization.AtPrime m) M :=
        ((algebraMap L M).comp (algebraMap (Localization.AtPrime m) L)).toAlgebra
      letI : IsScalarTower (Localization.AtPrime m) L M :=
        IsScalarTower.of_algebraMap_eq fun _ => rfl
      Stacks.KummerExtension.IsTamelyRamified (Localization.AtPrime m) L M) :
    letI : Module.Finite K M := Module.Finite.trans L M
    letI : Algebra.IsSeparable K M := Algebra.IsSeparable.trans K L M
    Stacks.KummerExtension.IsTamelyRamified A K M := by
  let : Module.Finite K M := Module.Finite.trans L M
  let : Algebra.IsSeparable K M := Algebra.IsSeparable.trans K L M
  let B := integralClosure A L
  let C := integralClosure A M
  let f : B →ₐ[A] C := closureMap A L M
  let : Algebra B C := f.toAlgebra
  let : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun a => (f.commutes a).symm
  let : IsScalarTower B C M := IsScalarTower.of_algebraMap_eq fun z => closureMap_commutes A L M z
  let : Algebra.IsIntegral B C := ⟨fun z =>
    IsIntegral.tower_bot (FaithfulSMul.algebraMap_injective C M) z.2.tower_top⟩
  let : IsDedekindDomain B :=
    IsIntegralClosure.isDedekindDomain A K L B
  let : IsDedekindDomain C :=
    IsIntegralClosure.isDedekindDomain A K M C
  let : Module.IsTorsionFree A L := .trans_faithfulSMul A K L
  let : Module.IsTorsionFree A B := Subalgebra.instIsTorsionFree B
  let : IsScalarTower B L M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Module.IsTorsionFree B M := .trans_faithfulSMul B L M
  let : Module.IsTorsionFree B C :=
    Module.IsTorsionFree.of_faithfulSMul C B M
  intro q hq hqA
  let : q.IsMaximal := hq
  let : q.IsPrime := hq.isPrime
  let : Field (C ⧸ q) := Ideal.Quotient.field q
  let p := q.comap (algebraMap B C)
  have hp : p.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal q
  let : p.IsMaximal := hp
  let : p.IsPrime := hp.isPrime
  let : Field (B ⧸ p) := Ideal.Quotient.field p
  let : q.LiesOver p := ⟨rfl⟩
  let hpA : p.LiesOver (IsLocalRing.maximalIdeal A) :=
    Ideal.LiesOver.tower_bot q p (IsLocalRing.maximalIdeal A)
  have hp0 : p ≠ ⊥ :=
    Ideal.ne_bot_of_liesOver_of_ne_bot (IsDiscreteValuationRing.not_a_field A) p
  have hup := isSeparable_and_coprime_ramificationIdx_of_isTamelyRamified
    A K L M hML q hq p hp hp0 rfl
  have hlo := hLK p hp hpA
  let : Field (A ⧸ IsLocalRing.maximalIdeal A) :=
    Ideal.Quotient.field (IsLocalRing.maximalIdeal A)
  constructor
  · let : Algebra (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ p) :=
      Ideal.Quotient.algebraOfLiesOver p (IsLocalRing.maximalIdeal A)
    let : Algebra (A ⧸ IsLocalRing.maximalIdeal A) (C ⧸ q) :=
      Ideal.Quotient.algebraOfLiesOver q (IsLocalRing.maximalIdeal A)
    let : Algebra.IsSeparable (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ p) := hlo.1
    let : Algebra.IsSeparable (B ⧸ p) (C ⧸ q) := hup.1
    let : Algebra (B ⧸ p) (C ⧸ q) := Ideal.Quotient.algebraOfLiesOver q p
    let : IsScalarTower (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ p) (C ⧸ q) :=
      isScalarTower_quotient_of_liesOver (IsLocalRing.maximalIdeal A) p q
    exact Algebra.IsSeparable.trans _ (B ⧸ p) (C ⧸ q)
  · rcases hlo.2 with hzero | hcop₁
    · exact Or.inl hzero
    · have hchar : ringChar (A ⧸ IsLocalRing.maximalIdeal A) = ringChar (B ⧸ p) :=
        Algebra.ringChar_eq (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ p)
      rcases hup.2 with hzero | hcop₂
      · exact Or.inl (hchar.trans hzero)
      · right
        rw [Ideal.ramificationIdx'_algebra_tower' (IsLocalRing.maximalIdeal A) p q]
        exact hcop₁.mul_right (hchar ▸ hcop₂)

set_option synthInstance.maxHeartbeats 100000 in
-- Synthesizing the quotient-field tower below exceeds the default typeclass budget.
/-- Every intermediate extension of a finite separable extension tamely ramified
with respect to a discrete valuation ring is itself tamely ramified. -/
@[stacks 0EXV, sga "1 XIII 2.0.3" "subalgebra of tame"]
theorem isTamelyRamified_of_isTamelyRamified_tower
    (A : Type u) (K : Type v) (L : Type w) (M : Type x)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Field M]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [Algebra A L] [IsScalarTower A K L]
    [Algebra A M] [IsScalarTower A K M] [IsScalarTower A L M]
    [Module.Finite K L] [Algebra.IsSeparable K L]
    [Module.Finite L M] [Algebra.IsSeparable L M]
    (hM : letI : Module.Finite K M := Module.Finite.trans L M
      letI : Algebra.IsSeparable K M := Algebra.IsSeparable.trans K L M
      Stacks.KummerExtension.IsTamelyRamified A K M) :
    Stacks.KummerExtension.IsTamelyRamified A K L := by
  let B := integralClosure A L
  let C := integralClosure A M
  let f : B →ₐ[A] C :=
    ((IsScalarTower.toAlgHom A L M).comp (integralClosure A L).val).codRestrict C
      (fun a => IsIntegral.map (IsScalarTower.toAlgHom A L M) a.property)
  let : Algebra B C := f.toAlgebra
  let : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq <| fun a => (f.commutes a).symm
  have hf : Function.Injective f := fun _ _ hab =>
    Subtype.ext ((algebraMap L M).injective (congrArg Subtype.val hab))
  let : FaithfulSMul B C := (faithfulSMul_iff_algebraMap_injective B C).mpr hf
  let : FaithfulSMul A L := (faithfulSMul_iff_algebraMap_injective A L).mpr <| by
    intro a b hab
    apply IsFractionRing.injective A K
    apply (algebraMap K L).injective
    simpa only [IsScalarTower.algebraMap_apply A K L] using hab
  let : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr fun _ _ hab =>
    FaithfulSMul.algebraMap_injective A L (congrArg Subtype.val hab)
  let : Module.Finite K M := Module.Finite.trans L M
  let : Algebra.IsSeparable K M := Algebra.IsSeparable.trans K L M
  let : IsDedekindDomain B := integralClosure.isDedekindDomain A K L
  let : IsDedekindDomain C := integralClosure.isDedekindDomain A K M
  let : Algebra.IsIntegral B C := Algebra.IsIntegral.tower_top A
  let : Module.Finite A C := IsIntegralClosure.finite A K M C
  let : Module.Finite B C := Module.Finite.of_restrictScalars_finite A B C
  intro m hm hover
  let : m.IsMaximal := hm
  let : m.IsPrime := hm.isPrime
  obtain ⟨n, hn, hn_over⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := C) m
  let : n.IsMaximal := hn
  let : n.IsPrime := hn.isPrime
  let : n.LiesOver m := hn_over
  have hnA : n.LiesOver (IsLocalRing.maximalIdeal A) :=
    Ideal.LiesOver.trans n m (IsLocalRing.maximalIdeal A)
  obtain ⟨hsep, hram⟩ := hM n hn hnA
  constructor
  · let : Algebra (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ m) :=
      Ideal.Quotient.algebraOfLiesOver m (IsLocalRing.maximalIdeal A)
    let : Algebra (B ⧸ m) (C ⧸ n) := Ideal.Quotient.algebraOfLiesOver n m
    let : Algebra (A ⧸ IsLocalRing.maximalIdeal A) (C ⧸ n) :=
      Ideal.Quotient.algebraOfLiesOver n (IsLocalRing.maximalIdeal A)
    let : IsScalarTower (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ m) (C ⧸ n) :=
      isScalarTower_quotient_of_liesOver (IsLocalRing.maximalIdeal A) m n
    let : Field (A ⧸ IsLocalRing.maximalIdeal A) :=
      Ideal.Quotient.field (IsLocalRing.maximalIdeal A)
    let : Field (B ⧸ m) := Ideal.Quotient.field m
    let : Field (C ⧸ n) := Ideal.Quotient.field n
    exact Algebra.isSeparable_tower_bot_of_isSeparable
      (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ m) (C ⧸ n)
  · rcases hram with hchar | hcop
    · exact Or.inl hchar
    · rw [Ideal.ramificationIdx'_algebra_tower' (IsLocalRing.maximalIdeal A) m n] at hcop
      exact Or.inr (Nat.coprime_mul_iff_right.mp hcop).1

end IsDiscreteValuationRing
