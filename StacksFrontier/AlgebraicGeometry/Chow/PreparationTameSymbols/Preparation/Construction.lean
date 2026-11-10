module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.LocalProperties.Basic
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.Length
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import StacksFrontier.AlgebraicGeometry.Chow.PreparationTameSymbols.Basic
public import StacksFrontier.AlgebraicGeometry.SemilocalFibre.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.Parameters
public import StacksFrontier.RingTheory.Length.SemilocalDecomposition
public import StacksFrontier.RingTheory.Localization.Glueing.RingHomGluing.Away
import StacksFrontier.RingTheory.Length.SemiLocal
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.PreparationTameSymbols.Preparation.Defs
import all StacksFrontier.AlgebraicGeometry.Chow.PreparationTameSymbols.Preparation.Defs
public import StacksFrontier.AlgebraicGeometry.Chow.PreparationTameSymbols.Preparation.LocalOrders
import all StacksFrontier.AlgebraicGeometry.Chow.PreparationTameSymbols.Preparation.LocalOrders
public import StacksFrontier.AlgebraicGeometry.Chow.PreparationTameSymbols.Preparation.LocalGluing
import all StacksFrontier.AlgebraicGeometry.Chow.PreparationTameSymbols.Preparation.LocalGluing

/-!
# Preparing nonzerodivisors for the tame symbol: the construction

Finitely many nonzerodivisors in a one-dimensional Noetherian local ring can be made, after a
finite modification supported at the maximal ideal, into unit multiples of powers of one common
element at every maximal ideal of the modification. This file constructs such a preparation. Two
nonzerodivisors are prepared by induction on the order of the first one, using the comparison of
orders in
`StacksFrontier.AlgebraicGeometry.Chow.PreparationTameSymbols.Preparation.LocalOrders`; a longer
family is prepared by adding its elements one at a time, glueing local preparations with
`StacksFrontier.AlgebraicGeometry.Chow.PreparationTameSymbols.Preparation.LocalGluing`.

## Main results

* `AlgebraicGeometry.exists_tameSymbolPreparation` constructs a tame-symbol preparation for a
  family of at least two nonzerodivisors which are not all units, given the two named inputs.
* `AlgebraicGeometry.tameSymbolPreparation` is a chosen such preparation, bundled as an
  `AlgebraicGeometry.PreparedTameSymbolExtension`.

## References

* [Stacks Project, Tag 0EAG](https://stacks.math.columbia.edu/tag/0EAG)
-/

@[expose] public section

open IsLocalRing

universe u v

namespace AlgebraicGeometry

private theorem transport_power_factorization
    {R : Type*} [CommRing R] {r : ℕ} (a : Fin r → R)
    {p s : R} (u : Fin r → Rˣ) (e : Fin r → ℕ)
    (h : ∀ i, a i = (u i : R) * p ^ e i)
    (v : Rˣ) (f : ℕ) (hp : p = (v : R) * s ^ f) :
    ∀ i, a i = ((u i * v ^ e i : Rˣ) : R) * s ^ (f * e i) := by
  intro i
  rw [h i, hp, mul_pow, pow_mul]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val]
  ring

private theorem isLocalRing_of_unique_maximal
    {S : Type*} [CommRing S] (q : MaximalSpectrum S)
    (huniq : ∀ q' : MaximalSpectrum S, q' = q) : IsLocalRing S := by
  let : Subsingleton (MaximalSpectrum S) :=
    ⟨fun q₁ q₂ => (huniq q₁).trans (huniq q₂).symm⟩
  let : Nonempty (MaximalSpectrum S) := ⟨q⟩
  exact IsLocalRing.of_singleton_maximalSpectrum

private noncomputable def localAlgEquiv_at_unique_maximal
    {S : Type*} [CommRing S] (q : MaximalSpectrum S)
    (huniq : ∀ q' : MaximalSpectrum S, q' = q) :
    S ≃ₐ[S] Localization.AtPrime q.asIdeal := by
  letI : IsLocalRing S := isLocalRing_of_unique_maximal q huniq
  have hunit : q.asIdeal.primeCompl ≤ IsUnit.submonoid S := by
    intro s hs
    change IsUnit (s : S)
    apply (notMem_maximalIdeal).mp
    rw [← eq_maximalIdeal q.isMaximal]
    exact hs
  exact IsLocalization.atUnits S q.asIdeal.primeCompl hunit

private theorem divides_of_divides_at_unique_maximal
    {S : Type u} [CommRing S] (q : MaximalSpectrum S)
    (huniq : ∀ q' : MaximalSpectrum S, q' = q)
    {x y : S}
    (hdiv : algebraMap S (Localization.AtPrime q.asIdeal) x ∣
      algebraMap S (Localization.AtPrime q.asIdeal) y) : x ∣ y := by
  let e := localAlgEquiv_at_unique_maximal q huniq
  obtain ⟨z, hz⟩ := hdiv
  refine ⟨e.symm z, ?_⟩
  apply e.injective
  have he (s : S) : e s = algebraMap S (Localization.AtPrime q.asIdeal) s := by
    simpa using e.commutes s
  rw [map_mul, he y, he x, e.apply_symm_apply]
  exact hz

private theorem dimension_one_of_unique_finite_extension
    {A S : Type u} [CommRing A] [IsLocalRing A]
    [CommRing S] [Algebra A S] [Algebra.IsIntegral A S]
    (hdim : ringKrullDim A = 1)
    {a : A} (ham : a ∈ maximalIdeal A)
    (ha : IsRegular (algebraMap A S a))
    (q : MaximalSpectrum S)
    (huniq : ∀ q' : MaximalSpectrum S, q' = q) :
    ringKrullDim S = 1 :=
  (ringKrullDim_eq_of_ringEquiv (localAlgEquiv_at_unique_maximal q huniq).toRingEquiv).trans
    (local_dimension_one_of_integral hdim ham ha q.asIdeal)

private theorem finite_order_toNat_lt {a b : ℕ∞}
    (hab : a < b) (hb : b ≠ ⊤) : a.toNat < b.toNat := by
  have ha : a ≠ ⊤ := ne_top_of_lt hab
  rw [← ENat.natCast_toNat ha, ← ENat.natCast_toNat hb] at hab
  exact_mod_cast hab

private theorem maximalIdeal_pow_le_span_of_regular_nonunit
    {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hdim : ringKrullDim A = 1) {a : A}
    (ha : IsRegular a) (hunit : ¬ IsUnit a) :
    ∃ n : ℕ, maximalIdeal A ^ n ≤ Ideal.span {a} := by
  have ham : a ∈ maximalIdeal A := (mem_maximalIdeal a).2 hunit
  have hmin : ∀ p ∈ minimalPrimes A, a ∉ p := by
    intro p hp hmem
    exact (notMem_nonZeroDivisors_of_mem_mem_minimalPrimes hmem hp)
      ha.mem_nonZeroDivisors
  have hrad : (Ideal.span {a}).radical = maximalIdeal A :=
    (IsLocalRing.radical_span_eq_maximalIdeal_iff_notMem_minimalPrimes
      hdim ham).2 hmin
  exact Ideal.exists_pow_le_of_le_radical_of_fg (le_of_eq hrad.symm)
    (IsNoetherian.noetherian _)

private theorem regular_map_of_regular_map_nonunit
    {A B : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [CommRing B] [Algebra A B]
    (hdim : ringKrullDim A = 1) {a x : A}
    (ha : IsRegular (algebraMap A B a)) (hanot : ¬ IsUnit a)
    (hx : IsRegular x) : IsRegular (algebraMap A B x) := by
  by_cases hux : IsUnit x
  · exact (hux.map (algebraMap A B)).isRegular
  obtain ⟨n, hn⟩ := maximalIdeal_pow_le_span_of_regular_nonunit hdim hx hux
  have ham : a ∈ maximalIdeal A := (mem_maximalIdeal a).2 hanot
  have hdiv : x ∣ a ^ n := by
    have hmem : a ^ n ∈ Ideal.span ({x} : Set A) := hn (Ideal.pow_mem_pow ham n)
    exact (Ideal.mem_span_singleton).mp hmem
  obtain ⟨c, hc⟩ := hdiv
  have hregpow : IsRegular (algebraMap A B a ^ n) := ha.pow n
  rw [← map_pow, hc, map_mul] at hregpow
  exact (isRegular_mul_iff.mp hregpow).1

private theorem exists_global_maximal_factorization_exponent
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hdim : ringKrullDim A = 1) {a b : A}
    (ha : IsRegular a) (hb : IsRegular b)
    (ham : a ∈ maximalIdeal A) :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra A S),
      (algebraMap A S).Finite ∧ Function.Injective (algebraMap A S) ∧
      (∃ j : ℕ, maximalIdeal A ^ j • (⊤ : Submodule A S) ≤
        LinearMap.range (Algebra.linearMap A S)) ∧
      IsRegular (algebraMap A S a) ∧ IsRegular (algebraMap A S b) ∧
      ∃ m : ℕ, ∃ c : S,
        algebraMap A S b = (algebraMap A S a) ^ m * c ∧
        ∀ (T : Type u) [CommRing T] [Algebra A T],
          (algebraMap A T).Finite → Function.Injective (algebraMap A T) →
          (∃ j : ℕ, maximalIdeal A ^ j • (⊤ : Submodule A T) ≤
            LinearMap.range (Algebra.linearMap A T)) →
          IsRegular (algebraMap A T a) → IsRegular (algebraMap A T b) →
          ∀ k : ℕ, (∃ d : T,
            algebraMap A T b = (algebraMap A T a) ^ k * d) → k ≤ m := by
  classical
  obtain ⟨n, hn⟩ :=
    exists_bound_factorization_exponent_of_finite_extension
      A hdim ha.isSMulRegular hb.isSMulRegular ham
  let P : ℕ → Prop := fun m =>
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra A S),
      (algebraMap A S).Finite ∧ Function.Injective (algebraMap A S) ∧
      (∃ j : ℕ, maximalIdeal A ^ j • (⊤ : Submodule A S) ≤
        LinearMap.range (Algebra.linearMap A S)) ∧
      IsRegular (algebraMap A S a) ∧ IsRegular (algebraMap A S b) ∧
      ∃ c : S, algebraMap A S b = (algebraMap A S a) ^ m * c
  let m := Nat.findGreatest P n
  have hzero : P 0 := by
    refine ⟨A, inferInstance, inferInstance, ?_, ?_, ?_, ?_, ?_, b, ?_⟩
    · change Module.Finite A A
      infer_instance
    · simpa using (Function.injective_id : Function.Injective (id : A → A))
    · refine ⟨0, ?_⟩
      intro x hx
      exact ⟨x, by simp⟩
    · simpa using ha
    · simpa using hb
    · simp
  have hm : P m := Nat.findGreatest_spec (Nat.zero_le n) hzero
  obtain ⟨S, instS, algS, hfin, hinj, hquot, hareg, hbreg, c, hc⟩ := hm
  let _ : CommRing S := instS
  let _ : Algebra A S := algS
  refine ⟨S, instS, algS, hfin, hinj, hquot, hareg, hbreg, m, c, hc, ?_⟩
  intro T instT algT hfinT hinjT hquotT haregT hbregT k hk
  let _ : CommRing T := instT
  let _ : Algebra A T := algT
  have hkn : k ≤ n := hn T hfinT hinjT k hk
  exact Nat.le_findGreatest hkn
    ⟨T, instT, algT, hfinT, hinjT, hquotT, haregT, hbregT, hk⟩

private theorem factorization_exponent_succ_of_residual_divides
    {A S T : Type*} [CommRing A] [CommRing S] [CommRing T]
    [Algebra A S] [Algebra S T] [Algebra A T] [IsScalarTower A S T]
    {a b : A} {m : ℕ} {d : T} {cS : S}
    (hfac : algebraMap A S b = (algebraMap A S a) ^ m * cS)
    (hc : algebraMap S T cS = algebraMap A T a * d) :
    algebraMap A T b = (algebraMap A T a) ^ (m + 1) * d := by
  rw [IsScalarTower.algebraMap_apply A S T b, hfac, map_mul, map_pow,
    ← IsScalarTower.algebraMap_apply A S T a, hc, pow_succ]
  ring

private theorem residual_not_divisible_at_maximal_exponent
    {A S T : Type u} [CommRing A] [IsLocalRing A]
    [CommRing S] [CommRing T]
    [Algebra A S] [Algebra S T] [Algebra A T] [IsScalarTower A S T]
    {a b : A} {m : ℕ} {c : S}
    (hfac : algebraMap A S b = (algebraMap A S a) ^ m * c)
    (hmax : ∀ (U : Type u) [CommRing U] [Algebra A U],
      (algebraMap A U).Finite → Function.Injective (algebraMap A U) →
      (∃ j : ℕ, maximalIdeal A ^ j • (⊤ : Submodule A U) ≤
        LinearMap.range (Algebra.linearMap A U)) →
      IsRegular (algebraMap A U a) → IsRegular (algebraMap A U b) →
      ∀ k : ℕ, (∃ d : U,
        algebraMap A U b = (algebraMap A U a) ^ k * d) → k ≤ m)
    (hfin : (algebraMap A T).Finite)
    (hinj : Function.Injective (algebraMap A T))
    (hquot : ∃ j : ℕ, maximalIdeal A ^ j • (⊤ : Submodule A T) ≤
      LinearMap.range (Algebra.linearMap A T))
    (ha : IsRegular (algebraMap A T a))
    (hb : IsRegular (algebraMap A T b))
    {d : T} (hdiv : algebraMap S T c = algebraMap A T a * d) : False := by
  have hnext : algebraMap A T b = (algebraMap A T a) ^ (m + 1) * d :=
    factorization_exponent_succ_of_residual_divides hfac hdiv
  have hle := hmax T hfin hinj hquot ha hb (m + 1) ⟨d, hnext⟩
  omega

private theorem nonunit_cofactor_of_no_reverse_division
    {R : Type*} [CommRing R] {x c d : R}
    (h : x = c * d) (hnot : ¬ x ∣ c) : ¬ IsUnit d := by
  intro hd
  apply hnot
  rw [h]
  exact (hd.mul_right_dvd).mpr (dvd_refl c)

private theorem cofactor_of_unique_local_comparison
    {T : Type u} [CommRing T]
    (q : MaximalSpectrum T) (huniq : ∀ q' : MaximalSpectrum T, q' = q)
    {x c : T} (hnot : ¬ x ∣ c)
    (hcomp : algebraMap T (Localization.AtPrime q.asIdeal) x ∣
        algebraMap T (Localization.AtPrime q.asIdeal) c ∨
      algebraMap T (Localization.AtPrime q.asIdeal) c ∣
        algebraMap T (Localization.AtPrime q.asIdeal) x) :
    ∃ d : T, x = c * d ∧ ¬ IsUnit d := by
  rcases hcomp with hxc | hcx
  · exact (hnot (divides_of_divides_at_unique_maximal q huniq hxc)).elim
  · obtain ⟨d, hd⟩ := divides_of_divides_at_unique_maximal q huniq hcx
    exact ⟨d, hd, nonunit_cofactor_of_no_reverse_division hd hnot⟩

private theorem regular_atPrime_of_regular
    {B : Type*} [CommRing B] (q : Ideal B) [q.IsPrime]
    {x : B} (hx : IsRegular x) :
    IsRegular (algebraMap B (Localization.AtPrime q) x) :=
  isRegular_iff_mem_nonZeroDivisors.mpr
    (IsLocalization.map_nonZeroDivisors_le q.primeCompl (Localization.AtPrime q)
      ⟨x, hx.mem_nonZeroDivisors, rfl⟩)

private theorem regular_of_regular_at_all_maximal_ideals
    {R : Type*} [CommRing R] {x : R}
    (h : ∀ (q : Ideal R) [q.IsMaximal],
      IsRegular (algebraMap R (Localization.AtPrime q) x)) :
    IsRegular x := by
  rw [isRegular_iff_mem_nonZeroDivisors, mem_nonZeroDivisors_iff_left]
  intro y hxy
  apply eq_zero_of_localization y
  intro q hq
  let : q.IsMaximal := hq
  apply (h q).left
  simpa only [map_mul, map_zero, mul_zero] using
    congrArg (algebraMap R (Localization.AtPrime q)) hxy

private theorem regular_map_of_preparation
    {A : Type*} {B : Type*} [CommRing A] [IsLocalRing A]
    [CommRing B] [Algebra A B] {r : ℕ} {a : Fin r → A}
    (P : TameSymbolPreparation a B) (i : Fin r) :
    IsRegular (algebraMap A B (a i)) := by
  apply regular_of_regular_at_all_maximal_ideals
  intro q hq
  rw [P.factorization q i]
  exact isRegular_mul_iff.mpr
    ⟨(P.factorUnit q i).isUnit.isRegular,
      (P.parameter_isRegular q).pow (P.exponent q i)⟩

private theorem regular_map_of_preparation_of_nonunit
    {A : Type*} {B : Type*} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] [CommRing B] [Algebra A B]
    {r : ℕ} {a : Fin r → A}
    (P : TameSymbolPreparation a B)
    (hunit : ¬ ∀ i, IsUnit (a i))
    (hdim : ringKrullDim A = 1)
    {x : A} (hx : IsRegular x) :
    IsRegular (algebraMap A B x) := by
  push Not at hunit
  obtain ⟨i, hi⟩ := hunit
  exact regular_map_of_regular_map_nonunit hdim
    (regular_map_of_preparation P i) hi hx

private def preparation_snoc_of_pair
    {R : Type u} [CommRing R] [IsLocalRing R]
    {r : ℕ} (a : Fin r → R) (b p : R)
    (v : Fin r → Rˣ) (e : Fin r → ℕ)
    (h : ∀ i, a i = (v i : R) * p ^ e i)
    {T : Type u} [CommRing T] [Algebra R T]
    (Q : TameSymbolPreparation ![p, b] T) :
    TameSymbolPreparation (Fin.snoc a b) T := by
  refine {
    finite := Q.finite
    algebraMap_injective := Q.algebraMap_injective
    quotient_annihilated_by_maximalIdeal_power :=
      Q.quotient_annihilated_by_maximalIdeal_power
    parameter := Q.parameter
    parameter_isRegular := Q.parameter_isRegular
    factorUnit := fun q _ =>
      Fin.snoc (fun i =>
        Units.map (algebraMap R (Localization.AtPrime q)).toMonoidHom (v i) *
          (Q.factorUnit q 0) ^ e i) (Q.factorUnit q 1)
    exponent := fun q _ =>
      Fin.snoc (fun i => Q.exponent q 0 * e i) (Q.exponent q 1)
    factorization := ?_ }
  intro q hq i
  refine Fin.lastCases ?_ ?_ i
  · simpa [Fin.snoc_last] using Q.factorization q 1
  · intro j
    have hmap (k : Fin r) :
        algebraMap T (Localization.AtPrime q) (algebraMap R T (a k)) =
          (Units.map (algebraMap R (Localization.AtPrime q)).toMonoidHom (v k) :
            (Localization.AtPrime q)ˣ) *
            (algebraMap T (Localization.AtPrime q) (algebraMap R T p)) ^ e k := by
      rw [← IsScalarTower.algebraMap_apply R T (Localization.AtPrime q),
        h k, map_mul, map_pow]
      simp only [RingHom.toMonoidHom_eq_coe, Units.coe_map, MonoidHom.coe_ofClass]
      rw [IsScalarTower.algebraMap_apply R T (Localization.AtPrime q) p]
    have hp := Q.factorization q 0
    have hh := transport_power_factorization
      (fun k => algebraMap T (Localization.AtPrime q) (algebraMap R T (a k)))
      (fun k => Units.map (algebraMap R (Localization.AtPrime q)).toMonoidHom (v k))
      e hmap (Q.factorUnit q 0) (Q.exponent q 0) hp
    simpa only [Fin.snoc_castSucc] using hh j

private def preparation_pair_of_monomials
    {R T : Type u} [CommRing R] [IsLocalRing R]
    [CommRing T] [Algebra R T]
    (c d a b : R) (m : ℕ)
    (ha : a = c * d) (hb : b = c ^ (m + 1) * d ^ m)
    (P : TameSymbolPreparation ![c, d] T) :
    TameSymbolPreparation ![a, b] T := by
  refine {
    finite := P.finite
    algebraMap_injective := P.algebraMap_injective
    quotient_annihilated_by_maximalIdeal_power :=
      P.quotient_annihilated_by_maximalIdeal_power
    parameter := P.parameter
    parameter_isRegular := P.parameter_isRegular
    factorUnit := fun q _ =>
      ![P.factorUnit q 0 * P.factorUnit q 1,
        P.factorUnit q 0 ^ (m + 1) * P.factorUnit q 1 ^ m]
    exponent := fun q _ =>
      ![P.exponent q 0 + P.exponent q 1,
        (m + 1) * P.exponent q 0 + m * P.exponent q 1]
    factorization := ?_ }
  intro q hq i
  have hc := P.factorization q 0
  have hd := P.factorization q 1
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one] at hc hd
  fin_cases i
  · change (algebraMap T (Localization.AtPrime q))
        (algebraMap R T a) =
        ((P.factorUnit q 0 * P.factorUnit q 1 :
          (Localization.AtPrime q)ˣ) : Localization.AtPrime q) *
          P.parameter q ^ (P.exponent q 0 + P.exponent q 1)
    rw [ha, map_mul, map_mul]
    rw [hc, hd]
    simp only [Units.val_mul, pow_add]
    ring
  · change (algebraMap T (Localization.AtPrime q))
        (algebraMap R T b) =
        ((P.factorUnit q 0 ^ (m + 1) * P.factorUnit q 1 ^ m :
          (Localization.AtPrime q)ˣ) : Localization.AtPrime q) *
          P.parameter q ^ ((m + 1) * P.exponent q 0 + m * P.exponent q 1)
    rw [hb]
    simp only [map_mul, map_pow]
    rw [hc, hd]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, mul_pow, ← pow_mul, pow_add]
    ring

/-- A preparation over some finite extension gives a bundled prepared extension. -/
private theorem nonempty_preparedTameSymbolExtension_of_exists
    {R : Type u} [CommRing R] [IsLocalRing R] {r : ℕ} {a : Fin r → R}
    (h : ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T),
      Nonempty (TameSymbolPreparation a T)) :
    Nonempty (PreparedTameSymbolExtension a) := by
  obtain ⟨T, _, _, hT⟩ := h
  exact hT.map fun Q => { extension := CommAlgCat.of R T, preparation := Q }

private theorem exists_preparation_snoc_of_pair_solver
    (h0EAE : RingHomGluingAtMaximalIdeals.{u})
    (pair : ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
      [IsLocalRing R] (x y : R), ringKrullDim R = 1 →
      IsRegular x → IsRegular y → ¬ IsUnit x →
      ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T),
        Nonempty (TameSymbolPreparation ![x, y] T))
    {A S : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [CommRing S] [Algebra A S]
    {r : ℕ} (a : Fin r → A) (b : A)
    (_ha : ∀ i, IsRegular (a i)) (hb : IsRegular b)
    (hunit : ¬ ∀ i, IsUnit (a i)) (hdim : ringKrullDim A = 1)
    (P : TameSymbolPreparation a S) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C),
      Nonempty (TameSymbolPreparation (Fin.snoc a b) C) := by
  classical
  let : Module.Finite A S := P.finite
  let : IsNoetherianRing S := IsNoetherianRing.of_finite A S
  obtain ⟨k, hk⟩ := not_forall.mp hunit
  let localPair (q : MaximalSpectrum S) :
      PreparedTameSymbolExtension
        ![P.parameter q.asIdeal,
          algebraMap S (Localization.AtPrime q.asIdeal) (algebraMap A S b)] :=
    Classical.choice <| nonempty_preparedTameSymbolExtension_of_exists <| by
      let R := Localization.AtPrime q.asIdeal
      have hdimq : ringKrullDim R = 1 :=
        local_dimension_one_of_integral hdim
          ((mem_maximalIdeal (a k)).2 hk) (regular_map_of_preparation P k)
          q.asIdeal
      have hbq : IsRegular (algebraMap S R (algebraMap A S b)) :=
        regular_atPrime_of_regular q.asIdeal
          (regular_map_of_preparation_of_nonunit P hunit hdim hb)
      have hpq : ¬ IsUnit (P.parameter q.asIdeal) :=
        (mem_maximalIdeal (P.parameter q.asIdeal)).mp
          (P.parameter_mem_maximal hunit q.asIdeal)
      exact pair R (P.parameter q.asIdeal)
        (algebraMap S R (algebraMap A S b)) hdimq
        (P.parameter_isRegular q.asIdeal) hbq hpq
  let B (q : MaximalSpectrum S) : Type u := (localPair q).extension
  have hlocal (q : MaximalSpectrum S) :
      TameSymbolPreparation
        (fun i => algebraMap S (Localization.AtPrime q.asIdeal)
          (algebraMap A S ((Fin.snoc a b : Fin (r + 1) → A) i))) (B q) := by
    let R := Localization.AtPrime q.asIdeal
    have heq :
        Fin.snoc (fun i => algebraMap S R (algebraMap A S (a i)))
          (algebraMap S R (algebraMap A S b)) =
        (fun i => algebraMap S R
          (algebraMap A S ((Fin.snoc a b : Fin (r + 1) → A) i))) := by
      funext i
      refine Fin.lastCases ?_ ?_ i
      · simp
      · intro j
        simp
    rw [← heq]
    exact preparation_snoc_of_pair
      (fun i => algebraMap S R (algebraMap A S (a i)))
      (algebraMap S R (algebraMap A S b)) (P.parameter q.asIdeal)
      (P.factorUnit q.asIdeal) (P.exponent q.asIdeal)
      (P.factorization q.asIdeal) (localPair q).preparation
  exact exists_preparation_of_local_preparations h0EAE (Fin.snoc a b)
    P.algebraMap_injective P.quotient_annihilated_by_maximalIdeal_power B hlocal

private theorem exists_preparation_of_pair_solver
    (h0EAE : RingHomGluingAtMaximalIdeals.{u})
    (pair : ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
      [IsLocalRing R] (x y : R), ringKrullDim R = 1 →
      IsRegular x → IsRegular y → ¬ IsUnit x →
      ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T),
        Nonempty (TameSymbolPreparation ![x, y] T))
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {r : ℕ} (hr : 2 ≤ r) (a : Fin r → A)
    (ha : ∀ i, IsRegular (a i))
    (hunit : ¬ ∀ i, IsUnit (a i)) (hdim : ringKrullDim A = 1) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B),
      Nonempty (TameSymbolPreparation a B) := by
  classical
  have hAll : ∀ n : ℕ, ∀ (R : Type u) [CommRing R]
      [IsNoetherianRing R] [IsLocalRing R]
      (a : Fin (n + 2) → R), (∀ i, IsRegular (a i)) →
      (¬ ∀ i, IsUnit (a i)) → ringKrullDim R = 1 →
      ∃ (B : Type u) (_ : CommRing B) (_ : Algebra R B),
        Nonempty (TameSymbolPreparation a B) := by
    intro n
    induction n with
    | zero =>
        intro R instR noethR localR a ha hunit hdim
        by_cases hx : IsUnit (a 0)
        · apply exists_tameSymbolPreparation_of_one_nonunit a ha 1
          intro i hi
          fin_cases i
          · exact hx
          · exact (hi rfl).elim
        · obtain ⟨B, ringB, algB, hB⟩ :=
            pair R (a 0) (a 1) hdim (ha 0) (ha 1) hx
          have heq : ![a 0, a 1] = a := by
            funext i
            fin_cases i <;> simp
          simpa only [heq] using
            (show ∃ (B : Type u) (_ : CommRing B) (_ : Algebra R B),
              Nonempty (TameSymbolPreparation ![a 0, a 1] B) from
                ⟨B, ringB, algB, hB⟩)
    | succ n ih =>
        intro R instR noethR localR a ha hunit hdim
        let a₀ : Fin (n + 2) → R := Fin.init a
        let b : R := a (Fin.last (n + 2))
        by_cases hunit₀ : ∀ i, IsUnit (a₀ i)
        · apply exists_tameSymbolPreparation_of_one_nonunit a ha
            (Fin.last (n + 2))
          intro i hi
          obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
          exact hunit₀ j
        · obtain ⟨S, ringS, algS, ⟨P⟩⟩ :=
            ih R a₀ (fun i => ha i.castSucc) hunit₀ hdim
          let _ : CommRing S := ringS
          let _ : Algebra R S := algS
          have h := exists_preparation_snoc_of_pair_solver h0EAE pair a₀ b
            (fun i => ha i.castSucc) (ha (Fin.last (n + 2)))
            hunit₀ hdim P
          simpa only [a₀, b, Fin.snoc_init_self] using h
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 2 := ⟨r - 2, by omega⟩
  exact hAll n A a ha hunit hdim

private theorem exists_pair_preparation_of_order_drop
    (h0EAE : RingHomGluingAtMaximalIdeals.{u})
    (n : ℕ)
    (lower : ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
      [IsLocalRing R] (x y : R), ringKrullDim R = 1 →
      IsRegular x → IsRegular y → ¬ IsUnit x →
      (Ring.ord R x).toNat < n →
      ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T),
        Nonempty (TameSymbolPreparation ![x, y] T))
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (x y : A) (hdim : ringKrullDim A = 1)
    (hx : IsRegular x) (hnotx : ¬ IsUnit x)
    (hbound : (Ring.ord A x).toNat ≤ n)
    (S : Type u) [CommRing S] [Algebra A S] [Module.Finite A S]
    (hinj : Function.Injective (algebraMap A S))
    (hquot : ∃ k : ℕ, maximalIdeal A ^ k • (⊤ : Submodule A S) ≤
      LinearMap.range (Algebra.linearMap A S))
    (hxS : IsRegular (algebraMap A S x))
    (hyS : IsRegular (algebraMap A S y))
    (hdrop : ∀ q : MaximalSpectrum S,
      Ring.ord (Localization.AtPrime q.asIdeal)
        (algebraMap S (Localization.AtPrime q.asIdeal)
          (algebraMap A S x)) < Ring.ord A x) :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra A T),
      Nonempty (TameSymbolPreparation ![x, y] T) := by
  classical
  let : Ring.KrullDimLE 1 A :=
    Ring.krullDimLE_iff.mpr (by rw [hdim]; exact le_rfl)
  let : IsNoetherianRing S := IsNoetherianRing.of_finite A S
  let localPair (q : MaximalSpectrum S) :
      PreparedTameSymbolExtension
        ![algebraMap S (Localization.AtPrime q.asIdeal) (algebraMap A S x),
          algebraMap S (Localization.AtPrime q.asIdeal) (algebraMap A S y)] :=
    Classical.choice <| nonempty_preparedTameSymbolExtension_of_exists <| by
      let R := Localization.AtPrime q.asIdeal
      have hnotxq : ¬ IsUnit (algebraMap S R (algebraMap A S x)) := by
        let : IsLocalHom (algebraMap A R) :=
          isLocalHom_atPrime_of_module_finite (A := A) (B := S) q
        rw [← IsScalarTower.algebraMap_apply A S R]
        exact (isUnit_map_iff (algebraMap A R) x).not.mpr hnotx
      have hlt : (Ring.ord R (algebraMap S R (algebraMap A S x))).toNat < n :=
        (finite_order_toNat_lt (hdrop q)
          (Ring.ord_ne_top hx.mem_nonZeroDivisors)).trans_le hbound
      exact lower R
        (algebraMap S R (algebraMap A S x))
        (algebraMap S R (algebraMap A S y))
        (local_dimension_one_of_integral hdim
          ((mem_maximalIdeal x).2 hnotx) hxS q.asIdeal)
        (regular_atPrime_of_regular q.asIdeal hxS)
        (regular_atPrime_of_regular q.asIdeal hyS)
        hnotxq hlt
  let B (q : MaximalSpectrum S) : Type u := (localPair q).extension
  have hlocal (q : MaximalSpectrum S) :
      TameSymbolPreparation
        (fun i => algebraMap S (Localization.AtPrime q.asIdeal)
          (algebraMap A S ((![x, y] : Fin 2 → A) i))) (B q) := by
    have heq :
        ![algebraMap S (Localization.AtPrime q.asIdeal) (algebraMap A S x),
          algebraMap S (Localization.AtPrime q.asIdeal) (algebraMap A S y)] =
        (fun i => algebraMap S (Localization.AtPrime q.asIdeal)
          (algebraMap A S ((![x, y] : Fin 2 → A) i))) := by
      funext i
      fin_cases i <;> simp
    rw [← heq]
    exact (localPair q).preparation
  exact exists_preparation_of_local_preparations h0EAE ![x, y] hinj hquot B hlocal

private theorem exists_pair_preparation_by_order
    (h0EAE : RingHomGluingAtMaximalIdeals.{u})
    (h02Q7 : FiniteExtensionPreparingTwoNonzerodivisors.{u})
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (x y : A) (hdim : ringKrullDim A = 1)
    (hx : IsRegular x) (hy : IsRegular y) (hnotx : ¬ IsUnit x) :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra A T),
      Nonempty (TameSymbolPreparation ![x, y] T) := by
  classical
  have hAll : ∀ n : ℕ, ∀ (R : Type u) [CommRing R]
      [IsNoetherianRing R] [IsLocalRing R]
      (a b : R), ringKrullDim R = 1 →
      IsRegular a → IsRegular b → ¬ IsUnit a →
      (Ring.ord R a).toNat ≤ n →
      ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T),
        Nonempty (TameSymbolPreparation ![a, b] T) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro R instR noethR localR a b hdim ha hb hnota hbound
        have lower : ∀ (B : Type u) [CommRing B] [IsNoetherianRing B]
            [IsLocalRing B] (s t : B), ringKrullDim B = 1 →
            IsRegular s → IsRegular t → ¬ IsUnit s →
            (Ring.ord B s).toNat < n →
            ∃ (U : Type u) (_ : CommRing U) (_ : Algebra B U),
              Nonempty (TameSymbolPreparation ![s, t] U) :=
          fun B _ _ _ s t hdimB hs ht hnot hlt => ih _ hlt B s t hdimB hs ht hnot le_rfl
        obtain ⟨S, ringS, algS, hfin, hinj, hquot, haS, hbS,
          m, c, hfac, hmax⟩ :=
          exists_global_maximal_factorization_exponent hdim ha hb
            ((mem_maximalIdeal a).2 hnota)
        let : CommRing S := ringS
        let : Algebra R S := algS
        let : Module.Finite R S := (RingHom.finite_algebraMap).1 hfin
        obtain ⟨k, hk⟩ := hquot
        rcases finite_modification_order_dichotomy hdim hinj haS hnota hk with
          hdrop | ⟨q, huniq, hdegree⟩
        · exact exists_pair_preparation_of_order_drop h0EAE n lower R a b
            hdim ha hnota hbound S hinj ⟨k, hk⟩ haS hbS hdrop
        · let : IsLocalRing S := isLocalRing_of_unique_maximal q huniq
          by_cases hc : IsUnit c
          · exact exists_pair_preparation_of_unit_residual_in_finite_local_extension
              a b hinj ⟨k, hk⟩ haS m c hc hfac
          · let : IsNoetherianRing S := IsNoetherianRing.of_finite R S
            let : IsLocalHom (algebraMap R S) :=
              isLocalHom_of_module_finite_local (A := R) (S := S)
            have hnotaS : ¬ IsUnit (algebraMap R S a) :=
              (isUnit_map_iff (algebraMap R S) a).not.mpr hnota
            have hdimS : ringKrullDim S = 1 :=
              dimension_one_of_unique_finite_extension hdim
                ((mem_maximalIdeal a).2 hnota) haS q huniq
            have hregc : IsRegular c := by
              rw [hfac] at hbS
              exact (isRegular_mul_iff.mp hbS).2
            obtain ⟨T, ringT, algT, hfinST, hinjST, hquotST,
              haT', hcT, hcompT⟩ :=
              exists_finite_extension_pair_locally_comparable h02Q7 hdimS
                (algebraMap R S a) c haS hregc
                ((mem_maximalIdeal (algebraMap R S a)).2 hnotaS)
            let : CommRing T := ringT
            let : Algebra S T := algT
            let : Algebra R T :=
              ((algebraMap S T).comp (algebraMap R S)).toAlgebra
            let : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl
            let : Module.Finite S T := hfinST
            let : Module.Finite R T := Module.Finite.trans S T
            have hinjRT : Function.Injective (algebraMap R T) := hinjST.comp hinj
            have hquotRT : ∃ j : ℕ, maximalIdeal R ^ j • (⊤ : Submodule R T) ≤
                LinearMap.range (Algebra.linearMap R T) :=
              annihilated_quotient_trans_of_local_finite_extensions
                (isLocalHom_of_module_finite_local (A := R) (S := S))
                ⟨k, hk⟩ hquotST
            have haT : IsRegular (algebraMap R T a) := by
              change IsRegular (algebraMap S T (algebraMap R S a))
              exact haT'
            have hbT : IsRegular (algebraMap R T b) := by
              change IsRegular (algebraMap S T (algebraMap R S b))
              exact regular_map_of_regular_map_nonunit hdimS haT' hnotaS hbS
            obtain ⟨j, hj⟩ := hquotRT
            rcases finite_modification_order_dichotomy hdim hinjRT haT hnota hj with
              hdropT | ⟨qT, huniqT, hdegreeT⟩
            · exact exists_pair_preparation_of_order_drop h0EAE n lower R a b
                hdim ha hnota hbound T hinjRT ⟨j, hj⟩ haT hbT hdropT
            · let : IsLocalRing T := isLocalRing_of_unique_maximal qT huniqT
              have hno : ¬ algebraMap S T (algebraMap R S a) ∣
                  algebraMap S T c := by
                rintro ⟨d, hd⟩
                apply residual_not_divisible_at_maximal_exponent hfac hmax
                  ((RingHom.finite_algebraMap).2 (Module.Finite.trans S T))
                  hinjRT ⟨j, hj⟩ haT hbT
                simpa only [IsScalarTower.algebraMap_apply R S T a] using hd
              obtain ⟨d, hd, hnotd⟩ :=
                cofactor_of_unique_local_comparison qT huniqT hno
                  (hcompT qT.asIdeal).2
              let Q := Localization.AtPrime qT.asIdeal
              let aq : Q := algebraMap T Q (algebraMap R T a)
              let bq : Q := algebraMap T Q (algebraMap R T b)
              let cq : Q := algebraMap T Q (algebraMap S T c)
              let dq : Q := algebraMap T Q d
              have hxa : aq = cq * dq := by
                dsimp [aq, cq, dq]
                rw [IsScalarTower.algebraMap_apply R S T a, hd, map_mul]
              have hnotcq : ¬ IsUnit cq := by
                let : IsLocalHom (algebraMap S Q) :=
                  isLocalHom_atPrime_of_module_finite (A := S) (B := T) qT
                change ¬ IsUnit (algebraMap S Q c)
                exact (isUnit_map_iff (algebraMap S Q) c).not.mpr hc
              have hnotdq : ¬ IsUnit dq := by
                let : IsLocalHom (algebraMap T Q) :=
                  isLocalHom_atPrime_of_module_finite (A := T) (B := T) qT
                exact (isUnit_map_iff (algebraMap T Q) d).not.mpr hnotd
              have hltord : Ring.ord Q cq < Ring.ord R a :=
                residual_local_order_lt_base_of_unique_degree_one
                  hdim hinjRT haT hnota hj qT huniqT hdegreeT hxa hnotdq
              let : Ring.KrullDimLE 1 R :=
                Ring.krullDimLE_iff.mpr (by rw [hdim]; exact le_rfl)
              have hlt : (Ring.ord Q cq).toNat < n :=
                (finite_order_toNat_lt hltord
                  (Ring.ord_ne_top ha.mem_nonZeroDivisors)).trans_le hbound
              have hcq : IsRegular cq :=
                regular_atPrime_of_regular qT.asIdeal hcT
              have haq : IsRegular aq :=
                regular_atPrime_of_regular qT.asIdeal haT
              have hdq : IsRegular dq := by
                rw [hxa] at haq
                exact (isRegular_mul_iff.mp haq).2
              let : IsNoetherianRing T := IsNoetherianRing.of_finite R T
              obtain ⟨U, ringU, algU, ⟨P⟩⟩ :=
                ih _ hlt Q cq dq (hcompT qT.asIdeal).1 hcq hdq hnotcq le_rfl
              let : CommRing U := ringU
              let : Algebra Q U := algU
              have hfacT : algebraMap R T b =
                  (algebraMap R T a) ^ m * algebraMap S T c := by
                rw [IsScalarTower.algebraMap_apply R S T b, hfac,
                  map_mul, map_pow, ← IsScalarTower.algebraMap_apply R S T a]
              have hyq : bq = aq ^ m * cq := by
                simpa only [bq, aq, cq, map_mul, map_pow] using
                  congrArg (algebraMap T Q) hfacT
              have hmon : bq = cq ^ (m + 1) * dq ^ m := by
                rw [hyq, hxa, mul_pow, pow_succ]
                ring
              let Pxy : TameSymbolPreparation ![aq, bq] U :=
                preparation_pair_of_monomials cq dq aq bq m hxa hmon P
              let B (_ : MaximalSpectrum T) : Type u := U
              let : ∀ q' : MaximalSpectrum T, CommRing (B q') :=
                fun _ => ringU
              let : ∀ q' : MaximalSpectrum T,
                  Algebra (Localization.AtPrime q'.asIdeal) (B q') := by
                intro q'
                cases huniqT q'
                exact algU
              have hlocal (q' : MaximalSpectrum T) :
                  TameSymbolPreparation
                    (fun i => algebraMap T (Localization.AtPrime q'.asIdeal)
                      (algebraMap R T ((![a, b] : Fin 2 → R) i))) (B q') := by
                have hqq : q' = qT := huniqT q'
                subst q'
                have heq :
                    (fun i => algebraMap T Q
                      (algebraMap R T ((![a, b] : Fin 2 → R) i))) =
                    ![aq, bq] := by
                  funext i
                  fin_cases i <;> simp [aq, bq]
                rw [heq]
                exact Pxy
              exact exists_preparation_of_local_preparations h0EAE ![a, b]
                hinjRT ⟨j, hj⟩ B hlocal
  exact hAll (Ring.ord A x).toNat A x y hdim hx hy hnotx le_rfl

/-- Nonzerodivisors in a one-dimensional Noetherian local ring, not all of
which are units, admit a simultaneous tame-symbol preparation after a finite
extension whose quotient is supported at the maximal ideal.

The two hypotheses are the ring-theoretic inputs of the construction, each stated in full by the
`Prop`-valued definition naming it. -/
theorem exists_tameSymbolPreparation
    (h0EAE : RingHomGluingAtMaximalIdeals.{u})
    (h02Q7 : FiniteExtensionPreparingTwoNonzerodivisors.{u})
    {A : Type u} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] {r : ℕ} (hr : 2 ≤ r)
    (a : Fin r → A) (ha : ∀ i, IsRegular (a i))
    (hunit : ¬ ∀ i, IsUnit (a i)) (hdim : ringKrullDim A = 1) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B),
      Nonempty (TameSymbolPreparation a B) := by
  classical
  by_cases hsingle : ∃ k : Fin r, ∀ i, i ≠ k → IsUnit (a i)
  · obtain ⟨k, hk⟩ := hsingle
    exact exists_tameSymbolPreparation_of_one_nonunit a ha k hk
  · exact exists_preparation_of_pair_solver h0EAE
      (fun R _ _ _ x y hdim hx hy hnotx =>
        exists_pair_preparation_by_order h0EAE h02Q7 R x y hdim hx hy hnotx)
      hr a ha hunit hdim

/-- A chosen finite extension equipped with its simultaneous tame-symbol
preparation.  Its carrier and all factorization data are available through the
projections of `PreparedTameSymbolExtension`. -/
noncomputable def tameSymbolPreparation
    (h0EAE : RingHomGluingAtMaximalIdeals.{u})
    (h02Q7 : FiniteExtensionPreparingTwoNonzerodivisors.{u})
    {A : Type u} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] {r : ℕ} (hr : 2 ≤ r)
    (a : Fin r → A) (ha : ∀ i, IsRegular (a i))
    (hunit : ¬ ∀ i, IsUnit (a i)) (hdim : ringKrullDim A = 1) :
    PreparedTameSymbolExtension a :=
  Classical.choice (by
    obtain ⟨B, ringB, algebraB, h⟩ :=
      exists_tameSymbolPreparation h0EAE h02Q7 hr a ha hunit hdim
    let _ : CommRing B := ringB
    let _ : Algebra A B := algebraB
    exact h.map fun preparation ↦
      { extension := CommAlgCat.of A B, preparation := preparation })

end AlgebraicGeometry
