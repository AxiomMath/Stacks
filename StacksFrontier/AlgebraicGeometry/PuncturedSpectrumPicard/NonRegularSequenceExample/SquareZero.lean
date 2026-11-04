module

public import StacksFrontier.AlgebraicGeometry.PuncturedSpectrumPicard.NonRegularSequenceExample.Rings
import StacksFrontier.AlgebraicGeometry.LocalCohomology.Generalities.QuasiCoherentExtension
import StacksFrontier.RingTheory.LocalCohomology.DepthVanishing.DepthEqLocalCohomology
import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.ComplementSheafCohomology
import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.CohomologyWithSupportComparison
import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityLocalCase.PuncturedComplement
import StacksFrontier.AlgebraicGeometry.Modules.TildeExactness
import StacksFrontier.RingTheory.LocalCohomology.VanishingTFAE.ComplementSections
import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.ComparisonAndDegreeZero
import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.GlobalSheafCohomologyComparison

/-!
# The square-zero description of the non-regular-sequence example

The coordinate inclusion `A₀ → A` and reduction `A → A₀`, the square-zero description
`A ≅ A₀[w]/(w²)` (`exampleRing_equiv_truncatedPolynomial`), `depth A = 2`, and the global
functions on the punctured spectra of `A₀` and `A`, for [Stacks, Tag 0F9L].
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.MvPowerSeries.RegularParameters

namespace Stacks.PuncturedSpectrumPicard.NonRegularSequence

universe u

private theorem four_element_set_rotate {α : Type*} (a b c d : α) :
    ({a, b, c, d} : Set α) = {d, a, b, c} := by
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

private theorem powerSeries_eq_remainder_mod_X_sq {R : Type*} [CommSemiring R]
    (f : PowerSeries R) :
    ∃ g : PowerSeries R,
      f = PowerSeries.C (PowerSeries.coeff 0 f) +
        PowerSeries.C (PowerSeries.coeff 1 f) * PowerSeries.X +
          PowerSeries.X ^ 2 * g := by
  refine ⟨PowerSeries.mk (fun n => PowerSeries.coeff (n + 2) f), ?_⟩
  have htrunc :
      (PowerSeries.trunc 2 f : PowerSeries R) =
        PowerSeries.C (PowerSeries.coeff 0 f) +
          PowerSeries.C (PowerSeries.coeff 1 f) * PowerSeries.X := by
    apply PowerSeries.ext
    intro n
    rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
    by_cases h0 : n = 0
    · subst n
      simp
    · by_cases h1 : n = 1
      · subst n
        simp
      · have hn : ¬ n < 2 := by omega
        simp [PowerSeries.coeff_C, PowerSeries.coeff_X, h0, h1, hn]
  calc
    f = PowerSeries.X ^ 2 * PowerSeries.mk (fun n => PowerSeries.coeff (n + 2) f) +
        (PowerSeries.trunc 2 f : PowerSeries R) :=
      PowerSeries.eq_X_pow_mul_shift_add_trunc 2 f
    _ = _ := by rw [htrunc]; ring

private theorem powerSeries_X_sq_dvd_iff {R : Type*} [CommSemiring R]
    (f : PowerSeries R) :
    (PowerSeries.X : PowerSeries R) ^ 2 ∣ f ↔
      PowerSeries.coeff 0 f = 0 ∧ PowerSeries.coeff 1 f = 0 := by
  rw [PowerSeries.X_pow_dvd_iff]
  constructor
  · exact fun h => ⟨h 0 (by omega), h 1 (by omega)⟩
  · rintro ⟨h0, h1⟩ n hn
    interval_cases n <;> assumption

private theorem polynomial_mem_X_sq_iff_powerSeries_mem_X_sq {R : Type*} [CommRing R]
    (p : Polynomial R) :
    (p : PowerSeries R) ∈ Ideal.span {(PowerSeries.X : PowerSeries R) ^ 2} ↔
      p ∈ Ideal.span {(Polynomial.X : Polynomial R) ^ 2} := by
  rw [Ideal.mem_span_singleton, Ideal.mem_span_singleton]
  show (PowerSeries.X : PowerSeries R) ^ 2 ∣ (p : PowerSeries R) ↔
    (Polynomial.X : Polynomial R) ^ 2 ∣ p
  rw [PowerSeries.X_pow_dvd_iff, Polynomial.X_pow_dvd_iff]
  simp only [Polynomial.coeff_coe]

private noncomputable def powerSeriesQuotient_X_sq_equiv_polynomialQuotient
    (R : Type*) [CommRing R] :
    PowerSeries R ⧸ Ideal.span {(PowerSeries.X : PowerSeries R) ^ 2} ≃+*
      Polynomial R ⧸ Ideal.span {(Polynomial.X : Polynomial R) ^ 2} := by
  let I : Ideal (PowerSeries R) := Ideal.span {(PowerSeries.X : PowerSeries R) ^ 2}
  let J : Ideal (Polynomial R) := Ideal.span {(Polynomial.X : Polynomial R) ^ 2}
  let f : Polynomial R →+* (PowerSeries R ⧸ I) :=
    (Ideal.Quotient.mk I).comp Polynomial.coeToPowerSeries.ringHom
  have hker : RingHom.ker f = J := by
    ext p
    change Ideal.Quotient.mk I (p : PowerSeries R) = 0 ↔ p ∈ J
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact polynomial_mem_X_sq_iff_powerSeries_mem_X_sq p
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨h, hh⟩ := powerSeries_eq_remainder_mod_X_sq g
    refine ⟨Polynomial.C (PowerSeries.coeff 0 g) +
      Polynomial.C (PowerSeries.coeff 1 g) * Polynomial.X, ?_⟩
    change Ideal.Quotient.mk I
      ((Polynomial.C (PowerSeries.coeff 0 g) +
        Polynomial.C (PowerSeries.coeff 1 g) * Polynomial.X : Polynomial R) : PowerSeries R) =
      Ideal.Quotient.mk I g
    rw [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_X, hh]
    simp [I, PowerSeries.coeff_X_pow_mul']
  let φ : Polynomial R ⧸ J →+* PowerSeries R ⧸ I :=
    Ideal.Quotient.lift J f (fun p hp => (show J ≤ RingHom.ker f from hker.ge) hp)
  have hinj : Function.Injective φ := by
    intro x y h
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective y
    apply Ideal.Quotient.eq.mpr
    rw [← hker]
    exact (RingHom.sub_mem_ker_iff f).mpr h
  exact (RingEquiv.ofBijective φ ⟨hinj,
    Ideal.Quotient.lift_surjective_of_surjective _ _ hsurj⟩).symm

private theorem powerSeriesQuotient_X_sq_equiv_polynomialQuotient_C
    (R : Type*) [CommRing R] (a : R) :
    powerSeriesQuotient_X_sq_equiv_polynomialQuotient R
      (Ideal.Quotient.mk _ (PowerSeries.C a)) =
        Ideal.Quotient.mk _ (Polynomial.C a) := by
  apply (powerSeriesQuotient_X_sq_equiv_polynomialQuotient R).symm.injective
  rw [RingEquiv.symm_apply_apply]
  show Ideal.Quotient.mk _ (PowerSeries.C a) =
    Ideal.Quotient.mk _ ((Polynomial.C a : Polynomial R) : PowerSeries R)
  rw [Polynomial.coe_C]

private theorem powerSeriesQuotient_X_sq_equiv_polynomialQuotient_X
    (R : Type*) [CommRing R] :
    powerSeriesQuotient_X_sq_equiv_polynomialQuotient R
      (Ideal.Quotient.mk _ (PowerSeries.X : PowerSeries R)) =
        Ideal.Quotient.mk _ (Polynomial.X : Polynomial R) := by
  apply (powerSeriesQuotient_X_sq_equiv_polynomialQuotient R).symm.injective
  rw [RingEquiv.symm_apply_apply]
  show Ideal.Quotient.mk _ (PowerSeries.X : PowerSeries R) =
    Ideal.Quotient.mk _ ((Polynomial.X : Polynomial R) : PowerSeries R)
  rw [Polynomial.coe_X]

private theorem powerSeriesQuotient_X_sq_equiv_polynomialQuotient_remainder
    (R : Type*) [CommRing R] (f : PowerSeries R) :
    powerSeriesQuotient_X_sq_equiv_polynomialQuotient R (Ideal.Quotient.mk _ f) =
      Ideal.Quotient.mk _
        (Polynomial.C (PowerSeries.coeff 0 f) +
          Polynomial.C (PowerSeries.coeff 1 f) * Polynomial.X) := by
  obtain ⟨g, hg⟩ := powerSeries_eq_remainder_mod_X_sq f
  have hmem : f -
      (PowerSeries.C (PowerSeries.coeff 0 f) +
        PowerSeries.C (PowerSeries.coeff 1 f) * PowerSeries.X) ∈
      Ideal.span {(PowerSeries.X : PowerSeries R) ^ 2} := by
    nth_rw 1 [hg]
    have hmul : PowerSeries.X ^ 2 * g ∈
        Ideal.span {(PowerSeries.X : PowerSeries R) ^ 2} :=
      (Ideal.span {(PowerSeries.X : PowerSeries R) ^ 2}).mul_mem_right _
        (Ideal.subset_span (by simp))
    convert hmul using 1
    ring
  have hq : Ideal.Quotient.mk
      (Ideal.span {(PowerSeries.X : PowerSeries R) ^ 2}) f =
      Ideal.Quotient.mk _
        (PowerSeries.C (PowerSeries.coeff 0 f) +
          PowerSeries.C (PowerSeries.coeff 1 f) * PowerSeries.X) := by
    apply Ideal.Quotient.eq.mpr
    simpa [sub_eq_zero] using hmem
  rw [hq]
  simp only [map_add, map_mul,
    powerSeriesQuotient_X_sq_equiv_polynomialQuotient_C,
    powerSeriesQuotient_X_sq_equiv_polynomialQuotient_X]


/-- The square-zero polynomial extension of `A₀`. -/
public abbrev truncatedPolynomialRing (k : Type u) [Field k] :=
  (Polynomial (intermediateRing k)) ⧸
    Ideal.span ({(Polynomial.X : Polynomial (intermediateRing k)) ^ 2} :
      Set (Polynomial (intermediateRing k)))

local instance truncatedPolynomialIdeal_isTwoSided (k : Type u) [Field k] :
    (Ideal.span ({(Polynomial.X : Polynomial (intermediateRing k)) ^ 2} :
      Set (Polynomial (intermediateRing k)))).IsTwoSided := by
  let : CommRing (intermediateRing k) := inferInstance
  let : CommRing (Polynomial (intermediateRing k)) := inferInstance
  infer_instance

/-- Expose the quotient ring structure without relying on deep instance search through
the nested polynomial quotient. -/
public instance (k : Type u) [Field k] : CommRing (truncatedPolynomialRing k) := by
  letI : CommRing (intermediateRing k) := inferInstance
  letI : CommRing (Polynomial (intermediateRing k)) := inferInstance
  exact inferInstance

/-- The distinguished nilpotent coordinate `w` of the eight-variable quotient. -/
public def squareZeroCoordinate (k : Type u) [Field k] : exampleRing k :=
  Ideal.Quotient.mk (eightVariableIdeal k) (MvPowerSeries.X (7 : Fin 8))

/-- The inclusion of the seven retained power-series coordinates. -/
public abbrev sevenToEight : Fin 7 ↪ Fin 8 := Fin.castLEEmb (by decide)

private theorem rename_sevenVariableIdeal_le_eightVariableIdeal
    (k : Type u) [Field k] :
    Ideal.map (MvPowerSeries.rename (sevenToEight : Fin 7 ↪ Fin 8)).toRingHom
      (sevenVariableIdeal k) ≤ eightVariableIdeal k := by
  rw [sevenVariableIdeal, Ideal.map_span]
  apply Ideal.span_le.2
  rintro _ ⟨x, hx | hx | hx, rfl⟩ <;> subst x <;>
    simp only [map_add, map_mul, map_pow] <;> exact Ideal.subset_span (by simp [sevenToEight])

private theorem killCompl_X_seven (k : Type u) [Field k] :
    MvPowerSeries.killCompl (R := k) (sevenToEight : Fin 7 ↪ Fin 8)
      (MvPowerSeries.X (7 : Fin 8)) ∈ sevenVariableIdeal k := by
  have hnot : (7 : Fin 8) ∉ Set.range (sevenToEight : Fin 7 ↪ Fin 8) := by
    rintro ⟨i, hi⟩
    have hval := congrArg Fin.val hi
    simp [sevenToEight] at hval
    have hi' := i.isLt
    omega
  rw [MvPowerSeries.killCompl_X_eq_zero hnot]
  simp

private theorem killCompl_eightVariableIdeal_le_sevenVariableIdeal
    (k : Type u) [Field k] :
    Ideal.map (MvPowerSeries.killCompl (sevenToEight : Fin 7 ↪ Fin 8)).toRingHom
      (eightVariableIdeal k) ≤ sevenVariableIdeal k := by
  rw [eightVariableIdeal, Ideal.map_span]
  apply Ideal.span_le.2
  rintro y ⟨x, hx, hxy⟩
  subst y
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  have hX (i : Fin 7) : MvPowerSeries.killCompl (R := k) (sevenToEight : Fin 7 ↪ Fin 8)
      (MvPowerSeries.X (sevenToEight i)) = MvPowerSeries.X i :=
    MvPowerSeries.killCompl_X i
  have h0 : MvPowerSeries.killCompl (R := k) (sevenToEight : Fin 7 ↪ Fin 8)
      (MvPowerSeries.X (0 : Fin 8)) = MvPowerSeries.X (0 : Fin 7) := hX 0
  have h1 : MvPowerSeries.killCompl (R := k) (sevenToEight : Fin 7 ↪ Fin 8)
      (MvPowerSeries.X (1 : Fin 8)) = MvPowerSeries.X (1 : Fin 7) := hX 1
  have h2 : MvPowerSeries.killCompl (R := k) (sevenToEight : Fin 7 ↪ Fin 8)
      (MvPowerSeries.X (2 : Fin 8)) = MvPowerSeries.X (2 : Fin 7) := hX 2
  have h3 : MvPowerSeries.killCompl (R := k) (sevenToEight : Fin 7 ↪ Fin 8)
      (MvPowerSeries.X (3 : Fin 8)) = MvPowerSeries.X (3 : Fin 7) := hX 3
  have h4 : MvPowerSeries.killCompl (R := k) (sevenToEight : Fin 7 ↪ Fin 8)
      (MvPowerSeries.X (4 : Fin 8)) = MvPowerSeries.X (4 : Fin 7) := hX 4
  rcases hx with rfl | rfl | rfl | rfl
  · simp only [map_pow]
    show (MvPowerSeries.killCompl (sevenToEight : Fin 7 ↪ Fin 8)
      (MvPowerSeries.X (0 : Fin 8))) ^ 3 ∈ sevenVariableIdeal k
    rw [h0]
    exact Ideal.subset_span (by simp)
  · simp only [map_pow]
    show (MvPowerSeries.killCompl (sevenToEight : Fin 7 ↪ Fin 8)
      (MvPowerSeries.X (1 : Fin 8))) ^ 3 ∈ sevenVariableIdeal k
    rw [h1]
    exact Ideal.subset_span (by simp)
  · simp only [map_add, map_mul, map_pow]
    show MvPowerSeries.killCompl (sevenToEight : Fin 7 ↪ Fin 8)
        (MvPowerSeries.X (2 : Fin 8)) *
          (MvPowerSeries.killCompl (sevenToEight : Fin 7 ↪ Fin 8)
            (MvPowerSeries.X (0 : Fin 8))) ^ 2 +
        MvPowerSeries.killCompl (sevenToEight : Fin 7 ↪ Fin 8)
          (MvPowerSeries.X (3 : Fin 8)) *
          MvPowerSeries.killCompl (sevenToEight : Fin 7 ↪ Fin 8)
            (MvPowerSeries.X (0 : Fin 8)) *
          MvPowerSeries.killCompl (sevenToEight : Fin 7 ↪ Fin 8)
            (MvPowerSeries.X (1 : Fin 8)) +
        MvPowerSeries.killCompl (sevenToEight : Fin 7 ↪ Fin 8)
          (MvPowerSeries.X (4 : Fin 8)) *
          (MvPowerSeries.killCompl (sevenToEight : Fin 7 ↪ Fin 8)
            (MvPowerSeries.X (1 : Fin 8))) ^ 2 ∈ sevenVariableIdeal k
    rw [h0, h1, h2, h3, h4]
    exact Ideal.subset_span (by simp)
  · simp only [map_pow]
    show (MvPowerSeries.killCompl (sevenToEight : Fin 7 ↪ Fin 8)
      (MvPowerSeries.X (7 : Fin 8))) ^ 2 ∈ sevenVariableIdeal k
    exact Ideal.pow_mem_of_mem _ (killCompl_X_seven k) 2 (by norm_num)

private noncomputable def coordinateInclusion (k : Type u) [Field k] :
    intermediateRing k →+* exampleRing k :=
  Ideal.Quotient.lift (sevenVariableIdeal k)
    ((Ideal.Quotient.mk (eightVariableIdeal k)).comp
      (MvPowerSeries.rename (sevenToEight : Fin 7 ↪ Fin 8)).toRingHom)
    (by
      intro p hp
      change Ideal.Quotient.mk (eightVariableIdeal k)
        ((MvPowerSeries.rename (sevenToEight : Fin 7 ↪ Fin 8)).toRingHom p) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      have hmap :=
        (Ideal.map_le_iff_le_comap.mp (rename_sevenVariableIdeal_le_eightVariableIdeal k)) hp
      change (MvPowerSeries.rename (sevenToEight : Fin 7 ↪ Fin 8)).toRingHom p ∈
        eightVariableIdeal k at hmap
      exact hmap)

private noncomputable def coordinateReduction (k : Type u) [Field k] :
    exampleRing k →+* intermediateRing k :=
  Ideal.Quotient.lift (eightVariableIdeal k)
    ((Ideal.Quotient.mk (sevenVariableIdeal k)).comp
      (MvPowerSeries.killCompl (sevenToEight : Fin 7 ↪ Fin 8)).toRingHom)
    (by
      intro p hp
      change Ideal.Quotient.mk (sevenVariableIdeal k)
        ((MvPowerSeries.killCompl (sevenToEight : Fin 7 ↪ Fin 8)).toRingHom p) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      have hmap :=
        (Ideal.map_le_iff_le_comap.mp (killCompl_eightVariableIdeal_le_sevenVariableIdeal k)) hp
      change (MvPowerSeries.killCompl (sevenToEight : Fin 7 ↪ Fin 8)).toRingHom p ∈
        sevenVariableIdeal k at hmap
      exact hmap)

private theorem coordinateInclusion_mk (k : Type u) [Field k]
    (p : powerSeriesRing k 7) :
    coordinateInclusion k (Ideal.Quotient.mk (sevenVariableIdeal k) p) =
      Ideal.Quotient.mk (eightVariableIdeal k) (MvPowerSeries.rename sevenToEight p) := by
  simp [coordinateInclusion]

private theorem coordinateReduction_mk (k : Type u) [Field k]
    (p : powerSeriesRing k 8) :
    coordinateReduction k (Ideal.Quotient.mk (eightVariableIdeal k) p) =
      Ideal.Quotient.mk (sevenVariableIdeal k) (MvPowerSeries.killCompl sevenToEight p) := by
  simp [coordinateReduction]

private theorem coordinateReduction_coordinateInclusion (k : Type u) [Field k]
    (a : intermediateRing k) : coordinateReduction k (coordinateInclusion k a) = a := by
  let : CommRing (PowerSeries (intermediateRing k)) := inferInstance
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [coordinateInclusion_mk, coordinateReduction_mk, MvPowerSeries.killCompl_rename_app]

private theorem coordinateReduction_squareZeroCoordinate (k : Type u) [Field k] :
    coordinateReduction k (squareZeroCoordinate k) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact killCompl_X_seven k

private theorem coordinateInclusion_injective (k : Type u) [Field k] :
    Function.Injective (coordinateInclusion k) :=
  Function.LeftInverse.injective (coordinateReduction_coordinateInclusion k)

private theorem coordinateReduction_surjective (k : Type u) [Field k] :
    Function.Surjective (coordinateReduction k) :=
  Function.LeftInverse.surjective (coordinateReduction_coordinateInclusion k)

theorem squareZeroCoordinate_sq (k : Type u) [Field k] :
    squareZeroCoordinate k ^ 2 = 0 := by
  show Ideal.Quotient.mk (eightVariableIdeal k)
    ((MvPowerSeries.X (7 : Fin 8)) ^ 2) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (by simp)

private noncomputable def truncatedPolynomialLiftToExample (k : Type u) [Field k] :
    truncatedPolynomialRing k →+* exampleRing k :=
  Ideal.Quotient.lift _
    (Polynomial.eval₂RingHom (coordinateInclusion k) (squareZeroCoordinate k))
    (by
      intro p hp
      obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.mp hp
      rw [← hq]
      simp [squareZeroCoordinate_sq])

private theorem truncatedPolynomialLiftToExample_mk (k : Type u) [Field k]
    (p : Polynomial (intermediateRing k)) :
    truncatedPolynomialLiftToExample k (Ideal.Quotient.mk _ p) =
      Polynomial.eval₂RingHom (coordinateInclusion k) (squareZeroCoordinate k) p := by
  simp [truncatedPolynomialLiftToExample]

private theorem truncatedPolynomialLiftToExample_C (k : Type u) [Field k]
    (a : intermediateRing k) :
    truncatedPolynomialLiftToExample k
      (Ideal.Quotient.mk _ (Polynomial.C a)) = coordinateInclusion k a := by
  rw [truncatedPolynomialLiftToExample_mk]
  simp

private theorem truncatedPolynomialLiftToExample_X (k : Type u) [Field k] :
    truncatedPolynomialLiftToExample k
      (Ideal.Quotient.mk _ (Polynomial.X : Polynomial (intermediateRing k))) =
      squareZeroCoordinate k := by
  rw [truncatedPolynomialLiftToExample_mk]
  simp

private def lastCoordinateToPowerSeriesIndex : Fin 8 ≃ Fin 8 where
  toFun i := if h : i.val = 7 then 0 else ⟨i.val + 1, by omega⟩
  invFun i := if h : i.val = 0 then 7 else ⟨i.val - 1, by omega⟩
  left_inv i := by
    apply Fin.ext
    by_cases h : i.val = 7 <;> simp [h]
  right_inv i := by
    apply Fin.ext
    by_cases h : i.val = 0
    · simp [h]
    · have h7 : i.val - 1 ≠ 7 := by omega
      simp [h, h7]
      omega

private theorem lastCoordinateToPowerSeriesIndex_fin (i : Fin 7) :
    lastCoordinateToPowerSeriesIndex i.castSucc = i.succ := by
  apply Fin.ext
  have hlt : (i : ℕ) < 7 := i.isLt
  have h : (i : ℕ) ≠ 7 := by omega
  simp [lastCoordinateToPowerSeriesIndex, h]

private theorem lastCoordinateToPowerSeriesIndex_last :
    lastCoordinateToPowerSeriesIndex (Fin.last 7) = 0 := by
  apply Fin.ext
  simp [lastCoordinateToPowerSeriesIndex]

private theorem lastCoordinateToPowerSeriesIndex_zero :
    lastCoordinateToPowerSeriesIndex (0 : Fin 8) = (1 : Fin 8) := by decide

private theorem lastCoordinateToPowerSeriesIndex_one :
    lastCoordinateToPowerSeriesIndex (1 : Fin 8) = (2 : Fin 8) := by decide

private theorem lastCoordinateToPowerSeriesIndex_two :
    lastCoordinateToPowerSeriesIndex (2 : Fin 8) = (3 : Fin 8) := by decide

private theorem lastCoordinateToPowerSeriesIndex_three :
    lastCoordinateToPowerSeriesIndex (3 : Fin 8) = (4 : Fin 8) := by decide

private theorem lastCoordinateToPowerSeriesIndex_four :
    lastCoordinateToPowerSeriesIndex (4 : Fin 8) = (5 : Fin 8) := by decide

private theorem lastCoordinateToPowerSeriesIndex_seven :
    lastCoordinateToPowerSeriesIndex (7 : Fin 8) = (0 : Fin 8) := by decide

private noncomputable def rotateFinSuccPowerSeriesEquiv (k : Type u) [Field k] :
    powerSeriesRing k 8 ≃+* PowerSeries (powerSeriesRing k 7) :=
  ((MvPowerSeries.renameEquiv k lastCoordinateToPowerSeriesIndex).trans
    (MvPowerSeries.finSuccEquiv k 7)).toRingEquiv

private theorem rotateFinSuccPowerSeriesEquiv_rename (k : Type u) [Field k]
    (p : powerSeriesRing k 7) :
    rotateFinSuccPowerSeriesEquiv k (MvPowerSeries.rename sevenToEight p) =
      PowerSeries.C p := by
  have hidx : (fun i : Fin 7 => lastCoordinateToPowerSeriesIndex (sevenToEight i)) =
      Fin.succ := by
    funext i
    rw [show sevenToEight i = i.castSucc from Fin.ext rfl]
    exact lastCoordinateToPowerSeriesIndex_fin i
  show MvPowerSeries.finSuccEquiv k 7
    (MvPowerSeries.rename lastCoordinateToPowerSeriesIndex
      (MvPowerSeries.rename sevenToEight p)) = _
  rw [MvPowerSeries.rename_rename]
  show MvPowerSeries.finSuccEquiv k 7
    (MvPowerSeries.rename (fun i => lastCoordinateToPowerSeriesIndex (sevenToEight i)) p) = _
  rw [hidx]
  ext n x
  rw [MvPowerSeries.coeff_coeff_finSuccEquiv]
  by_cases hn : n = 0
  · subst n
    have hx : x.cons 0 = Finsupp.embDomain (Fin.succEmb 7) x := by
      ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [Finsupp.embDomain_apply]
      · exact (Finsupp.embDomain_apply_self (Fin.succEmb 7) x j).symm
    show MvPowerSeries.coeff (x.cons 0) (MvPowerSeries.rename (Fin.succEmb 7) p) = _
    rw [hx, MvPowerSeries.coeff_embDomain_rename]
    simp
  · rw [MvPowerSeries.coeff_rename_eq_zero]
    · simp [PowerSeries.coeff_C, hn]
    · rintro ⟨y, hy⟩
      have hy0 := congrArg (fun d : Fin 8 →₀ ℕ => d 0) hy
      change (Finsupp.mapDomain (Fin.succEmb 7) y) 0 = _ at hy0
      rw [← Finsupp.embDomain_eq_mapDomain (Fin.succEmb 7)] at hy0
      simp [Finsupp.embDomain_apply] at hy0
      exact hn hy0.symm


private theorem rotateFinSuccPowerSeriesEquiv_X_seven (k : Type u) [Field k] :
    rotateFinSuccPowerSeriesEquiv k (MvPowerSeries.X (7 : Fin 8)) = PowerSeries.X := by
  show MvPowerSeries.finSuccEquiv k 7
    (MvPowerSeries.rename lastCoordinateToPowerSeriesIndex (MvPowerSeries.X 7)) = _
  rw [MvPowerSeries.rename_X, lastCoordinateToPowerSeriesIndex_seven,
    MvPowerSeries.finSuccEquiv_X_zero]

private theorem rotateFinSuccPowerSeriesEquiv_map_eightVariableIdeal
    (k : Type u) [Field k] :
    Ideal.map (rotateFinSuccPowerSeriesEquiv k).toRingHom (eightVariableIdeal k) =
      Ideal.span {(PowerSeries.X : PowerSeries (powerSeriesRing k 7)) ^ 2} ⊔
        Ideal.map PowerSeries.C (sevenVariableIdeal k) := by
  let E := (rotateFinSuccPowerSeriesEquiv k).toRingHom
  have hX (i : Fin 7) : E (MvPowerSeries.X (sevenToEight i)) =
      PowerSeries.C (MvPowerSeries.X i) := by
    simpa only [E, RingEquiv.coe_toRingHom, MvPowerSeries.rename_X] using!
      rotateFinSuccPowerSeriesEquiv_rename k (MvPowerSeries.X i)
  have h0 : E (MvPowerSeries.X 0) = _ := hX 0
  have h1 : E (MvPowerSeries.X 1) = _ := hX 1
  have h2 : E (MvPowerSeries.X 2) = _ := hX 2
  have h3 : E (MvPowerSeries.X 3) = _ := hX 3
  have h4 : E (MvPowerSeries.X 4) = _ := hX 4
  have h7 : E (MvPowerSeries.X (7 : Fin 8)) = PowerSeries.X :=
    rotateFinSuccPowerSeriesEquiv_X_seven k
  show Ideal.map E (eightVariableIdeal k) = _
  rw [eightVariableIdeal, sevenVariableIdeal, Ideal.map_span, Ideal.map_span]
  simp only [Set.image_insert_eq, Set.image_singleton, map_pow, map_add, map_mul,
    h0, h1, h2, h3, h4, h7]
  rw [← Ideal.span_union]
  congr 1
  simp only [Set.singleton_union]
  exact four_element_set_rotate _ _ _ _


private theorem powerSeries_map_quotient_X_sq_ker {R S : Type*} [CommRing R]
    [CommRing S] (q : R →+* S) :
    RingHom.ker ((Ideal.Quotient.mk
      (Ideal.span ({(PowerSeries.X : PowerSeries S) ^ 2} : Set (PowerSeries S)))).comp
        (PowerSeries.map q)) =
      Ideal.span ({(PowerSeries.X : PowerSeries R) ^ 2} : Set (PowerSeries R)) ⊔
        Ideal.map PowerSeries.C (RingHom.ker q) := by
  classical
  let K : Ideal (PowerSeries R) := Ideal.span { (PowerSeries.X : PowerSeries R) ^ 2 }
  let K' : Ideal (PowerSeries S) := Ideal.span { (PowerSeries.X : PowerSeries S) ^ 2 }
  let L : Ideal (PowerSeries R) := Ideal.map PowerSeries.C (RingHom.ker q)
  ext f
  show Ideal.Quotient.mk K' (PowerSeries.map q f) = 0 ↔ f ∈ K ⊔ L
  rw [Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · intro hf
    have hc : ∀ n, n < 2 → q (PowerSeries.coeff n f) = 0 := fun n hn => by
      simpa [PowerSeries.coeff_map] using
        PowerSeries.X_pow_dvd_iff.mp (Ideal.mem_span_singleton.mp hf) n hn
    obtain ⟨g, hg⟩ := powerSeries_eq_remainder_mod_X_sq f
    have h0 : PowerSeries.C (PowerSeries.coeff 0 f) ∈ L :=
      Ideal.mem_map_of_mem PowerSeries.C (RingHom.mem_ker.mpr (hc 0 (by omega)))
    have h1 : PowerSeries.C (PowerSeries.coeff 1 f) * PowerSeries.X ∈ L :=
      L.mul_mem_right _ <| Ideal.mem_map_of_mem PowerSeries.C
        (RingHom.mem_ker.mpr (hc 1 (by omega)))
    have h2 : PowerSeries.X ^ 2 * g ∈ K := K.mul_mem_right _ (Ideal.subset_span (by simp))
    rw [hg]
    exact (K ⊔ L).add_mem ((K ⊔ L).add_mem (Ideal.mem_sup_right h0) (Ideal.mem_sup_right h1))
      (Ideal.mem_sup_left h2)
  · intro hf
    have hle : Ideal.map (PowerSeries.map q) (K ⊔ L) ≤ K' := by
      rw [Ideal.map_sup]
      apply sup_le
      · rw [Ideal.map_le_iff_le_comap]
        apply Ideal.span_le.2
        rintro _ hx
        simp only [Set.mem_singleton_iff] at hx
        subst_vars
        exact Ideal.subset_span (by simp)
      · rw [Ideal.map_le_iff_le_comap]
        intro x hx
        have hker : L ≤ RingHom.ker (PowerSeries.map q) := by
          rw [Ideal.map_le_iff_le_comap]
          intro y hy
          show PowerSeries.map q (PowerSeries.C y) = 0
          rw [PowerSeries.map_C, show q y = 0 from hy, map_zero]
        have hz : PowerSeries.map q x = 0 := hker hx
        simp [hz]
    exact hle (Ideal.mem_map_of_mem (PowerSeries.map q) hf)

private noncomputable def exampleToPowerSeriesQuotientMap (k : Type u) [Field k] :
    powerSeriesRing k 8 →+*
      PowerSeries (intermediateRing k) ⧸
        Ideal.span ({(PowerSeries.X : PowerSeries (intermediateRing k)) ^ 2} :
          Set (PowerSeries (intermediateRing k))) :=
  (Ideal.Quotient.mk _).comp
    ((PowerSeries.map (Ideal.Quotient.mk (sevenVariableIdeal k))).comp
      (rotateFinSuccPowerSeriesEquiv k).toRingHom)

private theorem exampleToPowerSeriesQuotientMap_ker (k : Type u) [Field k] :
    RingHom.ker (exampleToPowerSeriesQuotientMap k) = eightVariableIdeal k := by
  let E := rotateFinSuccPowerSeriesEquiv k
  let q : powerSeriesRing k 7 →+* intermediateRing k :=
    Ideal.Quotient.mk (sevenVariableIdeal k)
  let K : Ideal (PowerSeries (intermediateRing k)) :=
    Ideal.span {(PowerSeries.X : PowerSeries (intermediateRing k)) ^ 2}
  let F : PowerSeries (powerSeriesRing k 7) →+* PowerSeries (intermediateRing k) ⧸ K :=
    (Ideal.Quotient.mk K).comp (PowerSeries.map q)
  have hq : RingHom.ker q = sevenVariableIdeal k := by
    ext p
    simp [q]
  have hmap : Ideal.map E.toRingHom (eightVariableIdeal k) =
      Ideal.span {(PowerSeries.X : PowerSeries (powerSeriesRing k 7)) ^ 2} ⊔
        Ideal.map PowerSeries.C (RingHom.ker q) := by
    rw [hq]
    exact rotateFinSuccPowerSeriesEquiv_map_eightVariableIdeal k
  ext p
  show F (E p) = 0 ↔ p ∈ eightVariableIdeal k
  have hF : F (E p) = 0 ↔ E p ∈
      Ideal.span {(PowerSeries.X : PowerSeries (powerSeriesRing k 7)) ^ 2} ⊔
        Ideal.map PowerSeries.C (RingHom.ker q) := by
    rw [← powerSeries_map_quotient_X_sq_ker q]
    rfl
  rw [hF, ← hmap]
  show E p ∈ Ideal.map E (eightVariableIdeal k) ↔ _
  rw [Ideal.mem_map_of_equiv]
  exact ⟨fun ⟨x, hx, hxp⟩ => E.injective hxp ▸ hx, fun hp => ⟨p, hp, rfl⟩⟩

private theorem exampleToPowerSeriesQuotientMap_surjective (k : Type u) [Field k] :
    Function.Surjective (exampleToPowerSeriesQuotientMap k) :=
  Ideal.Quotient.mk_surjective.comp
    ((PowerSeries.map_surjective _ Ideal.Quotient.mk_surjective).comp
      (rotateFinSuccPowerSeriesEquiv k).surjective)

private noncomputable def exampleToTruncatedPolynomialEquiv (k : Type u) [Field k] :
    exampleRing k ≃+* truncatedPolynomialRing k :=
  ((Ideal.quotEquivOfEq (exampleToPowerSeriesQuotientMap_ker k)).symm.trans
    (RingHom.quotientKerEquivOfSurjective
      (exampleToPowerSeriesQuotientMap_surjective k))).trans
        (powerSeriesQuotient_X_sq_equiv_polynomialQuotient (intermediateRing k))

private theorem exampleToTruncatedPolynomialEquiv_mk (k : Type u) [Field k]
    (p : powerSeriesRing k 8) :
    exampleToTruncatedPolynomialEquiv k (Ideal.Quotient.mk _ p) =
      powerSeriesQuotient_X_sq_equiv_polynomialQuotient (intermediateRing k)
        (exampleToPowerSeriesQuotientMap k p) := by
  simp [exampleToTruncatedPolynomialEquiv, RingHom.quotientKerEquivOfSurjective_apply_mk]

private theorem exampleToTruncatedPolynomialEquiv_inclusion (k : Type u) [Field k]
    (a : intermediateRing k) :
    exampleToTruncatedPolynomialEquiv k (coordinateInclusion k a) =
      Ideal.Quotient.mk _ (Polynomial.C a) := by
  let : CommRing (PowerSeries (intermediateRing k)) := inferInstance
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [coordinateInclusion_mk, exampleToTruncatedPolynomialEquiv_mk]
  show powerSeriesQuotient_X_sq_equiv_polynomialQuotient (intermediateRing k)
    (Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries (intermediateRing k)) ^ 2})
      (PowerSeries.map (Ideal.Quotient.mk (sevenVariableIdeal k))
      (rotateFinSuccPowerSeriesEquiv k (MvPowerSeries.rename sevenToEight p)))) = _
  rw [rotateFinSuccPowerSeriesEquiv_rename, PowerSeries.map_C]
  exact powerSeriesQuotient_X_sq_equiv_polynomialQuotient_C _ _

private theorem exampleToTruncatedPolynomialEquiv_coordinate (k : Type u) [Field k] :
    exampleToTruncatedPolynomialEquiv k (squareZeroCoordinate k) =
      Ideal.Quotient.mk _ (Polynomial.X : Polynomial (intermediateRing k)) := by
  let : CommRing (PowerSeries (intermediateRing k)) := inferInstance
  rw [squareZeroCoordinate, exampleToTruncatedPolynomialEquiv_mk]
  show powerSeriesQuotient_X_sq_equiv_polynomialQuotient (intermediateRing k)
    (Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries (intermediateRing k)) ^ 2})
      (PowerSeries.map (Ideal.Quotient.mk (sevenVariableIdeal k))
      (rotateFinSuccPowerSeriesEquiv k (MvPowerSeries.X 7)))) = _
  rw [rotateFinSuccPowerSeriesEquiv_X_seven, PowerSeries.map_X]
  exact powerSeriesQuotient_X_sq_equiv_polynomialQuotient_X _

private theorem truncatedPolynomial_exists_representative (R : Type*) [CommRing R]
    (a : Polynomial R ⧸ Ideal.span {(Polynomial.X : Polynomial R) ^ 2}) :
    ∃ c d : R, a = Ideal.Quotient.mk _
      (Polynomial.C c + Polynomial.C d * Polynomial.X) := by
  let e := powerSeriesQuotient_X_sq_equiv_polynomialQuotient R
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (e.symm a)
  refine ⟨PowerSeries.coeff 0 p, PowerSeries.coeff 1 p, ?_⟩
  simpa [e, powerSeriesQuotient_X_sq_equiv_polynomialQuotient_remainder] using
    (congrArg e hp).symm

private theorem truncatedPolynomial_X_mul_C_injective (R : Type*) [CommRing R] :
    Function.Injective (fun a : R => Ideal.Quotient.mk
      (Ideal.span {(Polynomial.X : Polynomial R) ^ 2})
        (Polynomial.X * Polynomial.C a)) := by
  intro a b h
  simpa [sub_eq_zero] using
    Polynomial.X_pow_dvd_iff.mp (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp h)) 1
      (by decide)

private theorem exampleRing_exists_coordinates (k : Type u) [Field k]
    (a : exampleRing k) :
    ∃ c d : intermediateRing k,
      a = coordinateInclusion k c + squareZeroCoordinate k * coordinateInclusion k d := by
  obtain ⟨c, d, h⟩ := truncatedPolynomial_exists_representative (intermediateRing k)
    (exampleToTruncatedPolynomialEquiv k a)
  refine ⟨c, d, (exampleToTruncatedPolynomialEquiv k).injective ?_⟩
  rw [map_add, map_mul, exampleToTruncatedPolynomialEquiv_coordinate,
    exampleToTruncatedPolynomialEquiv_inclusion, exampleToTruncatedPolynomialEquiv_inclusion]
  simpa only [map_add, map_mul, mul_comm] using h

/-- The square-zero description, with the inclusion of `A₀` identified with constant
polynomials and the chosen eighth variable identified with `X`. -/
@[stacks 0F9L "square-zero extension with its chosen coordinates"]
public theorem exampleRing_equiv_truncatedPolynomial (k : Type u) [Field k] :
    ∃ (e : exampleRing k ≃+* truncatedPolynomialRing k)
      (ι : intermediateRing k →+* exampleRing k)
      (q : exampleRing k →+* intermediateRing k),
      (∀ p : powerSeriesRing k 7,
        ι (Ideal.Quotient.mk (sevenVariableIdeal k) p) =
          Ideal.Quotient.mk (eightVariableIdeal k) (MvPowerSeries.rename sevenToEight p)) ∧
      (∀ p : powerSeriesRing k 8,
        q (Ideal.Quotient.mk (eightVariableIdeal k) p) =
          Ideal.Quotient.mk (sevenVariableIdeal k) (MvPowerSeries.killCompl sevenToEight p)) ∧
      (∀ a : intermediateRing k,
        e (ι a) = Ideal.Quotient.mk _ (Polynomial.C a)) ∧
      e (squareZeroCoordinate k) =
        Ideal.Quotient.mk _ (Polynomial.X : Polynomial (intermediateRing k)) ∧
      (∀ a : intermediateRing k, q (ι a) = a) ∧
      q (squareZeroCoordinate k) = 0 ∧
      Function.Injective (fun a : intermediateRing k => squareZeroCoordinate k * ι a) ∧
      Function.Exact
        (fun a : intermediateRing k => squareZeroCoordinate k * ι a)
        q := by
  refine ⟨exampleToTruncatedPolynomialEquiv k, coordinateInclusion k, coordinateReduction k,
    coordinateInclusion_mk k, coordinateReduction_mk k,
    exampleToTruncatedPolynomialEquiv_inclusion k,
    exampleToTruncatedPolynomialEquiv_coordinate k,
    coordinateReduction_coordinateInclusion k,
    coordinateReduction_squareZeroCoordinate k, ?_, ?_⟩
  · intro a b h
    apply truncatedPolynomial_X_mul_C_injective (intermediateRing k)
    simpa only [map_mul, exampleToTruncatedPolynomialEquiv_coordinate,
      exampleToTruncatedPolynomialEquiv_inclusion] using
        congrArg (exampleToTruncatedPolynomialEquiv k) h
  · intro a
    constructor
    · intro ha
      obtain ⟨c, d, rfl⟩ := exampleRing_exists_coordinates k a
      simp only [map_add, map_mul, coordinateReduction_coordinateInclusion,
        coordinateReduction_squareZeroCoordinate, zero_mul, add_zero] at ha
      subst c
      exact ⟨d, by simp⟩
    · rintro ⟨b, rfl⟩
      simp [coordinateReduction_squareZeroCoordinate]

open scoped Pointwise

/-- **Stacks 0F9L** (depth of the eight-variable quotient).
The ring `A = k⟦a,b,x,y,z,u,v,w⟧/(a³, b³, xa² + yab + zb², w²)` has depth `2` along its
maximal ideal. -/
@[stacks 0F9L "depth of the eight-variable quotient"]
public theorem exampleRing_depth (k : Type u) [Field k] :
    Module.depth (exampleRing k) (IsLocalRing.maximalIdeal (exampleRing k))
      (exampleRing k) = 2 := by
  let R := intermediateRing k
  let : CommRing (PowerSeries R) := inferInstance
  let Q := PowerSeries R ⧸ Ideal.span {(PowerSeries.X : PowerSeries R) ^ 2}
  let : CommRing Q := inferInstance
  let e : exampleRing k ≃+* Q := (exampleToTruncatedPolynomialEquiv k).trans
    (powerSeriesQuotient_X_sq_equiv_polynomialQuotient R).symm
  let : Nontrivial (exampleRing k) := exampleRing_nontrivial k
  let : Nontrivial Q := e.symm.toEquiv.nontrivial
  let : IsLocalRing Q :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  let : IsNoetherianRing (powerSeriesRing k 7) := inferInstance
  let : IsNoetherianRing R :=
    isNoetherianRing_of_surjective _ _ (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have hx : (PowerSeries.X : PowerSeries R) ∈ IsLocalRing.maximalIdeal (PowerSeries R) := by
    show ¬ IsUnit (PowerSeries.X : PowerSeries R)
    simp [PowerSeries.isUnit_iff_constantCoeff]
  have hx2 : (PowerSeries.X : PowerSeries R) ^ 2 ∈
      IsLocalRing.maximalIdeal (PowerSeries R) := by
    simpa only [pow_two] using (IsLocalRing.maximalIdeal (PowerSeries R)).mul_mem_left
      PowerSeries.X hx
  have h := depth_quotient_add_one (PowerSeries R) (PowerSeries.X ^ 2) hx2
    PowerSeries.X_pow_mul_injective
  rw [depth_powerSeries, intermediateRing_depth k] at h
  rw [Module.depth_self_eq_of_ringEquiv e]
  exact ENat.add_left_injective_of_ne_top (by simp : (1 : ℕ∞) ≠ ⊤) h

private lemma puncturedSpectrum_appTop_isIso_of_two_le_depth
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hd : 2 ≤ Module.depth A (IsLocalRing.maximalIdeal A) A) :
    IsIso (Stacks.Divisors.puncturedSpectrum A).ι.appTop := by
  let U := Stacks.Divisors.puncturedSpectrum A
  have hstalk (x : Spec (.of A)) (hx : IsClosed ({x} : Set (Spec (.of A)))) :
      2 ≤ Module.depth ((Spec (.of A)).presheaf.stalk x)
        (IsLocalRing.maximalIdeal ((Spec (.of A)).presheaf.stalk x))
        ((Spec (.of A)).presheaf.stalk x) := by
    obtain rfl : x = IsLocalRing.closedPoint A := PrimeSpectrum.ext <|
      (IsLocalRing.isMaximal_iff (R := A)).mp
        ((PrimeSpectrum.isClosed_singleton_iff_isMaximal x).mp hx)
    let e : A ≃+* (Spec (.of A)).presheaf.stalk (IsLocalRing.closedPoint A) :=
      ((IsLocalization.atUnits A (IsLocalRing.maximalIdeal A).primeCompl
        (S := Localization.AtPrime (IsLocalRing.maximalIdeal A))
          fun _ hx => IsLocalRing.notMem_maximalIdeal.mp hx).toRingEquiv).trans
        (Spec.stalkIso (.of A) (IsLocalRing.closedPoint A)).commRingCatIsoToRingEquiv.symm
    let : Nontrivial ((Spec (.of A)).presheaf.stalk (IsLocalRing.closedPoint A)) :=
      e.injective.nontrivial
    let : IsLocalRing ((Spec (.of A)).presheaf.stalk (IsLocalRing.closedPoint A)) :=
      IsLocalRing.of_surjective' (e : A →+* _) e.surjective
    rwa [← Module.depth_self_eq_of_ringEquiv e]
  obtain ⟨e, he⟩ := AlgebraicGeometry.exists_iso_spec_sections_punctured_spectrum
    A (𝟙 (Spec (.of A))) hstalk
  simp only [Scheme.Hom.id_preimage] at e he
  let r := (Spec (.of A)).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
  have hr : IsIso (Spec.map r) :=
    @IsIso.of_isIso_fac_left _ _ _ _ _ _ _ _ e.isIso_hom
      (IsAffine.affine : IsIso (Spec (.of A)).toSpecΓ) he
  have hr' : IsIso r :=
    (ConcreteCategory.isIso_iff_bijective r).2 ((isIso_SpecMap_iff).1 hr)
  have hcomp : U.ι.appTop ≫ U.topIso.hom = r := by
    let f : op (⊤ : (Spec (.of A)).Opens) ⟶ op (U.ι ''ᵁ ⊤) := (homOfLE le_top).op
    let g : op (U.ι ''ᵁ ⊤) ⟶ op U := (eqToHom U.ι_image_top.symm).op
    have hfg : f ≫ g = (homOfLE le_top).op := Subsingleton.elim _ _
    simp only [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom, r, ← hfg]
    convert ((Spec (.of A)).presheaf.map_comp f g).symm using 1
    congr 1
  exact @IsIso.of_isIso_fac_right _ _ _ _ _ _ _ _ U.topIso.isIso_hom hr' hcomp

/-- Depth two identifies the global functions on the seven-variable punctured
spectrum with the original quotient, via the canonical restriction map. -/
@[stacks 0F9L "global functions on the punctured spectrum of A₀"]
public theorem intermediateRing_globalSections_puncturedSpectrum (k : Type u) [Field k] :
    let U := Stacks.Divisors.puncturedSpectrum (intermediateRing k)
    Function.Bijective
      (((Scheme.ΓSpecIso (.of (intermediateRing k))).inv ≫ U.ι.appTop).hom)  := by
  let : IsNoetherianRing (intermediateRing k) := inferInstance
  have := puncturedSpectrum_appTop_isIso_of_two_le_depth (intermediateRing k)
    (by rw [intermediateRing_depth])
  exact ConcreteCategory.bijective_of_isIso _

/-- The same global-functions identification for the square-zero quotient. -/
@[stacks 0F9L "global functions on the punctured spectrum of A"]
public theorem exampleRing_globalSections_puncturedSpectrum (k : Type u) [Field k] :
    let U := Stacks.Divisors.puncturedSpectrum (exampleRing k)
    Function.Bijective
      (((Scheme.ΓSpecIso (.of (exampleRing k))).inv ≫ U.ι.appTop).hom)  := by
  let : IsNoetherianRing (exampleRing k) := inferInstance
  have := puncturedSpectrum_appTop_isIso_of_two_le_depth (exampleRing k)
    (by rw [exampleRing_depth])
  exact ConcreteCategory.bijective_of_isIso _

end Stacks.PuncturedSpectrumPicard.NonRegularSequence
