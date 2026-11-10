module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Smooth.Field
public import Mathlib.RingTheory.Smooth.Locus
public import Mathlib.RingTheory.WittVector.Domain
public import Mathlib.RingTheory.WittVector.Identities
public import Mathlib.RingTheory.WittVector.Teichmuller
public import Mathlib.RingTheory.WittVector.Truncated

/-!
# Lifting points to the Witt vectors of length two

Let `R` be a domain of characteristic zero of finite type over `ℤ`. Then `Spec R` is smooth over
`ℤ` near its generic point, and at every point `s` of the smooth locus with residue field `κ(s)`
of characteristic `p` the canonical map `R ⟶ κ(s)` lifts to the ring `W₂(κ(s))` of Witt vectors
of length two. Base change of a model over `R` along that lift is the lift over `W₂(κ(s))` of
the fibre at `s` that Deligne–Illusie asks for.

## Main definitions

* `AlgebraicGeometry.HodgeSpreadingOut.wittTwoToField`: the canonical surjection
  `W₂(F) ⟶ F`, `x ↦ x₀`.

## Main results

* `AlgebraicGeometry.HodgeSpreadingOut.wittTwoToField_surjective` and
  `AlgebraicGeometry.HodgeSpreadingOut.isNilpotent_ker_wittTwoToField`: it is surjective, and in
  characteristic `p` its kernel squares to zero.
* `AlgebraicGeometry.HodgeSpreadingOut.mem_smoothLocus_int_bot`: **generic smoothness over `ℤ`**:
  the generic point of `Spec R` is in the smooth locus of `R` over `ℤ`.
* `AlgebraicGeometry.HodgeSpreadingOut.exists_wittTwo_lift`: at a point of the smooth locus the
  map `R ⟶ κ(s)` lifts to `W₂(κ(s))`.

## Implementation notes

The kernel of `W₂(F) ⟶ F` consists of the truncations of Verschiebungs `V x`, and
`V x · V y = V(x · F V y) = V(x · y · p)`, whose first two coordinates vanish in characteristic
`p`. Generic smoothness is the formal smoothness of the fraction field `K` of `R` over `ℤ`: `K` is
essentially of finite type over the perfect field `ℚ`, hence formally smooth over it
(`Algebra.FormallySmooth.of_perfectField`), and `ℚ` is a localization of `ℤ`.
-/

@[expose] public noncomputable section

open WittVector

universe u

namespace AlgebraicGeometry.HodgeSpreadingOut

section Witt

variable (p : ℕ) [Fact p.Prime] (F : Type u) [CommRing F]

/-- The zeroth coordinate of a product of truncated Witt vectors of length two is the product of
the zeroth coordinates. -/
theorem truncatedWittVector_two_mul_coeff_zero (x y : TruncatedWittVector p 2 F) :
    (x * y).coeff 0 = x.coeff 0 * y.coeff 0 := by
  obtain ⟨w, rfl⟩ := WittVector.truncate_surjective p 2 F x
  obtain ⟨v, rfl⟩ := WittVector.truncate_surjective p 2 F y
  rw [← map_mul, coeff_truncate, coeff_truncate, coeff_truncate]
  exact mul_coeff_zero w v

/-- **The canonical map `W₂(F) ⟶ F`**, the zeroth coordinate of a truncated Witt vector of length
two. -/
def wittTwoToField : TruncatedWittVector p 2 F →+* F where
  toFun x := x.coeff 0
  map_zero' := TruncatedWittVector.coeff_zero p 2 F 0
  map_one' := by
    rw [← map_one (WittVector.truncate (p := p) (R := F) 2), coeff_truncate]
    exact one_coeff_zero p F
  map_add' x y := by
    obtain ⟨w, rfl⟩ := WittVector.truncate_surjective p 2 F x
    obtain ⟨v, rfl⟩ := WittVector.truncate_surjective p 2 F y
    rw [← map_add, coeff_truncate, coeff_truncate, coeff_truncate]
    exact add_coeff_zero w v
  map_mul' := truncatedWittVector_two_mul_coeff_zero p F

/-- The map `W₂(F) ⟶ F` sends the truncation of a Witt vector `w` to its zeroth coefficient. -/
theorem wittTwoToField_truncate (w : WittVector p F) :
    wittTwoToField p F (WittVector.truncate 2 w) = w.coeff 0 :=
  coeff_truncate w 0

/-- The map `W₂(F) ⟶ F` is surjective. -/
theorem wittTwoToField_surjective : Function.Surjective (wittTwoToField p F) := fun a =>
  ⟨WittVector.truncate 2 (teichmuller p a), by
    rw [wittTwoToField_truncate, teichmuller_coeff_zero]⟩

/-- In characteristic `p` the product of two elements of the kernel of `W₂(F) ⟶ F` vanishes. -/
theorem mul_eq_zero_of_mem_ker_wittTwoToField [CharP F p] {x y : TruncatedWittVector p 2 F}
    (hx : x ∈ RingHom.ker (wittTwoToField p F)) (hy : y ∈ RingHom.ker (wittTwoToField p F)) :
    x * y = 0 := by
  obtain ⟨w, rfl⟩ := WittVector.truncate_surjective p 2 F x
  obtain ⟨v, rfl⟩ := WittVector.truncate_surjective p 2 F y
  rw [RingHom.mem_ker, wittTwoToField_truncate] at hx hy
  have hw : w = verschiebung (w.shift 1) :=
    eq_iterate_verschiebung (n := 1) fun i hi => by rwa [Nat.lt_one_iff.mp hi]
  have hv : v = verschiebung (v.shift 1) :=
    eq_iterate_verschiebung (n := 1) fun i hi => by rwa [Nat.lt_one_iff.mp hi]
  rw [← map_mul, ← RingHom.mem_ker, mem_ker_truncate]
  intro i hi
  rw [hw, ← verschiebung_mul_frobenius, hv, frobenius_verschiebung]
  interval_cases i
  · exact verschiebung_coeff_zero _
  · rw [verschiebung_coeff_succ, ← mul_assoc, mul_charP_coeff_zero]

/-- **In characteristic `p` the kernel of `W₂(F) ⟶ F` is nilpotent**: it squares to zero. -/
theorem isNilpotent_ker_wittTwoToField [CharP F p] :
    IsNilpotent (RingHom.ker (wittTwoToField p F)) := by
  refine ⟨2, ?_⟩
  rw [pow_two, Submodule.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
  intro x hx y hy
  rw [Ideal.mem_bot]
  exact mul_eq_zero_of_mem_ker_wittTwoToField p F hx hy

/-- **Lifting to `W₂` along a formally smooth localization.** If `R_r` is formally smooth over
`ℤ` and `φ : R ⟶ F` inverts `r`, with `F` of characteristic `p`, then `φ` lifts along
`W₂(F) ⟶ F`. -/
theorem exists_wittTwo_lift_of_formallySmooth {R : Type u} [CommRing R] (r : R)
    [Algebra.FormallySmooth ℤ (Localization.Away r)] [CharP F p] (φ : R →+* F)
    (hr : IsUnit (φ r)) :
    ∃ ψ : R →+* TruncatedWittVector p 2 F, (wittTwoToField p F).comp ψ = φ := by
  let φ' : Localization.Away r →+* F := IsLocalization.Away.lift r hr
  let f : Localization.Away r →ₐ[ℤ] F :=
    { toRingHom := φ'
      commutes' := fun n => by
        change φ' (algebraMap ℤ (Localization.Away r) n) = algebraMap ℤ F n
        rw [eq_intCast (algebraMap ℤ (Localization.Away r)), eq_intCast (algebraMap ℤ F),
          map_intCast] }
  let ψ' := Algebra.FormallySmooth.liftOfSurjective f
    (wittTwoToField p F).toIntAlgHom (wittTwoToField_surjective p F)
    (isNilpotent_ker_wittTwoToField p F)
  refine ⟨ψ'.toRingHom.comp (algebraMap R _), RingHom.ext fun x => ?_⟩
  have h := Algebra.FormallySmooth.liftOfSurjective_apply f
    (wittTwoToField p F).toIntAlgHom (wittTwoToField_surjective p F)
    (isNilpotent_ker_wittTwoToField p F) (algebraMap R _ x)
  simpa [ψ', f, φ'] using h

end Witt

section GenericSmoothness

/-- **Generic smoothness over `ℤ`.** The generic point of the spectrum of a domain of
characteristic zero of finite type over `ℤ` lies in the smooth locus over `ℤ`. -/
theorem mem_smoothLocus_int_bot (R : Type u) [CommRing R] [IsDomain R] [CharZero R]
    [Algebra.FiniteType ℤ R] :
    (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ∈ Algebra.smoothLocus ℤ R := by
  have := @IsScalarTower.of_algebraMap_eq' ℤ ℚ (FractionRing R) _ _ _ _ _ _
    (RingHom.ext_int _ _)
  have : Algebra.EssFiniteType ℚ (FractionRing R) :=
    Algebra.EssFiniteType.of_comp ℤ ℚ (FractionRing R)
  have : Algebra.FormallySmooth ℤ ℚ := Algebra.FormallySmooth.of_isLocalization (nonZeroDivisors ℤ)
  have : Algebra.FormallySmooth ℤ (FractionRing R) :=
    Algebra.FormallySmooth.comp ℤ ℚ (FractionRing R)
  change Algebra.FormallySmooth ℤ (Localization.AtPrime (⊥ : Ideal R))
  have : IsFractionRing R (Localization.AtPrime (⊥ : Ideal R)) := by
    simpa [Ideal.primeCompl_bot] using Localization.isLocalization (M := (⊥ : Ideal R).primeCompl)
  exact Algebra.FormallySmooth.of_equiv
    ((IsLocalization.algEquiv (nonZeroDivisors R) (FractionRing R)
      (Localization.AtPrime (⊥ : Ideal R))).restrictScalars ℤ)

/-- **At a point of the smooth locus over `ℤ`, the map to the residue field lifts to `W₂`.** -/
theorem exists_wittTwo_lift (R : Type u) [CommRing R] [Algebra.FinitePresentation ℤ R]
    {s : PrimeSpectrum R} (hs : s ∈ Algebra.smoothLocus ℤ R) (p : ℕ) [Fact p.Prime]
    [CharP s.asIdeal.ResidueField p] :
    ∃ ψ : R →+* TruncatedWittVector p 2 s.asIdeal.ResidueField,
      (wittTwoToField p _).comp ψ = algebraMap R s.asIdeal.ResidueField := by
  obtain ⟨_, ⟨r, rfl⟩, hsr, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hs
      Algebra.isOpen_smoothLocus
  have : Algebra.FormallySmooth ℤ (Localization.Away r) :=
    Algebra.basicOpen_subset_smoothLocus_iff.mp hsub
  refine exists_wittTwo_lift_of_formallySmooth p _ r _ ?_
  refine isUnit_iff_ne_zero.mpr fun h0 => ?_
  rw [Ideal.algebraMap_residueField_eq_zero] at h0
  exact hsr h0

end GenericSmoothness

end AlgebraicGeometry.HodgeSpreadingOut
