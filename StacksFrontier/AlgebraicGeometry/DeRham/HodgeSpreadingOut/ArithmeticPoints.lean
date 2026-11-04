module

public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.Spectrum.Prime.Jacobson
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Data.Nat.Prime.Factorial
public import StacksFrontier.RingTheory.Jacobson.Examples

/-!
# Points with finite residue fields of large characteristic

Let `R` be a domain of characteristic zero which is a finitely generated `ℤ`-algebra. Every
nonempty open subset of `Spec R` contains a maximal ideal whose residue field is finite, of
characteristic larger than any given bound. This is how the spreading out argument for the
degeneration of the Hodge-to-de Rham spectral sequence in characteristic zero finds a fibre over a
finite field of large characteristic.

## Main results

* `AlgebraicGeometry.HodgeSpreadingOut.finite_of_moduleFinite_int`: a field which is a finitely
  generated abelian group is finite.
* `AlgebraicGeometry.HodgeSpreadingOut.exists_isMaximal_finite_lt_ringChar`: the points of a
  nonempty open subset of `Spec R`.

## Implementation notes

`R` is a Jacobson ring, being of finite type over the Jacobson ring `ℤ`
(`int_isJacobsonRing`, [Stacks, Tag 00G4]), so the nonempty open set `U ∩ D(N!)` contains a closed
point. Its residue field is a field of finite type over `ℤ`, hence a finite `ℤ`-module by Zariski's
lemma ([Stacks, Tag 0CY7]), hence finite; its characteristic does not divide `N!`, so it exceeds
`N`.

## References

* [Stacks Project, Tag 00G4](https://stacks.math.columbia.edu/tag/00G4)
* [Stacks Project, Tag 0CY7](https://stacks.math.columbia.edu/tag/0CY7)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.HodgeSpreadingOut

/-- **A field which is a finitely generated abelian group is finite.** In characteristic `p` it is
a finitely generated vector space over `𝔽_p`; in characteristic zero it would be a free abelian
group of positive rank on which multiplication by `2` is invertible, which is absurd. -/
theorem finite_of_moduleFinite_int (K : Type*) [Field K] [Module.Finite ℤ K] : Finite K := by
  obtain ⟨p, hp⟩ := CharP.exists K
  rcases CharP.char_is_prime_or_zero K p with hprime | rfl
  · have := Fact.mk hprime
    let : Algebra (ZMod p) K := ZMod.algebra K p
    have : Module.Finite (ZMod p) K := Module.Finite.of_restrictScalars_finite ℤ (ZMod p) K
    exact Module.finite_of_finite (ZMod p)
  · exfalso
    have : CharZero K := CharP.charP_zero_iff_charZero K |>.mp hp
    have : Module.Free ℤ K := Module.free_of_finite_type_torsion_free'
    let b := Module.Free.chooseBasis ℤ K
    obtain ⟨i⟩ := b.index_nonempty
    have hv : b i = (2 : ℤ) • ((2 : K)⁻¹ * b i) := by
      rw [zsmul_eq_mul, Int.cast_ofNat, ← mul_assoc, mul_inv_cancel₀ two_ne_zero, one_mul]
    have := congrArg (fun v => b.repr v i) hv
    simp only [Module.Basis.repr_self, Finsupp.single_eq_same, map_zsmul, Finsupp.smul_apply,
      smul_eq_mul] at this
    omega

/-- **A nonempty open subset of the spectrum of a finitely generated `ℤ`-algebra of
characteristic zero contains a maximal ideal with finite residue field of characteristic
larger than `N`.** -/
theorem exists_isMaximal_finite_lt_ringChar (R : Type u) [CommRing R] [IsDomain R] [CharZero R]
    [Algebra.FiniteType ℤ R] {U : Set (PrimeSpectrum R)} (hU : IsOpen U) (hne : U.Nonempty)
    (N : ℕ) :
    ∃ x ∈ U, x.asIdeal.IsMaximal ∧ Finite x.asIdeal.ResidueField ∧
      N < ringChar x.asIdeal.ResidueField := by
  have : IsJacobsonRing ℤ := int_isJacobsonRing
  have : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := ℤ) (B := R)
  have hD : (PrimeSpectrum.basicOpen ((N.factorial : ℕ) : R) : Set (PrimeSpectrum R)).Nonempty :=
    ⟨⟨⊥, Ideal.isPrime_bot⟩, by simpa [PrimeSpectrum.mem_basicOpen] using N.factorial_ne_zero⟩
  have hV : (U ∩ PrimeSpectrum.basicOpen ((N.factorial : ℕ) : R)).Nonempty :=
    nonempty_preirreducible_inter hU (PrimeSpectrum.basicOpen _).isOpen hne hD
  obtain ⟨x, ⟨hxU, hxN⟩, hxc⟩ := nonempty_inter_closedPoints hV
    (hU.inter (PrimeSpectrum.basicOpen _).isOpen).isLocallyClosed
  have hmax : x.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal x).1 hxc
  let K := x.asIdeal.ResidueField
  have : Algebra.FiniteType ℤ K := Algebra.FiniteType.trans (S := R) inferInstance inferInstance
  have : Module.Finite ℤ K := by
    convert finite_of_finite_type_of_isJacobsonRing ℤ K <;>
      first | rfl | exact Subsingleton.elim _ _
  have hfin : Finite K := finite_of_moduleFinite_int K
  refine ⟨x, hxU, hmax, hfin, ?_⟩
  obtain ⟨p, hchar⟩ := CharP.exists K
  have hp : p.Prime :=
    (CharP.char_is_prime_or_zero K p).resolve_right (CharP.char_ne_zero_of_finite K p)
  rw [ringChar.eq K p]
  by_contra! hle
  apply hxN
  rw [← Ideal.algebraMap_residueField_eq_zero, map_natCast]
  exact (CharP.cast_eq_zero_iff K p _).mpr ((Nat.Prime.dvd_factorial hp).mpr hle)

end AlgebraicGeometry.HodgeSpreadingOut
