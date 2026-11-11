module

public import Mathlib.Algebra.Field.ULift
public import Mathlib.FieldTheory.Finite.Extension
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeSpreadingOut.ArithmeticPoints

/-!
# Maximal ideals of finitely generated `ℤ`-algebras and extensions of finite fields

Let `R` be a finitely generated `ℤ`-algebra. Since `ℤ` is a Jacobson ring, the residue field
`R/m` at a maximal ideal `m` is a field of finite type over `ℤ`, hence a finitely generated
abelian group by Zariski's lemma, hence a finite field. If moreover `R` is a domain of
characteristic zero, every nonempty basic open `D(f)` of `Spec R` contains closed points of two
different residue characteristics.

We also record that a finite field `K` has, for every `d`, a finite extension into which every
extension of `K` of degree at most `d` embeds: the extension of degree `d!`.

## Main results

* `finite_quotient_of_isMaximal_of_finiteType_int`: `R/m` is finite.
* `exists_isMaximal_ringChar_ne`: two maximal ideals avoiding `f` with different residue
  characteristics.
* `FiniteField.exists_algHom_of_finrank_le`: a common finite extension receiving every extension
  of degree at most `d`.

## References

* [Stacks Project, Tag 00G4](https://stacks.math.columbia.edu/tag/00G4)
* [Stacks Project, Tag 0CY7](https://stacks.math.columbia.edu/tag/0CY7)
-/

@[expose] public section

universe u

/-- **The residue field at a maximal ideal of a finitely generated `ℤ`-algebra is finite.**
It is a field of finite type over the Jacobson ring `ℤ`, hence a finite `ℤ`-module by Zariski's
lemma, and a field which is a finitely generated abelian group is finite. -/
theorem finite_quotient_of_isMaximal_of_finiteType_int {R : Type u} [CommRing R]
    [Algebra.FiniteType ℤ R] (m : Ideal R) [m.IsMaximal] : Finite (R ⧸ m) := by
  let := Ideal.Quotient.field m
  have : IsJacobsonRing ℤ := int_isJacobsonRing
  have : Algebra.FiniteType ℤ (R ⧸ m) :=
    Algebra.FiniteType.trans (S := R) inferInstance inferInstance
  have : Module.Finite ℤ (R ⧸ m) := by
    convert finite_of_finite_type_of_isJacobsonRing ℤ (R ⧸ m)
  exact AlgebraicGeometry.HodgeSpreadingOut.finite_of_moduleFinite_int (R ⧸ m)

/-- The characteristic of `R/m` is that of the residue field of `R` at the maximal ideal `m`. -/
private theorem ringChar_quotient_eq_ringChar_residueField {R : Type u} [CommRing R]
    (m : Ideal R) [m.IsMaximal] : ringChar (R ⧸ m) = ringChar m.ResidueField := by
  let := Ideal.Quotient.field m
  have := charP_of_injective_algebraMap (algebraMap (R ⧸ m) m.ResidueField).injective
    (ringChar (R ⧸ m))
  exact (ringChar.eq m.ResidueField (ringChar (R ⧸ m))).symm

/-- **A nonempty basic open of the spectrum of a finitely generated `ℤ`-algebra of
characteristic zero contains closed points of two different residue characteristics.**
A first closed point of `D(f)` has finite residue field of some characteristic `ℓ`; a second
closed point of `D(f)` has finite residue field of characteristic larger than `ℓ`. -/
theorem exists_isMaximal_ringChar_ne {R : Type u} [CommRing R] [IsDomain R] [CharZero R]
    [Algebra.FiniteType ℤ R] (f : R) (hf : f ≠ 0) :
    ∃ m₁ m₂ : Ideal R, m₁.IsMaximal ∧ m₂.IsMaximal ∧ f ∉ m₁ ∧ f ∉ m₂ ∧
      ringChar (R ⧸ m₁) ≠ ringChar (R ⧸ m₂) := by
  have hne : (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)).Nonempty :=
    ⟨⟨⊥, Ideal.isPrime_bot⟩, by simpa [PrimeSpectrum.mem_basicOpen] using hf⟩
  obtain ⟨x, hx, hxm, -, -⟩ :=
    AlgebraicGeometry.HodgeSpreadingOut.exists_isMaximal_finite_lt_ringChar
      R (PrimeSpectrum.basicOpen f).isOpen hne 0
  obtain ⟨y, hy, hym, -, hlt⟩ :=
    AlgebraicGeometry.HodgeSpreadingOut.exists_isMaximal_finite_lt_ringChar
      R (PrimeSpectrum.basicOpen f).isOpen hne (ringChar x.asIdeal.ResidueField)
  refine ⟨x.asIdeal, y.asIdeal, hxm, hym, (PrimeSpectrum.mem_basicOpen f x).1 hx,
    (PrimeSpectrum.mem_basicOpen f y).1 hy, ?_⟩
  rw [ringChar_quotient_eq_ringChar_residueField, ringChar_quotient_eq_ringChar_residueField]
  exact hlt.ne

/-- **A finite field `K` has a finite extension into which every extension of `K` of degree at
most `d` embeds.** The extension of degree `d!` does: an extension of degree `e ≤ d` has
`e ∣ d!`, and an extension of finite fields of degree `e` embeds into one of degree `n` when
`e ∣ n`. The extension is lifted to the universe of `K`. -/
theorem FiniteField.exists_algHom_of_finrank_le (K : Type u) [Field K] [Finite K] (d : ℕ) :
    ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : Algebra K F),
      ∀ (L : Type u) [Field L] [Algebra K L] [Module.Finite K L], Module.finrank K L ≤ d →
        Nonempty (L →ₐ[K] F) := by
  obtain ⟨p, hp⟩ := CharP.exists K
  have : Fact p.Prime :=
    ⟨(CharP.char_is_prime_or_zero K p).resolve_right (CharP.char_ne_zero_of_finite K p)⟩
  have : NeZero d.factorial := ⟨d.factorial_ne_zero⟩
  let E := FiniteField.Extension K p d.factorial
  refine ⟨ULift.{u} E, inferInstance, inferInstance, inferInstance, fun L _ _ _ hL => ?_⟩
  have hdvd : Module.finrank K L ∣ Module.finrank K E := by
    rw [FiniteField.finrank_extension]
    exact Nat.dvd_factorial Module.finrank_pos hL
  obtain ⟨φ⟩ := FiniteField.nonempty_algHom_of_finrank_dvd hdvd
  exact ⟨ULift.algEquiv.symm.toAlgHom.comp φ⟩
