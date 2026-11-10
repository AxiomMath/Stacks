module

public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
public import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# The radical tower algebra over the rationals

This file builds the commutative `ℚ`-algebra
`ℚ[x₀, x₁, x₂, …]/(x₀² - 2, x₁³ - 2, x₂⁴ - 2, …)`
obtained by adjoining an `(i + 2)`-nd root of `2` for every natural number `i`, and proves the
arithmetic fact that makes it a counterexample: it is nonzero, yet it admits no ring
homomorphism to any finite extension field of `ℚ`.

## Main definitions

* `Stacks.Examples.RadicalTower.relation` is the polynomial `Xᵢ ^ (i + 2) - 2`.
* `Stacks.Examples.RadicalTower.Alg` is the quotient of `MvPolynomial ℕ ℚ` by those relations.
* `Stacks.Examples.RadicalTower.root` is the image of `Xᵢ`, an `(i + 2)`-nd root of `2`.

## Main results

* `Stacks.Examples.RadicalTower.xPowSubTwo_irreducible`: `X ^ n - 2` is irreducible over `ℚ`
  for `2 ≤ n`, by Eisenstein's criterion at the prime `2` together with Gauss' lemma.
* `Stacks.Examples.RadicalTower.le_finrank_of_pow_eq_two`: a finite extension of `ℚ` containing
  an `n`-th root of `2` has degree at least `n`.
* `Stacks.Examples.RadicalTower.not_forall_exists_pow_eq_two`: no finite extension of `ℚ`
  contains an `n`-th root of `2` for every `n`.
* `Stacks.Examples.RadicalTower.one_ne_zero`: the algebra is nonzero, because it maps to an
  algebraic closure of `ℚ`.
* `Stacks.Examples.RadicalTower.no_ringHom_to_finiteDimensional`: there is no ring homomorphism
  from the algebra to a finite extension of `ℚ`.

## Implementation notes

The exponents grow with the index, so a single radicand `2` suffices and irreducibility is
Eisenstein rather than a Kummer-theoretic degree computation: a finite extension of `ℚ` can
contain an `n`-th root of `2` only for `n` bounded by its degree. Nontriviality of the quotient
is witnessed by the evaluation sending `Xᵢ` to a chosen `(i + 2)`-nd root of `2` in an algebraic
closure of `ℚ`.

## References

* [Stacks Project, Tag 077B](https://stacks.math.columbia.edu/tag/077B)
-/

@[expose] public section

open Polynomial

namespace Stacks.Examples.RadicalTower

/-- The polynomial `X ^ n - 2` is irreducible over `ℚ` as soon as `2 ≤ n`: over `ℤ` it is
Eisenstein at the prime `2`, and Gauss' lemma transfers irreducibility to `ℚ`. -/
theorem xPowSubTwo_irreducible (n : ℕ) (hn : 2 ≤ n) :
    Irreducible ((X : ℚ[X]) ^ n - C (2 : ℚ)) := by
  have hcoeff : (((X : ℤ[X]) ^ n - C (2 : ℤ)).coeff 0) = -2 := by
    simp only [coeff_sub, coeff_X_pow, coeff_C]
    simp [show 0 ≠ n by omega]
  have hmon : ((X : ℤ[X]) ^ n - C (2 : ℤ)).Monic := monic_X_pow_sub_C (2 : ℤ) (by omega)
  have hp : (Ideal.span ({(2 : ℤ)} : Set ℤ)).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime Int.prime_two
  have heis : ((X : ℤ[X]) ^ n - C (2 : ℤ)).IsEisensteinAt
      (Ideal.span ({(2 : ℤ)} : Set ℤ)) := by
    refine hmon.isEisensteinAt_of_mem_of_notMem ?_ ?_ ?_
    · intro htop
      have h1 : (1 : ℤ) ∈ Ideal.span ({(2 : ℤ)} : Set ℤ) := by simp [htop]
      norm_num [Ideal.mem_span_singleton] at h1
    · intro k hk
      rw [natDegree_X_pow_sub_C] at hk
      by_cases hk0 : k = 0
      · subst k
        rw [hcoeff]
        exact Ideal.mem_span_singleton.mpr ⟨-1, by norm_num⟩
      · rw [coeff_sub, coeff_X_pow, coeff_C]
        simp [hk0, ne_of_lt hk]
    · intro h
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, hcoeff] at h
      norm_num at h
  have hmap : Polynomial.map (Int.castRingHom ℚ) ((X : ℤ[X]) ^ n - C (2 : ℤ)) =
      (X : ℚ[X]) ^ n - C (2 : ℚ) := by
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
    norm_num
  rw [← hmap]
  exact (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
    hmon.isPrimitive).mp
    (heis.irreducible hp hmon.isPrimitive (by rw [natDegree_X_pow_sub_C]; omega))

/-- A finite extension of `ℚ` containing an `n`-th root of `2` has degree at least `n`, because
`X ^ n - 2` is the minimal polynomial of that root. -/
theorem le_finrank_of_pow_eq_two {K : Type*} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    (n : ℕ) (hn : 2 ≤ n) (x : K) (hx : x ^ n = (2 : K)) : n ≤ Module.finrank ℚ K := by
  calc
    n = Module.finrank ℚ (IntermediateField.adjoin ℚ {x}) := by
      rw [IntermediateField.adjoin.finrank (IsIntegral.of_finite ℚ x),
        ← minpoly.eq_of_irreducible_of_monic (xPowSubTwo_irreducible n hn) (by simp [hx])
          (monic_X_pow_sub_C (2 : ℚ) (by omega)), natDegree_X_pow_sub_C]
    _ ≤ Module.finrank ℚ (⊤ : IntermediateField ℚ K) :=
      IntermediateField.finrank_le_of_le_right (K := ℚ) (L := K) le_top
    _ = Module.finrank ℚ K := by simp

/-- No finite extension of `ℚ` contains an `n`-th root of `2` for every `n`. -/
theorem not_forall_exists_pow_eq_two {K : Type*} [Field K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] : ¬ ∀ n : ℕ, 2 ≤ n → ∃ x : K, x ^ n = (2 : K) := by
  intro h
  obtain ⟨x, hx⟩ := h (Module.finrank ℚ K + 2) (by omega)
  have := le_finrank_of_pow_eq_two (K := K) (Module.finrank ℚ K + 2) (by omega) x hx
  omega

/-- The relation imposed on the `i`-th variable: it is an `(i + 2)`-nd root of `2`. -/
noncomputable def relation (i : ℕ) : MvPolynomial ℕ ℚ := MvPolynomial.X i ^ (i + 2) - 2

/-- The ideal generated by all the radical relations. -/
noncomputable def relationsIdeal : Ideal (MvPolynomial ℕ ℚ) := Ideal.span (Set.range relation)

/-- The `ℚ`-algebra `ℚ[x₀, x₁, …]/(xᵢ ^ (i + 2) - 2)` obtained by adjoining an `(i + 2)`-nd
root of `2` for every `i`. -/
abbrev Alg := MvPolynomial ℕ ℚ ⧸ relationsIdeal

/-- The image of the `i`-th variable: a chosen `(i + 2)`-nd root of `2`. -/
noncomputable def root (i : ℕ) : Alg := Ideal.Quotient.mk relationsIdeal (MvPolynomial.X i)

/-- The `i`-th generator is an `(i + 2)`-nd root of `2`. -/
theorem root_pow (i : ℕ) : root i ^ (i + 2) = 2 := by
  have hrel : (Ideal.Quotient.mk relationsIdeal) (relation i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
  rw [relation, map_sub, map_pow] at hrel
  exact (sub_eq_zero.mp hrel).trans (map_ofNat (Ideal.Quotient.mk relationsIdeal) 2)

section Nontrivial

/-- An `(i + 2)`-nd root of `2` exists in an algebraic closure of `ℚ`. -/
theorem exists_algebraicClosure_root (i : ℕ) : ∃ x : AlgebraicClosure ℚ, x ^ (i + 2) = 2 := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (k := AlgebraicClosure ℚ)
    ((X : (AlgebraicClosure ℚ)[X]) ^ (i + 2) - C (2 : AlgebraicClosure ℚ)) (by
      rw [degree_X_pow_sub_C (by omega) (2 : AlgebraicClosure ℚ)]
      exact_mod_cast (Nat.ne_of_gt (by omega : 0 < i + 2)))
  exact ⟨x, sub_eq_zero.mp (by simpa using hx)⟩

/-- A chosen `(i + 2)`-nd root of `2` in an algebraic closure of `ℚ`. -/
noncomputable def algebraicRoot (i : ℕ) : AlgebraicClosure ℚ :=
  Classical.choose (exists_algebraicClosure_root i)

/-- The element `algebraicRoot i` is an `(i + 2)`-nd root of `2`. -/
@[simp] theorem algebraicRoot_pow (i : ℕ) :
    algebraicRoot i ^ (i + 2) = (2 : AlgebraicClosure ℚ) :=
  Classical.choose_spec (exists_algebraicClosure_root i)

/-- The relations vanish at the chosen roots in an algebraic closure. -/
theorem relationsIdeal_le_ker : relationsIdeal ≤
    RingHom.ker (MvPolynomial.eval₂Hom (algebraMap ℚ (AlgebraicClosure ℚ)) algebraicRoot) := by
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨i, rfl⟩
  change MvPolynomial.eval₂Hom _ _ (relation i) = 0
  simp [relation]

/-- Evaluation of the radical tower algebra at the chosen roots in an algebraic closure. -/
noncomputable def evaluation : Alg →+* AlgebraicClosure ℚ :=
  Ideal.Quotient.lift relationsIdeal
    (MvPolynomial.eval₂Hom (algebraMap ℚ (AlgebraicClosure ℚ)) algebraicRoot)
    (fun _ hx => relationsIdeal_le_ker hx)

/-- The radical tower algebra is nonzero. -/
theorem one_ne_zero : (1 : Alg) ≠ 0 := fun h => by
  simpa using congrArg evaluation h

/-- The radical tower algebra is nontrivial. -/
instance : Nontrivial Alg := nontrivial_of_ne 1 0 one_ne_zero

end Nontrivial

/-- There is no ring homomorphism from the radical tower algebra to a finite extension
of `ℚ`: the image of the `i`-th generator would be an `(i + 2)`-nd root of `2`, and a finite
extension of `ℚ` has roots of `2` of only boundedly many orders. -/
theorem no_ringHom_to_finiteDimensional {K : Type*} [Field K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] (φ : Alg →+* K) : False := by
  refine not_forall_exists_pow_eq_two (K := K) fun n hn => ⟨φ (root (n - 2)), ?_⟩
  have h := congrArg φ (root_pow (n - 2))
  rw [show n - 2 + 2 = n by omega, map_pow] at h
  rw [h, map_ofNat]

/-- Two `ℚ`-algebra maps out of the radical tower algebra agree as soon as they agree on each
generator, because the generators generate it as a `ℚ`-algebra. -/
theorem algHom_ext {B : Type*} [CommRing B] [Algebra ℚ B] {f g : Alg →ₐ[ℚ] B}
    (h : ∀ i, f (root i) = g (root i)) : f = g :=
  Ideal.Quotient.algHom_ext ℚ (MvPolynomial.algHom_ext h)

/-- Two is invertible in the radical tower algebra, which is an algebra over `ℚ`. -/
theorem isUnit_two : IsUnit (2 : Alg) := by
  rw [show (2 : Alg) = algebraMap ℚ Alg 2 from (map_ofNat (algebraMap ℚ Alg) 2).symm]
  exact (isUnit_iff_ne_zero.mpr (by norm_num : (2 : ℚ) ≠ 0)).map (algebraMap ℚ Alg)

/-- Each generator is invertible, since its `(i + 2)`-nd power is the unit `2`. -/
theorem isUnit_root (i : ℕ) : IsUnit (root i) := by
  rw [← isUnit_pow_iff (n := i + 2) (by omega), root_pow]
  exact isUnit_two

/-- The `i`-th generator, as a unit of the radical tower algebra. -/
noncomputable def rootUnit (i : ℕ) : Algˣ := (isUnit_root i).unit

/-- The unit `rootUnit i` has underlying element the `i`-th generator `root i`. -/
@[simp] theorem rootUnit_val (i : ℕ) : (rootUnit i : Alg) = root i := rfl

/-- Two, as a unit of the radical tower algebra. -/
noncomputable def twoUnit : Algˣ := isUnit_two.unit

/-- The unit `twoUnit` has underlying element `2`. -/
@[simp] theorem twoUnit_val : (twoUnit : Alg) = 2 := rfl

/-- The `(i + 2)`-nd power of the `i`-th generator is `2`, as units. -/
theorem rootUnit_pow (i : ℕ) : rootUnit i ^ (i + 2) = twoUnit :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, rootUnit_val, root_pow, twoUnit_val])

end Stacks.Examples.RadicalTower

end
