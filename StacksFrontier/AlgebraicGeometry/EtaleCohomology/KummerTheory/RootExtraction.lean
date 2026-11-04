module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import StacksFrontier.RingTheory.Etale.ResidueFieldColimit

/-!
# Étale extraction of roots of units

For a commutative ring `A`, a natural number `n` which is invertible in `A`, and a unit `u` of
`A`, the algebra `A[X]/(Xⁿ - u)` is étale over `A`, free of rank `n` as an `A`-module, surjective
on prime spectra, and contains an `n`-th root of `u` which is itself a unit.

## Main results

* `Stacks.Kummer.etale_adjoinRoot_unit`: `A[X]/(Xⁿ - u)` is étale over `A` when `n` is
  invertible in `A`.
* `Stacks.Kummer.root_pow_eq_unit`: the adjoined root is an `n`-th root of `u`.
* `Stacks.Kummer.isUnit_root_unit`: the adjoined root is a unit.
* `Stacks.Kummer.comap_surjective_adjoinRoot_unit`: the induced map of prime spectra is
  surjective.

## References

* [Stacks Project, Tag 03PL](https://stacks.math.columbia.edu/tag/03PL)
* [Stacks Project, Tag 09E0](https://stacks.math.columbia.edu/tag/09E0)
-/

@[expose] public noncomputable section

open Polynomial

universe u

namespace Stacks.Kummer

variable {A : Type u} [CommRing A] {n : ℕ}

/-- The polynomial `Xⁿ - u` is monic for `n ≠ 0`. -/
theorem monic_X_pow_sub_C_unit (hn : n ≠ 0) (v : Aˣ) : (X ^ n - C (v : A)).Monic :=
  monic_X_pow_sub_C (v : A) hn

/-- The derivative of `Xⁿ - u` becomes a unit in `A[X]/(Xⁿ - u)` when `n` is invertible in
`A`. -/
theorem isUnit_mk_derivative_X_pow_sub_C_unit (hn : IsUnit (n : A)) (v : Aˣ) :
    IsUnit (AdjoinRoot.mk (X ^ n - C (v : A)) (derivative (X ^ n - C (v : A)))) := by
  obtain ⟨a, b, hab⟩ := separable_X_pow_sub_C_unit v hn
  have h := congrArg (AdjoinRoot.mk (X ^ n - C (v : A))) hab
  rw [map_add, map_mul, map_mul, AdjoinRoot.mk_self, mul_zero, zero_add, map_one] at h
  exact ⟨⟨_, AdjoinRoot.mk _ b, by rwa [mul_comm], h⟩, rfl⟩

/-- For `n` invertible in `A` and `u` a unit of `A`, the algebra `A[X]/(Xⁿ - u)` is étale over
`A`. -/
theorem etale_adjoinRoot_unit (hn : IsUnit (n : A)) (hn0 : n ≠ 0) (v : Aˣ) :
    Algebra.Etale A (AdjoinRoot (X ^ n - C (v : A))) :=
  Stacks.Etale.ResidueFieldColimit.etale_adjoinRoot (monic_X_pow_sub_C_unit hn0 v)
    (isUnit_mk_derivative_X_pow_sub_C_unit hn v)

/-- `A[X]/(Xⁿ - u)` is a free `A`-module. -/
theorem free_adjoinRoot_unit (hn : n ≠ 0) (v : Aˣ) :
    Module.Free A (AdjoinRoot (X ^ n - C (v : A))) :=
  (monic_X_pow_sub_C_unit hn v).free_adjoinRoot

/-- `A[X]/(Xⁿ - u)` is a finite `A`-module. -/
theorem finite_adjoinRoot_unit (hn : n ≠ 0) (v : Aˣ) :
    Module.Finite A (AdjoinRoot (X ^ n - C (v : A))) :=
  (monic_X_pow_sub_C_unit hn v).finite_adjoinRoot

/-- The adjoined root is an `n`-th root of `u`. -/
theorem root_pow_eq_unit (v : Aˣ) :
    AdjoinRoot.root (X ^ n - C (v : A)) ^ n =
      algebraMap A (AdjoinRoot (X ^ n - C (v : A))) (v : A) := by
  have h : (AdjoinRoot.mk (X ^ n - C (v : A))) (X ^ n - C (v : A)) = 0 := AdjoinRoot.mk_self
  rwa [← AdjoinRoot.aeval_eq, map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] at h

/-- The adjoined `n`-th root of a unit is itself a unit. -/
theorem isUnit_root_unit (hn : n ≠ 0) (v : Aˣ) :
    IsUnit (AdjoinRoot.root (X ^ n - C (v : A))) := by
  rw [← isUnit_pow_iff hn, root_pow_eq_unit v]
  exact v.isUnit.map (algebraMap A (AdjoinRoot (X ^ n - C (v : A))))

/-- `A[X]/(Xⁿ - u)` is faithfully flat over a nonzero ring `A`. -/
theorem faithfullyFlat_adjoinRoot_unit [Nontrivial A] (hn : n ≠ 0) (v : Aˣ) :
    Module.FaithfullyFlat A (AdjoinRoot (X ^ n - C (v : A))) :=
  have := free_adjoinRoot_unit hn v
  have : Nontrivial (AdjoinRoot (X ^ n - C (v : A))) :=
    (AdjoinRoot.nontrivial_iff_of_monic (monic_X_pow_sub_C_unit hn v)).mpr <| by
      rw [degree_X_pow_sub_C (Nat.pos_of_ne_zero hn)]
      exact_mod_cast Nat.pos_of_ne_zero hn
  inferInstance

/-- The map of prime spectra induced by `A → A[X]/(Xⁿ - u)` is surjective. -/
theorem comap_surjective_adjoinRoot_unit (hn : n ≠ 0) (v : Aˣ) :
    Function.Surjective
      (PrimeSpectrum.comap (algebraMap A (AdjoinRoot (X ^ n - C (v : A))))) := by
  rcases subsingleton_or_nontrivial A with h | h
  · exact fun p ↦ isEmptyElim p
  · have := faithfullyFlat_adjoinRoot_unit hn v
    exact PrimeSpectrum.comap_surjective_of_faithfullyFlat

end Stacks.Kummer

end
