module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.Module.Submodule.RestrictScalars
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `Iⁿ • ⊤` as an ideal of an algebra

For an `R`-algebra `U` and an ideal `I` of `R`, the `R`-submodule `Iⁿ • (⊤ : Submodule R U)` is
the ideal `(IU)ⁿ` of `U` read through restriction of scalars. More generally, for an `S`-module
`M` with `IsScalarTower R S M`, `Iⁿ • (⊤ : Submodule R M)` is `(IS)ⁿ • (⊤ : Submodule S M)`.

## Main definitions

* `quotEquivMapPowModule`: the `R`-linear equivalence `M ⧸ Iⁿ • ⊤ ≃ₗ[R] M ⧸ (IS)ⁿ • ⊤` induced by
  the identity of `M`.
* `quotEquivMapPow`: the `R`-linear equivalence `U ⧸ Iⁿ • ⊤ ≃ₗ[R] U ⧸ (IU)ⁿ` induced by the
  identity of `U`.

## Main results

* `smul_top_pow_eq_restrictScalars_module`: `Iⁿ • ⊤ = ((IS)ⁿ • ⊤).restrictScalars R` in `M`.
* `smul_top_pow_eq_restrictScalars`: `Iⁿ • ⊤ = ((IU)ⁿ • ⊤).restrictScalars R` in `U`.
-/

@[expose] public section

/-- For an `R`-algebra `S` and an `S`-module `M`, the `R`-submodule `Iⁿ • (⊤ : Submodule R M)` is
the `S`-submodule `(I S)ⁿ • (⊤ : Submodule S M)`, read through restriction of scalars. -/
@[ega "0 1.0.4" "JM = (BJ)M"]
theorem smul_top_pow_eq_restrictScalars_module {R : Type*} [CommRing R] (I : Ideal R)
    (S : Type*) [CommRing S] [Algebra R S] (M : Type*) [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] {J : Ideal S} (hJ : J = I.map (algebraMap R S)) (n : ℕ) :
    (I ^ n • (⊤ : Submodule R M)) = ((J ^ n • (⊤ : Submodule S M)).restrictScalars R) := by
  subst hJ
  rw [← Ideal.map_pow, Submodule.restrictScalars_map_smul_eq, Submodule.restrictScalars_top]

/-- The `R`-linear equivalence `M ⧸ Iⁿ • ⊤ ≃ₗ[R] M ⧸ Jⁿ • ⊤`, for `J = I S`, sending the class
of `x` to the class of `x`. -/
def quotEquivMapPowModule {R : Type*} [CommRing R] (I : Ideal R) (S : Type*) [CommRing S]
    [Algebra R S] (M : Type*) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    {J : Ideal S} (hJ : J = I.map (algebraMap R S)) (n : ℕ) :
    (M ⧸ (I ^ n • (⊤ : Submodule R M))) ≃ₗ[R] (M ⧸ (J ^ n • (⊤ : Submodule S M))) :=
  (Submodule.quotEquivOfEq _ _ (smul_top_pow_eq_restrictScalars_module I S M hJ n)).trans
    (Submodule.Quotient.restrictScalarsEquiv R _)

/-- `quotEquivMapPowModule` sends the class of `x` to the class of `x`. -/
@[simp]
theorem quotEquivMapPowModule_mk {R : Type*} [CommRing R] (I : Ideal R) (S : Type*) [CommRing S]
    [Algebra R S] (M : Type*) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    {J : Ideal S} (hJ : J = I.map (algebraMap R S)) (n : ℕ) (x : M) :
    quotEquivMapPowModule I S M hJ n (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := rfl

/-- `Iⁿ • (⊤ : Submodule R U)` is the ideal `(IU)ⁿ` of `U`, read as an `R`-submodule. -/
@[ega "0 1.0.4" "commutative B and M = B"]
theorem smul_top_pow_eq_restrictScalars {R : Type*} [CommRing R] (I : Ideal R)
    (U : Type*) [CommRing U] [Algebra R U] (n : ℕ) :
    (I ^ n • (⊤ : Submodule R U)) =
      (((I.map (algebraMap R U)) ^ n • (⊤ : Ideal U)).restrictScalars R) := by
  rw [Ideal.smul_top_eq_map, Ideal.smul_eq_mul, Ideal.mul_top, ← Ideal.map_pow]

/-- The `R`-linear equivalence `U ⧸ Iⁿ • ⊤ ≃ₗ[R] U ⧸ (IU)ⁿ` sending the class of `x` to the
class of `x`. -/
def quotEquivMapPow {R : Type*} [CommRing R] (I : Ideal R) (U : Type*) [CommRing U]
    [Algebra R U] (n : ℕ) :
    (U ⧸ (I ^ n • (⊤ : Submodule R U))) ≃ₗ[R]
      (U ⧸ ((I.map (algebraMap R U)) ^ n • (⊤ : Ideal U))) :=
  (Submodule.quotEquivOfEq _ _ (smul_top_pow_eq_restrictScalars I U n)).trans
    (Submodule.Quotient.restrictScalarsEquiv R _)
