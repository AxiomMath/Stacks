module

public import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Polynomial evaluations of intertwined endomorphisms

A linear map `f : M → N` with `f ∘ A = B ∘ f` for endomorphisms `A` of `M` and `B` of `N` satisfies
`f ∘ p(A) = p(B) ∘ f` for every polynomial `p`.

## Main results

* `LinearMap.comp_aeval_of_comp_eq`: the identity of linear maps.
* `LinearMap.apply_aeval_of_apply_eq`: its pointwise form.
-/

@[expose] public section

namespace LinearMap

open Polynomial

section Algebra

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
  {N : Type*} [AddCommGroup N] [Module R N]

/-- A linear map intertwining two endomorphisms intertwines their polynomial evaluations:
if `f ∘ A = B ∘ f` then `f ∘ p(A) = p(B) ∘ f` for every polynomial `p`. -/
theorem comp_aeval_of_comp_eq {A : Module.End R M} {B : Module.End R N} {f : M →ₗ[R] N}
    (h : f ∘ₗ A = B ∘ₗ f) (p : R[X]) : f ∘ₗ aeval A p = aeval B p ∘ₗ f := by
  have hpow (n : ℕ) : f ∘ₗ (A ^ n) = (B ^ n) ∘ₗ f :=
    (Module.End.commute_pow_left_of_commute h.symm n).symm
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, LinearMap.comp_add, LinearMap.add_comp]
  | monomial n r =>
    simp [aeval_monomial, Algebra.algebraMap_eq_smul_one, LinearMap.comp_smul,
      LinearMap.smul_comp, hpow]

/-- Pointwise form of `comp_aeval_of_comp_eq`: if `f (A v) = B (f v)` for all `v`, then
`f (p(A) v) = p(B) (f v)`. -/
theorem apply_aeval_of_apply_eq {A : Module.End R M} {B : Module.End R N} {f : M →ₗ[R] N}
    (h : ∀ v, f (A v) = B (f v)) (p : R[X]) (v : M) : f (aeval A p v) = aeval B p (f v) :=
  LinearMap.congr_fun (comp_aeval_of_comp_eq (LinearMap.ext h) p) v

end Algebra

end LinearMap

