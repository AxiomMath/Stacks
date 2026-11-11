module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Ring.Regular

/-!
# A countable product of modules with free retracts does not localize

Let `A` be a domain, `x ∈ A` a nonzero non-unit, and `φ : A ⟶ A'` a ring map inverting `x`. Let
`M_m`, `m ∈ ℕ`, be `A`-modules each of which has a vector `e_m` and an `A`-linear form
`ψ_m : M_m ⟶ A` with `ψ_m(e_m) = 1`, and let `r_m : M_m ⟶ M'_m` be `φ`-semilinear maps to
`A'`-modules whose kernels are killed by powers of `x` (as for a localization at `x`). Then the
product `∏ M'_m` cannot receive, from an `A`-module `H` mapping compatibly to `∏ M_m`, a
`φ`-semilinear map `H ⟶ ∏ M'_m` all of whose targets become images after multiplying by a power
of `φ(x)`. The vector `(e_m / x^m)_m` has unbounded denominators.

This is the algebra behind the last step of the discussion of **Stacks 07DC**: the degree zero
cohomology sheaf of `Rf_*E` there is, over the affine objects, the product of the quasi-coherent
modules `R^m f_* 𝒪_𝒳`, each of which contains `k[x]` as a retract, and so it is not
quasi-coherent.

## Main results

* `Stacks.Localization.false_of_retracts_of_surjective_up_to_powers`: the statement above.

## References

* [Stacks Project, Tag 07DC](https://stacks.math.columbia.edu/tag/07DC)
-/

@[expose] public section

namespace Stacks.Localization

/-- **A countable product of modules with free rank-one retracts does not localize.** See the
module documentation. -/
theorem false_of_retracts_of_surjective_up_to_powers {A A' : Type*} [CommRing A] [IsDomain A]
    [CommRing A'] (φ : A →+* A') (x : A) (hx0 : x ≠ 0) (hxu : ¬ IsUnit x) (hφx : IsUnit (φ x))
    {M M' : ℕ → Type*} [∀ m, AddCommGroup (M m)] [∀ m, Module A (M m)]
    [∀ m, AddCommGroup (M' m)] [∀ m, Module A' (M' m)]
    (r : ∀ m, M m →+ M' m) (hr : ∀ m (a : A) (v : M m), r m (a • v) = φ a • r m v)
    (hker : ∀ m (v : M m), r m v = 0 → ∃ N : ℕ, x ^ N • v = 0)
    (e : ∀ m, M m) (ψ : ∀ m, M m →ₗ[A] A) (he : ∀ m, ψ m (e m) = 1)
    {H H' : Type*} [AddCommGroup H] [AddCommGroup H'] [Module A' H']
    (rH : H →+ H') (α : H →+ ∀ m, M m) (α' : H' ≃+ ∀ m, M' m)
    (hα'smul : ∀ (a : A') (h' : H') m, α' (a • h') m = a • α' h' m)
    (hα : ∀ (h : H) m, α' (rH h) m = r m (α h m))
    (hsurj : ∀ h' : H', ∃ (h : H) (n : ℕ), φ x ^ n • h' = rH h) : False := by
  obtain ⟨u, hu⟩ := hφx
  let w : ∀ m, M' m := fun m => ((u⁻¹ : A'ˣ) : A') ^ m • r m (e m)
  obtain ⟨h, n, hn⟩ := hsurj (α'.symm w)
  have hcomp := congrArg (fun z => α' z (n + 1)) hn
  simp only [hα'smul, AddEquiv.apply_symm_apply, hα] at hcomp
  -- `hcomp : φ x ^ n • w (n + 1) = r (n + 1) (α h (n + 1))`
  set y := α h (n + 1)
  have hw : φ x ^ n • w (n + 1) = ((u⁻¹ : A'ˣ) : A') • r (n + 1) (e (n + 1)) := by
    simp only [w, smul_smul, ← hu]
    congr 1
    rw [pow_succ, ← mul_assoc, ← mul_pow, Units.mul_inv, one_pow, one_mul]
  rw [hw] at hcomp
  have hre : r (n + 1) (e (n + 1) - x • y) = 0 := by
    rw [map_sub, hr, ← hcomp, ← hu, smul_smul, Units.mul_inv, one_smul, sub_self]
  obtain ⟨N, hN⟩ := hker _ _ hre
  have hψ := congrArg (ψ (n + 1)) hN
  rw [map_smul, map_sub, map_smul, he, map_zero, smul_eq_mul, smul_eq_mul] at hψ
  have h1 : 1 - x * ψ (n + 1) y = 0 :=
    (mul_eq_zero.mp hψ).resolve_left (pow_ne_zero N hx0)
  have h2 : x * ψ (n + 1) y = 1 := (sub_eq_zero.mp h1).symm
  exact hxu ⟨⟨x, ψ (n + 1) y, h2, by rw [mul_comm]; exact h2⟩, rfl⟩

end Stacks.Localization
