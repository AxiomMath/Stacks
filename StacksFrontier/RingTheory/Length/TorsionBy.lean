module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Length

/-!
# Lengths of torsion submodules

For an `R`-module `M` and `a b : R`, the length of the `ab`-torsion of `M` is at most the sum of
the lengths of the `a`-torsion and the `b`-torsion. Hence the length of the `aⁿ`-torsion is at
most `n` times the length of the `a`-torsion, which bounds the length of the `a`-torsion for any
`a` dividing a power of a fixed element.

## Main results

* `Module.length_eq_add_length_quotient`: the length of a module is the length of a submodule
  plus the length of the corresponding quotient.
* `Module.length_torsionBy_mul_le`: subadditivity of the length of torsion submodules in the
  scalar.
* `Module.length_torsionBy_pow_le`: the length of the `aⁿ`-torsion is at most `n` times the
  length of the `a`-torsion.
* `Module.length_torsionBy_le_of_dvd_pow`: a bound on the length of the `c`-torsion bounds the
  length of the `a`-torsion whenever `a` divides a power of `c`.

## Implementation notes

The statements hold for an arbitrary module over a commutative ring, with no finiteness
hypothesis: lengths are valued in `ℕ∞`, as in `Module.length_eq_add_of_exact`.

## References

* [Stacks Project, Tag 0AXJ](https://stacks.math.columbia.edu/tag/0AXJ)
-/

@[expose] public section

universe u v

namespace Module

variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

open Submodule

/-- The length of a module is the length of a submodule plus the length of the quotient by it. -/
theorem length_eq_add_length_quotient (N : Submodule R M) :
    Module.length R M = Module.length R ↥N + Module.length R (M ⧸ N) :=
  Module.length_eq_add_of_exact N.subtype N.mkQ (Submodule.subtype_injective N)
    (Submodule.mkQ_surjective N) (LinearMap.exact_subtype_mkQ N)

/-- The length of the `ab`-torsion of a module is at most the length of its `a`-torsion plus the
length of its `b`-torsion. -/
theorem length_torsionBy_mul_le (a b : R) :
    Module.length R ↥(torsionBy R M (a * b)) ≤
      Module.length R ↥(torsionBy R M a) + Module.length R ↥(torsionBy R M b) := by
  have hKL : torsionBy R M a ≤ torsionBy R M (a * b) :=
    torsionBy_le_torsionBy_of_dvd a (a * b) ⟨b, rfl⟩
  have hmem : ∀ x : ↥(torsionBy R M (a * b)),
      ((DistribSMul.toLinearMap R M a).comp (torsionBy R M (a * b)).subtype) x
        ∈ torsionBy R M b := by
    intro x
    have hx : (a * b) • (x : M) = 0 := (mem_torsionBy_iff _ _).mp x.2
    simp only [LinearMap.comp_apply, coe_subtype, mem_torsionBy_iff]
    show b • a • (x : M) = 0
    rw [smul_smul, mul_comm b a, hx]
  set φ := LinearMap.codRestrict (torsionBy R M b)
    ((DistribSMul.toLinearMap R M a).comp (torsionBy R M (a * b)).subtype) hmem with hφ
  have hker : LinearMap.ker φ
      = Submodule.comap (torsionBy R M (a * b)).subtype (torsionBy R M a) := by
    ext x
    simp only [hφ, LinearMap.mem_ker, LinearMap.codRestrict_apply, Submodule.mem_comap,
      coe_subtype, mem_torsionBy_iff, Subtype.ext_iff, ZeroMemClass.coe_zero,
      LinearMap.comp_apply]
    rfl
  have h1 : Module.length R ↥(torsionBy R M (a * b))
      = Module.length R ↥(LinearMap.ker φ)
        + Module.length R (↥(torsionBy R M (a * b)) ⧸ LinearMap.ker φ) :=
    length_eq_add_length_quotient R _ (LinearMap.ker φ)
  have h2 : Module.length R ↥(LinearMap.ker φ) = Module.length R ↥(torsionBy R M a) := by
    rw [hker]
    exact (Submodule.comapSubtypeEquivOfLe hKL).length_eq
  have h3 : Module.length R (↥(torsionBy R M (a * b)) ⧸ LinearMap.ker φ)
      ≤ Module.length R ↥(torsionBy R M b) := by
    rw [φ.quotKerEquivRange.length_eq]
    exact Module.length_le_of_injective (Submodule.subtype _) (Submodule.subtype_injective _)
  rw [h1, h2]
  gcongr

/-- The length of the `aⁿ`-torsion of a module is at most `n` times the length of its
`a`-torsion. -/
theorem length_torsionBy_pow_le (a : R) (n : ℕ) :
    Module.length R ↥(torsionBy R M (a ^ n)) ≤ n * Module.length R ↥(torsionBy R M a) := by
  induction n with
  | zero => rw [pow_zero, torsionBy_one]; simp
  | succ n ih =>
    calc Module.length R ↥(torsionBy R M (a ^ (n + 1)))
        ≤ Module.length R ↥(torsionBy R M (a ^ n))
            + Module.length R ↥(torsionBy R M a) := by
          rw [pow_succ]; exact length_torsionBy_mul_le R M _ _
      _ ≤ n * Module.length R ↥(torsionBy R M a)
            + Module.length R ↥(torsionBy R M a) := by gcongr
      _ = (n + 1 : ℕ) * Module.length R ↥(torsionBy R M a) := by
          push_cast; rw [add_mul, one_mul]

/-- If `a` divides `cⁿ` then the length of the `a`-torsion of a module is at most `n` times the
length of its `c`-torsion. -/
theorem length_torsionBy_le_of_dvd_pow {a c : R} {n : ℕ} (h : a ∣ c ^ n) :
    Module.length R ↥(torsionBy R M a) ≤ n * Module.length R ↥(torsionBy R M c) :=
  le_trans (Module.length_le_of_injective
      (Submodule.inclusion (torsionBy_le_torsionBy_of_dvd a (c ^ n) h))
      (Submodule.inclusion_injective _))
    (length_torsionBy_pow_le R M c n)

end Module

end
