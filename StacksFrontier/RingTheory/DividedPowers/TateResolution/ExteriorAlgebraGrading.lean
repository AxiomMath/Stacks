module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.Basic

/-! # The exterior algebra is strictly graded commutative

The exterior algebra `⋀[R] M`, graded by its exterior powers (`ExteriorAlgebra.gradedAlgebra`), is
strictly graded commutative in the sense of `DividedPowers.TateResolution.IsStrictlyGradedComm`:
homogeneous elements commute up to the Koszul sign, and a homogeneous element of odd exterior
degree squares to zero. This file also proves that `ExteriorAlgebra.map` preserves exterior
degree, that it is an algebra equivalence when its argument is a linear equivalence, and that all
positive exterior powers of a subsingleton module vanish.

## Main definitions

* `ExteriorAlgebra.mapAlgEquiv` — the algebra equivalence induced by a linear equivalence.

## Main results

* `ExteriorAlgebra.mul_comm_exteriorPower` — the Koszul commutation rule on homogeneous
  elements.
* `ExteriorAlgebra.sq_eq_zero_of_mem_odd_exteriorPower` — an element of odd exterior degree
  squares to zero.
* `ExteriorAlgebra.instIsStrictlyGradedComm` — the resulting instance.
* `ExteriorAlgebra.map_mem_exteriorPower` — `ExteriorAlgebra.map` preserves exterior degree.
* `ExteriorAlgebra.exteriorPower_eq_bot` — positive exterior powers of a subsingleton module
  vanish.

## References

* [Stacks Project, Tag 09PG](https://stacks.math.columbia.edu/tag/09PG)
* [Stacks Project, Tag 09PH](https://stacks.math.columbia.edu/tag/09PH)
-/

@[expose] public section

namespace ExteriorAlgebra

open scoped ExteriorAlgebra
open DividedPowers.TateResolution

universe u v w

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- A sign in the units of `ℤ` acts on an `R`-algebra as the corresponding sign in `R`. -/
public theorem zunits_neg_one_pow_smul (k : ℕ) (z : ExteriorAlgebra R M) :
    ((-1 : ℤˣ) ^ k) • z = ((-1 : R) ^ k) • z := by
  rw [Units.smul_def, ← Int.cast_smul_eq_zsmul R]
  push_cast
  rfl

/-- The image of a vector lies in the first exterior power. -/
public theorem ι_mem_exteriorPower_one (x : M) : ι R x ∈ ⋀[R]^1 M := by
  simp [exteriorPower]

/-- The Koszul commutation rule: elements of exterior degrees `i` and `j` commute up to the
sign `(-1) ^ (i * j)`. -/
public theorem mul_comm_exteriorPower {i j : ℕ} {x y : ExteriorAlgebra R M}
    (hx : x ∈ ⋀[R]^i M) (hy : y ∈ ⋀[R]^j M) :
    x * y = (-1 : R) ^ (i * j) • (y * x) := by
  rw [← (Submodule.ext_iff.mp (ιMulti_span_fixedDegree R i))] at hx
  rw [← (Submodule.ext_iff.mp (ιMulti_span_fixedDegree R j))] at hy
  refine Submodule.span_induction₂ (p := fun x y _ _ ↦
    x * y = (-1 : R) ^ (i * j) • (y * x)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro x y ⟨u, rfl⟩ ⟨v, rfl⟩
    rw [ιMulti_mul_ιMulti_anticomm R u v, zunits_neg_one_pow_smul, Nat.mul_comm j i]
  all_goals simp +contextual [add_mul, mul_add, smul_add, smul_smul, mul_comm]

/-- An element of odd exterior degree squares to zero. -/
public theorem sq_eq_zero_of_mem_odd_exteriorPower {d : ℕ} {x : ExteriorAlgebra R M}
    (hx : x ∈ ⋀[R]^(2 * d + 1) M) : x ^ 2 = 0 := by
  have hspan := Submodule.ext_iff.mp (ιMulti_span_fixedDegree R (2 * d + 1) (M := M))
  have key : ∀ y ∈ Submodule.span R (Set.range (ιMulti R (2 * d + 1) (M := M))),
      y * y = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨u, rfl⟩ := hz
      rw [ιMulti_mul_ιMulti]
      refine ιMulti_eq_zero_of_not_inj fun hinj => ?_
      simpa [Fin.ext_iff] using
        @hinj (Fin.castAdd (2 * d + 1) 0) (Fin.natAdd (2 * d + 1) 0)
          (by rw [Fin.append_left, Fin.append_right])
    | zero => simp
    | add a b ha hb iha ihb =>
      have hab : a * b = -(b * a) := by
        rw [mul_comm_exteriorPower ((hspan a).mp ha) ((hspan b).mp hb),
          ((odd_two_mul_add_one d).mul (odd_two_mul_add_one d)).neg_one_pow, neg_one_smul]
      rw [mul_add, add_mul, add_mul, iha, ihb, hab]
      abel
    | smul r a _ iha => rw [mul_smul_comm, smul_mul_assoc, iha, smul_zero, smul_zero]
  exact (pow_two x).trans (key x ((hspan x).mpr hx))

/-- The exterior algebra, graded by its exterior powers, is strictly graded commutative. -/
public instance instIsStrictlyGradedComm :
    IsStrictlyGradedComm (fun i : ℕ ↦ ⋀[R]^i M) where
  graded_comm hx hy := mul_comm_exteriorPower hx hy
  odd_sq_zero hx := sq_eq_zero_of_mem_odd_exteriorPower hx

section Map

variable {N : Type w} [AddCommGroup N] [Module R N]

/-- `ExteriorAlgebra.map` preserves exterior degree. -/
public theorem map_mem_exteriorPower (f : M →ₗ[R] N) {m : ℕ} {x : ExteriorAlgebra R M}
    (hx : x ∈ ⋀[R]^m M) : map f x ∈ ⋀[R]^m N := by
  rw [← (Submodule.ext_iff.mp (ιMulti_span_fixedDegree R m))] at hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨u, rfl⟩ := hz
    rw [map_apply_ιMulti, ← (Submodule.ext_iff.mp (ιMulti_span_fixedDegree R m))]
    exact Submodule.subset_span ⟨f ∘ u, rfl⟩
  | zero => simp
  | add a b _ _ iha ihb => simpa using Submodule.add_mem _ iha ihb
  | smul r a _ iha => simpa using Submodule.smul_mem _ r iha

/-- The algebra equivalence of exterior algebras induced by a linear equivalence. -/
public noncomputable def mapAlgEquiv (e : M ≃ₗ[R] N) :
    ExteriorAlgebra R M ≃ₐ[R] ExteriorAlgebra R N :=
  AlgEquiv.ofAlgHom (map (e : M →ₗ[R] N)) (map (e.symm : N →ₗ[R] M))
    (by rw [map_comp_map]; simp)
    (by rw [map_comp_map]; simp)

/-- `ExteriorAlgebra.mapAlgEquiv e` acts as `ExteriorAlgebra.map e`. -/
@[simp]
public theorem mapAlgEquiv_apply (e : M ≃ₗ[R] N) (x : ExteriorAlgebra R M) :
    mapAlgEquiv e x = map (e : M →ₗ[R] N) x := rfl

end Map

/-- Every positive exterior power of a subsingleton module vanishes. -/
public theorem exteriorPower_eq_bot [Subsingleton M] (m : ℕ) :
    ⋀[R]^(m + 1) M = ⊥ := by
  rw [exteriorPower, LinearMap.range_eq_bot.mpr (LinearMap.ext fun x => by
    simp [Subsingleton.elim x 0]), Submodule.bot_pow (Nat.succ_ne_zero m)]

end ExteriorAlgebra

end
