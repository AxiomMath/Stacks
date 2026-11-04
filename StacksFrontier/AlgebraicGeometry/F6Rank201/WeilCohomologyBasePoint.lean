module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.GroupWithZero.Idempotent
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.TensorProduct.Finite
public import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology of the base point of a Weil cohomology theory

Let `F` be the coefficient field of a Weil cohomology theory and let `H i` be the degree-`i`
cohomology of `Spec(k)`. Since `Spec(k) × Spec(k) = Spec(k)`, the Künneth axiom (B)(a) is a family
of `F`-linear isomorphisms `⨁ⱼ H j ⊗_F H (n - j) ≅ H n`. By these and by the normalisation axiom
(C)(d), `H i = 0` for `i ≠ 0`, and the structural map `F → H⁰(Spec k)` is the unique `F`-algebra
isomorphism. If the cycle class of the fundamental class of the point is idempotent, as (C)(c)
asserts, then it is the unit, and the integral of the unit is `1`.

## Main results

* `Stacks.Weil.subsingleton_cohomology_of_ne_zero` — the cohomology of the base point
  vanishes outside degree zero.
* `Stacks.Weil.existsUnique_algebraEquiv_degree_zero` — there is a unique `F`-algebra
  isomorphism `F ≅ H⁰(Spec k)`, namely the structural one.
* `Stacks.Weil.cycleClass_fundamentalClass_eq_one` — the cycle class of the fundamental
  class of the point is the unit.
* `Stacks.Weil.trace_one_eq_one` — integration of `1` over the point gives `1`.

## Implementation notes

The cycle group `Z` is an arbitrary abelian group with an arbitrary element `fundamentalClass`,
so the idempotency of `cycleClass fundamentalClass` is the hypothesis
`cycleClass_fundamental_mul`. The last two results above assume it; the first two do not.

## References

* [Stacks Project, Tag 0FHE](https://stacks.math.columbia.edu/tag/0FHE)
-/

@[expose] public section

open Module

namespace Stacks.Weil

universe u v w z

/-- For `j ≠ k`, the Künneth isomorphisms give
`dim H j * dim H (n - j) + dim H k * dim H (n - k) ≤ dim H n`. -/
private theorem finrank_mul_add_mul_le (F : Type u) [Field F] (H : ℤ → Type v)
    [∀ i : ℤ, AddCommGroup (H i)] [∀ i : ℤ, Module F (H i)]
    [∀ i : ℤ, FiniteDimensional F (H i)]
    (kunneth : ∀ n : ℤ,
      DirectSum ℤ (fun j : ℤ ↦ TensorProduct F (H j) (H (n - j))) ≃ₗ[F] H n)
    {n j k a b : ℤ} (hjk : j ≠ k) (ha : a = n - j) (hb : b = n - k) :
    finrank F (H j) * finrank F (H a) + finrank F (H k) * finrank F (H b) ≤
      finrank F (H n) := by
  subst ha hb
  classical
  set M : ℤ → Type v := fun i ↦ TensorProduct F (H i) (H (n - i))
  have hfin : ∀ i : ℤ, Module.Finite F (M i) := fun i ↦
    inferInstanceAs (Module.Finite F (TensorProduct F (H i) (H (n - i))))
  have hfree : ∀ i : ℤ, Module.Free F (M i) := fun i ↦
    inferInstanceAs (Module.Free F (TensorProduct F (H i) (H (n - i))))
  let f : (M j × M k) →ₗ[F] DirectSum ℤ M :=
    (DirectSum.lof F ℤ M j).comp (LinearMap.fst F (M j) (M k)) +
      (DirectSum.lof F ℤ M k).comp (LinearMap.snd F (M j) (M k))
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    simp only [f, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply] at hx
    have h1 := congrArg (DirectSum.component F ℤ M j) hx
    have h2 := congrArg (DirectSum.component F ℤ M k) hx
    simp only [map_add, DirectSum.component.lof_self, DirectSum.component.of, hjk.symm,
      ↓reduceDIte, add_zero, map_zero, hjk, zero_add] at h1 h2
    exact Prod.ext h1 h2
  have hle := LinearMap.finrank_le_finrank_of_injective
    (f := (kunneth n).toLinearMap.comp f) ((kunneth n).injective.comp hf)
  rwa [Module.finrank_prod, Module.finrank_tensorProduct, Module.finrank_tensorProduct] at hle

variable (F : Type u) [Field F]
  (H : ℤ → Type v)
  [∀ i : ℤ, AddCommGroup (H i)] [∀ i : ℤ, Module F (H i)]
  [∀ i : ℤ, FiniteDimensional F (H i)]
  (kunneth : ∀ n : ℤ,
    DirectSum ℤ (fun j : ℤ ↦ TensorProduct F (H j) (H (n - j))) ≃ₗ[F] H n)
  (Hpoint : Type w) [CommRing Hpoint] [Algebra F Hpoint]
  (degreeZero : H 0 ≃ₗ[F] Hpoint)
  (Z : Type z) [AddCommGroup Z]
  (fundamentalClass : Z) (cycleClass : Z →+ Hpoint)
  (trace : Hpoint →ₗ[F] F)
  (trace_fundamental : trace (cycleClass fundamentalClass) = 1)
  (cycleClass_fundamental_mul :
    cycleClass fundamentalClass * cycleClass fundamentalClass =
      cycleClass fundamentalClass)

include kunneth degreeZero trace_fundamental in
/-- The degree-zero cohomology of the base point is one-dimensional. -/
private theorem finrank_degree_zero_eq_one : finrank F (H 0) = 1 := by
  have hntP : Nontrivial Hpoint := (subsingleton_or_nontrivial Hpoint).resolve_left fun _ ↦ by
    simp [Subsingleton.elim (cycleClass fundamentalClass) 0] at trace_fundamental
  have hnt0 : Nontrivial (H 0) := degreeZero.symm.injective.nontrivial
  have hpos : 0 < finrank F (H 0) := Module.finrank_pos
  have hsq := finrank_mul_add_mul_le F H kunneth (n := 0) (j := 0) (k := 1)
    (a := 0) (b := -1) (by norm_num) (by norm_num) (by norm_num)
  have h1 : finrank F (H 0) * finrank F (H 0) ≤ finrank F (H 0) :=
    (Nat.le_add_right _ _).trans hsq
  have h2 : finrank F (H 0) ≤ 1 := Nat.le_of_mul_le_mul_left (by simpa using h1) hpos
  lia

include kunneth degreeZero trace_fundamental in
/-- The cohomology of the base point vanishes outside degree zero. -/
@[stacks 0FHE "vanishing away from degree zero"]
theorem subsingleton_cohomology_of_ne_zero (i : ℤ) (hi : i ≠ 0) :
    Subsingleton (H i) := by
  rw [← Module.finrank_zero_iff (R := F)]
  have h0 : finrank F (H 0) = 1 :=
    finrank_degree_zero_eq_one F H kunneth Hpoint degreeZero Z fundamentalClass cycleClass
      trace trace_fundamental
  have h := finrank_mul_add_mul_le F H kunneth (n := i) (j := 0) (k := i)
    (a := i) (b := 0) (Ne.symm hi) (by ring) (by ring)
  rw [h0] at h
  lia

include kunneth degreeZero trace_fundamental in
/-- The coefficient-field algebra map is an isomorphism onto degree-zero
cohomology of the base point, and it is the unique algebra isomorphism. -/
@[stacks 0FHE "coefficient-field algebra isomorphism"]
theorem existsUnique_algebraEquiv_degree_zero :
    ∃! e : F ≃ₐ[F] Hpoint,
      ∀ a : F, e a = algebraMap F Hpoint a := by
  have h0 : finrank F (H 0) = 1 :=
    finrank_degree_zero_eq_one F H kunneth Hpoint degreeZero Z fundamentalClass
      cycleClass trace trace_fundamental
  have hnt0 : Nontrivial (H 0) := Module.nontrivial_of_finrank_pos (R := F) (by lia)
  have hntP : Nontrivial Hpoint := degreeZero.injective.nontrivial
  have : FiniteDimensional F Hpoint := degreeZero.finiteDimensional
  have hrank : finrank F Hpoint = finrank F F := by
    rw [Module.finrank_self, ← degreeZero.finrank_eq, h0]
  have hinj : Function.Injective (Algebra.linearMap F Hpoint) :=
    (algebraMap F Hpoint).injective
  have hsurj : Function.Surjective (Algebra.linearMap F Hpoint) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank.symm).mp hinj
  exact ⟨AlgEquiv.ofBijective (Algebra.ofId F Hpoint) ⟨hinj, hsurj⟩, fun a ↦ rfl,
    fun e he ↦ AlgEquiv.ext he⟩

/- The forms of the two results below that assume only Weil axiom `(C)(c)`, taking the cycle group
to be `A_0(Spec(k))`, are `Stacks.Weil.cycleClass_fundamentalChowClass_eq_one` and
`Stacks.Weil.trace_one_fundamentalChowClass_eq_one`. -/
include kunneth degreeZero trace_fundamental cycleClass_fundamental_mul in
/-- The cycle class of the fundamental class of the point is the unit, provided it is
idempotent. -/
theorem cycleClass_fundamentalClass_eq_one : cycleClass fundamentalClass = 1 := by
  obtain ⟨e, he, -⟩ :=
    existsUnique_algebraEquiv_degree_zero F H kunneth Hpoint degreeZero Z fundamentalClass
      cycleClass trace trace_fundamental
  obtain ⟨x, hx⟩ := e.surjective (cycleClass fundamentalClass)
  have hidem : IsIdempotentElem x :=
    e.injective (by rw [map_mul, hx, cycleClass_fundamental_mul])
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp hidem with rfl | rfl
  · simp [← hx] at trace_fundamental
  · simpa using hx.symm

include kunneth degreeZero trace_fundamental cycleClass_fundamental_mul in
/-- Integration of `1` over the point is `1`, provided the cycle class of the fundamental class
is idempotent. -/
theorem trace_one_eq_one : trace 1 = 1 := by
  rwa [← cycleClass_fundamentalClass_eq_one F H kunneth Hpoint degreeZero Z fundamentalClass
    cycleClass trace trace_fundamental cycleClass_fundamental_mul]

end Stacks.Weil
