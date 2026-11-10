module

public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.Module.BigOperators

/-!
# The kernel of a surjection onto a module of rank one

Let `P` be a free module with basis `(f_j)_{j ∈ ι}` together with one more vector `f₀`, and let
`u : P ⟶ L` be a linear map with `u(f_j) = y_j u(f₀)` such that multiplication by `u(f₀)` is
injective on scalars. Then the kernel of `u` is free with basis `y_j f₀ - f_j`. This is the
description of the kernel of the tautological surjection `π^*(𝒞 ⊕ 𝒪) ⟶ 𝒪(1)` of a projective
completion on the open where the last coordinate does not vanish.

## Main results

* `Module.Basis.exists_basis_of_ker`: the kernel basis, read through an injective map `κ` onto the
  kernel.
* `injective_smul_of_surjective_smul`: on a module isomorphic to the ring, multiplication by a
  generator is injective.
-/

@[expose] public section

namespace Module.Basis

variable {R P L K : Type*} [CommRing R] [AddCommGroup P] [Module R P] [AddCommGroup L]
  [Module R L] [AddCommGroup K] [Module R K] {ι : Type*} [Finite ι]

/-- **The kernel of a map with `u(f_j) = y_j u(f₀)`.** If `(f_j, f₀)` is a basis of `P`,
`u(f_j) = y_j u(f₀)`, multiplication by `u(f₀)` is injective on scalars and `κ : K ⟶ P` is
injective with image the kernel of `u`, then `K` has a basis `e` with `κ(e_j) = y_j f₀ - f_j`. -/
theorem exists_basis_of_ker (f : Module.Basis (ι ⊕ Unit) R P) (u : P →ₗ[R] L) (κ : K →ₗ[R] P)
    (hκ : Function.Injective κ) (hu : ∀ k, u (κ k) = 0) (hex : ∀ p, u p = 0 → ∃ k, κ k = p)
    (y : ι → R) (hy : ∀ j, u (f (.inl j)) = y j • u (f (.inr ())))
    (hinj : ∀ c : R, c • u (f (.inr ())) = 0 → c = 0) :
    ∃ e : Module.Basis ι R K, ∀ j, κ (e j) = y j • f (.inr ()) - f (.inl j) := by
  classical
  have := Fintype.ofFinite ι
  choose k hk using fun j => hex (y j • f (.inr ()) - f (.inl j)) (by
    rw [map_sub, map_smul, hy, sub_self])
  have hli : LinearIndependent R k := by
    refine LinearIndependent.of_comp κ ?_
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h := congrArg (fun p => f.repr p (.inl i)) hg
    simp only [Function.comp_apply, hk, map_sum, map_smul, map_sub, Basis.repr_self,
      Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, Finsupp.coe_sub,
      Pi.sub_apply, Finsupp.single_apply, reduceCtorEq, ite_false, smul_eq_mul, mul_zero,
      zero_sub, Sum.inl.injEq, map_zero, Finsupp.coe_zero, Pi.zero_apply] at h
    simpa [Finset.sum_ite_eq'] using h
  have hsp : ⊤ ≤ Submodule.span R (Set.range k) := by
    intro x _
    set a := f.repr (κ x)
    have hsum : κ x = (∑ j, a (.inl j) • f (.inl j)) + a (.inr ()) • f (.inr ()) := by
      have h := (f.sum_repr (κ x)).symm
      rw [Fintype.sum_sum_type] at h
      simpa only [Finset.univ_unique, Finset.sum_singleton] using h
    have h0 : (∑ j, a (.inl j) * y j + a (.inr ())) • u (f (.inr ())) = 0 := by
      have h := hu x
      rw [hsum, map_add, map_sum] at h
      simp only [map_smul, hy, smul_smul] at h
      rwa [add_smul, Finset.sum_smul]
    have ha0 : a (.inr ()) = -∑ j, a (.inl j) * y j := by linear_combination hinj _ h0
    have hx : κ x = κ (∑ j, (-a (.inl j)) • k j) := by
      rw [map_sum]
      simp only [map_smul, hk]
      rw [hsum, ha0]
      simp only [smul_sub, neg_smul, smul_smul, Finset.sum_smul, sub_neg_eq_add]
      rw [Finset.sum_add_distrib]
      simp only [neg_mul, neg_smul, Finset.sum_neg_distrib]
      exact add_comm _ _
    rw [hκ hx]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  exact ⟨Basis.mk hli hsp, fun j => by rw [Basis.mk_apply, hk]⟩

end Module.Basis

/-- **On a module isomorphic to the ring, multiplication by a generator is injective**: if
`c ↦ c • g` is onto `L ≅ R`, then the coordinate of `g` is a unit. -/
theorem injective_smul_of_surjective_smul {R L : Type*} [CommRing R] [AddCommGroup L]
    [Module R L] (e : L ≃ₗ[R] R) {g : L} (h : Function.Surjective fun c : R => c • g) :
    Function.Injective fun c : R => c • g := by
  obtain ⟨c, hc⟩ := h (e.symm 1)
  have hu : IsUnit (e g) := .of_mul_eq_one_right c (by simpa using congrArg e hc)
  intro a b hab
  exact hu.mul_left_inj.1 (by simpa using congrArg e hab)
