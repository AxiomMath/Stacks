module

public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Tensoring with a product almost all of whose factors are trivial

Let `A` be a commutative ring, let `N : ι → Type*` be a family of `A`-modules and let `M` be an
`A`-module.  The canonical map

`(∀ i, N i) ⊗_A M ⟶ ∀ i, (N i ⊗_A M)`,  `n ⊗ m ↦ fun i ↦ n i ⊗ m`

is an isomorphism when the index type is finite, which is `TensorProduct.piLeft`. This file
records the same conclusion under the weaker hypothesis that all but finitely many of the `N i`
are *trivial*: the product is then carried by the finite set of indices at which `N i` may be
nonzero, and both sides restrict bijectively to it.

## Main results

* `Stacks.subsingleton_tensorProduct_of_subsingleton_left`: a tensor product with a trivial
  left factor is trivial.
* `Stacks.bijective_restrict_of_subsingleton_notMem`: restriction of a product of modules to a
  finite set of indices outside of which the factors are trivial is bijective.
* `Stacks.bijective_pi_rTensor_proj`: **the canonical map above is bijective as soon as all but
  finitely many of the factors are trivial.**
* `Stacks.bijective_pi_rTensor_of_bijective_pi`: the same conclusion for a jointly bijective
  family of linear maps out of a single module.
-/

@[expose] public section

open TensorProduct

universe u v w t

namespace Stacks

variable {A : Type u} [CommRing A] {ι : Type v} {N : ι → Type w}
    [∀ i, AddCommGroup (N i)] [∀ i, Module A (N i)]
    {M : Type t} [AddCommGroup M] [Module A M]

/-- **A tensor product with a trivial left factor is trivial.** -/
theorem subsingleton_tensorProduct_of_subsingleton_left {P : Type w} [AddCommGroup P]
    [Module A P] [Subsingleton P] : Subsingleton (P ⊗[A] M) := by
  have h : ∀ z : P ⊗[A] M, z = 0 := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul p m => rw [Subsingleton.elim p 0, TensorProduct.zero_tmul]
    | add a b ha hb => rw [ha, hb, add_zero]
  exact ⟨fun x y => (h x).trans (h y).symm⟩

/-- **Restriction of a product of modules to a finite set of indices outside of which the
factors are trivial is bijective.** -/
theorem bijective_restrict_of_subsingleton_notMem (s : Finset ι)
    (hs : ∀ i ∉ s, Subsingleton (N i)) :
    Function.Bijective fun n : ∀ i, N i => fun j : {x : ι // x ∈ s} => n j.1 := by
  classical
  refine ⟨fun n n' h => funext fun i => ?_, fun g => ?_⟩
  · by_cases hi : i ∈ s
    · exact congrFun h ⟨i, hi⟩
    · exact (hs i hi).elim _ _
  · refine ⟨fun i => if hi : i ∈ s then g ⟨i, hi⟩ else 0, funext fun j => ?_⟩
    change (if hi : j.1 ∈ s then g ⟨j.1, hi⟩ else 0) = g j
    rw [dite_eq_left j.2]

/-- The restriction of a product of modules to a finite set of indices, as a linear map. -/
def piRestrict (s : Finset ι) : (∀ i, N i) →ₗ[A] ∀ j : {x : ι // x ∈ s}, N j.1 :=
  LinearMap.pi fun j => LinearMap.proj j.1

/-- `piRestrict s n` evaluated at `j` is `n j`. -/
@[simp]
theorem piRestrict_apply (s : Finset ι) (n : ∀ i, N i) (j : {x : ι // x ∈ s}) :
    piRestrict (A := A) (N := N) s n j = n j.1 := rfl

/-- **Tensoring with a product almost all of whose factors are trivial commutes with the
product.**  The canonical map `(∀ i, N i) ⊗_A M ⟶ ∀ i, N i ⊗_A M` is bijective as soon as the
factors `N i` are trivial outside a finite set of indices. -/
theorem bijective_pi_rTensor_proj (s : Finset ι) (hs : ∀ i ∉ s, Subsingleton (N i)) :
    Function.Bijective fun z : (∀ i, N i) ⊗[A] M =>
      fun i => LinearMap.rTensor M (LinearMap.proj i) z := by
  classical
  have h₁ : Function.Bijective (piRestrict (A := A) (N := N) s) :=
    bijective_restrict_of_subsingleton_notMem s hs
  let e₁ : (∀ i, N i) ≃ₗ[A] ∀ j : {x : ι // x ∈ s}, N j.1 :=
    LinearEquiv.ofBijective (piRestrict s) h₁
  have hts : ∀ i ∉ s, Subsingleton (N i ⊗[A] M) := fun i hi =>
    let := hs i hi
    subsingleton_tensorProduct_of_subsingleton_left
  have h₂ : Function.Bijective fun u : ∀ i, N i ⊗[A] M =>
      fun j : {x : ι // x ∈ s} => u j.1 :=
    bijective_restrict_of_subsingleton_notMem (N := fun i => N i ⊗[A] M) s hts
  set e₂ := TensorProduct.piLeft (R := A) (N := M)
    (M := fun j : {x : ι // x ∈ s} => N j.1) with he₂
  have hsq : (LinearMap.pi fun j : {x : ι // x ∈ s} =>
        LinearMap.rTensor M (LinearMap.proj j.1 : (∀ i, N i) →ₗ[A] N j.1)) =
      e₂.toLinearMap ∘ₗ (LinearEquiv.rTensor M e₁).toLinearMap := by
    refine TensorProduct.ext' fun n m => funext fun j => ?_
    change LinearMap.rTensor M (LinearMap.proj j.1) (n ⊗ₜ[A] m) =
      e₂ (LinearEquiv.rTensor M e₁ (n ⊗ₜ[A] m)) j
    rfl
  have hcomp : Function.Bijective
      ((fun u : ∀ i, N i ⊗[A] M => fun j : {x : ι // x ∈ s} => u j.1) ∘
        fun z : (∀ i, N i) ⊗[A] M => fun i => LinearMap.rTensor M (LinearMap.proj i) z) := by
    have h : ((fun u : ∀ i, N i ⊗[A] M => fun j : {x : ι // x ∈ s} => u j.1) ∘
          fun z : (∀ i, N i) ⊗[A] M => fun i => LinearMap.rTensor M (LinearMap.proj i) z) =
        fun z => e₂ (LinearEquiv.rTensor M e₁ z) := by
      funext z
      exact congrFun (congrArg (fun L : (∀ i, N i) ⊗[A] M →ₗ[A]
        ∀ j : {x : ι // x ∈ s}, N j.1 ⊗[A] M => fun w => L w) hsq) z
    rw [h]
    exact e₂.bijective.comp (LinearEquiv.rTensor M e₁).bijective
  exact (h₂.of_comp_iff' _).mp hcomp

/-- **Tensoring with a product almost all of whose factors are trivial commutes with the
product, in the form of a family of linear maps.**  Given a jointly bijective family
`cp i : K →ₗ[A] N i` and a finite set of indices outside which the `N i` are trivial, the family
`z ↦ cp i ⊗ id` is jointly bijective on `K ⊗_A M`. -/
theorem bijective_pi_rTensor_of_bijective_pi {K : Type*} [AddCommGroup K] [Module A K]
    (cp : ∀ i, K →ₗ[A] N i) (hc : Function.Bijective fun a : K => fun i => cp i a)
    (s : Finset ι) (hs : ∀ i ∉ s, Subsingleton (N i)) :
    Function.Bijective fun z : K ⊗[A] M => fun i => LinearMap.rTensor M (cp i) z := by
  classical
  set c : K →ₗ[A] ∀ i, N i := LinearMap.pi cp with hcdef
  have hcbij : Function.Bijective c := hc
  set e := LinearEquiv.ofBijective c hcbij with he
  have hfac : ∀ (i : ι) (z : K ⊗[A] M), LinearMap.rTensor M (cp i) z =
      LinearMap.rTensor M (LinearMap.proj i) (LinearMap.rTensor M c z) := by
    intro i z
    induction z using TensorProduct.inductionOn with
    | tmul a m => rfl
    | add y w hy hw => rw [map_add, map_add, map_add, hy, hw]
  have hcomp : (fun z : K ⊗[A] M => fun i => LinearMap.rTensor M (cp i) z) =
      (fun y : (∀ i, N i) ⊗[A] M => fun i => LinearMap.rTensor M (LinearMap.proj i) y) ∘
        fun z => LinearEquiv.rTensor M e z :=
    funext fun z => funext fun i => hfac i z
  rw [hcomp]
  exact (bijective_pi_rTensor_proj s hs).comp (LinearEquiv.rTensor M e).bijective

end Stacks

end
