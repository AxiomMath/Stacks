module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Basic
public import StacksFrontier.RingTheory.AdicCompletion.MapOfPowLe

/-!
# Linearity over an adic completion comes for free on separated modules

Let `I` be a finitely generated ideal of a commutative ring `A` and write `Â` for the `I`-adic
completion of `A`. A map between `Â`-modules which is only assumed `A`-linear is automatically
`Â`-linear as soon as its target is `I`-adically separated. The reason is that `A` already
exhausts `Â` modulo every power of `I` (`AdicCompletion.exists_sub_mem_map_pow`): given `a ∈ Â`
and `n`, there is `c ∈ A` with `a - c ∈ Iⁿ · Â`, so for an `A`-linear `f` the discrepancy
`f(a • x) - a • f x` equals `f(b • x) - b • f x` for `b = a - c ∈ Iⁿ · Â`, and both terms lie in
`Iⁿ · N`. The discrepancy therefore lies in `⋂ₙ Iⁿ · N`, which is zero.

## Main definitions

* `AdicCompletion.toCompletionLinearMap`: an `A`-linear map between `Â`-modules with separated
  target, as an `Â`-linear map.
* `AdicCompletion.toCompletionLinearEquiv`: an `A`-linear equivalence between `Â`-modules with
  separated target, as an `Â`-linear equivalence.

## Main results

* `AdicCompletion.map_smul_of_isHausdorff`: an `A`-linear map between `Â`-modules commutes with
  the `Â`-action when the target is `I`-adically separated.
-/

@[expose] public section

namespace AdicCompletion

variable {A : Type*} [CommRing A] {I : Ideal A}

/-- An `A`-linear map carries `Iⁿ • ⊤` into `Iⁿ • ⊤`. -/
public theorem map_mem_pow_smul_top {A : Type*} [CommRing A] {M N : Type*} [AddCommGroup M]
    [Module A M] [AddCommGroup N] [Module A N] (f : M →ₗ[A] N) (I : Ideal A) (n : ℕ) {x : M}
    (hx : x ∈ (I ^ n) • (⊤ : Submodule A M)) :
    f x ∈ (I ^ n) • (⊤ : Submodule A N) := by
  have := Submodule.mem_map_of_mem (f := f) hx
  rw [Submodule.map_smul''] at this
  exact Submodule.smul_mono le_rfl le_top this

/-- Scalar multiplication by an element of `Iⁿ · Â` carries any `Â`-module into `Iⁿ` times
itself. -/
private theorem smul_mem_pow_smul_top {P : Type*} [AddCommGroup P] [Module A P]
    [Module (AdicCompletion I A) P] [IsScalarTower A (AdicCompletion I A) P]
    {n : ℕ} {a : AdicCompletion I A}
    (ha : a ∈ (I ^ n) • (⊤ : Submodule A (AdicCompletion I A))) (p : P) :
    a • p ∈ (I ^ n) • (⊤ : Submodule A P) :=
  map_mem_pow_smul_top ((LinearMap.toSpanSingleton _ P p).restrictScalars A) I n ha

section

variable {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
  [Module (AdicCompletion I A) M] [IsScalarTower A (AdicCompletion I A) M]
  [Module (AdicCompletion I A) N] [IsScalarTower A (AdicCompletion I A) N]

/-- **An `A`-linear map between `Â`-modules is `Â`-linear when its target is separated.** Here
`Â` is the `I`-adic completion of `A` for a finitely generated ideal `I`, and separatedness of
`N` is `IsHausdorff I N`, that is `⋂ₙ Iⁿ · N = 0`. -/
theorem map_smul_of_isHausdorff (hI : I.FG) [IsHausdorff I N]
    (f : M →ₗ[A] N) (a : AdicCompletion I A) (x : M) :
    f (a • x) = a • f x := by
  rw [← sub_eq_zero]
  refine IsHausdorff.haus ‹IsHausdorff I N› _ fun n => ?_
  rw [SModEq.zero]
  obtain ⟨c, hc⟩ := exists_sub_mem_map_pow I hI n a
  set b := a - algebraMap A (AdicCompletion I A) c with hb
  have hbmem : b ∈ (I ^ n) • (⊤ : Submodule A (AdicCompletion I A)) := by
    rw [Ideal.smul_top_eq_map]
    exact hc
  have hsplit : f (a • x) - a • f x = f (b • x) - b • f x := by
    have ha : a = b + algebraMap A (AdicCompletion I A) c := by rw [hb]; ring
    have h1 : f ((algebraMap A (AdicCompletion I A) c) • x) =
        (algebraMap A (AdicCompletion I A) c) • f x := by
      rw [algebraMap_smul, algebraMap_smul, f.map_smul]
    rw [ha, add_smul, map_add, add_smul, h1]
    abel
  rw [hsplit]
  exact Submodule.sub_mem _ (map_mem_pow_smul_top f I _ (smul_mem_pow_smul_top hbmem x))
    (smul_mem_pow_smul_top hbmem (f x))

/-- An `A`-linear map between `Â`-modules with separated target, read as a `Â`-linear map. -/
def toCompletionLinearMap (hI : I.FG) [IsHausdorff I N] (f : M →ₗ[A] N) :
    M →ₗ[AdicCompletion I A] N where
  toFun := f
  map_add' := f.map_add
  map_smul' a x := map_smul_of_isHausdorff hI f a x

/-- The map `toCompletionLinearMap hI f` agrees with `f` on every element. -/
@[simp]
theorem toCompletionLinearMap_apply (hI : I.FG) [IsHausdorff I N] (f : M →ₗ[A] N) (x : M) :
    toCompletionLinearMap hI f x = f x :=
  rfl

/-- An `A`-linear equivalence between `Â`-modules with separated target, read as a `Â`-linear
equivalence. -/
def toCompletionLinearEquiv (hI : I.FG) [IsHausdorff I N] (e : M ≃ₗ[A] N) :
    M ≃ₗ[AdicCompletion I A] N where
  __ := toCompletionLinearMap hI (e : M →ₗ[A] N)
  invFun := e.symm
  left_inv := e.left_inv
  right_inv := e.right_inv

/-- The equivalence `toCompletionLinearEquiv hI e` agrees with `e` on every element. -/
@[simp]
theorem toCompletionLinearEquiv_apply (hI : I.FG) [IsHausdorff I N] (e : M ≃ₗ[A] N) (x : M) :
    toCompletionLinearEquiv hI e x = e x :=
  rfl

end

end AdicCompletion

end
