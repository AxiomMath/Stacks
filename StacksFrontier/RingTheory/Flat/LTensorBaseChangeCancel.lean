module

public import StacksFrontier.RingTheory.Flat.MakeMapZeroIdeal
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Extension of scalars to a base change, read as a tensor product over the base

Let `R` be a commutative ring, let `A` and `R'` be `R`-algebras, and let `C` be an `A`-algebra
isomorphic to `A ⊗_R R'` over `A`.  For an `A`-module `N` whose `R`-action is the restriction
of its `A`-action, the extension of scalars `C ⊗_A N` is `N ⊗_R R'`.

Consequently, if the extension of scalars to `C` of a map `u : M ⟶ N` of `A`-modules vanishes,
then `u(m) ⊗ 1` vanishes in `N ⊗_R R'` for every `m`, which is the hypothesis of
`Stacks.Flattening.mem_ker_smul_top_of_tmul_eq_zero`.

## Main definitions

* `Stacks.Flattening.lTensorBaseChangeEquiv`: the identification `C ⊗_A N ≃ N ⊗_R R'`.

## Main results

* `Stacks.Flattening.lTensorBaseChangeEquiv_one_tmul`: it sends `1 ⊗ n` to `n ⊗ 1`.
* `Stacks.Flattening.tmul_one_eq_zero_of_lTensor_eq_zero`: vanishing of the extension of
  scalars of `u` to `C` gives the vanishing of `u(m) ⊗ 1` in `N ⊗_R R'`.

## Implementation notes

The identification is `TensorProduct.AlgebraTensorModule.cancelBaseChange`, which asks for the
base-changed factor on the right, so the symmetry of the tensor product is applied first.  Only
the value on `1 ⊗ n` is recorded, because that is the whole use: the element whose vanishing a
chart-wise criterion delivers is `1 ⊗ u(m)`.

Geometrically `A` is the ring of functions of an affine étale chart of an algebraic space over
the affine base `\Spec R`, `R'` is the ring of functions of an affine test scheme over the base,
and `C` is the ring of functions of the base change of the chart by the test scheme — the
isomorphism `C ≃ A ⊗_R R'` is then
`AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.chartRingBaseTestAlgEquiv`.

## References

* [Stacks Project, Tag 083K](https://stacks.math.columbia.edu/tag/083K)
-/

@[expose] public section

open TensorProduct

namespace Stacks.Flattening

variable {R : Type*} [CommRing R] {R' : Type*} [CommRing R'] [Algebra R R']
    {A : Type*} [CommRing A] [Algebra R A]
    {C : Type*} [CommRing C] [Algebra A C]
    {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [Module R N] [IsScalarTower R A N]

/-- **The extension of scalars of an `A`-module along `A ⟶ C = A ⊗_R R'` is its base change to
`R'` over `R`.** -/
noncomputable def lTensorBaseChangeEquiv (e : C ≃ₐ[A] A ⊗[R] R') :
    TensorProduct A C N ≃ₗ[A] TensorProduct R N R' :=
  TensorProduct.comm A C N ≪≫ₗ
    TensorProduct.congr (LinearEquiv.refl A N) e.toLinearEquiv ≪≫ₗ
      TensorProduct.AlgebraTensorModule.cancelBaseChange R A A N R'

/-- The identification sends `1 ⊗ n` to `n ⊗ 1`. -/
theorem lTensorBaseChangeEquiv_one_tmul (e : C ≃ₐ[A] A ⊗[R] R') (n : N) :
    lTensorBaseChangeEquiv (N := N) e ((1 : C) ⊗ₜ[A] n) = n ⊗ₜ[R] (1 : R') := by
  change TensorProduct.AlgebraTensorModule.cancelBaseChange R A A N R'
      (n ⊗ₜ[A] e (1 : C)) = n ⊗ₜ[R] (1 : R')
  rw [map_one, Algebra.TensorProduct.one_def,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul]

/-- **If the extension of scalars of a map of `A`-modules to `C = A ⊗_R R'` vanishes, then each
value of the map tensored with `1` vanishes in `N ⊗_R R'`.**

This is the hypothesis of `Stacks.Flattening.mem_ker_smul_top_of_tmul_eq_zero`, which for a flat
`N` turns it into membership of `\ker(R ⟶ R') \cdot N`. -/
theorem tmul_one_eq_zero_of_lTensor_eq_zero (e : C ≃ₐ[A] A ⊗[R] R') (u : M →ₗ[A] N)
    (h : LinearMap.lTensor C u = 0) (m : M) :
    u m ⊗ₜ[R] (1 : R') = 0 := by
  have h1 : (1 : C) ⊗ₜ[A] u m = 0 := by
    have h2 := LinearMap.congr_fun h ((1 : C) ⊗ₜ[A] m)
    rwa [LinearMap.lTensor_tmul, LinearMap.zero_apply] at h2
  have h3 := congrArg (lTensorBaseChangeEquiv (N := N) e) h1
  rwa [lTensorBaseChangeEquiv_one_tmul, map_zero] at h3

end Stacks.Flattening

end
