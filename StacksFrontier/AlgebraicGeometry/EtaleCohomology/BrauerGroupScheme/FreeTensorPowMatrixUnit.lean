module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.AltProjectorFreeSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.FreeDualMatrixLocal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.FreeTensorPowFamilyMatrix

/-!
# A matrix unit of the algebra of size `d ^ m` is a tensor of matrix units

Let `S` be a scheme. Under the identification `natTensorPowFreeIso` of the `m`-fold tensor power
of the free sheaf of `𝒪_S`-modules of rank `d` with the free sheaf on `Fin m → Fin d`, the
`(c, e)` matrix unit of the endomorphism algebra of the latter is the tensor product, over
`j : Fin m`, of the `(c j, e j)` matrix units of the endomorphism algebra of the former.

This is what makes the overlap step of [Stacks, Tag 0A2L] computable: the tensor power of an
automorphism of `Mat_d(𝒪_S)` acts factorwise on tensors of endomorphisms
(`pointMap_natTensorPowEndConj`), so once the matrix units of `Mat_{d ^ m}(𝒪_S)` are exhibited as
such tensors, its action on *every* matrix of the big algebra is determined by its action on the
matrix units of the small one -- and that action is locally conjugation by one invertible matrix
of sections.

The proof is the iterated Kronecker law for a family,
`Stacks.EtaleCohomology.BrauerScheme.freeEndMatrixEquiv_natTensorPowFam`, together with the
dictionary bridge `Stacks.EtaleCohomology.BrauerScheme.freeDualMatrix_eq_freeEndMatrixEquiv`: on
both sides the matrix is an indicator, and a product of indicators over `j` is the indicator of
the conjunction, which is exactly equality of the two index functions.

## Main results

* `Stacks.EtaleCohomology.BrauerScheme.conj_natTensorPowFreeIso_uncurry'_matIncl`: **the matrix
  unit of the algebra of size `d ^ m` is the tensor of the matrix units of the algebra of size
  `d`.**

## References

* [Stacks Project, Tag 0A2L](https://stacks.math.columbia.edu/tag/0A2L)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry TopologicalSpace
open Stacks.SheafOfModules

universe u

noncomputable section

namespace Stacks.EtaleCohomology.BrauerScheme

attribute [local instance] hasFiniteBiproductsModuleSheaf monoidalPreadditiveModuleSheaf

/-- A product of indicators of equalities is the indicator of the conjunction. -/
theorem prod_single_ulift {T : Scheme.{u}} {d m : ℕ} (c e : Fin m → Fin d) (k l : Fin m → Fin d) :
    (∏ j, Matrix.single (ULift.up.{u, 0} (c j)) (ULift.up.{u, 0} (e j)) (1 : R₀ T)
        (ULift.up.{u, 0} (k j)) (ULift.up.{u, 0} (l j)))
      = Matrix.single (ULift.up.{u, 0} c) (ULift.up.{u, 0} e) (1 : R₀ T)
          (ULift.up.{u, 0} k) (ULift.up.{u, 0} l) := by
  simp only [Matrix.single_apply, ULift.up.injEq, funext_iff, Finset.prod_ite_zero,
    Finset.mem_univ, true_implies, forall_and, Finset.prod_const_one]

/-- **A matrix unit of the algebra of size `d ^ m` is the tensor of matrix units of the algebra
of size `d`**: under the identification `natTensorPowFreeIso` of the `m`-fold tensor power of
`𝒪_S^d` with the free sheaf of modules on `Fin m → Fin d`, the `(c, e)` matrix unit of the big
algebra is the tensor over `j` of the `(c j, e j)` matrix units of the small one. -/
theorem conj_natTensorPowFreeIso_uncurry'_matIncl (T : Scheme.{u}) (d m : ℕ)
    (c e : Fin m → Fin d) :
    (natTensorPowFreeIso T d m).hom ≫
        MonoidalClosed.uncurry' (matIncl (S := T)
          (ULift.up.{u, 0} c, ULift.up.{u, 0} e)) ≫
        (natTensorPowFreeIso T d m).inv
      = natTensorPowFam m fun j => MonoidalClosed.uncurry' (matIncl (S := T)
          (ULift.up.{u, 0} (c j), ULift.up.{u, 0} (e j))) := by
  have key : ∀ (I : Type) [Fintype I] [DecidableEq I] (a b i j : I),
      freeEndMatrixEquiv T I (MonoidalClosed.uncurry' (matIncl (S := T)
        (ULift.up.{u, 0} a, ULift.up.{u, 0} b))) i j
      = Matrix.single (ULift.up.{u, 0} a) (ULift.up.{u, 0} b) (1 : R₀ T)
          (ULift.up.{u, 0} i) (ULift.up.{u, 0} j) := fun I _ _ a b i j ↦ by
    rw [← freeDualMatrix_eq_freeEndMatrixEquiv T I _ i j, freeDualMatrix_uncurry'_matIncl]
  rw [← Iso.eq_inv_comp, Iso.comp_inv_eq, Category.assoc]
  refine (freeEndMatrixEquiv T (Fin m → Fin d)).injective ?_
  funext k l
  rw [freeEndMatrixEquiv_natTensorPowFam T d m _ k l, key, Finset.prod_congr rfl
    fun j (_ : j ∈ Finset.univ) ↦ key (Fin d) (c j) (e j) (k j) (l j), prod_single_ulift]

end Stacks.EtaleCohomology.BrauerScheme

end

end
