module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.TensorPowerFreeMatrix
public import StacksFrontier.CategoryTheory.Monoidal.InternalEndTensorPoints

/-!
# The iterated Kronecker law for a family of endomorphisms

`Stacks.EtaleCohomology.BrauerScheme.freeEndMatrixEquiv_natTensorPowMap` reads the matrix of the
`j`-fold tensor power `f^{⊗ j}` of a single endomorphism of `𝒪_S^d` as the `j`-fold Kronecker
power of the matrix of `f`. The overlap step of [Stacks, Tag 0A2L] needs the same statement for a
tensor product of *different* endomorphisms, because the matrix units of the algebra of size
`d ^ d` are tensors of **varying** matrix units of the algebra of size `d`: the `(k, l)` matrix
unit over `Fin d → Fin d` is the tensor over `j` of the `(k j, l j)` matrix units over `Fin d`.

The proof is the induction of `freeEndMatrixEquiv_natTensorPowMap_apply` with the constant family
replaced by an arbitrary one: the step is the two-factor Kronecker law with reindexing,
`Stacks.EtaleCohomology.BrauerScheme.freeEndMatrixEquiv_tensorIso_reindex`, and
`Fin.prod_univ_castSucc` splits off the last factor, matching the way
`Stacks.EtaleCohomology.BrauerScheme.natTensorPowFam` adds its factors on the right.

## Main results

* `Stacks.EtaleCohomology.BrauerScheme.freeEndMatrixEquiv_natTensorPowFam`: **the matrix of a
  tensor product of a family of endomorphisms of `𝒪_S^d` is the entrywise product of their
  matrices**, under the identification `natTensorPowFreeIso` of the `m`-fold tensor power of
  `𝒪_S^d` with the free sheaf of modules on `Fin m → Fin d`.

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

/-- **THE ITERATED KRONECKER LAW FOR A FAMILY.** Under the identification `natTensorPowFreeIso`
of the `m`-fold tensor power of `𝒪_S^d` with the free sheaf of modules on `Fin m → Fin d`, the
matrix of the tensor product of a family `fam` of endomorphisms of `𝒪_S^d` has `(k, l)` entry the
product over `j` of the `(k j, l j)` entries of the matrices of the `fam j`. -/
theorem freeEndMatrixEquiv_natTensorPowFam (S : Scheme.{u}) (d : ℕ) :
    ∀ (m : ℕ)
      (fam : Fin m → (_root_.SheafOfModules.free (R := Tensor.ringSheaf S.sheaf)
        (ULift.{u, 0} (Fin d)) ⟶ _root_.SheafOfModules.free (R := Tensor.ringSheaf S.sheaf)
          (ULift.{u, 0} (Fin d)))) (k l : Fin m → Fin d),
      freeEndMatrixEquiv S (Fin m → Fin d)
          ((natTensorPowFreeIso S d m).inv ≫ natTensorPowFam m fam ≫
            (natTensorPowFreeIso S d m).hom) k l
        = ∏ j, freeEndMatrixEquiv S (Fin d) (fam j) (k j) (l j)
  | 0, fam, k, l => by
    obtain rfl : k = l := Subsingleton.elim _ _
    rw [natTensorPowFam_zero, Category.id_comp, Iso.inv_hom_id, freeEndMatrixEquiv_id,
      Matrix.one_apply_eq]
    simp
  | m + 1, fam, k, l => by
    have step : freeEndMatrixEquiv S (Fin (m + 1) → Fin d)
          ((natTensorPowFreeIso S d (m + 1)).inv ≫ natTensorPowFam (m + 1) fam ≫
            (natTensorPowFreeIso S d (m + 1)).hom) k l =
        freeEndMatrixEquiv S (Fin m → Fin d)
            ((natTensorPowFreeIso S d m).inv ≫ natTensorPowFam m (Fin.init fam) ≫
              (natTensorPowFreeIso S d m).hom) (Fin.init k) (Fin.init l) *
          freeEndMatrixEquiv S (Fin d) (fam (Fin.last m)) (k (Fin.last m)) (l (Fin.last m)) :=
      freeEndMatrixEquiv_tensorIso_reindex S (Fin m → Fin d) (Fin d) (Fin (m + 1) → Fin d)
        (finSnocEquiv m d) (natTensorPowFreeIso S d m) (natTensorPowFam m (Fin.init fam))
        (fam (Fin.last m)) k l
    rw [step, freeEndMatrixEquiv_natTensorPowFam S d m (Fin.init fam) (Fin.init k) (Fin.init l),
      Fin.prod_univ_castSucc]
    rfl

end Stacks.EtaleCohomology.BrauerScheme

end

end
