module

public import StacksFrontier.RingTheory.Dualizing.BaseRingAbsoluteTensor
public import StacksFrontier.Algebra.DifferentialGraded.Module.AbsoluteTensorModuleLeftFunctor

/-!
# Tensoring over the base ring in degree zero, naturally

`Dualizing.baseAbsBalanceIso` identifies the relative tensor product `K ⊗_R M` of Tag 09LM with
the absolute tensor product of the underlying complexes, for a right differential graded module
`K` over the base ring placed in degree zero and a differential graded `(R, B)`-bimodule `M`.
This file upgrades that identification to an isomorphism of *functors* of `K`:

`DifferentialGraded.Bimodule.tensorCompFunctor M ≅
  DifferentialGradedModule.absoluteTensorLeftFunctor M.rightModule`.

Both sides send a homomorphism to the map induced on pure tensors, so the naturality square is
checked on a pure tensor through `DifferentialGraded.Bimodule.tensorObj_hom_ext`.

## Main definitions

* `Dualizing.baseAbsBalanceNatIso`: **the relative tensor product over the base ring in degree
  zero is the absolute tensor product, naturally in the left variable.**
* `Dualizing.baseBimoduleAbsBalanceNatIso`: the same isomorphism with the second argument a
  plain right differential graded module rather than a bimodule.

## Main results

* `Dualizing.baseAbsForward_naturality`: the naturality square of
  `Dualizing.baseAbsForward`.

## References

* [Stacks Project, Tag 09LM](https://stacks.math.columbia.edu/tag/09LM) is the relative tensor
  product with a differential graded bimodule.
-/

@[expose] public noncomputable section

open CategoryTheory DifferentialGraded DifferentialGradedModule
open scoped TensorProduct DirectSum

universe u

namespace Dualizing

attribute [local instance] DifferentialGradedModule.absModRightModule
  DifferentialGradedModule.absModRightScalarTower
  DifferentialGradedModule.absModDecomposition

variable {R : Type u} [CommRing R] (B : DifferentialGradedAlgebra.{u, u} R)

/-- **Naturality of the identification.** Both the relative and the absolute tensor product send
a homomorphism `φ : K ⟶ K'` to the map induced on pure tensors, so the identification of the two
commutes with them. -/
theorem baseAbsForward_naturality (M : Bimodule (baseAlgebra R) B)
    {K K' : DifferentialGradedModule.{u, u, u} (baseAlgebra R)} (φ : K ⟶ K') :
    (Bimodule.tensorCompFunctor M).map φ ≫ baseAbsForward B K' M =
      baseAbsForward B K M ≫ absModLeftMap φ M.rightModule := by
  refine Bimodule.tensorObj_hom_ext M K _ _ fun x y => ?_
  have hleft : ((Bimodule.tensorCompFunctor M).map φ).toFun
      ((Bimodule.tensorPure M K).toLinearMap x y) =
      (Bimodule.tensorPure M K').toLinearMap (φ.toFun x) y :=
    Bimodule.tensorCompFunctor_map_pure M φ x y
  have hK' : (baseAbsForward B K' M).toFun
      ((Bimodule.tensorPure M K').toLinearMap (φ.toFun x) y) =
      (φ.toFun x ⊗ₜ[R] y : K'.M ⊗[R] M.rightModule.M) :=
    baseAbsForward_pure B K' M (φ.toFun x) y
  have hK : (baseAbsForward B K M).toFun ((Bimodule.tensorPure M K).toLinearMap x y) =
      (x ⊗ₜ[R] y : K.M ⊗[R] M.rightModule.M) :=
    baseAbsForward_pure B K M x y
  change (baseAbsForward B K' M).toFun
      (((Bimodule.tensorCompFunctor M).map φ).toFun
        ((Bimodule.tensorPure M K).toLinearMap x y)) =
    (absModLeftMap φ M.rightModule).toFun
      ((baseAbsForward B K M).toFun ((Bimodule.tensorPure M K).toLinearMap x y))
  rw [hleft, hK', hK, absModLeftMap_tmul]

/-- **The relative tensor product over the base ring in degree zero is the absolute tensor
product, naturally in the left variable.** For a differential graded `(R, B)`-bimodule `M`, the
tensor functor of Tag 09LM on right differential graded modules over the base ring placed in
degree zero is the absolute tensor product with the underlying right differential graded
`B`-module of `M`. -/
def baseAbsBalanceNatIso (M : Bimodule (baseAlgebra R) B) :
    Bimodule.tensorCompFunctor M ≅
      absoluteTensorLeftFunctor (A := baseAlgebra R) M.rightModule :=
  NatIso.ofComponents (fun K => baseAbsBalanceIso B K M)
    (fun φ => baseAbsForward_naturality B M φ)

/-- The component of `Dualizing.baseAbsBalanceNatIso` at `K` is `Dualizing.baseAbsForward`. -/
@[simp]
theorem baseAbsBalanceNatIso_hom_app (M : Bimodule (baseAlgebra R) B)
    (K : DifferentialGradedModule.{u, u, u} (baseAlgebra R)) :
    (baseAbsBalanceNatIso B M).hom.app K = baseAbsForward B K M := rfl

/-- The component of the inverse of `Dualizing.baseAbsBalanceNatIso` at `K` is
`Dualizing.baseAbsInverse`. -/
@[simp]
theorem baseAbsBalanceNatIso_inv_app (M : Bimodule (baseAlgebra R) B)
    (K : DifferentialGradedModule.{u, u, u} (baseAlgebra R)) :
    (baseAbsBalanceNatIso B M).inv.app K = baseAbsInverse B K M := rfl

/-- **The tensor functor of Tag 09LM at a right differential graded `B`-module read over the
base ring in degree zero is the absolute tensor product with that module.** This is
`Dualizing.baseAbsBalanceNatIso` at `Dualizing.baseBimodule`; by
`Dualizing.bimodule_eq_baseBimodule` every bimodule over the base ring is of that form, so no
generality is lost. -/
def baseBimoduleAbsBalanceNatIso (M : DifferentialGradedModule.{u, u, u} B) :
    Bimodule.tensorCompFunctor (baseBimodule B M) ≅
      absoluteTensorLeftFunctor (A := baseAlgebra R) M :=
  baseAbsBalanceNatIso B (baseBimodule B M)

end Dualizing

end
