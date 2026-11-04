module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.StructureSheafStalk
public import StacksFrontier.AlgebraicGeometry.Flatness.WeaklyAssociatedTensorPullback

/-!
# Tensoring with the pullback of the structure sheaf of the base

For a morphism `f : X ⟶ S` and an `𝒪_X`-module `F`, the module `F ⊗_{𝒪_X} f^* 𝒪_S` has the
same stalks as `F`: the stalk of `f^* 𝒪_S` at `x` is `𝒪_{X, x} ⊗_{𝒪_{S, f x}} 𝒪_{S, f x}`, that
is `𝒪_{X, x}`, and tensoring `F_x` with it changes nothing.

## Main results

* `AlgebraicGeometry.isWeaklyAssociatedPoint_tensorPullback_structureSheaf_iff`: a point is
  weakly associated to `F ⊗_{𝒪_X} f^* 𝒪_S` exactly when it is weakly associated to `F`.

## Implementation notes

Only the consequence for weakly associated points is recorded, which is all that the proof of
Stacks tag 05PD needs, and it is obtained from a linear equivalence of stalks rather than from
an isomorphism of sheaves: the stalk computations
`Stacks.Divisors.exists_tensorStalkLinearEquiv` and
`RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv` are available as data only
up to a `Nonempty`, and the predicate on a point only sees the stalk.

The assembly of the four equivalences is the one of
`Stacks.Divisors.mem_relativeAssassin_of_isWeaklyAssociatedPoint_tensorPullback`, with the
stalk of the structure sheaf of the base identified with the local ring by
`AlgebraicGeometry.structureSheafStalkLinearEquiv` and the two tensor factors cancelled by
`TensorProduct.AlgebraTensorModule.cancelBaseChange` and
`TensorProduct.AlgebraTensorModule.rid`.

## References

* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 05PD](https://stacks.math.columbia.edu/tag/05PD)
-/

@[expose] public section

open CategoryTheory TensorProduct Stacks.Divisors

universe u

namespace AlgebraicGeometry

/-- A point of `X` is weakly associated to `F ⊗_{𝒪_X} f^* 𝒪_S` exactly when it is weakly
associated to `F`: the two modules have linearly equivalent stalks at every point. -/
theorem isWeaklyAssociatedPoint_tensorPullback_structureSheaf_iff
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (x : X) :
    IsWeaklyAssociatedPoint
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((X.toLocallyRingedSpace.toRingedSpace)).presheaf,
              ((X.toLocallyRingedSpace.toRingedSpace)).IsSheaf⟩).obj (F)).obj
          (((Scheme.Modules.pullback f).obj (structureSheafModule S))))) x ↔
      IsWeaklyAssociatedPoint F x := by
  classical
  let R := S.presheaf.stalk (f x)
  let B := X.presheaf.stalk x
  let φ : R →+* B := (f.stalkMap x).hom
  let : Algebra R B := φ.toAlgebra
  let : IsLocalHom φ := f.toLRSHom.prop x
  let N := TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x
  let M := TopCat.Presheaf.stalk (C := Ab.{u}) (structureSheafModule S).val.presheaf (f x)
  let : Module R N := Module.compHom N φ
  have : IsScalarTower R B N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let P := (Scheme.Modules.pullback f).obj (structureSheafModule S)
  let tens := (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((X.toLocallyRingedSpace.toRingedSpace)).presheaf,
        ((X.toLocallyRingedSpace.toRingedSpace)).IsSheaf⟩).obj (F)).obj (P))
  obtain ⟨eTensor⟩ := exists_tensorStalkLinearEquiv F P x
  let ePull : TopCat.Presheaf.stalk (C := Ab.{u}) P.val.presheaf x ≃ₗ[B]
      TensorProduct R B M := Classical.choose
    (RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv
      f.toLRSHom.toShHom (structureSheafModule S) x)
  let eM : M ≃ₗ[R] R := structureSheafStalkLinearEquiv S (f x)
  let : Module B (TopCat.Presheaf.stalk (C := Ab.{u}) tens.val.presheaf x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) tens.val x
  exact LinearEquiv.isWeaklyAssociatedPrime_iff
    (eTensor.trans ((ePull.lTensor N).trans
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange R B B N M).trans
        ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B N) eM).trans
          (TensorProduct.AlgebraTensorModule.rid R B N))))) _

end AlgebraicGeometry

end
