module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineAssociatedTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedInvertibleQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RepresentedAffinePushforwardPerfect
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.Invertible

/-!
# Invertible associated modules on an affine algebraic space

Let `U` be an object of the big fppf site whose underlying scheme is affine, with ring of global
functions `R`. An `R`-module `N` is invertible exactly when its associated module `N^~` on the
small étale site of the algebraic space `yoneda.obj U` is invertible in the sense of Stacks 01CS.

## Main results

* `AlgebraicGeometry.Space.isInvertibleModule_representedAffineAssociated_iff`: `N^~` is
  invertible exactly when `N` is.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]

/-- **An associated module on an affine algebraic space is invertible exactly when the module
is.** -/
theorem isInvertibleModule_representedAffineAssociated_iff
    (N : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    IsInvertibleModule (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS)
        ((representedAffineAssociated B S hS U).obj N) ↔
      Module.Invertible Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) N := by
  let Z : AlgebraicSpaces B S hS := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩
  let R := Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
  have h₁ : HasWeakSheafify (SmallEtale.topology B S hS (yoneda.obj U)) AddCommGrpCat.{u} :=
    inferInstance
  have h₂ : (SmallEtale.topology B S hS (yoneda.obj U)).WEqualsLocallyBijective
      AddCommGrpCat.{u} := inferInstance
  constructor
  · intro h
    obtain ⟨P, ⟨e⟩⟩ := (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit _).1 h
    have hP : IsInvertibleModule Z P :=
      (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit _).2
        ⟨_, ⟨Stacks.SheafOfModules.Invertible.tensorLeftFunctorSwap _ _ _ _ ≪≫ e⟩⟩
    have hPq := isQuasicoherentOnSite_of_isInvertibleModule Z P hP
    have := isIso_representedAffineAssociatedAdjunction_counit_app B S hS P hPq
    let c := asIso ((representedAffineAssociatedAdjunction B S hS U).counit.app P)
    let Q := (representedAffineSections B S hS U).obj P
    let e' : (representedAffineAssociated B S hS U).obj (MonoidalCategory.tensorObj N Q) ≅
        (representedAffineAssociated B S hS U).obj (ModuleCat.of R R) :=
      (representedAffineAssociatedTensorIso B S hS U Q).app N ≪≫
        ((representedAffineTensor B S hS U).obj
          ((representedAffineAssociated B S hS U).obj N)).mapIso c ≪≫ e ≪≫
        (representedAffineAssociatedUnitIso B S hS U).symm
    let e'' := (representedAffineAssociatedFullyFaithful B S hS U).preimageIso e'
    exact Module.Invertible.left (M := N) (N := Q) e''.toLinearEquiv
  · intro h
    let D := ModuleCat.of R (Module.Dual R N)
    let ε : MonoidalCategory.tensorObj N D ≅ ModuleCat.of R R :=
      ((TensorProduct.comm R N (Module.Dual R N)).trans
        (Module.Invertible.linearEquiv R N)).toModuleIso
    exact (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit _).2
      ⟨(representedAffineAssociated B S hS U).obj D,
        ⟨((representedAffineAssociatedTensorIso B S hS U D).app N).symm ≪≫
          (representedAffineAssociated B S hS U).mapIso ε ≪≫
          representedAffineAssociatedUnitIso B S hS U⟩⟩

end AlgebraicGeometry.Space
