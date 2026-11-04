module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.StandardModel
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.DerivedStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingModule

/-!
# The relative dualizing complex `a(𝒪_Y)` at the standard model

Let `f : X ⟶ Y` be a morphism of quasi-compact and quasi-separated schemes and let `a` be the
right adjoint of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` of [Stacks, Tag 0A9E]. The object
`ω_{X/Y} = a(𝒪_Y)` is the relative dualizing complex of [Stacks, Remark 0B6S] when `f` is proper,
flat and of finite presentation.

This file fixes the object at the standard model `HasDerivedCategory.standard` of the derived
categories, the model at which the derived internal Hom, the duals of perfect objects and the
relative perfectness of [Stacks, Tag 0DI0] used in [Stacks, Tag 0E4L] are available; the right
adjoint there is `Stacks.Duality.StandardModel.isLeftAdjoint_quasiCoherentDerivedPushforward`.

## Main definitions

* `Stacks.Duality.StandardModel.structureSheaf` — `𝒪_Y` in degree zero, in `D_QCoh(𝒪_Y)`.
* `Stacks.Duality.StandardModel.relativeDualizingComplex` — `a(𝒪_Y)`, in `D_QCoh(𝒪_X)`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Duality.StandardModel

attribute [local instance 10000] HasDerivedCategory.standard

/-- `𝒪_Y` in degree zero, as an object of `D_QCoh(𝒪_Y)` at the standard model. -/
def structureSheaf (Y : Scheme.{u}) : quasiCoherentDerivedCategory Y :=
  ⟨(DerivedCategory.singleFunctor Y.Modules 0).obj (SheafOfModules.unit Y.ringCatSheaf),
    DerivedPushforward.derivedCategoryB_singleFunctor_obj _
      (inferInstance : (SheafOfModules.unit Y.ringCatSheaf : Y.Modules).IsQuasicoherent)⟩

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [CompactSpace X] [QuasiSeparatedSpace X]
  [CompactSpace Y] [QuasiSeparatedSpace Y]

/-- **The relative dualizing complex `ω_{X/Y} = a(𝒪_Y)`** of [Stacks, Remark 0B6S], at the
standard model: the value at `𝒪_Y` of the right adjoint `a` of
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` ([Stacks, Tag 0A9E]). -/
def relativeDualizingComplex : quasiCoherentDerivedCategory X :=
  (twistedInverseImage f (isQuasicoherent_homology_derivedPushforward f)).obj (structureSheaf Y)

/-- The defining adjunction `Hom(K, ω_{X/Y}) ≃ Hom(Rf_*K, 𝒪_Y)` for `K ∈ D_QCoh(𝒪_X)`. -/
def relativeDualizingComplexHomEquiv (K : quasiCoherentDerivedCategory X) :
    (K ⟶ relativeDualizingComplex f) ≃
      ((quasiCoherentDerivedPushforward f (isQuasicoherent_homology_derivedPushforward f)).obj K ⟶
        structureSheaf Y) :=
  ((twistedInverseImageAdjunction f (isQuasicoherent_homology_derivedPushforward f)).homEquiv
    K (structureSheaf Y)).symm

end Stacks.Duality.StandardModel

end
