module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedTensor
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.QuasiCoherentPullback
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedTensorExact
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedMonoidalUnitors

/-!
# Tensoring and derived pullback on `D_QCoh` are exact functors

Let `X` be a scheme. On `D_QCoh(𝒪_X)`, at the locally small model, the functor `K ↦ K ⊗ᴸ L`
commutes with the shift and is exact for every `L`, and for a morphism `f : X ⟶ Y` so is the
restricted derived pullback `Lf^*`, hence so is `K ↦ Lf^*K ⊗ᴸ M`. Each is the restriction of an
exact functor of the ambient derived categories to the triangulated subcategories `D_QCoh`.

## Main results

* `Stacks.Duality.commShift_quasiCoherentDerivedTensor_flip_obj` and
  `Stacks.Duality.isTriangulated_quasiCoherentDerivedTensor_flip_obj`: `- ⊗ᴸ L` on `D_QCoh(𝒪_X)`.
* `Stacks.Duality.commShift_quasiCoherentDerivedPullback_restrict` and
  `Stacks.Duality.isTriangulated_quasiCoherentDerivedPullback`: `Lf^*` on `D_QCoh`.
* `Stacks.Duality.isTriangulated_quasiCoherentDerivedPullback_comp_tensor`: `Lf^*(-) ⊗ᴸ M`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u

namespace Stacks.Duality

/-! ### Tensoring with a fixed object -/

section Tensor

variable (Z : Scheme.{u}) (L : quasiCoherentDerivedCategory Z)

/-- **`- ⊗ᴸ L` commutes with the shift on `D_QCoh(𝒪_Z)`**, as the restriction of the derived
tensor product of [Stacks, Tag 06YU], which commutes with the shift in each variable. -/
instance commShift_quasiCoherentDerivedTensor_flip_obj :
    ((quasiCoherentDerivedTensor Z).flip.obj L).CommShift ℤ :=
  letI : ((derivedTensor Z).flip.obj L.obj).CommShift ℤ :=
    (Stacks.Cohomology.TorAmplitude.derTensor Z.toRingedSpace).commShift_left L.obj
  Functor.CommShift.ofComp (quasiCoherentDerivedTensorFlipObjCompιIso Z L) ℤ

/-- **`- ⊗ᴸ L` is an exact functor on `D_QCoh(𝒪_Z)`**: the derived tensor product is exact in
each variable, and `D_QCoh(𝒪_Z)` is a triangulated subcategory of `D(𝒪_Z)`. -/
instance isTriangulated_quasiCoherentDerivedTensor_flip_obj :
    ((quasiCoherentDerivedTensor Z).flip.obj L).IsTriangulated := by
  let : ((derivedTensor Z).flip.obj L.obj).CommShift ℤ :=
    (Stacks.Cohomology.TorAmplitude.derTensor Z.toRingedSpace).commShift_left L.obj
  have : ((derivedTensor Z).flip.obj L.obj).IsTriangulated :=
    (Stacks.Cohomology.TorAmplitude.derTensor Z.toRingedSpace).exact_left L.obj
  have : NatTrans.CommShift (quasiCoherentDerivedTensorFlipObjCompιIso Z L).hom ℤ :=
    Functor.CommShift.ofComp_compatibility (quasiCoherentDerivedTensorFlipObjCompιIso Z L) ℤ
  exact (Functor.isTriangulated_iff_comp_right
    (quasiCoherentDerivedTensorFlipObjCompιIso Z L)).2 inferInstance

end Tensor

/-! ### Derived pullback -/

section Pullback

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (hpull : ∀ (K : quasiCoherentDerivedCategory Y) (i : ℤ),
    ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((derivedPullback f).obj K.obj)).IsQuasicoherent)

/-- **The restriction of `Lf^*` to `D_QCoh` commutes with the shift**: `Lf^*` does on `D(𝒪)`,
being left adjoint to `Rf_*`, and `D_QCoh` is stable under the shift. -/
instance commShift_quasiCoherentDerivedPullback_restrict :
    (quasiCoherentDerivedPullback f hpull).CommShift ℤ :=
  letI := (derivedAdjunction f).leftAdjointCommShift ℤ
  Functor.CommShift.ofComp (quasiCoherentDerivedPullbackCompιIso f hpull) ℤ

/-- **The restriction of `Lf^*` to `D_QCoh` is exact**: `Lf^*` is exact on `D(𝒪)`, being left
adjoint to the exact functor `Rf_*`, and `D_QCoh` is a triangulated subcategory on either side. -/
instance isTriangulated_quasiCoherentDerivedPullback :
    (quasiCoherentDerivedPullback f hpull).IsTriangulated := by
  let := (derivedAdjunction f).leftAdjointCommShift ℤ
  let := (derivedAdjunction f).commShift_of_rightAdjoint ℤ
  have : (derivedPullback f).IsTriangulated := (derivedAdjunction f).isTriangulated_leftAdjoint
  have : NatTrans.CommShift (quasiCoherentDerivedPullbackCompιIso f hpull).hom ℤ :=
    Functor.CommShift.ofComp_compatibility (quasiCoherentDerivedPullbackCompιIso f hpull) ℤ
  exact (Functor.isTriangulated_iff_comp_right (quasiCoherentDerivedPullbackCompιIso f hpull)).2
    inferInstance

/-- **`K ↦ Lf^*K ⊗ᴸ M` is exact** on `D_QCoh`, as a composite of exact functors. -/
instance isTriangulated_quasiCoherentDerivedPullback_comp_tensor
    (M : quasiCoherentDerivedCategory X) :
    (quasiCoherentDerivedPullback f hpull ⋙
      (quasiCoherentDerivedTensor X).flip.obj M).IsTriangulated :=
  Functor.IsTriangulated.instComp (F := quasiCoherentDerivedPullback f hpull)
    (G := (quasiCoherentDerivedTensor X).flip.obj M)

end Pullback

end Stacks.Duality

end
