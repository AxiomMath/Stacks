module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedTensorExact
public import StacksFrontier.CategoryTheory.Monoidal.ComparisonUnitCommShift
public import StacksFrontier.CategoryTheory.Triangulated.ConnectingMorphismNatTrans

/-!
# The derived tensor product on `D_QCoh(𝒪_X)` acts on morphisms compatibly with the shift

Let `X` be a scheme and `g : M ⟶ M'` a morphism of `D_QCoh(𝒪_X)`. The morphism of functors
`K ↦ K ⊗ᴸ g : (- ⊗ᴸ M) ⟶ (- ⊗ᴸ M')` commutes with the shift, for the commutations of
`- ⊗ᴸ M` and `- ⊗ᴸ M'` with the shift of
`Stacks.Duality.commShift_quasiCoherentDerivedTensorFlipObj`. On `D(𝒪_X)` this is the
`commShift_flip_map` field of the two-variable shift structure `commShift₂` of the derived tensor
product of [Stacks, Tag 06YU], and it passes to `D_QCoh` along the faithful inclusion.

## Main results

* `Stacks.Duality.commShift_quasiCoherentDerivedTensor_flip_map` — the statement for the
  bifunctor `Stacks.Duality.quasiCoherentDerivedTensor X`.
* `Stacks.Duality.commShift_tensorRightMap_quasiCoherentDerivedMonoidal` — the same for the
  monoidal structure `Stacks.Duality.quasiCoherentDerivedMonoidal X`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory

universe u

namespace Stacks.Duality

variable (X : Scheme.{u})

/-- **Tensoring a morphism in the second variable commutes with the shift on `D_QCoh(𝒪_X)`.**
For `g : M ⟶ M'` the morphism of functors `(- ⊗ᴸ M) ⟶ (- ⊗ᴸ M')` is compatible with the
commutations of the two functors with the shift. -/
theorem commShift_quasiCoherentDerivedTensor_flip_map {M M' : quasiCoherentDerivedCategory X}
    (g : M ⟶ M') :
    NatTrans.CommShift ((quasiCoherentDerivedTensor X).flip.map g) ℤ := by
  let := commShiftDerivedTensorFlipObj X M.obj
  let := commShiftDerivedTensorFlipObj X M'.obj
  have hσ : NatTrans.CommShift ((derivedTensor X).flip.map g.hom) ℤ :=
    (Stacks.Cohomology.TorAmplitude.derTensor X.toRingedSpace).commShift₂.commShift_flip_map
      g.hom
  refine Stacks.Triangulated.natTransCommShift_of_whiskerRight_eq ℤ
    (DerivedCategoryB.derivedCategoryB (A := X.Modules)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι
    ((quasiCoherentDerivedTensor X).flip.map g) (quasiCoherentDerivedTensorFlipObjCompιIso X M)
    (quasiCoherentDerivedTensorFlipObjCompιIso X M')
    (Functor.whiskerLeft _ ((derivedTensor X).flip.map g.hom))
    (Functor.CommShift.ofComp_compatibility _ _) (Functor.CommShift.ofComp_compatibility _ _)
    inferInstance ?_
  ext K
  simp only [quasiCoherentDerivedTensorFlipObjCompιIso, Functor.whiskerRight_app,
    Functor.flip_map_app, NatTrans.comp_app, Functor.whiskerLeft_app, ObjectProperty.ι_map,
    quasiCoherentDerivedTensor_obj_map_hom]
  exact ((Category.id_comp _).trans (Category.comp_id _)).symm

/-- **Tensoring a morphism in the second variable commutes with the shift**, for the monoidal
structure `Stacks.Duality.quasiCoherentDerivedMonoidal X` on `D_QCoh(𝒪_X)`. -/
instance commShift_tensorRightMap_quasiCoherentDerivedMonoidal
    {M M' : quasiCoherentDerivedCategory X} (g : M ⟶ M') :
    NatTrans.CommShift
      (@MonoidalProjectionFormula.tensorRightMap _ _ (quasiCoherentDerivedMonoidal X) M M' g)
      ℤ :=
  commShift_quasiCoherentDerivedTensor_flip_map X g

end Stacks.Duality

end
