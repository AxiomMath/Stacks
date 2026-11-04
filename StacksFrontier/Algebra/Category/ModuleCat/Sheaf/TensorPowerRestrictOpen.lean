module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafOverSlice
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.LocalizationComparison
public import StacksFrontier.Topology.Sheaves.Modules.RingSheafIsStructureSheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tensor powers commute with restriction to an open of a ringed space

Let `X` be a ringed space, `U ⊆ X` open, and `L` a sheaf of `𝒪_X`-modules invertible on `X` and
on `U`. Then

`(L^{⊗ n})|_U ≅ (L|_U)^{⊗ n}` for every `n : ℤ`,

where restriction is `Stacks.Cohomology.HigherDirectImage.moduleRestriction` and the tensor power
is `Stacks.SheafOfModules.TensorPower.tensorPower`, the image of the structure sheaf under the
`n`th power of the autoequivalence `- ⊗ L`.

## Main results

* `Stacks.SheafOfModules.TensorPower.ringedSpaceIsSheaf`: the structure sheaf of a ringed space,
  as a presheaf of rings, is a sheaf.
* `Stacks.SheafOfModules.TensorPower.openImageFunctor_isCocontinuous`: the open-image functor
  `Opens U ⥤ Opens X` is cocontinuous.
* `Stacks.SheafOfModules.TensorPower.moduleRestriction_eq_whiskerRestriction`: restriction to an
  open is restriction along the open-image functor of sites.
* `Stacks.SheafOfModules.TensorPower.restrictTensorSheafIso`: `(M ⊗ L)|_U ≅ M|_U ⊗ L|_U`.
* `Stacks.SheafOfModules.TensorPower.restrictTensorSheafIso_naturality`: that isomorphism is
  natural in both variables.
* `Stacks.SheafOfModules.TensorPower.restrictTensorPowerIso`: `(L^{⊗ n})|_U ≅ (L|_U)^{⊗ n}`.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.HigherDirectImage

universe u

namespace Stacks.SheafOfModules.TensorPower

/-- The structure presheaf of a ringed space, as a presheaf of not-necessarily-commutative rings,
is a sheaf. -/
theorem ringedSpaceIsSheaf (X : RingedSpace.{u, u}) :
    Presheaf.IsSheaf (Opens.grothendieckTopology (X : TopCat))
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf X.presheaf) :=
  (_root_.structureSheaf X.sheaf).property

/-- The open-image functor `Opens U ⥤ Opens X` of an open subset is continuous. -/
@[sga "4 III 1.9.2"]
instance openImageFunctor_isContinuous {Z : TopCat.{u}} (U : Opens Z) :
    (U.isOpenEmbedding.functor).IsContinuous
      (Opens.grothendieckTopology ((Opens.toTopCat Z).obj U))
      (Opens.grothendieckTopology Z) :=
  U.isOpenEmbedding.functor_isContinuous

/-- The open-image functor `Opens U ⥤ Opens X` of an open subset is cocontinuous. -/
instance openImageFunctor_isCocontinuous {Z : TopCat.{u}} (U : Opens Z) :
    (U.isOpenEmbedding.functor).IsCocontinuous
      (Opens.grothendieckTopology ((Opens.toTopCat Z).obj U))
      (Opens.grothendieckTopology Z) :=
  (IsOpenMap.adjunction U.isOpenEmbedding.isOpenMap).isCocontinuous_iff_coverPreserving _ _
    |>.mpr (coverPreserving_opens_map _)

variable (X : RingedSpace.{u, u}) (U : Opens X.carrier)

/-- Restriction of sheaves of modules to an open is restriction along the open-image functor of
sites. -/
theorem moduleRestriction_eq_whiskerRestriction :
    moduleRestriction X U =
      whiskerRestriction X.presheaf (ringedSpaceIsSheaf X) U.isOpenEmbedding.functor :=
  rfl

/-- The isomorphism `(M ⊗ L)|_U ≅ M|_U ⊗ L|_U` of sheaves of modules on a ringed space. -/
noncomputable def restrictTensorSheafIso
    (M L : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    (moduleRestriction X U).obj (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.presheaf, X.IsSheaf⟩).obj M).obj L) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(restrictToOpen X U).presheaf, (restrictToOpen X U).IsSheaf⟩).obj
          ((moduleRestriction X U).obj M)).obj ((moduleRestriction X U).obj L) :=
  whiskerTensorSheafIso X.presheaf (ringedSpaceIsSheaf X) U.isOpenEmbedding.functor M L

/-- The isomorphism `(M ⊗ L)|_U ≅ M|_U ⊗ L|_U` is natural in both variables: it carries the
restriction of the morphism induced by `f : M ⟶ M'` and `g : L ⟶ L'` to the morphism induced by
their restrictions. -/
theorem restrictTensorSheafIso_naturality
    {M M' L L' : _root_.SheafOfModules.{u} (structureSheafRing X)} (f : M ⟶ M') (g : L ⟶ L') :
    (moduleRestriction X U).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨X.presheaf, X.IsSheaf⟩).map (X := M) (Y := M') f).app L ≫
            ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              ⟨X.presheaf, X.IsSheaf⟩).obj M').map (X := L) (Y := L') g) ≫
        (restrictTensorSheafIso X U M' L').hom =
      (restrictTensorSheafIso X U M L).hom ≫
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨(restrictToOpen X U).presheaf, (restrictToOpen X U).IsSheaf⟩).map
            (X := (moduleRestriction X U).obj M) (Y := (moduleRestriction X U).obj M')
            ((moduleRestriction X U).map f)).app ((moduleRestriction X U).obj L) ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨(restrictToOpen X U).presheaf, (restrictToOpen X U).IsSheaf⟩).obj
              ((moduleRestriction X U).obj M')).map
                (X := (moduleRestriction X U).obj L) (Y := (moduleRestriction X U).obj L')
                ((moduleRestriction X U).map g)) :=
  whiskerTensorSheafIso_naturality X.presheaf (ringedSpaceIsSheaf X) U.isOpenEmbedding.functor f g

variable (L : _root_.SheafOfModules.{u} (structureSheafRing X))
  [((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    ⟨X.presheaf, X.IsSheaf⟩).flip.obj L).IsEquivalence]
  [((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    ⟨(restrictToOpen X U).presheaf, (restrictToOpen X U).IsSheaf⟩).flip.obj
      ((moduleRestriction X U).obj L)).IsEquivalence]

/-- For a sheaf of modules `L` invertible on a ringed space `X` and with restriction invertible on
`U`, the isomorphism `(L^{⊗ n})|_U ≅ (L|_U)^{⊗ n}` for every integer `n`. -/
noncomputable def restrictTensorPowerIso (n : ℤ) :
    (moduleRestriction X U).obj (tensorPower X.presheaf (ringedSpaceIsSheaf X) L n) ≅
      tensorPower (restrictToOpen X U).presheaf (ringedSpaceIsSheaf (restrictToOpen X U))
        ((moduleRestriction X U).obj L) n := by
  letI : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (J := Opens.grothendieckTopology ((Opens.toTopCat (X : TopCat)).obj U))
      ⟨(U.isOpenEmbedding.functor.op ⋙ X.presheaf),
        Presheaf.isSheaf_of_isSheaf_comp _ (U.isOpenEmbedding.functor.op ⋙ X.presheaf)
          (forget₂ CommRingCat RingCat)
          (whiskerStructureIsSheaf
            (J' := Opens.grothendieckTopology ((Opens.toTopCat (X : TopCat)).obj U))
            X.presheaf (ringedSpaceIsSheaf X) U.isOpenEmbedding.functor)⟩).flip.obj
      ((whiskerRestriction X.presheaf (ringedSpaceIsSheaf X)
        U.isOpenEmbedding.functor).obj L)).IsEquivalence :=
    inferInstanceAs ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨(restrictToOpen X U).presheaf, (restrictToOpen X U).IsSheaf⟩).flip.obj
        ((moduleRestriction X U).obj L)).IsEquivalence
  exact whiskerTensorPowerIso X.presheaf (ringedSpaceIsSheaf X) U.isOpenEmbedding.functor L n

end Stacks.SheafOfModules.TensorPower
