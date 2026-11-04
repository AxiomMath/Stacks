module

public import StacksFrontier.AlgebraicGeometry.PicardBaseChange.Injectivity
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleQuotients.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerConstraints

/-!
# Pullbacks of inverses of invertible modules

The pullback of the inverse `L^{⊗ -1}` of an invertible module is the inverse of the pullback
(`Stacks.Cube.nonempty_pullback_inv_iso`), and the inverse of a trivial module is trivial
(`Stacks.Cube.nonempty_inv_iso_unit`). Both follow because tensoring with an invertible module
is an equivalence.

## References

* [Stacks Project, Tag 01CR](https://stacks.math.columbia.edu/tag/01CR)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open Stacks.SheafOfModules.Invertible

universe u

namespace Stacks.Cube

variable {X Y : Scheme.{u}}

/-- Two modules whose tensor products with an invertible module are isomorphic are isomorphic. -/
theorem nonempty_iso_of_tensor (L : Y.Modules)
    [hL : AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.property L]
    (M M' : Y.Modules)
    (e : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨Y.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ Y.presheaf (forget₂ CommRingCat RingCat)
          Y.ringCatSheaf.property⟩).obj L).obj M ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨Y.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ Y.presheaf (forget₂ CommRingCat RingCat)
          Y.ringCatSheaf.property⟩).obj L).obj M') :
    Nonempty (M ≅ M') :=
  have : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Y.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ Y.presheaf (forget₂ CommRingCat RingCat)
        Y.ringCatSheaf.property⟩).obj L).IsEquivalence :=
    @Stacks.SheafOfModules.tensorLeftFunctor_isEquivalence _ _ _ Y.presheaf
      Y.ringCatSheaf.property _ _ L
      (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL)
  ⟨(Functor.asEquivalence
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Y.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ Y.presheaf (forget₂ CommRingCat RingCat)
        Y.ringCatSheaf.property⟩).obj L)).fullyFaithfulFunctor.preimageIso e⟩

/-- **The pullback of the inverse is the inverse of the pullback.** -/
theorem nonempty_pullback_inv_iso (p : Y ⟶ X) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L] :
    haveI : AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.property
        ((Scheme.Modules.pullback p).obj L) :=
      (Stacks.ProjectiveBundleQuotients.isInvertible_pullback_obj p L).toAlgebraicGeometry
    Nonempty ((Scheme.Modules.pullback p).obj (tensorPowerModule L (-1)) ≅
      tensorPowerModule ((Scheme.Modules.pullback p).obj L) (-1)) := by
  have : AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.property
      ((Scheme.Modules.pullback p).obj L) :=
    (Stacks.ProjectiveBundleQuotients.isInvertible_pullback_obj p L).toAlgebraicGeometry
  exact nonempty_iso_of_tensor ((Scheme.Modules.pullback p).obj L) _ _
    (Stacks.AlgebraicGeometry.PicardBaseChange.pullbackMulNegOneIso p L ≪≫
      (mulNegOneIso Y.presheaf Y.ringCatSheaf.property ((Scheme.Modules.pullback p).obj L)).symm)

/-- **The inverse of a trivial invertible module is trivial.** -/
theorem nonempty_inv_iso_unit (L : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.property L]
    (e : SheafOfModules.unit Y.ringCatSheaf ≅ L) :
    Nonempty (SheafOfModules.unit Y.ringCatSheaf ≅ tensorPowerModule L (-1)) :=
  nonempty_iso_of_tensor L _ _
    (Stacks.SheafOfModules.tensorLeftFunctorObjUnitIso Y.presheaf Y.ringCatSheaf.property L ≪≫
      e.symm ≪≫ (mulNegOneIso Y.presheaf Y.ringCatSheaf.property L).symm)

end Stacks.Cube

end
