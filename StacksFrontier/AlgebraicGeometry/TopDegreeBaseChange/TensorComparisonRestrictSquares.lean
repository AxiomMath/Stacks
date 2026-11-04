module

public import StacksFrontier.AlgebraicGeometry.AffinePushforward.BaseChange
public import StacksFrontier.AlgebraicGeometry.Ample.DescentStep
public import StacksFrontier.AlgebraicGeometry.ProjectionFormulaAffine.IsIso0FZE
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SchemeRestriction
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TensorComparisonFunctor
public import StacksFrontier.Deformation.RingedSpaceThickening.ExtensionActionNaturality

/-!
# The two functors of Tag 0EX3 (b) commute with restriction to an open of the base

Conclusion (b) of [Stacks, Tag 0EX3] compares the two functors

> `G ↦ R^n f_* F ⊗_{𝒪_Y} G`  and  `G ↦ R^n f_*(F ⊗_{𝒪_X} f^* G)`

of the module on the base.  This file proves that each of them commutes with restriction to an
open `V` of the base, as an isomorphism of functors — so naturally in the module on the base, not
only object by object:

`(R^n f_* F ⊗ G)|_V  ≅  R^n (f ∣_V)_* (F|_{f⁻¹V}) ⊗ G|_V`

and

`(R^n f_*(F ⊗ f^* G))|_V  ≅  R^n (f ∣_V)_*(F|_{f⁻¹V} ⊗ (f ∣_V)^* G|_V)`.

Three identifications supply the three factors:

* the sheafified tensor product commutes with inverse image, [Stacks, Tag 01CD]
  (`Stacks.RingedSpace.comparisonBifunctorIso`, a morphism of bifunctors);
* the higher direct image commutes with restriction, [Stacks, Tag 01E5]
  (`Stacks.AlgebraicGeometry.SchemeHigherDirectImage.rightDerivedPlusRestrictIso`, functorial);
* the inverse image commutes with restriction
  (`Stacks.AlgebraicGeometry.AffinePushforward.pullbackRestrictIso`, functorial).

## Main definitions

All of the following live in the namespace `Stacks.AlgebraicGeometry.TopDegreeBaseChange`.

* `restrictTensorLeftFunctorIso`: **restriction to an open subscheme commutes with tensoring by
  a fixed module**, as an isomorphism of functors.
* `sourceRestrictIso`: **the source functor of conclusion (b) commutes with restriction to an
  open of the base.**
* `targetRestrictIso`: **the target functor of conclusion (b) commutes with restriction to an
  open of the base.**

## Implementation notes

*Why [Stacks, Tag 01CD] with the first factor fixed is taken apart here.*  The isomorphism
`AlgebraicGeometry.pullbackTensorLeftIso` is that statement already, but the module carrying it
brings a second `HasDerivedCategory` instance into scope, and under that instance
`CategoryTheory.Functor.rightDerivedPlus` is a different functor from the one
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.topDirectImage` is built from — the two squares
below would then not be about the higher direct images of conclusion (b) at all.  So the
comparison of the tag is fixed at its first argument here instead, which is one application of
`AlgebraicGeometry.RingedSpaceThickening.comparisonBifunctorIso_naturality_right`.

*Why restriction and not inverse image.*  The locality criterion
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.isIso_higherDirectImageTensorMap_of_isIso_restrict`
is phrased with `AlgebraicGeometry.Scheme.Modules.restrictFunctor`, and so are [Stacks, Tag 01E5]
and the inverse-image comparison above;
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` carries the tensor factor over
from the inverse image, which is the vocabulary Tag 01CD is available in.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.AlgebraicGeometry.SchemeHigherDirectImage
open Stacks.AlgebraicGeometry.AffinePushforward

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

noncomputable section

attribute [local instance] HasDerivedCategory.standard

/-! ### Restriction commutes with tensoring by a fixed module -/

variable {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] (A : Y.Modules)

/-- **Restriction to an open subscheme commutes with tensoring by a fixed module**, as an
isomorphism of functors: `(A ⊗ -)|_X ≅ A|_X ⊗ (-)|_X`.

Restriction is inverse image (`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`),
for which the statement is [Stacks, Tag 01CD] with the first tensor factor held fixed: the
comparison of that tag is a morphism of bifunctors, so fixing the first factor leaves a
transformation natural in the second, invertible because the comparison is. -/
def restrictTensorLeftFunctorIso :
    (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩).obj A ⋙
        Scheme.Modules.restrictFunctor j ≅
      Scheme.Modules.restrictFunctor j ⋙
        (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj
          ((Scheme.Modules.restrictFunctor j).obj A) :=
  Functor.isoWhiskerLeft
      ((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩).obj A)
      (Scheme.Modules.restrictFunctorIsoPullback j) ≪≫
    (NatIso.ofComponents
        (fun N => (Stacks.RingedSpace.comparisonBifunctorIso j.toLRSHom.toShHom).app (A, N))
        (fun ψ => by
          refine Eq.trans ?_
            ((AlgebraicGeometry.RingedSpaceThickening.comparisonBifunctorIso_naturality_right
              j.toLRSHom.toShHom A ψ).trans ?_)
          · exact congrArg (fun k => (Scheme.Modules.pullback j).map k ≫ _)
              ((Stacks.SheafOfModules.Tensor.sheafTensor_obj_map _ A ψ).trans
                (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map _ (𝟙 A) ψ).symm)
          · exact congrArg (fun k => _ ≫ k)
              ((Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map _ _ _).trans
                (Stacks.SheafOfModules.Tensor.sheafTensor_obj_map _ _ _).symm)) :
      (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩).obj A ⋙
          Scheme.Modules.pullback j ≅
        Scheme.Modules.pullback j ⋙
          (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj
            ((Scheme.Modules.pullback j).obj A)) ≪≫
    Functor.isoWhiskerLeft (Scheme.Modules.pullback j)
      (Stacks.SheafOfModules.Invertible.tensorLeftFunctorCongr X.presheaf (ringSheafCond X)
        ((Scheme.Modules.restrictFunctorIsoPullback j).app A).symm) ≪≫
    Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback j).symm
      ((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj
        ((Scheme.Modules.restrictFunctor j).obj A))

/-! ### The two squares of conclusion (b) -/

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) (F : X.Modules) (n : ℕ)

/-- **The source functor of conclusion (b) of [Stacks, Tag 0EX3] commutes with restriction to an
open `V` of the base**, naturally in the module on the base:

`(R^n f_* F ⊗_{𝒪_Y} G)|_V ≅ R^n (f ∣_V)_* (F|_{f⁻¹V}) ⊗_{𝒪_V} G|_V`.

The tensor product commutes with restriction, and the higher direct image in the left factor is
that of the restricted morphism by [Stacks, Tag 01E5]. -/
def sourceRestrictIso :
    topDirectImageTensorLeftFunctor f F n ⋙ Scheme.Modules.restrictFunctor V.ι ≅
      Scheme.Modules.restrictFunctor V.ι ⋙
        topDirectImageTensorLeftFunctor (f ∣_ V)
          ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F) n :=
  restrictTensorLeftFunctorIso V.ι (topDirectImage f F n) ≪≫
    Functor.isoWhiskerLeft (Scheme.Modules.restrictFunctor V.ι)
      (Stacks.SheafOfModules.Invertible.tensorLeftFunctorCongr (V : Scheme).presheaf
        (ringSheafCond (V : Scheme)) (rightDerivedPlusRestrictObjIso f V n F).symm)

/-- **The target functor of conclusion (b) of [Stacks, Tag 0EX3] commutes with restriction to an
open `V` of the base**, naturally in the module on the base:

`(R^n f_*(F ⊗_{𝒪_X} f^* G))|_V ≅ R^n (f ∣_V)_*(F|_{f⁻¹V} ⊗ (f ∣_V)^* G|_V)`.

Read from the outside in: the higher direct image commutes with restriction by
[Stacks, Tag 01E5], the tensor product by `restrictTensorLeftFunctorIso`, and the inverse image
by `Stacks.AlgebraicGeometry.AffinePushforward.pullbackRestrictIso`. -/
def targetRestrictIso :
    topDirectImageTensorFunctor f F n ⋙ Scheme.Modules.restrictFunctor V.ι ≅
      Scheme.Modules.restrictFunctor V.ι ⋙
        topDirectImageTensorFunctor (f ∣_ V)
          ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F) n :=
  Functor.isoWhiskerLeft
      (Scheme.Modules.pullback f ⋙
        (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F)
      (rightDerivedPlusRestrictIso f V n).symm ≪≫
    Functor.isoWhiskerLeft (Scheme.Modules.pullback f)
      (Functor.isoWhiskerRight (restrictTensorLeftFunctorIso (f ⁻¹ᵁ V).ι F)
        ((Scheme.Modules.pushforward (f ∣_ V)).rightDerivedPlus (n : ℤ))) ≪≫
    Functor.isoWhiskerRight (pullbackRestrictIso f V)
      ((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨(f ⁻¹ᵁ V : Scheme).toRingedSpace.presheaf,
              (f ⁻¹ᵁ V : Scheme).toRingedSpace.IsSheaf⟩).obj
          ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F) ⋙
        (Scheme.Modules.pushforward (f ∣_ V)).rightDerivedPlus (n : ℤ))

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
