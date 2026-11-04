module

public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaCokernel
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TensorComparisonUnitIso

/-!
# The canonical map of Tag 0EX3 (b) as a natural transformation of functors in `G`

Conclusion (b) of [Stacks, Tag 0EX3] compares two functors of the module on the base,

> `G ↦ R^n f_* F ⊗_{𝒪_Y} G`  and  `G ↦ R^n f_*(F ⊗_{𝒪_X} f^* G)`,

and the canonical map of `TensorComparisonCanonical.lean` is natural in `G`
(`higherDirectImageTensorMap_naturality`).  This file packages the two functors and that
naturality into one natural transformation, which is the shape the Eilenberg-Watts rigidity
criterion `Stacks.EilenbergWatts.isIso_of_isIso_app_self` consumes: *a natural transformation
between two right exact functors commuting with direct sums is invertible as soon as it is
invertible at the base ring*.  Its value at the structure sheaf is invertible, by
`TensorComparisonUnitIso.lean`.

Both functors are existing constants: the source is
`Stacks.SheafOfModules.tensorLeftFunctor`, whose value at `G` is the
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf` of this directory on the nose and
whose action on morphisms is `tensorSheafMap` with the identity in the first factor, and the
target is the composite of the pullback, that same functor on `X` and the derived pushforward.
Both identifications are `rfl`, so the naturality statement is consumed unchanged.

## Main definitions

All of the following live in the namespace `Stacks.AlgebraicGeometry.TopDegreeBaseChange`.

* `topDirectImageTensorLeftFunctor`: the source functor `G ↦ R^n f_* F ⊗_{𝒪_Y} G`.
* `topDirectImageTensorFunctor`: the target functor `G ↦ R^n f_*(F ⊗_{𝒪_X} f^* G)`.
* `higherDirectImageTensorNatTrans`: **the canonical map of conclusion (b), as a natural
  transformation of functors of the module on the base.**

## Main results

* `higherDirectImageTensorNatTrans_app`: its component is the canonical map.
* `isIso_higherDirectImageTensorNatTrans_app_unitModule` and
  `isIso_higherDirectImageTensorMap_of_iso_unitModule`: **it is invertible at the structure
  sheaf of the base**, and at every module isomorphic to it, for an arbitrary morphism of
  schemes, an arbitrary module upstairs and an arbitrary degree.
* `topDirectImageTensorComparisonUnitModule`: **conclusion (b) of [Stacks, Tag 0EX3] at
  `G = 𝒪_Y`, with every hypothesis discharged.**  Not the conclusion itself, which quantifies
  over the module on the base; the one value of it at which the conclusion is unconditional.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

noncomputable section

attribute [local instance] HasDerivedCategory.standard

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) (n : ℕ)

/-- **The source functor of conclusion (b) of [Stacks, Tag 0EX3]**, `G ↦ R^n f_* F ⊗_{𝒪_Y} G`. -/
abbrev topDirectImageTensorLeftFunctor : Y.Modules ⥤ Y.Modules :=
  (Stacks.SheafOfModules.Tensor.sheafTensor
    ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩).obj (topDirectImage f F n)

/-- **The target functor of conclusion (b) of [Stacks, Tag 0EX3]**,
`G ↦ R^n f_*(F ⊗_{𝒪_X} f^* G)`. -/
abbrev topDirectImageTensorFunctor : Y.Modules ⥤ Y.Modules :=
  Scheme.Modules.pullback f ⋙
    (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F ⋙
      (Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)

/-- The source functor takes `G` to the tensor sheaf of [Stacks, Tag 01CB]. -/
theorem topDirectImageTensorLeftFunctor_obj (G : Y.Modules) :
    (topDirectImageTensorLeftFunctor f F n).obj G =
      (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩).obj (topDirectImage f F n)).obj G) :=
    rfl

/-- The target functor takes `G` to the sheaf conclusion (b) compares. -/
theorem topDirectImageTensorFunctor_obj (G : Y.Modules) :
    (topDirectImageTensorFunctor f F n).obj G = topDirectImageTensor f F G n := rfl

/-- The naturality of the canonical map, read through the two functors above.  It is stated in
its own declaration because the identification of the functors' action on morphisms with the
`tensorSheafMap`s of the existing naturality statement is one definitional unfolding of the
sheafification of the presheaf tensor product, and a declaration that performs it twice exceeds
the kernel's budget. -/
theorem higherDirectImageTensorNatTrans_naturality {G G' : Y.Modules} (ψ : G ⟶ G') :
    (topDirectImageTensorLeftFunctor f F n).map ψ ≫ higherDirectImageTensorMap f F G' n =
      higherDirectImageTensorMap f F G n ≫ (topDirectImageTensorFunctor f F n).map ψ := by
  change (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩).obj (topDirectImage f F n)).map ψ) ≫
      higherDirectImageTensorMap f F G' n =
    higherDirectImageTensorMap f F G n ≫
      ((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).map
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).map
            ((Scheme.Modules.pullback f).map ψ)))
  exact higherDirectImageTensorMap_naturality f F n G G' ψ

/-- **The canonical map of conclusion (b) of [Stacks, Tag 0EX3], as a natural transformation of
functors of the module on the base.** -/
def higherDirectImageTensorNatTrans :
    topDirectImageTensorLeftFunctor f F n ⟶ topDirectImageTensorFunctor f F n where
  app G := higherDirectImageTensorMap f F G n
  naturality _ _ ψ := higherDirectImageTensorNatTrans_naturality f F n ψ

/-- The component of the natural transformation is the canonical map. -/
theorem higherDirectImageTensorNatTrans_app (G : Y.Modules) :
    (higherDirectImageTensorNatTrans f F n).app G = higherDirectImageTensorMap f F G n := rfl

/-- **The natural transformation is invertible at the structure sheaf of the base.** -/
instance isIso_higherDirectImageTensorNatTrans_app_unitModule :
    IsIso ((higherDirectImageTensorNatTrans f F n).app (Scheme.unitModule Y)) :=
  isIso_higherDirectImageTensorMap_unitModule f F n

/-- **The canonical map of conclusion (b) is invertible at every module isomorphic to the
structure sheaf of the base.**  Naturality in `G` moves the invertibility across the
isomorphism. -/
theorem isIso_higherDirectImageTensorMap_of_iso_unitModule {G : Y.Modules}
    (α : G ≅ Scheme.unitModule Y) : IsIso (higherDirectImageTensorMap f F G n) :=
  CategoryTheory.NatTrans.isIso_app_of_iso (higherDirectImageTensorNatTrans f F n) α.symm
    (isIso_higherDirectImageTensorNatTrans_app_unitModule f F n)

/-- **Conclusion (b) of [Stacks, Tag 0EX3] at `G = 𝒪_Y`, with every hypothesis discharged.**
For an arbitrary morphism of schemes, an arbitrary sheaf of modules on the source and an
arbitrary degree there is an isomorphism

`R^n f_*(F ⊗_{𝒪_X} f^* 𝒪_Y) ≅ R^n f_* F ⊗_{𝒪_Y} 𝒪_Y`

whose inverse satisfies the canonicity condition of the tag.  This is *not* conclusion (b),
which quantifies over the module on the base; it is the one value of that module at which the
conclusion holds with no hypothesis whatever, and it is the base case the source's
Eilenberg-Watts argument propagates from. -/
def topDirectImageTensorComparisonUnitModule :
    { e : ((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).obj
            ((Scheme.Modules.pullback f).obj (Scheme.unitModule Y)))) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩).obj
          (((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj F)).obj
            (Scheme.unitModule Y)) //
      IsHigherDirectImageTensorMap f F (Scheme.unitModule Y) n e.inv } :=
  topDirectImageTensorComparisonOfIsIso' f F (Scheme.unitModule Y) n

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
