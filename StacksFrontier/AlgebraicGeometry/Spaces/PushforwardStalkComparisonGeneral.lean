module

public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardStalkComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAbelianDirectImageGeneral

/-!
# The stalk comparison for the direct image along an arbitrary morphism of algebraic spaces

`AlgebraicGeometry.Space.smallEtaleAbelianPushforwardStalkMap` is the canonical comparison
`(f_*F)_{x̄} ⟶ F_ȳ` for a morphism `f : Y ⟶ X` of algebraic spaces whose underlying morphism of
presheaves is relatively representable.  This file gives the same comparison for an *arbitrary*
morphism, built the same way out of the direct image, the inverse image, their adjunction and
Stacks 04K2 part (4) of
`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAbelianDirectImageGeneral`.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleAbelianDirectImageStalkMap` is that comparison, as a
  morphism of functors `f_* ⋙ (-)_{x̄} ⟶ (-)_ȳ`, for an arbitrary `f`.

## Main results

* `AlgebraicGeometry.Space.smallEtaleAbelianDirectImageStalkMap_app` and
  `AlgebraicGeometry.Space.isIso_app_smallEtaleAbelianDirectImageStalkMap_iff_counit`: the two
  bridges that let the argument be run on the adjunction counit and the answer read back on the
  stalk comparison, as in the representable case.

## References

* [Stacks Project, Tag 04K2](https://stacks.math.columbia.edu/tag/04K2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X Y : AlgebraicSpaces B S hS}

/-- **The canonical map from the stalk of a direct image to the stalk of the sheaf, for an
arbitrary morphism of algebraic spaces.**  For `f : Y ⟶ X` and a geometric point `ȳ` of `Y`
with image `x̄ = f(ȳ)`, the map `(f_*F)_{x̄} ⟶ F_ȳ`, natural in the abelian sheaf `F` on the
small étale site of `Y`.

It is the composite of the identification `(f_*F)_{x̄} = (f^{-1}f_*F)_ȳ` of Stacks 04K2
part (4) with the stalk at `ȳ` of the counit `f^{-1}f_*F ⟶ F`.  This is
`AlgebraicGeometry.Space.smallEtaleAbelianPushforwardStalkMap` with the hypothesis that `f` be
representable removed. -/
def smallEtaleAbelianDirectImageStalkMap (f : Y ⟶ X) (y : GeometricPoint B S hS Y.1) :
    smallEtaleAbelianDirectImage B S hS f ⋙
        smallEtaleAbelianStalk B S hS (geometricPointMap f.hom y) ⟶
      smallEtaleAbelianStalk B S hS y :=
  Functor.whiskerLeft _ (smallEtaleAbelianGeneralInverseImageStalkIso B S hS f y).inv ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (smallEtaleAbelianGeneralAdjunction B S hS f).counit
      (smallEtaleAbelianStalk B S hS y) ≫
    (Functor.leftUnitor _).hom

/-- The stalk comparison at a sheaf, written out: the identification of Stacks 04K2 part (4)
followed by the geometric stalk of the adjunction counit. -/
theorem smallEtaleAbelianDirectImageStalkMap_app (f : Y ⟶ X)
    (y : GeometricPoint B S hS Y.1)
    (F : Sheaf (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{u + 1}) :
    (smallEtaleAbelianDirectImageStalkMap B S hS f y).app F =
      (smallEtaleAbelianGeneralInverseImageStalkIso B S hS f y).inv.app
          ((smallEtaleAbelianDirectImage B S hS f).obj F) ≫
        (smallEtaleAbelianStalk B S hS y).map
          ((smallEtaleAbelianGeneralAdjunction B S hS f).counit.app F) := by
  simp [smallEtaleAbelianDirectImageStalkMap]

/-- The stalk comparison at a sheaf is invertible exactly when the geometric stalk of the
counit at that sheaf is: the comparison is that stalk preceded by the identification of
Stacks 04K2 part (4), which is invertible. -/
theorem isIso_app_smallEtaleAbelianDirectImageStalkMap_iff_counit (f : Y ⟶ X)
    (y : GeometricPoint B S hS Y.1)
    (K : Sheaf (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{u + 1}) :
    IsIso ((smallEtaleAbelianDirectImageStalkMap B S hS f y).app K) ↔
      IsIso ((smallEtaleAbelianStalk B S hS y).map
        ((smallEtaleAbelianGeneralAdjunction B S hS f).counit.app K)) := by
  rw [smallEtaleAbelianDirectImageStalkMap_app]
  exact isIso_comp_left_iff _ _

end AlgebraicGeometry.Space

end
