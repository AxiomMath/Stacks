module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkTensorComparison
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Flatness of sheaves of modules on stalks, under weak sheafification

A sheaf of modules over a sheaf of commutative rings is flat if and only if its stalks at a
conservative family of points are flat modules, assuming only that weak sheafification of abelian
groups exists and that the weak equivalences are the locally bijective morphisms.

## Main results

* `Stacks.isFlat_iff_forall_isFlatModuleStalk_of_weakSheafify`: a sheaf of modules is flat if and
  only if its stalks at a conservative family of points are flat, under
  `HasWeakSheafify J AddCommGrpCat.{w}` and `J.WEqualsLocallyBijective AddCommGrpCat.{w}`.

## References

* [Stacks Project, Tag 05VC](https://stacks.math.columbia.edu/tag/05VC)
-/

@[expose] public section

open CategoryTheory

universe w v u

namespace Stacks

/-- A sheaf of modules is flat if and only if its stalks at a conservative family of points are
flat, assuming `HasWeakSheafify J AddCommGrpCat.{w}` and
`J.WEqualsLocallyBijective AddCommGrpCat.{w}`. -/
@[stacks 05VC, sga "4 V 1.6" "2)"]
theorem isFlat_iff_forall_isFlatModuleStalk_of_weakSheafify {C : Type u} [Category.{v} C]
    [LocallySmall.{w} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
    {t : Type*} (p : t → J.Point.{w})
    (hp : (ObjectProperty.ofObj p).IsConservativeFamilyOfPoints) (O : Sheaf J CommRingCat.{w})
    (F : SheafOfModules.{w} (commRingSheafToRingSheaf O)) :
    SheafOfModules.IsFlat F ↔ ∀ i, IsFlatModuleStalk (p i) O F := by
  let : HasSheafify J AddCommGrpCat.{w} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  exact isFlat_iff_forall_isFlatModuleStalk O F p hp

end Stacks

end
