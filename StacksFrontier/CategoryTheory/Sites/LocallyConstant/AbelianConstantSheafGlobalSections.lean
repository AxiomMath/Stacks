module

public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.AbelianInternalization
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.ConstantSheafGlobalSections
public import StacksFrontier.CategoryTheory.Sites.Topos.AbelianPushforwardExact

/-!
# Constant abelian sheaves and global sections along a morphism of topoi, with no final object

Let `f : Sh(C) → Sh(D)` be a morphism of topoi between the topoi of sheaves of sets on two small
sites. This file proves, with **no final object assumed in either site**, that

* the inverse image of abelian sheaves carries the constant abelian sheaf on an abelian group to
  the constant abelian sheaf on that group,
  `MorphismOfTopoi.abelianInverseImageConstantSheafIsoOfSmallSites`;
* the global sections of a direct image of abelian sheaves are the global sections of the sheaf,
  `Γ(D, f_*F) = Γ(C, F)`, `MorphismOfTopoi.abelianPushforwardGammaIsoOfSmallSites`.

The first is `Stacks.ConstantSheaf.inverseImageConstantSheafIsoOfSmallSites` on sheaves of sets,
lifted to internal commutative group objects by `CategoryTheory.Functor.mapCommGrpNatIso`, with
the two constant sheaves read on internal commutative groups by
`Stacks.Sites.AbelianPullback.constantSheafInternalIso` and `.constantSheafExternalIso`. The
second follows by uniqueness of right adjoints: `constantSheaf D ⋙ f⁻¹` is left adjoint to
`f_* ⋙ Γ(D, -)` and `constantSheaf C` to `Γ(C, -)`, `Γ` being by definition the right adjoint of
the constant sheaf functor. These are the forms of `MorphismOfTopoi.abelianConstantSheafIso` and
`Stacks.ConstantSheaf.abelianPushforwardSectionsIso` for sites without final objects, such as the
étale site of a simplicial algebraic space (Section 0DE7).

## References

* [Stacks Project, Tag 093R](https://stacks.math.columbia.edu/tag/093R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Sites CategoryTheory.Sites.AbelianSheaf
open Stacks.ConstantSheaf Stacks.Sites.AbelianPullback Stacks.Topos.Skyscraper

universe w

namespace MorphismOfTopoi

attribute [local instance] cartesianPresheafTypes braidedPresheafTypes cartesianSheafTypes
  braidedSheafTypes braidedSheafToPresheafTypes

variable {C : Type w} [SmallCategory C] {D : Type w} [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w)))

/-- **The inverse image of abelian sheaves carries constant sheaves to constant sheaves, with no
final object in either site**: `f⁻¹ M_D ≅ M_C`, naturally in the abelian group `M`. -/
public def abelianInverseImageConstantSheafIsoOfSmallSites :
    constantSheaf K AddCommGrpCat.{w} ⋙ CategoryTheory.Sites.abelianInverseImage f ≅
      constantSheaf J AddCommGrpCat.{w} := by
  haveI : PreservesFiniteLimits f.inverseImage := f.preservesFiniteLimits
  letI : f.inverseImage.Braided := .ofChosenFiniteProducts _
  letI : (constantSheaf K (Type w)).Braided := .ofChosenFiniteProducts _
  letI : (constantSheaf J (Type w)).Braided := .ofChosenFiniteProducts _
  exact Functor.isoWhiskerRight (constantSheafInternalIso K)
      (f.inverseImage.mapCommGrp ⋙ externalSheaf J) ≪≫
    Functor.isoWhiskerLeft commGrpAddEquivalence.inverse
      (Functor.isoWhiskerRight (Functor.mapCommGrpCompIso
        (F := constantSheaf K (Type w)) (G := f.inverseImage)).symm (externalSheaf J)) ≪≫
    Functor.isoWhiskerLeft commGrpAddEquivalence.inverse
      (Functor.isoWhiskerRight (Functor.mapCommGrpNatIso
        (inverseImageConstantSheafIsoOfSmallSites f.adj)) (externalSheaf J)) ≪≫
    constantSheafExternalIso J

/-- **Global sections of a direct image of abelian sheaves, with no final object in either
site**: `Γ(D, f_*F) = Γ(C, F)`, naturally in the abelian sheaf `F` on `C`. Both sides are right
adjoint to the constant sheaf functor on `C`, by
`MorphismOfTopoi.abelianInverseImageConstantSheafIsoOfSmallSites`. -/
public def abelianPushforwardGammaIsoOfSmallSites :
    Stacks.Topos.AbelianPushforward.abelianPushforward J f ⋙ Sheaf.Γ K AddCommGrpCat.{w} ≅
      Sheaf.Γ J AddCommGrpCat.{w} :=
  (((constantSheafΓAdj K AddCommGrpCat.{w}).comp
      (Stacks.Topos.AbelianPushforward.abelianInverseImageAdjPushforward J f)).ofNatIsoLeft
    (abelianInverseImageConstantSheafIsoOfSmallSites f)).rightAdjointUniq
    (constantSheafΓAdj J AddCommGrpCat.{w})

end MorphismOfTopoi

end
