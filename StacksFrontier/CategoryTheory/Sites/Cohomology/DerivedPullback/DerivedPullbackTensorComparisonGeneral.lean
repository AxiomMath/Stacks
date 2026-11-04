module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorComparison

/-! # The K-flat complexes with flat terms as a localization, site universes free

This module generalizes the section `Localization` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorComparison`
from a ringed topos `Y : RingedTopos.{u, u, u}` to a ringed topos `Y : RingedTopos.{v, u, w}`
whose site lives in universes `u`, `v` independent of the universe `w` of its sheaves of rings and
modules, as for the small étale site of an algebraic space. The proofs are those of the base
module.

## Main definitions

* `Stacks.Sheaves.DerivedPullbackGeneral.flatKFlatModelsQ`,
  `Stacks.Sheaves.DerivedPullbackGeneral.flatKFlatModelsW` and
  `Stacks.Sheaves.DerivedPullbackGeneral.flatKFlatModelsQ_isLocalization`: generalize
  `Stacks.Sheaves.DerivedPullback.flatKFlatModelsQ`,
  `Stacks.Sheaves.DerivedPullback.flatKFlatModelsW` and
  `Stacks.Sheaves.DerivedPullback.flatKFlatModelsQ_isLocalization`.
* `Stacks.Sheaves.DerivedPullbackGeneral.flatKFlatModelPairsQ`,
  `Stacks.Sheaves.DerivedPullbackGeneral.flatKFlatModelPairsW`,
  `Stacks.Sheaves.DerivedPullbackGeneral.flatKFlatModelPairsQ_isLocalization`,
  `Stacks.Sheaves.DerivedPullbackGeneral.flatKFlatModelPairsIso` and
  `Stacks.Sheaves.DerivedPullbackGeneral.flatKFlatModelPairsIso_naturality`: generalize the
  declarations of the same names in `Stacks.Sheaves.DerivedPullback`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Sheaves.DerivedPullback.KFlatPullback

namespace Stacks.Sheaves.DerivedPullbackGeneral

universe v u w

section Localization

/- The standard model of the derived category: the derived functors this file uses (derived
pullback, pushforward, tensor product and internal Hom on ringed sites and topoi) are stated
on it, so the statements here must be too. -/
attribute [local instance] HasDerivedCategory.standard

variable (Y : RingedTopos.{v, u, w})
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The localization functor from the K-flat complexes of `O'`-modules with flat terms, as a
full subcategory of the unbounded homotopy category, to the derived category. -/
abbrev flatKFlatModelsQ :
    (IsKFlat (Y := Y)).FullSubcategory ⥤
      DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :=
  (IsKFlat (Y := Y)).ι ⋙ DerivedCategory.Qh

/-- The quasi-isomorphisms between K-flat complexes with flat terms. -/
abbrev flatKFlatModelsW :
    MorphismProperty (IsKFlat (Y := Y)).FullSubcategory :=
  (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (ComplexShape.up ℤ)).inverseImage (IsKFlat (Y := Y)).ι

/-- **Localizing only the K-flat complexes with flat terms already produces `D(O')`.** Every
complex receives a quasi-isomorphism from such a complex, by Stacks 06YS, so the inclusion of
the class into the homotopy category is a localized equivalence.

Generalizes `Stacks.Sheaves.DerivedPullback.flatKFlatModelsQ_isLocalization` to a ringed topos
`RingedTopos.{v, u, w}` with independent universes, in place of `RingedTopos.{u, u, u}`. -/
theorem flatKFlatModelsQ_isLocalization
    (Y : RingedTopos.{v, u, w}) [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [HasSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] :
    (flatKFlatModelsQ Y).IsLocalization (flatKFlatModelsW Y) := by
  have hres : (LeftDerivedByResolutions.inclusionLocalizerMorphism
      (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (ComplexShape.up ℤ))
      (IsKFlat (Y := Y))).HasLeftResolutions := fun M => by
    obtain ⟨K, hK, s, hs⟩ := hasResolutions_isKFlat (Y := Y) M
    exact ⟨{ X₁ := ⟨K, hK⟩, w := s, hw := hs }⟩
  have := LeftDerivedByResolutions.isLocalizedEquivalence_inclusionLocalizerMorphism
    (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))
    (IsKFlat (Y := Y))
  exact LocalizerMorphism.IsLocalizedEquivalence.isLocalization
    (LeftDerivedByResolutions.inclusionLocalizerMorphism _ (IsKFlat (Y := Y)))
    DerivedCategory.Qh

/-- Pairs of K-flat complexes with flat terms, as a localization of pairs of objects of
`D(O')`. -/
abbrev flatKFlatModelPairsQ :
    (IsKFlat (Y := Y)).FullSubcategory × (IsKFlat (Y := Y)).FullSubcategory ⥤
      DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ×
        DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :=
  (flatKFlatModelsQ Y).prod (flatKFlatModelsQ Y)

/-- Pairs of quasi-isomorphisms between K-flat complexes with flat terms.

Generalizes `Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsW` to a ringed topos
`RingedTopos.{v, u, w}` with independent universes, in place of `RingedTopos.{u, u, u}`. -/
abbrev flatKFlatModelPairsW
    (Y : RingedTopos.{v, u, w}) [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [HasSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] :
    MorphismProperty ((IsKFlat (Y := Y)).FullSubcategory ×
      (IsKFlat (Y := Y)).FullSubcategory) :=
  (flatKFlatModelsW Y).prod (flatKFlatModelsW Y)

/-- **Pairs of K-flat complexes with flat terms localize to pairs of objects of `D(O')`.**

Generalizes `Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsQ_isLocalization` to a ringed topos
`RingedTopos.{v, u, w}` with independent universes, in place of `RingedTopos.{u, u, u}`. -/
theorem flatKFlatModelPairsQ_isLocalization
    (Y : RingedTopos.{v, u, w}) [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [HasSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] :
    (flatKFlatModelPairsQ Y).IsLocalization (flatKFlatModelPairsW Y) := by
  have := flatKFlatModelsQ_isLocalization Y
  infer_instance

/-- The localization carries a pair of models to the pair of the objects of `D(O')` they
represent. -/
def flatKFlatModelPairsIso
    (P : (IsKFlat (Y := Y)).FullSubcategory × (IsKFlat (Y := Y)).FullSubcategory) :
    (flatKFlatModelPairsQ Y).obj P ≅
      (DerivedCategory.Q.obj P.1.obj.as, DerivedCategory.Q.obj P.2.obj.as) :=
  ((DerivedCategory.quotientCompQhIso
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).app P.1.obj.as).prod
    ((DerivedCategory.quotientCompQhIso
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).app P.2.obj.as)

/-- The identification of a pair of models with the pair of objects it represents is natural in
the pair of models.

Generalizes `Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsIso_naturality` to a ringed topos
`RingedTopos.{v, u, w}` with independent universes, in place of `RingedTopos.{u, u, u}`. -/
lemma flatKFlatModelPairsIso_naturality
    (Y : RingedTopos.{v, u, w}) [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [HasSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    {P R : (IsKFlat (Y := Y)).FullSubcategory × (IsKFlat (Y := Y)).FullSubcategory}
    (g : P ⟶ R) :
    (flatKFlatModelPairsQ Y).map g ≫ (flatKFlatModelPairsIso Y R).hom =
      (flatKFlatModelPairsIso Y P).hom ≫
        ((DerivedCategory.Q.map g.1.hom.out, DerivedCategory.Q.map g.2.hom.out) :
          ((DerivedCategory.Q.obj P.1.obj.as, DerivedCategory.Q.obj P.2.obj.as) : _ × _) ⟶
            (DerivedCategory.Q.obj R.1.obj.as, DerivedCategory.Q.obj R.2.obj.as)) := by
  have key {A B : (IsKFlat (Y := Y)).FullSubcategory} (f : A ⟶ B) :=
    HomotopyCategory.quotient_map_out f.hom ▸ DerivedCategory.quotientCompQhIso_hom_naturality
      (C := SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) f.hom.out
  exact Prod.ext (key g.1) (key g.2)

end Localization

end Stacks.Sheaves.DerivedPullbackGeneral

end
