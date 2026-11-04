module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackOnKFlatComplexes
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.KFlatPullbackCyclesInput
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ExistenceOnARingedSite
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.PullbackPreservesFlatness
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.TensorProduct

/-!
# The K-flat complexes with flat terms as a localization, at any universes

For a ringed topos `Y : RingedTopos.{v, u, w}` with arbitrary universes, the K-flat complexes of
`O_Y`-modules with flat terms, as a full subcategory of the homotopy category, localize to
`D(O_Y)`, and so do pairs of them to `D(O_Y) × D(O_Y)`: the statements of the section
`Localization` of `DerivedPullbackTensorComparison.lean` without its single-universe
restriction.

## References

* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Sheaves.DerivedPullback.KFlatPullback

namespace Stacks.Sheaves.DerivedPullback

/-! ## The K-flat complexes with flat terms as a localization -/

section Localization

universe v₂ u₂ w₂

attribute [local instance] HasDerivedCategory.standard

variable (Y : RingedTopos.{v₂, u₂, w₂})
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w₂} RingCat.{w₂})]
  [HasSheafify Y.J AddCommGrpCat.{w₂}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w₂}]

/-- The localization functor from the K-flat complexes of `O'`-modules with flat terms, as a
full subcategory of the unbounded homotopy category, to the derived category. -/
abbrev flatKFlatModelsQGeneral :
    (IsKFlat (Y := Y)).FullSubcategory ⥤
      DerivedCategory (SheafOfModules.{w₂} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :=
  (IsKFlat (Y := Y)).ι ⋙ DerivedCategory.Qh

/-- The quasi-isomorphisms between K-flat complexes with flat terms. -/
abbrev flatKFlatModelsWGeneral :
    MorphismProperty (IsKFlat (Y := Y)).FullSubcategory :=
  (HomotopyCategory.quasiIso (SheafOfModules.{w₂} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (ComplexShape.up ℤ)).inverseImage (IsKFlat (Y := Y)).ι

omit [Y.J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **Localizing only the K-flat complexes with flat terms already produces `D(O')`.** Every
complex receives a quasi-isomorphism from such a complex, by Stacks 06YS, so the inclusion of
the class into the homotopy category is a localized equivalence. -/
theorem flatKFlatModelsQGeneral_isLocalization :
    (flatKFlatModelsQGeneral Y).IsLocalization (flatKFlatModelsWGeneral Y) := by
  have hres : (LeftDerivedByResolutions.inclusionLocalizerMorphism
      (HomotopyCategory.quasiIso
        (SheafOfModules.{w₂} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))
      (IsKFlat (Y := Y))).HasLeftResolutions := fun M => by
    obtain ⟨K, hK, s, hs⟩ := hasResolutions_isKFlat (Y := Y) M
    exact ⟨{ X₁ := ⟨K, hK⟩, w := s, hw := hs }⟩
  have := LeftDerivedByResolutions.isLocalizedEquivalence_inclusionLocalizerMorphism
    (HomotopyCategory.quasiIso
      (SheafOfModules.{w₂} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))
    (IsKFlat (Y := Y))
  exact LocalizerMorphism.IsLocalizedEquivalence.isLocalization
    (LeftDerivedByResolutions.inclusionLocalizerMorphism _ (IsKFlat (Y := Y)))
    DerivedCategory.Qh

/-- Pairs of K-flat complexes with flat terms, as a localization of pairs of objects of
`D(O')`. -/
abbrev flatKFlatModelPairsQGeneral :
    (IsKFlat (Y := Y)).FullSubcategory × (IsKFlat (Y := Y)).FullSubcategory ⥤
      DerivedCategory (SheafOfModules.{w₂} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ×
        DerivedCategory (SheafOfModules.{w₂} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :=
  (flatKFlatModelsQGeneral Y).prod (flatKFlatModelsQGeneral Y)

/-- Pairs of quasi-isomorphisms between K-flat complexes with flat terms. -/
abbrev flatKFlatModelPairsWGeneral :
    MorphismProperty ((IsKFlat (Y := Y)).FullSubcategory ×
      (IsKFlat (Y := Y)).FullSubcategory) :=
  (flatKFlatModelsWGeneral Y).prod (flatKFlatModelsWGeneral Y)

omit [Y.J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **Pairs of K-flat complexes with flat terms localize to pairs of objects of `D(O')`.** -/
theorem flatKFlatModelPairsQGeneral_isLocalization :
    (flatKFlatModelPairsQGeneral Y).IsLocalization (flatKFlatModelPairsWGeneral Y) := by
  have := flatKFlatModelsQGeneral_isLocalization Y
  infer_instance

/-- The localization carries a pair of models to the pair of the objects of `D(O')` they
represent. -/
def flatKFlatModelPairsIsoGeneral
    (P : (IsKFlat (Y := Y)).FullSubcategory × (IsKFlat (Y := Y)).FullSubcategory) :
    (flatKFlatModelPairsQGeneral Y).obj P ≅
      (DerivedCategory.Q.obj P.1.obj.as, DerivedCategory.Q.obj P.2.obj.as) :=
  ((DerivedCategory.quotientCompQhIso
      (SheafOfModules.{w₂} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).app P.1.obj.as).prod
    ((DerivedCategory.quotientCompQhIso
      (SheafOfModules.{w₂} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).app P.2.obj.as)

omit [Y.J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The identification of a pair of models with the pair of objects it represents is natural in
the pair of models. -/
lemma flatKFlatModelPairsIsoGeneral_naturality
    {P R : (IsKFlat (Y := Y)).FullSubcategory × (IsKFlat (Y := Y)).FullSubcategory}
    (g : P ⟶ R) :
    (flatKFlatModelPairsQGeneral Y).map g ≫ (flatKFlatModelPairsIsoGeneral Y R).hom =
      (flatKFlatModelPairsIsoGeneral Y P).hom ≫
        ((DerivedCategory.Q.map g.1.hom.out, DerivedCategory.Q.map g.2.hom.out) :
          ((DerivedCategory.Q.obj P.1.obj.as, DerivedCategory.Q.obj P.2.obj.as) : _ × _) ⟶
            (DerivedCategory.Q.obj R.1.obj.as, DerivedCategory.Q.obj R.2.obj.as)) := by
  have key {A B : (IsKFlat (Y := Y)).FullSubcategory} (f : A ⟶ B) := by
    simpa using DerivedCategory.quotientCompQhIso_hom_naturality
      (C := SheafOfModules.{w₂} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) f.hom.out
  exact Prod.ext (key g.1) (key g.2)

end Localization

end Stacks.Sheaves.DerivedPullback

end
