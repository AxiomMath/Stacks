module

public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSiteSmallModel
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.FromTheStructureSheaf
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology

/-!
# The derived internal Hom of an essentially small ringed site

Let `X` be a ringed site whose underlying category is essentially small, with morphisms and
structure rings in `Type u` and objects possibly in a larger universe — the small étale ringed
site of an algebraic space is the case in view. The derived internal Hom
`AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor` is constructed for ringed sites all of
whose universes agree, so it does not apply to `X` directly. It applies to the small model
`AlgebraicGeometry.RingedSite.smallModel X`, whose sheaves of modules are those of `X` by the
Comparison Lemma; this file transports it back.

## Main definitions

* `AlgebraicGeometry.RingedSite.toSmallModelDerived` and
  `AlgebraicGeometry.RingedSite.fromSmallModelDerived` — the functors induced on derived
  categories by the Comparison Lemma `Mod(𝒪_X) ≌ Mod(𝒪_model)`, and
  `AlgebraicGeometry.RingedSite.fromToSmallModelDerivedIso`, the identification of their
  composite with the identity.
* `AlgebraicGeometry.RingedSite.smallModelDerivedSheafHom` — **the derived internal Hom
  `R𝓗om_{𝒪_X}(-, -)` of `X`**: the derived internal Hom of the model, read through the two
  functors.

## Main results

* `AlgebraicGeometry.RingedSite.smallModelDerivedSheafHomStructureSheafIso` — `R𝓗om(𝒪_X, M) ≅ M`.
* `AlgebraicGeometry.RingedSite.smallModelDerivedSheafHomHomologyIso` — the cohomology sheaves of
  `R𝓗om_{𝒪_X}(A, B)` are the cohomology sheaves of the derived internal Hom of the model, read
  back along the Comparison Lemma.

## Implementation notes

*The derived categories.* The derived category of `𝒪_X`-modules is an arbitrary
`CategoryTheory.HasDerivedCategory` instance. The derived category of the model, which only ever
appears inside the construction, is the standard one, `CategoryTheory.HasDerivedCategory.standard`,
recorded once as `AlgebraicGeometry.RingedSite.smallModelHasDerivedCategory`: the computations of
derived internal Hom out of free modules this construction is used with are stated there.

## References

* [Stacks Project, Tag 0A97](https://stacks.math.columbia.edu/tag/0A97)
* [Stacks Project, Tag 03A0](https://stacks.math.columbia.edu/tag/03A0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.DerivedCategoryComparisons

universe c u d

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{c, u, u}) [EssentiallySmall.{u} X.C]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The derived category of the model is the standard one. -/
abbrev smallModelHasDerivedCategory :
    HasDerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallModel X).O)) :=
  HasDerivedCategory.standard _

attribute [local instance] smallModelHasDerivedCategory

/-- The Comparison Lemma is additive, being an equivalence of preadditive categories. -/
instance smallModelModulesEquiv_functor_additive : (smallModelModulesEquiv X).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

variable [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

/-- The functor `D(𝒪_X) ⥤ D(𝒪_model)` induced by the Comparison Lemma. -/
abbrev toSmallModelDerived :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallModel X).O)) :=
  (smallModelModulesEquiv X).functor.mapDerivedCategory

/-- The functor `D(𝒪_model) ⥤ D(𝒪_X)` induced by the inverse of the Comparison Lemma. -/
abbrev fromSmallModelDerived :
    DerivedCategory (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallModel X).O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  (smallModelModulesEquiv X).inverse.mapDerivedCategory

/-- Going to the model and back is the identity of `D(𝒪_X)`. -/
def fromToSmallModelDerivedIso :
    toSmallModelDerived X ⋙ fromSmallModelDerived X ≅ 𝟭 _ :=
  (mapDerivedCategoryCompIso (smallModelModulesEquiv X).functor
      (smallModelModulesEquiv X).inverse).symm ≪≫
    mapDerivedCategoryIsoOfNatIso _ _ (smallModelModulesEquiv X).unitIso.symm ≪≫
    Stacks.Homology.mapDerivedCategoryIdIso

/-- **The derived internal Hom `R𝓗om_{𝒪_X}(-, -)` of `X`**, contravariant in its source: the
derived internal Hom of the small model, read through the Comparison Lemma. -/
def smallModelDerivedSheafHom :
    (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))ᵒᵖ ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
        DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  (toSmallModelDerived X).op ⋙ derivedSheafHomBifunctor (smallModel X) ⋙
    (Functor.whiskeringLeft _ _ _).obj (toSmallModelDerived X) ⋙
      (Functor.whiskeringRight _ _ _).obj (fromSmallModelDerived X)

/-- The value of `smallModelDerivedSheafHom` on a pair of objects, on the nose. -/
theorem smallModelDerivedSheafHom_obj_obj
    (A B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((smallModelDerivedSheafHom X).obj (op A)).obj B =
      (fromSmallModelDerived X).obj (((derivedSheafHomBifunctor (smallModel X)).obj
        (op ((toSmallModelDerived X).obj A))).obj ((toSmallModelDerived X).obj B)) :=
  rfl

/-- The Comparison Lemma carries the structure sheaf of `X` to the structure sheaf of the
model. -/
def smallModelModulesEquivUnitIso :
    (smallModelModulesEquiv X).functor.obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (smallModel X).O) :=
  Iso.refl _

/-- The functor to the model carries `𝒪_X[0]` to `𝒪_model[0]`. -/
def toSmallModelDerivedStructureSheafIso :
    (toSmallModelDerived X).obj ((DerivedCategory.singleFunctor _ 0).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ≅
      derivedStructureSheaf (smallModel X) :=
  ((smallModelModulesEquiv X).functor.mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (smallModelModulesEquivUnitIso X) ≪≫
    (DerivedCategory.singleFunctorIsoCompQ _ 0).app _

/-- **`R𝓗om_{𝒪_X}(𝒪_X, M) ≅ M`.** -/
def smallModelDerivedSheafHomStructureSheafIso
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((smallModelDerivedSheafHom X).obj (op ((DerivedCategory.singleFunctor _ 0).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))).obj M ≅ M :=
  (fromSmallModelDerived X).mapIso
      ((((derivedSheafHomBifunctor (smallModel X)).mapIso
        (toSmallModelDerivedStructureSheafIso X).op).app ((toSmallModelDerived X).obj M)).symm ≪≫
      derivedStructureSheafHomIso (smallModel X) _) ≪≫
    (fromToSmallModelDerivedIso X).app M

/-- **The cohomology sheaves of `R𝓗om_{𝒪_X}(A, B)`** are those of the derived internal Hom of
the model, read back along the Comparison Lemma. -/
def smallModelDerivedSheafHomHomologyIso (n : ℤ)
    (A B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (DerivedCategory.homologyFunctor _ n).obj (((smallModelDerivedSheafHom X).obj (op A)).obj B) ≅
      (smallModelModulesEquiv X).inverse.obj ((DerivedCategory.homologyFunctor _ n).obj
        (((derivedSheafHomBifunctor (smallModel X)).obj
          (op ((toSmallModelDerived X).obj A))).obj ((toSmallModelDerived X).obj B))) :=
  ((smallModelModulesEquiv X).inverse.mapDerivedCategoryHomologyIso n).app _

end AlgebraicGeometry.RingedSite

end
