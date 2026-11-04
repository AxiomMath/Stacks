module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SubcategoryLocalization
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ExistenceOnARingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.ComparisonWithTheDerivedTensorProductGeneral

/-!
# The K-flat complexes localize to `D(Mod(O))`, at general universes

Let `(C, O)` be a ringed site whose objects live in a universe `c` and whose morphisms and sections
live in the universe `u` of the sheaf of rings. The K-flat complexes of `O`-modules localize to
`D(Mod(O))` at the quasi-isomorphisms, and the derived tensor bifunctor descends the total tensor
product of K-flat complexes.

## Implementation notes

This is the part of
`StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.CanonicalDerivedTensorComparison` that does
not need `C` to be a `SmallCategory.{u}`, for a site `C : Type c` with `[Category.{u} C]`; the
statements and proofs are the same, in the namespace
`Stacks.SheafOfModules.DerivedMonoidalGeneral`. This applies to the small étale ringed site of an
algebraic space.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CochainComplex.KFlatBifunctor

universe d c u

namespace Stacks.SheafOfModules.DerivedMonoidalGeneral

variable {C : Type c} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasDerivedCategory.{d} (Mod R)]

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  CochainComplex.symmetricCategory

/- The monoidal structures on `Mod(O)` and `Comp(Mod(O))` at pinned universes, of
`StacksFrontier/CategoryTheory/Sites/Cohomology/Monoidal/DerivedCategory.lean`, back in scope.  The
sections universe of `SheafOfModules.monoidalCategorySheafTensor` is `max u v` in the two site
universes, which instance synthesis has to solve from the `u` of `Mod R` at every use; a monoidal
structure on `Comp(Mod(O))` synthesized from one whose universes are still unsolved is a structure
the whiskerings below cannot reduce through. -/
attribute [local instance] monoidalCategoryMod symmetricCategoryMod monoidalPreadditiveMod
  monoidalClosedMod hasTensorMod monoidalComplexes

/-! ### The K-flat complexes localize to `D(Mod(O))` -/

/-- `D(Mod(O))` is the localization of the K-flat objects of `K(Mod(O))` at the
quasi-isomorphisms.  This is `CochainComplex.KFlatBifunctor.kFlatQ_isLocalization` fed the
supply of K-flat resolutions of Tag 06YS, named here so that it can be a local instance. -/
theorem kFlatQ_isLocalization
    {C : Type c} [Category.{u} C] {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasDerivedCategory.{d} (Mod R)] :
    (kFlatQ (curriedTensor (Mod R))).IsLocalization (kFlatQuasiIso (curriedTensor (Mod R))) :=
  CochainComplex.KFlatBifunctor.kFlatQ_isLocalization _ (exists_kFlat_resolution R)

/-- The mirror of `Stacks.SheafOfModules.DerivedMonoidalGeneral.kFlatQ_isLocalization` for the
*left* K-flat objects, which is the localization `CochainComplex.KFlatBifunctor.derivedBifunctor`
descends along in its first variable. -/
theorem kFlatQLeft_isLocalization
    {C : Type c} [Category.{u} C] {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasDerivedCategory.{d} (Mod R)] :
    (kFlatQLeft (curriedTensor (Mod R))).IsLocalization
      (kFlatQuasiIsoLeft (curriedTensor (Mod R))) :=
  CochainComplex.KFlatBifunctor.kFlatQLeft_isLocalization _
    (CochainComplex.KFlatMonoidal.exists_kFlatLeft_quasiIso (Mod R) (exists_kFlat_resolution R))

attribute [local instance] kFlatQ_isLocalization kFlatQLeft_isLocalization

/-- K-flatness as a property of cochain complexes of `O`-modules: the class of the complex in
`K(Mod(O))` is K-flat.  This is `Stacks.SheafOfModules.KFlat.KFlat R`, in the form
`CategoryTheory.ObjectProperty.ι_comp_Q_isLocalization` consumes. -/
abbrev KFlatComplexes
    {C : Type c} [Category.{u} C] {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasDerivedCategory.{d} (Mod R)] :
    ObjectProperty (Complexes R) :=
  ObjectProperty.complexSubcategory (kFlatObjects (curriedTensor (Mod R)))

/-- The functor from the K-flat complexes of `O`-modules to `D(Mod(O))`. -/
abbrev kFlatComplexQ
    {C : Type c} [Category.{u} C] {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasDerivedCategory.{d} (Mod R)] :
    (KFlatComplexes R).FullSubcategory ⥤ DerivedModules R :=
  (KFlatComplexes R).ι ⋙ DerivedCategory.Q

/-- The quasi-isomorphisms between K-flat complexes of `O`-modules. -/
abbrev kFlatComplexQuasiIso
    {C : Type c} [Category.{u} C] {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasDerivedCategory.{d} (Mod R)] :
    MorphismProperty (KFlatComplexes R).FullSubcategory :=
  (HomologicalComplex.quasiIso (Mod R) (ComplexShape.up ℤ)).inverseImage (KFlatComplexes R).ι

/-- **`D(Mod(O))` is the localization of the K-flat complexes of `O`-modules at the
quasi-isomorphisms between them.**  So a bifunctor on K-flat complexes inverting those
quasi-isomorphisms descends to `D(Mod(O))`, and a pair of such descents of one bifunctor are
isomorphic. -/
instance kFlatComplexQ_isLocalization
    {C : Type c} [Category.{u} C] {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasDerivedCategory.{d} (Mod R)] :
    (kFlatComplexQ R).IsLocalization (kFlatComplexQuasiIso R) :=
  ObjectProperty.ι_comp_Q_isLocalization _

/-- The bifunctor on K-flat complexes of `O`-modules that both the derived tensor product of
Tag 06YU and `CochainComplex.KFlatBifunctor.derivedBifunctor` descend: the total tensor
product of complexes, pushed into `D(Mod(O))`. -/
abbrev kFlatTensorSource :
    (KFlatComplexes R).FullSubcategory ⥤ (KFlatComplexes R).FullSubcategory ⥤
      DerivedModules R :=
  (((Functor.whiskeringLeft₂ (DerivedModules R)).obj (KFlatComplexes R).ι).obj
      (KFlatComplexes R).ι).obj
    (curriedTensor (Complexes R) ⋙ (Functor.whiskeringRight _ _ _).obj DerivedCategory.Q)

/-- Naturality of `CochainComplex.KFlatBifunctor.comparisonRight` in the arbitrary left
complex, in the monoidal spelling.  No K-flatness is assumed on the left. -/
theorem derivedComparison_naturality_left
    {C : Type c} [Category.{u} C] {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasDerivedCategory.{d} (Mod R)]
    {K K' L : Complexes R} (f : K ⟶ K')
    (hL : CochainComplex.KFlatBifunctor.KFlat (curriedTensor (Mod R)) L) :
    ((derivedBifunctor (curriedTensor (Mod R))).map (DerivedCategory.Q.map f)).app
          (DerivedCategory.Q.obj L) ≫
        (comparisonRight (curriedTensor (Mod R)) K' L hL).hom =
      (comparisonRight (curriedTensor (Mod R)) K L hL).hom ≫
        DerivedCategory.Q.map (f ▷ L) :=
  comparisonRight_naturality_left (curriedTensor (Mod R)) f L hL

/-- Naturality of `CochainComplex.KFlatBifunctor.comparisonRight` in the K-flat right
complex, in the monoidal spelling. -/
theorem derivedComparison_naturality_right
    {C : Type c} [Category.{u} C] {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasDerivedCategory.{d} (Mod R)]
    (K : Complexes R) {L L' : Complexes R} (g : L ⟶ L')
    (hL : CochainComplex.KFlatBifunctor.KFlat (curriedTensor (Mod R)) L)
    (hL' : CochainComplex.KFlatBifunctor.KFlat (curriedTensor (Mod R)) L') :
    ((derivedBifunctor (curriedTensor (Mod R))).obj (DerivedCategory.Q.obj K)).map
          (DerivedCategory.Q.map g) ≫
        (comparisonRight (curriedTensor (Mod R)) K L' hL').hom =
      (comparisonRight (curriedTensor (Mod R)) K L hL).hom ≫
        DerivedCategory.Q.map (K ◁ g) :=
  comparisonRight_naturality_right (curriedTensor (Mod R)) K g hL hL'

/-- **`derivedBifunctor` descends the same bifunctor.**  Its own lifting datum is along
`kFlatQLeft` in the first variable and `kFlatQ` in the second; read along `kFlatComplexQ` in
both it is the one-sided comparison `CochainComplex.KFlatBifunctor.comparisonRight`, whose
naturality in each variable is already proved. -/
@[instance_reducible]
def derivedBifunctorLifting :
    Localization.Lifting₂ (kFlatComplexQ R) (kFlatComplexQ R)
      (kFlatComplexQuasiIso R) (kFlatComplexQuasiIso R)
      (kFlatTensorSource R) (derivedBifunctor (curriedTensor (Mod R))) where
  iso := NatIso.ofComponents
    (fun X ↦ NatIso.ofComponents
      (fun Y ↦ comparisonRight (curriedTensor (Mod R)) X.1 Y.1 Y.2)
      (fun g ↦ derivedComparison_naturality_right R _ g.hom _ _))
    (fun f ↦ by ext Y; exact derivedComparison_naturality_left R f.hom _)

end Stacks.SheafOfModules.DerivedMonoidalGeneral

end
