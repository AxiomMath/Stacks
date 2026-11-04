module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Existence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.CanonicalDerivedTensorComparisonGeneral
import all StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.InterfaceDerivedTensorComparison

/-!
# A derived tensor product datum and the monoidal structure of `D(O)`, at general universes

Let `(C, O)` be a ringed site whose objects live in a universe `c` and whose morphisms and sections
live in the universe `u` of the sheaf of rings. A derived tensor product datum on a ringed site
agrees with the tensor product of the monoidal structure of `D(Mod(O))`, computed on K-flat pairs.

## Implementation notes

This is the part of
`StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.InterfaceDerivedTensorComparison` that does
not need `C` to be a `SmallCategory.{u}`, for a site `C : Type c` with `[Category.{u} C]`; the
statements and proofs are the same, in the namespace
`Stacks.SheafOfModules.DerivedMonoidalGeneral`.
This applies to the small étale ringed site of an algebraic space.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CochainComplex.KFlatBifunctor

universe d c u

namespace Stacks.SheafOfModules.DerivedMonoidalGeneral

variable (X : AlgebraicGeometry.RingedSite.{c, u, u})
variable [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasDerivedCategory.{d} (Mod X.O)]

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  CochainComplex.symmetricCategory

attribute [local instance] kFlatQ_isLocalization kFlatQLeft_isLocalization

/-- `Mod(O)` is monoidal, with the universe arguments of
`SheafOfModules.monoidalCategorySheafTensor` pinned at this file's site and section universes.

The sections universe of that structure is free, so unifying it against the `u` of `Mod X.O`
can leave it undetermined; the whiskerings below cannot reduce through a monoidal structure on
`Comp(Mod(O))` synthesized from one whose universe is still a metavariable. -/
local instance monoidalCategoryModRingedSite : MonoidalCategory (Mod X.O) :=
  SheafOfModules.monoidalCategorySheafTensor.{u, c, u} X.O

variable (T : Stacks.SheafOfModules.DerivedTensorProduct.{c, u, u, d} X)

/-! ### Reading the merged naturality one variable at a time -/

/-- Naturality of the K-flat comparison in the first variable alone, in the monoidal spelling
of the total tensor product. -/
theorem interfaceComparison_naturality_left
    (X : AlgebraicGeometry.RingedSite.{c, u, u})
    [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasDerivedCategory.{d} (Mod X.O)]
    (T : Stacks.SheafOfModules.DerivedTensorProduct.{c, u, u, d} X)
    {K K' L : Complexes X.O} (f : K ⟶ K')
    (hK : Stacks.SheafOfModules.IsKFlat X.O K) (hK' : Stacks.SheafOfModules.IsKFlat X.O K')
    (hL : Stacks.SheafOfModules.IsKFlat X.O L) :
    (T.tensor.map (DerivedCategory.Q.map f)).app (DerivedCategory.Q.obj L) ≫
        (T.comparison K' L hK' hL).hom =
      (T.comparison K L hK hL).hom ≫ DerivedCategory.Q.map (f ▷ L) :=
  DerivedMonoidal.comp_id_comp_eq (T.comparison_naturality f (𝟙 L) hK hK' hL hL)
    (by rw [DerivedCategory.Q.map_id, CategoryTheory.Functor.map_id])

/-- Naturality of the K-flat comparison in the second variable alone. -/
theorem interfaceComparison_naturality_right
    (X : AlgebraicGeometry.RingedSite.{c, u, u})
    [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasDerivedCategory.{d} (Mod X.O)]
    (T : Stacks.SheafOfModules.DerivedTensorProduct.{c, u, u, d} X)
    (K : Complexes X.O) {L L' : Complexes X.O}
    (g : L ⟶ L') (hK : Stacks.SheafOfModules.IsKFlat X.O K)
    (hL : Stacks.SheafOfModules.IsKFlat X.O L)
    (hL' : Stacks.SheafOfModules.IsKFlat X.O L') :
    (T.tensor.obj (DerivedCategory.Q.obj K)).map (DerivedCategory.Q.map g) ≫
        (T.comparison K L' hK hL').hom =
      (T.comparison K L hK hL).hom ≫ DerivedCategory.Q.map (K ◁ g) :=
  DerivedMonoidal.id_comp_comp_eq (T.comparison_naturality (𝟙 K) g hK hK hL hL')
    (by rw [DerivedCategory.Q.map_id, CategoryTheory.Functor.map_id, NatTrans.id_app])

/-! ### The descent -/

/-- **The bifunctor of a `Stacks.SheafOfModules.DerivedTensorProduct` descends the total tensor
product of K-flat complexes.** The lifting isomorphism is the `comparison` field, and its two
naturality squares are the merged naturality field read one variable at a time. -/
@[instance_reducible]
def interfaceTensorLifting
    (X : AlgebraicGeometry.RingedSite.{c, u, u})
    [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasDerivedCategory.{d} (Mod X.O)]
    (T : Stacks.SheafOfModules.DerivedTensorProduct.{c, u, u, d} X) :
    Localization.Lifting₂ (kFlatComplexQ X.O) (kFlatComplexQ X.O)
      (kFlatComplexQuasiIso X.O) (kFlatComplexQuasiIso X.O)
      (kFlatTensorSource X.O) T.tensor where
  iso := NatIso.ofComponents
    (fun A ↦ NatIso.ofComponents (fun B ↦ T.comparison A.1 B.1 A.2 B.2)
      (fun g ↦ interfaceComparison_naturality_right X T _ g.hom _ _ _))
    (fun f ↦ by ext B; exact interfaceComparison_naturality_left X T f.hom _ _ _)

attribute [local instance] interfaceTensorLifting derivedBifunctorLifting

/-! ### The comparison -/

/-- **The derived tensor bifunctor of `CochainComplex.KFlatBifunctor` is the bifunctor of any
`Stacks.SheafOfModules.DerivedTensorProduct`.** Both descend the total tensor product of K-flat
complexes along `Stacks.SheafOfModules.DerivedMonoidalGeneral.kFlatComplexQ` in each variable, so
the comparison is `CategoryTheory.Localization.lift₂NatIso` of the identity. -/
def interfaceDerivedBifunctorTensorIso
    (X : AlgebraicGeometry.RingedSite.{c, u, u})
    [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasDerivedCategory.{d} (Mod X.O)]
    (T : Stacks.SheafOfModules.DerivedTensorProduct.{c, u, u, d} X) :
    derivedBifunctor (curriedTensor (Mod X.O)) ≅ T.tensor :=
  Localization.lift₂NatIso (kFlatComplexQ X.O) (kFlatComplexQ X.O)
    (kFlatComplexQuasiIso X.O) (kFlatComplexQuasiIso X.O)
    (kFlatTensorSource X.O) (kFlatTensorSource X.O)
    (derivedBifunctor (curriedTensor (Mod X.O))) T.tensor (Iso.refl _)

/-- **The comparison, computed on a pair of K-flat complexes**: the one-sided K-flat comparison
of `derivedBifunctor` followed by the inverse of the K-flat comparison of the given derived
tensor product. -/
theorem interfaceDerivedBifunctorTensorIso_hom_app_app
    (X : AlgebraicGeometry.RingedSite.{c, u, u})
    [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasDerivedCategory.{d} (Mod X.O)]
    (T : Stacks.SheafOfModules.DerivedTensorProduct.{c, u, u, d} X)
    (K L : Complexes X.O)
    (hK : Stacks.SheafOfModules.IsKFlat X.O K) (hL : Stacks.SheafOfModules.IsKFlat X.O L) :
    ((interfaceDerivedBifunctorTensorIso X T).hom.app (DerivedCategory.Q.obj K)).app
        (DerivedCategory.Q.obj L) =
      (comparisonRight (curriedTensor (Mod X.O)) K L hL).hom ≫ (T.comparison K L hK hL).inv := by
  refine (Localization.lift₂NatTrans_app_app (kFlatComplexQ X.O) (kFlatComplexQ X.O)
    (kFlatComplexQuasiIso X.O) (kFlatComplexQuasiIso X.O)
    (kFlatTensorSource X.O) (kFlatTensorSource X.O)
    (derivedBifunctor (curriedTensor (Mod X.O))) T.tensor (Iso.refl _).hom
    (⟨K, hK⟩ : (KFlatComplexes X.O).FullSubcategory)
    (⟨L, hL⟩ : (KFlatComplexes X.O).FullSubcategory)).trans ?_
  simp only [Iso.refl_hom, NatTrans.id_app, Category.id_comp]
  rfl

end Stacks.SheafOfModules.DerivedMonoidalGeneral

end
