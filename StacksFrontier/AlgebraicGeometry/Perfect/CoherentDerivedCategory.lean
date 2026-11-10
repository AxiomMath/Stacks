module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Coherent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentWeakSerre
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.AbelianCategory
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak

/-!
# The derived category of coherent modules

For a sheaf of rings on a topological space, the inclusion of the coherent sheaves of modules
into all sheaves of modules is exact, so it induces a functor on derived categories. Its image
lands in the full subcategory of objects whose cohomology sheaves are all coherent, and the
induced comparison functor is compatible with that inclusion.

## Main definitions

* `Stacks.SheafOfModules.coherentDerivedComparison` is the canonical functor from the derived
  category of coherent modules to the subcategory of the derived category with coherent
  cohomology.
* `Stacks.SheafOfModules.coherentDerivedComparison_comp_inclusion` identifies its composite
  with the inclusion as the derived functor of the inclusion of coherent modules.

## Main results

* `Stacks.SheafOfModules.coherentDerivedComparison_mem` states that the derived inclusion of
  coherent modules has coherent cohomology in every degree.

## Implementation notes

Coherent modules form a weak Serre subcategory, which is what makes the inclusion preserve
finite limits and finite colimits and hence additive; those three instances are installed
locally in each statement, exactly where the derived functor is formed, on top of the abelian
structure `Stacks.SheafOfModules.coherentModulesAbelian`. Cohomology commutes with an exact
functor on derived categories, which is what identifies the cohomology sheaves of the derived
inclusion.

## References

* [Stacks Project, Tag 08E1](https://stacks.math.columbia.edu/tag/08E1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

universe w w' v v' u'

/-- Homology commutes with an exact functor on the derived category. -/
private noncomputable def homologyMapDerivedCategoryObjIso
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : DerivedCategory C) (n : ℤ) :
    (DerivedCategory.homologyFunctor D n).obj (F.mapDerivedCategory.obj K) ≅
      F.obj ((DerivedCategory.homologyFunctor C n).obj K) := by
  let P := DerivedCategory.Q.objPreimage K
  let e := DerivedCategory.Q.objObjPreimageIso K
  exact (DerivedCategory.homologyFunctor D n).mapIso (F.mapDerivedCategory.mapIso e.symm) ≪≫
    (DerivedCategory.homologyFunctor D n).mapIso (F.mapDerivedCategoryFactors.app P) ≪≫
    (DerivedCategory.homologyFunctorFactors D n).app
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≪≫
    (P.sc n).mapHomologyIso F ≪≫
    F.mapIso ((DerivedCategory.homologyFunctorFactors C n).app P).symm ≪≫
    F.mapIso ((DerivedCategory.homologyFunctor C n).mapIso e)

/-- **Stacks Project, Tag 08E1.** The derived inclusion of coherent modules has coherent
cohomology in every degree. -/
@[stacks 08E1 "well-definedness"]
theorem coherentDerivedComparison_mem
    {X : Type u} [TopologicalSpace X]
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) :
    let P : ObjectProperty (_root_.SheafOfModules.{u} R) := fun M => IsCoherent M
    letI : Preadditive P.FullSubcategory := Abelian.toPreadditive
    letI : Preadditive (_root_.SheafOfModules.{u} R) := Abelian.toPreadditive
    let I : P.FullSubcategory ⥤ _root_.SheafOfModules.{u} R := P.ι
    letI : PreservesFiniteLimits I :=
      ObjectProperty.preservesFiniteLimits_ι_of_isWeakSerreClass P
    letI : PreservesFiniteColimits I :=
      ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass P
    letI : I.Additive := I.additive_of_preserves_binary_products
    ∀ K : DerivedCategory (CoherentModules R),
      (DerivedCategoryB.derivedCategoryB P) (I.mapDerivedCategory.obj K) := by
  let P : ObjectProperty (_root_.SheafOfModules.{u} R) := fun M => IsCoherent M
  let : Preadditive P.FullSubcategory := Abelian.toPreadditive
  let : Preadditive (_root_.SheafOfModules.{u} R) := Abelian.toPreadditive
  let I : P.FullSubcategory ⥤ _root_.SheafOfModules.{u} R := P.ι
  let : PreservesFiniteLimits I :=
    ObjectProperty.preservesFiniteLimits_ι_of_isWeakSerreClass P
  let : PreservesFiniteColimits I :=
    ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass P
  let : I.Additive := I.additive_of_preserves_binary_products
  change ∀ K : DerivedCategory P.FullSubcategory, ∀ i : ℤ,
    P ((DerivedCategory.homologyFunctor (_root_.SheafOfModules R) i).obj
      (I.mapDerivedCategory.obj K))
  intro K i
  exact ObjectProperty.prop_of_iso P (homologyMapDerivedCategoryObjIso I K i).symm
    (P.prop_ι_obj ((DerivedCategory.homologyFunctor P.FullSubcategory i).obj K))

/-- **Stacks Project, Tag 08E1.** The canonical functor from the derived category of coherent
modules to the subcategory of the derived category with coherent cohomology. -/
@[stacks 08E1 "comparison functor"]
noncomputable def coherentDerivedComparison
    {X : Type u} [TopologicalSpace X]
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) :
    DerivedCategory (CoherentModules R) ⥤
      (DerivedCategoryB.derivedCategoryB
        (fun M : _root_.SheafOfModules.{u} R => IsCoherent M)).FullSubcategory := by
  let P : ObjectProperty (_root_.SheafOfModules.{u} R) := fun M => IsCoherent M
  letI : Preadditive P.FullSubcategory := Abelian.toPreadditive
  letI : Preadditive (_root_.SheafOfModules.{u} R) := Abelian.toPreadditive
  let I : P.FullSubcategory ⥤ _root_.SheafOfModules.{u} R := P.ι
  letI : PreservesFiniteLimits I :=
    ObjectProperty.preservesFiniteLimits_ι_of_isWeakSerreClass P
  letI : PreservesFiniteColimits I :=
    ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass P
  letI : I.Additive := I.additive_of_preserves_binary_products
  exact (DerivedCategoryB.derivedCategoryB P).lift I.mapDerivedCategory
    (coherentDerivedComparison_mem R)

/-- **Stacks Project, Tag 08E1.** Forgetting the coherence condition after comparison gives the
derived functor of the inclusion of coherent modules. -/
@[stacks 08E1 "canonical comparison"]
noncomputable def coherentDerivedComparison_comp_inclusion
    {X : Type u} [TopologicalSpace X]
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) :
    let P : ObjectProperty (_root_.SheafOfModules.{u} R) := fun M => IsCoherent M
    letI : Preadditive P.FullSubcategory := Abelian.toPreadditive
    letI : Preadditive (_root_.SheafOfModules.{u} R) := Abelian.toPreadditive
    let I : P.FullSubcategory ⥤ _root_.SheafOfModules.{u} R := P.ι
    letI : PreservesFiniteLimits I :=
      ObjectProperty.preservesFiniteLimits_ι_of_isWeakSerreClass P
    letI : PreservesFiniteColimits I :=
      ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass P
    letI : I.Additive := I.additive_of_preserves_binary_products
    coherentDerivedComparison R ⋙ (DerivedCategoryB.derivedCategoryB P).ι ≅
      I.mapDerivedCategory := by
  let P : ObjectProperty (_root_.SheafOfModules.{u} R) := fun M => IsCoherent M
  letI : Preadditive P.FullSubcategory := Abelian.toPreadditive
  letI : Preadditive (_root_.SheafOfModules.{u} R) := Abelian.toPreadditive
  let I : P.FullSubcategory ⥤ _root_.SheafOfModules.{u} R := P.ι
  letI : PreservesFiniteLimits I :=
    ObjectProperty.preservesFiniteLimits_ι_of_isWeakSerreClass P
  letI : PreservesFiniteColimits I :=
    ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass P
  letI : I.Additive := I.additive_of_preserves_binary_products
  exact ObjectProperty.liftCompιIso _ _ _

end Stacks.SheafOfModules
