module

public import StacksFrontier.Algebra.Homology.HomotopyCategory.AdjunctionComparison
public import StacksFrontier.Algebra.Homology.HomotopyCategory.InducedCommShift

/-!
# The adjunction induced on homotopy categories commutes with the shift

An adjunction `F ⊣ G` between additive functors induces an adjunction between the functors
induced on the homotopy categories of cochain complexes indexed by `ℤ`
(`CategoryTheory.Adjunction.mapHomotopyCategory`). Its unit is the degreewise unit, which
commutes with the shift; so the induced adjunction is compatible with the shifts.

## Main results

* `CategoryTheory.commShift_mapHomotopyCategoryIdIso`: the comparison of the functor induced by
  the identity with the identity commutes with the shift.
* `CategoryTheory.Adjunction.commShift_mapHomotopyCategory_unit`: the unit of the induced
  adjunction commutes with the shift.
* `CategoryTheory.Adjunction.commShift_mapHomotopyCategory`: the induced adjunction is compatible
  with the shifts.
-/

@[expose] public section

universe v u v' u'

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {A : Type u} [Category.{v} A] [Preadditive A] {B : Type u'} [Category.{v'} B]
  [Preadditive B]

/-- **The comparison of the functor induced by the identity with the identity commutes with
the shift**: after restriction along the quotient it is the degreewise comparison, which does. -/
instance commShift_mapHomotopyCategoryIdIso :
    NatTrans.CommShift (Functor.mapHomotopyCategoryIdIso A (ComplexShape.up ℤ)).hom ℤ := by
  refine NatTrans.commShift_of_whiskerLeft
    (HomotopyCategory.quotient A (ComplexShape.up ℤ)) _ ?_
  refine NatTrans.commShift_of_eq (θ :=
    ((𝟭 A).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom ≫
      Functor.whiskerRight (Functor.mapHomologicalComplexIdIso A (ComplexShape.up ℤ)).hom
        (HomotopyCategory.quotient A (ComplexShape.up ℤ)) ≫
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)).leftUnitor.hom ≫
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)).rightUnitor.inv) ?_
  ext K
  exact ((Category.id_comp (obj := HomotopyCategory A (ComplexShape.up ℤ)) _).trans
    ((congrArg (_ ≫ ·) (Category.id_comp (obj := HomotopyCategory A (ComplexShape.up ℤ)) _)).trans
      (Category.comp_id (obj := HomotopyCategory A (ComplexShape.up ℤ)) _))).symm

/-- **The unit of the adjunction induced on homotopy categories commutes with the shift.** -/
instance Adjunction.commShift_mapHomotopyCategory_unit {F : A ⥤ B} {G : B ⥤ A} [F.Additive]
    [G.Additive] (adj : F ⊣ G) :
    NatTrans.CommShift (adj.mapHomotopyCategory (ComplexShape.up ℤ)).unit ℤ := by
  rw [Adjunction.mapHomotopyCategory_unit_eq]
  infer_instance

/-- **The adjunction induced on homotopy categories is compatible with the shifts.** -/
instance Adjunction.commShift_mapHomotopyCategory {F : A ⥤ B} {G : B ⥤ A} [F.Additive]
    [G.Additive] (adj : F ⊣ G) :
    (adj.mapHomotopyCategory (ComplexShape.up ℤ)).CommShift ℤ :=
  Adjunction.CommShift.mk' _ _ inferInstance

end CategoryTheory
