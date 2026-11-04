module

public import Mathlib.Algebra.Homology.HomotopyCategory

/-!
# An adjunction of additive functors descends to the homotopy categories

Let `F ⊣ G` be an adjunction of additive functors between preadditive categories. Applying `F`
and `G` degreewise to homological complexes gives an adjunction between the induced functors on
the homotopy categories, whose unit and counit are the images of the degreewise unit and counit.

## Main definitions

* `CategoryTheory.Adjunction.mapHomotopyCategory`: the induced adjunction between the homotopy
  categories, with the degreewise unit and counit.

## References

* [Stacks Project, Tag 09T5](https://stacks.math.columbia.edu/tag/09T5)
-/

@[expose] public noncomputable section

namespace CategoryTheory

universe v u v' u'

variable {ι : Type*} {V : Type u} [Category.{v} V] [Preadditive V] {W : Type u'}
  [Category.{v'} W] [Preadditive W]

/-- An adjunction `F ⊣ G` of additive functors induces an adjunction between the induced
functors on the homotopy categories of homological complexes, with the degreewise unit and
counit. -/
def Adjunction.mapHomotopyCategory {F : V ⥤ W} {G : W ⥤ V} [F.Additive] [G.Additive]
    (adj : F ⊣ G) (c : ComplexShape ι) :
    F.mapHomotopyCategory c ⊣ G.mapHomotopyCategory c where
  unit :=
    { app := fun X ↦ (HomotopyCategory.quotient V c).map
        ((NatTrans.mapHomologicalComplex adj.unit c).app X.as)
      naturality := by
        rintro ⟨K⟩ ⟨L⟩ ⟨f : K ⟶ L⟩
        change (HomotopyCategory.quotient V c).map f ≫ (HomotopyCategory.quotient V c).map _ =
          (HomotopyCategory.quotient V c).map _ ≫ (HomotopyCategory.quotient V c).map _
        exact ((HomotopyCategory.quotient V c).map_comp _ _).symm.trans
          ((congrArg (HomotopyCategory.quotient V c).map
            ((NatTrans.mapHomologicalComplex adj.unit c).naturality f)).trans
              ((HomotopyCategory.quotient V c).map_comp _ _)) }
  counit :=
    { app := fun X ↦ (HomotopyCategory.quotient W c).map
        ((NatTrans.mapHomologicalComplex adj.counit c).app X.as)
      naturality := by
        rintro ⟨K⟩ ⟨L⟩ ⟨f : K ⟶ L⟩
        change (HomotopyCategory.quotient W c).map _ ≫ (HomotopyCategory.quotient W c).map _ =
          (HomotopyCategory.quotient W c).map _ ≫ (HomotopyCategory.quotient W c).map f
        exact ((HomotopyCategory.quotient W c).map_comp _ _).symm.trans
          ((congrArg (HomotopyCategory.quotient W c).map
            ((NatTrans.mapHomologicalComplex adj.counit c).naturality f)).trans
              ((HomotopyCategory.quotient W c).map_comp _ _)) }
  left_triangle_components := by
    rintro ⟨K⟩
    refine ((HomotopyCategory.quotient W c).map_comp
      ((F.mapHomologicalComplex c).map ((NatTrans.mapHomologicalComplex adj.unit c).app K))
      ((NatTrans.mapHomologicalComplex adj.counit c).app
        ((F.mapHomologicalComplex c).obj K))).symm.trans
      ((congrArg (HomotopyCategory.quotient W c).map ?_).trans
        ((HomotopyCategory.quotient W c).map_id _))
    ext n
    simp
  right_triangle_components := by
    rintro ⟨K⟩
    refine ((HomotopyCategory.quotient V c).map_comp
      ((NatTrans.mapHomologicalComplex adj.unit c).app ((G.mapHomologicalComplex c).obj K))
      ((G.mapHomologicalComplex c).map
        ((NatTrans.mapHomologicalComplex adj.counit c).app K))).symm.trans
      ((congrArg (HomotopyCategory.quotient V c).map ?_).trans
        ((HomotopyCategory.quotient V c).map_id _))
    ext n
    simp

variable {F : V ⥤ W} {G : W ⥤ V} [F.Additive] [G.Additive] (adj : F ⊣ G) (c : ComplexShape ι)

/-- The unit of `Adjunction.mapHomotopyCategory` is the degreewise unit. -/
@[simp]
lemma Adjunction.mapHomotopyCategory_unit_app (X : HomotopyCategory V c) :
    (adj.mapHomotopyCategory c).unit.app X = (HomotopyCategory.quotient V c).map
      ((NatTrans.mapHomologicalComplex adj.unit c).app X.as) :=
  rfl

/-- The counit of `Adjunction.mapHomotopyCategory` is the degreewise counit. -/
@[simp]
lemma Adjunction.mapHomotopyCategory_counit_app (X : HomotopyCategory W c) :
    (adj.mapHomotopyCategory c).counit.app X = (HomotopyCategory.quotient W c).map
      ((NatTrans.mapHomologicalComplex adj.counit c).app X.as) :=
  rfl

end CategoryTheory

end
