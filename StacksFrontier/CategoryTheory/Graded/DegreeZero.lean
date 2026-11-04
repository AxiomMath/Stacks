module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Graded.Category

/-!
# The degree-zero category of a graded category

For a category graded over a ring `R`, the homogeneous morphisms of degree zero are closed under
composition and contain the identities, so they form a category with the same objects. This is
the category underlying the graded category, and the construction that turns a differential
graded category into the ordinary categories of complexes and of homotopy classes.

## Main definitions

* `CategoryTheory.GradedCategory.DegreeZero`: the objects of a graded category, carrying the
  category structure whose morphisms are the degree-zero homogeneous morphisms.
* `CategoryTheory.GradedCategory.DegreeZero.Hom`: the displayed formula for its morphisms.

## Implementation notes

`DegreeZero` is a type synonym of the object type, so that it can carry a category structure
different from the ambient one; it is implicitly reducible, so clients may use the same object
expressions in the ambient and in the degree-zero category. The identity and the composition are
given by `DegreeZero.identity` and `DegreeZero.comp`, whose only content beyond the ambient ones
is the verification that degree zero is preserved; the category laws then follow from the ambient
ones by `Subtype.ext`.

## References

* [Stacks Project, Tag 09ML](https://stacks.math.columbia.edu/tag/09ML)
-/

@[expose] public section

namespace CategoryTheory.GradedCategory

universe w v u

/-- The degree-zero category of a graded category. It has the same objects as the ambient
category, and its morphisms are the homogeneous morphisms of degree zero. -/
@[implicit_reducible, stacks 09ML]
def DegreeZero (_R : Type w) (C : Type u) := C

namespace DegreeZero

variable (R : Type w) [Ring R] (C : Type u) [Category.{v} C] [Preadditive C] [GradedCategory R C]

/-- The degree-zero homogeneous morphisms between two objects. -/
@[stacks 09ML]
abbrev Hom (X Y : DegreeZero R C) : Type v :=
  GradedCategory.grade (R := R) (show C from X) (show C from Y) 0

/-- The identity of an object of the degree-zero category. -/
def identity (X : DegreeZero R C) : Hom R C X X :=
  ⟨𝟙 (show C from X), GradedCategory.id_mem (R := R) _⟩

/-- Composition of degree-zero homogeneous morphisms. -/
def comp {X Y Z : DegreeZero R C} (f : Hom R C X Y) (g : Hom R C Y Z) : Hom R C X Z :=
  ⟨f.1 ≫ g.1, by simpa using GradedCategory.comp_mem (R := R) g.2 f.2⟩

/-- Composition and identities of a graded category restrict to its degree-zero morphisms. -/
@[stacks 09ML]
instance : Category.{v} (DegreeZero R C) where
  Hom := Hom R C
  id := identity R C
  comp := comp R C
  id_comp f := by apply Subtype.ext; exact Category.id_comp _
  comp_id f := by apply Subtype.ext; exact Category.comp_id _
  assoc f g h := by apply Subtype.ext; exact Category.assoc _ _ _

end DegreeZero

end CategoryTheory.GradedCategory
