module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRepresentableBaseChangeComp

/-!
# The two spellings of a composite of represented morphisms

A composite `representedSpaceMap a ≫ representedSpaceMap b` of represented morphisms of algebraic
spaces is elaborated with the category structure at the type `AlgebraicSpaces B S hS` when it
comes from a lemma at variable algebraic spaces, and at the unfolded full subcategory when it is
written between the anonymous constructors in the type of
`AlgebraicGeometry.Space.representedSpaceMap`.  The two are definitionally equal; this file states
the equality once, so that it is rewritten rather than unified inside larger terms.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A composite of represented morphisms, with the category structure of `AlgebraicSpaces`, is the
composite with the category structure of the full subcategory. -/
theorem representedSpaceMap_comp_algebraicSpaces {V W Z : BigFppfOver B S hS} (a : V ⟶ W)
    (b : W ⟶ Z) :
    @CategoryStruct.comp (AlgebraicSpaces B S hS) _ ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
        ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩
        ⟨yoneda.obj Z, isAlgebraicSpace_yoneda B S hS Z⟩
        (representedSpaceMap B S hS a) (representedSpaceMap B S hS b) =
      representedSpaceMap B S hS a ≫ representedSpaceMap B S hS b :=
  rfl

/-- The represented morphisms of two composites that agree have composites that agree, as
morphisms of `AlgebraicSpaces`. -/
theorem representedSpaceMap_comp_eq_of_comp_eq {V W W' Z : BigFppfOver B S hS} {a : V ⟶ W}
    {b : W ⟶ Z} {c : V ⟶ W'} {d : W' ⟶ Z} (h : a ≫ b = c ≫ d) :
    CategoryStruct.comp (obj := AlgebraicSpaces B S hS) (representedSpaceMap B S hS a)
        (representedSpaceMap B S hS b) =
      CategoryStruct.comp (obj := AlgebraicSpaces B S hS) (representedSpaceMap B S hS c)
        (representedSpaceMap B S hS d) :=
  ((representedSpaceMap_comp_algebraicSpaces B S hS a b).trans
    (representedSpaceMap_comp B S hS a b)).trans
    ((congrArg (representedSpaceMap B S hS) h).trans
      ((representedSpaceMap_comp_algebraicSpaces B S hS c d).trans
        (representedSpaceMap_comp B S hS c d)).symm)

end AlgebraicGeometry.Space
