module

public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Stacks.Representability
public import StacksFrontier.CategoryTheory.FiberedCategory.SliceAsElements
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.SliceOverMap

/-!
# The big fppf site of a scheme over the base, as a category fibred in groupoids

Let `S` be a scheme contained in a big fppf site `B` and let `U` be a scheme over `S` in that
site. The big fppf site of `U` is a category over the big fppf site of `S` through
`CategoryTheory.Over.map U.hom`, and it is fibred in groupoids — indeed in sets. As an object of
the 2-category of categories fibred in groupoids over the big fppf site of `S` it is
*representable by an algebraic space* in the sense of Stacks 04SV, namely by the algebraic space
`yoneda.obj U` of Stacks 025Z: the category of elements of that representable presheaf *is* the
big fppf site of `U`, over the big fppf site of `S`.

## Main definitions

* `AlgebraicGeometry.Stack.schemeSlice`: the big fppf site of `U` as a category fibred in
  groupoids over the big fppf site of `S`.

## Main results

* `AlgebraicGeometry.Stack.schemeSliceEquivalenceOver`: it is equivalent, over the big fppf site
  of `S`, to the category of elements of `yoneda.obj U`.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_schemeSlice`: **Stacks 04SV** for a
  scheme over the base.

## Implementation notes

The universes are those Stacks 04SV and Stacks 04XC are stated at: the big fppf site of `U` is a
`CategoryTheory.Category.{u}` structure on a `Type (u + 1)`, exactly like the big fppf site of
`S`, so the object of the 2-category lives at
`CategoryTheory.CatFiberedInGroupoids.{u, u, u + 1, u + 1}` with no `max` anywhere.

Fibredness in groupoids is `CategoryTheory.Functor.IsFiberedInGroupoids.over_map`, which needs
nothing about the fppf topology; the equivalence is
`CategoryTheory.PresheafOfCategories.overMapElementsEquivalenceOver` for the structure morphism of
`U`, read through `CategoryTheory.Over.mk U.hom = U`. Algebraicity of the representing presheaf is
Stacks 025Z (`AlgebraicGeometry.isAlgebraicSpace_yoneda`).

## References

* [Stacks Project, Tag 025Z](https://stacks.math.columbia.edu/tag/025Z)
* [Stacks Project, Tag 04SV](https://stacks.math.columbia.edu/tag/04SV)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

/-- The big fppf site of a scheme `U` over `S`, as an object of the 2-category of categories
fibred in groupoids over the big fppf site of `S`: its structure functor is postcomposition with
the structure morphism of `U`, which is fibred in groupoids. -/
def schemeSlice : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
  CatFiberedInGroupoids.mk (BasedCategory.ofFunctor (Over.map U.hom))
    (Functor.IsFiberedInGroupoids.over_map U.hom)

/-- The structure functor of `schemeSlice B S hS U` is postcomposition with the structure
morphism of `U`. -/
@[simp]
lemma schemeSlice_val_p : (schemeSlice B S hS U).val.p = Over.map U.hom := rfl

/-- The big fppf site of `U` is the category of elements of the presheaf represented by `U`, as an
equivalence in the 2-category of categories over the big fppf site of `S`. -/
def schemeSliceEquivalenceOver :
    StacksRepresentableCFG.EquivalenceOver (schemeSlice B S hS U).val.p
      (presheafOfCategories (yoneda.obj U ⋙ typeToCat)).p :=
  PresheafOfCategories.overMapElementsEquivalenceOver U.hom

/-- **Stacks 04SV for a scheme over the base.** The big fppf site of a scheme `U` over `S`, viewed
as a category fibred in groupoids over the big fppf site of `S`, is representable by an algebraic
space over `S`: by the algebraic space `yoneda.obj U` of Stacks 025Z. -/
theorem isRepresentableByAlgebraicSpace_schemeSlice :
    IsRepresentableByAlgebraicSpace B S hS (schemeSlice B S hS U) :=
  ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U, ⟨schemeSliceEquivalenceOver B S hS U⟩⟩

end AlgebraicGeometry.Stack

end
