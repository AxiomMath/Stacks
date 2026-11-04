module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupActions
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeAutomorphismTotalPresheaf
public import StacksFrontier.CategoryTheory.FiberedCategory.ElementsTotalEquivalence

/-!
# Stacks 06PP, part (1): the group algebraic space `Isom_{𝒳/𝒴}(x, x)` over `Z`

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`, let `Z` be an algebraic space over
`S` and let `x : Z ⟶ 𝒳` be an algebraic-space-valued point. Then `Isom_{𝒳/𝒴}(x, x)` is a group
algebraic space over `Z`. Its underlying object of `CategoryTheory.Over Z` is
`AlgebraicGeometry.Stack.relativeAutomorphismSpaceOver`, and its group law is the group object
`AlgebraicGeometry.Stack.relativeAutomorphismPresheafGrpObj` of presheaves on the category of
elements of `Z`, carried along the monoidal equivalence `PSh(El Z) ≌ CategoryTheory.Over Z` of
`CategoryTheory.PresheafOfCategories.elementsTotalFunctor`.

## Main definitions

* `AlgebraicGeometry.Stack.relativeAutomorphismSpaceOverGrpObj`: the group-object structure on
  `Isom_{𝒳/𝒴}(x, x)` as an object of `CategoryTheory.Over Z`.
* `AlgebraicGeometry.Stack.relativeAutomorphismGroupAlgebraicSpace`: `Isom_{𝒳/𝒴}(x, x)` as a
  group algebraic space over `Z`.

## Main results

* `AlgebraicGeometry.Stack.relativeAutomorphismGroupAlgebraicSpace_X` and
  `AlgebraicGeometry.Stack.relativeAutomorphismGroupAlgebraicSpace_left`: the object of the slice
  underlying the group algebraic space is `relativeAutomorphismSpaceOver`, and the presheaf
  underlying that is `relativeAutomorphismTotalPresheaf`.

## References

* [Stacks Project, Tag 043H](https://stacks.math.columbia.edu/tag/043H)
* [Stacks Project, Tag 050R](https://stacks.math.columbia.edu/tag/050R)
* [Stacks Project, Tag 06PP](https://stacks.math.columbia.edu/tag/06PP)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hZ : IsAlgebraicSpace B S hS Z)
variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- The group law on `Isom_{𝒳/𝒴}(x, x)` as an object over `Z`: the group object of presheaves on
the category of elements of `Z` whose sections at a point `a` are the automorphisms of `x(a)`
killed by `f` (`AlgebraicGeometry.Stack.relativeAutomorphismPresheafGrpObj`), carried along the
product-preserving equivalence `PSh(El Z) ≌ CategoryTheory.Over Z` of
`CategoryTheory.PresheafOfCategories.elementsTotalEquivalence`. The multiplication is the one
induced on the fibre product over `Z` by composition of relative automorphisms. -/
@[instance_reducible]
noncomputable def relativeAutomorphismSpaceOverGrpObj (f : 𝒳 ⟶ 𝒴)
    (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :
    GrpObj (relativeAutomorphismSpaceOver B S hS Z hZ f x) :=
  letI := PresheafOfCategories.elementsTotalFunctorMonoidal Z
  let P : ((presheafOfCategories (Z ⋙ typeToCat)).obj)ᵒᵖ ⥤ Type u :=
    relativeAutomorphismPresheaf B S hS Z hZ f x
  letI : GrpObj P := relativeAutomorphismPresheafGrpObj B S hS Z hZ f x
  Functor.grpObjObj (F := PresheafOfCategories.elementsTotalFunctor Z) (G := P)

/-- The inverse of the group object over `Z` is the image under the total-presheaf functor of the
inverse of the presheaf of groups: on a pair `(z, φ)` it is the inverse automorphism `φ⁻¹` at the
same point `z` of `Z`. -/
theorem relativeAutomorphismSpaceOverGrpObj_inv (f : 𝒳 ⟶ 𝒴)
    (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :
    GrpObj.inv (X := relativeAutomorphismSpaceOver B S hS Z hZ f x)
        (self := relativeAutomorphismSpaceOverGrpObj B S hS Z hZ f x) =
      (PresheafOfCategories.elementsTotalFunctor Z).map
        (GrpObj.inv (X := relativeAutomorphismPresheaf B S hS Z hZ f x)
          (self := relativeAutomorphismPresheafGrpObj B S hS Z hZ f x)) :=
  rfl

/-- `Isom_{𝒳/𝒴}(x, x)` as a group algebraic space over `Z`: the presheaf on the big fppf site
whose sections over `W` are the pairs of a point `z` of `Z` over `W` and an automorphism of `x(z)`
killed by `f`, together with its structure morphism to `Z`, the group law given by composition of
automorphisms, and the algebraicity of that presheaf. -/
@[stacks 06PP
  "part (1): Isom_{X/Y}(x, x) is a group algebraic space over Z, group law and algebraicity"]
noncomputable def relativeAutomorphismGroupAlgebraicSpace (f : 𝒳 ⟶ 𝒴)
    (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :
    Space.GroupAlgebraicSpace B S hS Z hZ where
  obj := { X := relativeAutomorphismSpaceOver B S hS Z hZ f x
           grp := relativeAutomorphismSpaceOverGrpObj B S hS Z hZ f x }
  property := isAlgebraicSpace_relativeAutomorphismSpaceOver_left B S hS Z hZ f x

/-- The object of `CategoryTheory.Over Z` underlying the group algebraic space
`relativeAutomorphismGroupAlgebraicSpace` is
`AlgebraicGeometry.Stack.relativeAutomorphismSpaceOver`. -/
@[simp] theorem relativeAutomorphismGroupAlgebraicSpace_X (f : 𝒳 ⟶ 𝒴)
    (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :
    (relativeAutomorphismGroupAlgebraicSpace B S hS Z hZ f x).obj.X =
      relativeAutomorphismSpaceOver B S hS Z hZ f x :=
  rfl

/-- The presheaf on the big fppf site underlying the group algebraic space
`relativeAutomorphismGroupAlgebraicSpace` is
`AlgebraicGeometry.Stack.relativeAutomorphismTotalPresheaf`. -/
@[simp] theorem relativeAutomorphismGroupAlgebraicSpace_left (f : 𝒳 ⟶ 𝒴)
    (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :
    (relativeAutomorphismGroupAlgebraicSpace B S hS Z hZ f x).obj.X.left =
      relativeAutomorphismTotalPresheaf B S hS Z hZ f x :=
  rfl

end AlgebraicGeometry.Stack

end
