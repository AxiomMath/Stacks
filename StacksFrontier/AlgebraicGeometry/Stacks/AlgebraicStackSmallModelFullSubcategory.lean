module

public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackSmallModelOpenSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordLocus
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverFullSubcategory

/-!
# An open substack of a small model is the full subcategory of the moduli stack itself

`AlgebraicGeometry.Stack.exists_smallModelOpenSubstack_property_eq` produces, from a property `Q`
of the objects of an algebraic stack `𝒳` whose hom types need not be small, an open substack of
the small model `AlgebraicGeometry.Stack.AlgebraicStacks.smallModel` of `𝒳`, cut out by `Q` read
on the objects of the small model. That open substack is an object of the 2-category of algebraic
stacks of Stacks 03YP, and so has `u`-small hom types; the full subcategory `Q.FullSubcategory`
of `𝒳` itself does not.

This file identifies the two, over the big fppf site: the open substack of the small model is
equivalent *over the site* to `Q.FullSubcategory`, by
`AlgebraicGeometry.Stack.OpenSubstack.equivalenceOverFullSubcategory`. Both 1-morphisms of the
equivalence commute strictly with the structure functors, which is what lets a moduli description
proved about `Q.FullSubcategory` be transported to a 1-morphism of categories fibred in groupoids
out of the open substack.

The construction is `StacksRepresentableCFG.EquivalenceOver.fullSubcategory` applied to
`AlgebraicGeometry.Stack.AlgebraicStacks.smallModelEquivalenceOver`: the property of the objects
of the small model is, by definition, the pullback of `Q` along the backward functor of that
equivalence.

## Main results

* `AlgebraicGeometry.Stack.smallModelObjectProperty_eq_inverseImage`: the property of the objects
  of the small model is the pullback of `Q` along the comparison out of the small model.
* `AlgebraicGeometry.Stack.smallModelFullSubcategoryEquivalenceOver`: the full subcategory of the
  small model cut out by `Q` is equivalent over the site to `Q.FullSubcategory`.
* `AlgebraicGeometry.Stack.OpenSubstack.equivalenceOverFullSubcategory`: the same for an open
  substack of the small model cut out by `Q`.

## References

* [Stacks Project, Tag 03YP](https://stacks.math.columbia.edu/tag/03YP)
* [Stacks Project, Tag 03YQ](https://stacks.math.columbia.edu/tag/03YQ)
* [Stacks Project, Tag 04YM](https://stacks.math.columbia.edu/tag/04YM)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w v

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : BasedCategory.{v, u + 1} (BigFppfOver B S hS)}

/-- **The property of the objects of the small model attached to a property `Q` of the objects of
`𝒳` is the pullback of `Q`** along the comparison functor out of the small model. This is
`AlgebraicGeometry.Stack.smallModelObjectProperty` unfolded. -/
theorem smallModelObjectProperty_eq_inverseImage (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳)
    (Q : ObjectProperty 𝒳.obj) :
    smallModelObjectProperty B S hS h𝒳 Q =
      Q.inverseImage (AlgebraicStacks.smallModelEquivalenceOver B S hS 𝒳 h𝒳).inv.functor :=
  rfl

/-- **The full subcategory of the small model cut out by a property of the objects is equivalent
over the site to the full subcategory of the moduli stack itself.** The small model has the same
objects as `𝒳` and only smaller hom types, and the property of its objects is `Q` read through
the comparison, so the two full subcategories are the restrictions of the comparison equivalence;
both 1-morphisms are strictly over the site. -/
def smallModelFullSubcategoryEquivalenceOver (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳)
    (Q : ObjectProperty 𝒳.obj) (hQ : Q.IsClosedUnderIsomorphisms) :
    StacksRepresentableCFG.EquivalenceOver
      ((smallModelObjectProperty B S hS h𝒳 Q).ι ⋙
        (AlgebraicStacks.smallModel B S hS 𝒳 h𝒳).val.val.p)
      (Q.ι ⋙ 𝒳.p) :=
  haveI := hQ
  (AlgebraicStacks.smallModelEquivalenceOver B S hS 𝒳 h𝒳).fullSubcategory Q

/-- **An open substack of the small model cut out by a property of the objects is equivalent over
the site to the full subcategory of the moduli stack itself.** This is
`AlgebraicGeometry.Stack.smallModelFullSubcategoryEquivalenceOver` read at the open substack
`AlgebraicGeometry.Stack.exists_smallModelOpenSubstack_property_eq` produces: an open substack is
the full subcategory its property selects, so only the identification of the properties is
needed.

This is the first link of the identification the smoothness clause of **Stacks 0DQ0** needs: the
relatively ample open substack of the small model of the Picard stack of a family of curves is the
relatively ample full subcategory of that Picard stack. -/
def OpenSubstack.equivalenceOverFullSubcategory (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳)
    (Q : ObjectProperty 𝒳.obj) (hQ : Q.IsClosedUnderIsomorphisms)
    (W : OpenSubstack (AlgebraicStacks.smallModel B S hS 𝒳 h𝒳))
    (hW : W.property = smallModelObjectProperty B S hS h𝒳 Q) :
    StacksRepresentableCFG.EquivalenceOver W.toAlgebraicStack.val.val.p (Q.ι ⋙ 𝒳.p) :=
  cast (congrArg (fun P : ObjectProperty (AlgebraicStacks.smallModel B S hS 𝒳 h𝒳).val.val.obj =>
      StacksRepresentableCFG.EquivalenceOver
        (P.ι ⋙ (AlgebraicStacks.smallModel B S hS 𝒳 h𝒳).val.val.p) (Q.ι ⋙ 𝒳.p)) hW).symm
    (smallModelFullSubcategoryEquivalenceOver B S hS h𝒳 Q hQ)

end AlgebraicGeometry.Stack

end
