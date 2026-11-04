module

public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackSmallModel
public import StacksFrontier.AlgebraicGeometry.Stacks.ObjectPropertyOpenLocus
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubstackOfPoints
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocus

/-!
# Open substacks of the small model of an algebraic stack

`AlgebraicGeometry.Stack.exists_openSubstack_property_eq` turns a property of the objects of an
algebraic stack which is inherited along morphisms and has an open locus into an open substack in
the sense of **Stacks 04YM**. A moduli stack whose hom types are not small — the stack of coherent
sheaves of Stacks 08KB, the Picard stack of Section 0372 — is not an object of the 2-category of
algebraic stacks of **Stacks 03YP** at all, so that statement cannot be applied to it directly:
the open substack has to be taken inside the object
`AlgebraicGeometry.Stack.AlgebraicStacks.smallModel` produces.

It can be. Shrinking the hom types of a category over the site changes neither its objects nor
the value of its structure functor on them, so a property of the objects is a property of the
objects of the small model and its open locus is the same open locus. That is
`AlgebraicGeometry.Stack.hasOpenObjectPropertyLocus_smallModel`, and
`AlgebraicGeometry.Stack.exists_smallModelOpenSubstack_property_eq` is the resulting open
substack.

Finally, an open substack is smooth over whatever the ambient stack is smooth over: its inclusion
is an open immersion, hence smooth, and smooth 1-morphisms compose (**Stacks 075V**). This is the
unconditional companion of
`AlgebraicGeometry.Stack.OpenSubstack.isSmooth_inclusion_comp_of_le`, which instead compares the
restrictions of one 1-morphism to two nested open substacks.

Together the two make the following available for the first time: an open locus proved about a
moduli stack with large hom types names an open substack of an object of
`AlgebraicGeometry.Stack.AlgebraicStacks`, and that open substack is smooth over the base as soon
as the moduli stack is. The relatively ample locus of a Picard stack over its base is the
instance the smoothness half of **Stacks 0DQ0** needs.

## Main definitions

* `AlgebraicGeometry.Stack.smallModelObjectProperty`: a property of the objects of an algebraic
  stack, read on the objects of its small model.

## Main results

* `AlgebraicGeometry.Stack.hasOpenObjectPropertyLocus_smallModel`: an open locus for a property
  of the objects is an open locus for the same property read on the small model.
* `AlgebraicGeometry.Stack.exists_smallModelOpenSubstack_property_eq`: such a property names an
  open substack of the small model.
* `AlgebraicGeometry.Stack.OpenSubstack.isSmooth_inclusion_comp`: an open substack is smooth over
  whatever the ambient algebraic stack is smooth over.

## References

* [Stacks Project, Tag 03YP](https://stacks.math.columbia.edu/tag/03YP)
* [Stacks Project, Tag 04YM](https://stacks.math.columbia.edu/tag/04YM)
* [Stacks Project, Tag 075U](https://stacks.math.columbia.edu/tag/075U)
* [Stacks Project, Tag 075V](https://stacks.math.columbia.edu/tag/075V)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w v

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {𝒳 : BasedCategory.{v, u + 1} (BigFppfOver B S hS)}

/-- The property of the objects of the small model of `𝒳` attached to a property `Q` of the
objects of `𝒳`: an object of the small model has it when the object of `𝒳` it names has `Q`. The
comparison out of the small model is the identity on objects, so this is `Q` itself. -/
noncomputable def smallModelObjectProperty (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳)
    (Q : ObjectProperty 𝒳.obj) :
    ObjectProperty (AlgebraicStacks.smallModel B S hS 𝒳 h𝒳).val.val.obj := fun x =>
  Q ((AlgebraicStacks.smallModelEquivalenceOver B S hS 𝒳 h𝒳).inv.functor.obj x)

/-- An object of `𝒳` has `Q` exactly when the object of the small model it names does. -/
theorem smallModelObjectProperty_apply (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳)
    (Q : ObjectProperty 𝒳.obj) (x : 𝒳.obj) :
    smallModelObjectProperty B S hS h𝒳 Q
        ((AlgebraicStacks.smallModelEquivalenceOver B S hS 𝒳 h𝒳).hom.functor.obj x) ↔ Q x :=
  Iff.rfl

/-- **An open locus for a property of the objects is an open locus for the same property read on
the small model.** The small model of a category over the site has the same objects, and its
structure functor is the comparison out of it followed by the original structure functor, so a
scheme-valued point of the small model becomes one of the original category by composing with the
comparison, and the open subscheme cut out there serves for both. -/
theorem hasOpenObjectPropertyLocus_smallModel (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳)
    (Q : ObjectProperty 𝒳.obj) (hopen : HasOpenObjectPropertyLocus B S hS 𝒳 Q) :
    HasOpenObjectPropertyLocus B S hS (AlgebraicStacks.smallModel B S hS 𝒳 h𝒳).val.val
      (smallModelObjectProperty B S hS h𝒳 Q) := fun U y hy =>
  hopen U (y ⋙ (AlgebraicStacks.smallModelEquivalenceOver B S hS 𝒳 h𝒳).inv.functor)
    (by rwa [Functor.assoc, (AlgebraicStacks.smallModelEquivalenceOver B S hS 𝒳 h𝒳).inv.w])

/-- **A property of the objects with an open locus names an open substack of the small model.**
Let `𝒳` be an algebraic stack over `S` whose hom types need not lie in the universe of the
schemes, and let `Q` be a property of its objects inherited along morphisms and with an open
locus over every scheme-valued point. Then `Q`, read on the objects of the small model of `𝒳`,
is the property of an open substack of that small model in the sense of Stacks 04YM.

This is `AlgebraicGeometry.Stack.exists_openSubstack_property_eq` applied to the small model,
which is possible because the open locus transports to it by
`AlgebraicGeometry.Stack.hasOpenObjectPropertyLocus_smallModel`. -/
theorem exists_smallModelOpenSubstack_property_eq (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳)
    (Q : ObjectProperty 𝒳.obj) (hQ : ∀ {a b : 𝒳.obj}, (a ⟶ b) → Q b → Q a)
    (hopen : HasOpenObjectPropertyLocus B S hS 𝒳 Q) :
    ∃ W : OpenSubstack (AlgebraicStacks.smallModel B S hS 𝒳 h𝒳),
      W.property = smallModelObjectProperty B S hS h𝒳 Q :=
  exists_openSubstack_property_eq (AlgebraicStacks.smallModel B S hS 𝒳 h𝒳)
    (smallModelObjectProperty B S hS h𝒳 Q)
    (fun {_ _} f h =>
      hQ ((AlgebraicStacks.smallModelEquivalenceOver B S hS 𝒳 h𝒳).inv.functor.map f) h)
    (hasOpenObjectPropertyLocus_smallModel B S hS h𝒳 Q hopen)

/-- **An open substack is smooth over whatever the ambient algebraic stack is smooth over.** The
inclusion of an open substack is an open immersion, hence smooth
(`AlgebraicGeometry.Stack.AlgebraicStacks.isSmooth_of_isOpenImmersion`), and smooth 1-morphisms
of algebraic stacks compose (**Stacks 075V**).

This is the unconditional companion of
`AlgebraicGeometry.Stack.OpenSubstack.isSmooth_inclusion_comp_of_le`, which compares the
restrictions of a fixed 1-morphism to two nested open substacks and so needs the smooth locus of
Stacks 0DZR; here the 1-morphism is smooth on all of `𝒳` and nothing is needed beyond
Stacks 075V. -/
theorem OpenSubstack.isSmooth_inclusion_comp {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (W : OpenSubstack 𝒳) (f : 𝒳 ⟶ 𝒴) (hf : AlgebraicStacks.IsSmooth B S hS f) :
    AlgebraicStacks.IsSmooth B S hS (W.inclusion ≫ f) :=
  AlgebraicStacks.isSmooth_comp B S hS W.inclusion f
    (AlgebraicStacks.isSmooth_of_isOpenImmersion B S hS W.inclusion W.isOpenImmersion) hf

end AlgebraicGeometry.Stack

end
