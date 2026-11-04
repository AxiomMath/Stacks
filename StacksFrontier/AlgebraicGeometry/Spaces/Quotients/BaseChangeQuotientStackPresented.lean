module

public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.BaseChangeQuotientStackComparisonFaithful
public import StacksFrontier.CategoryTheory.Sites.Stack.LocallyEssSurjOnFibersComp

/-!
# The Stacks 0DTG comparison on a presented object

Every object of a fibre of a quotient stack is, fppf-locally on the test object, the image of a
`T`-point of the object space (Stacks 044X (1)), so the two remaining halves of Stacks 0DTG —
fullness and local essential surjectivity on fibres of the comparison 1-morphism — are decided on
objects of this shape. This file computes the two components of the comparison 1-morphism there.

## Main results

* `AlgebraicGeometry.Stack.liftedQuotientStackToBase_obj_toQuotientStack`: the structure arrow of
  Stacks 044R sends the object of `[U/R]` presented by a `T`-point `u` of the object space to the
  `T`-point `U ⟶ B` of the base that `u` names.
* `AlgebraicGeometry.Stack.baseChangeQuotientStackComparison_obj_y`: the `𝒮_{X'}`-component of
  the comparison 1-morphism of Stacks 0DTG at an object of `[U'/R']` is its image under the left
  arrow of the square.
* `AlgebraicGeometry.Stack.baseChangeQuotientStackComparison_obj_x`: its `[U/R]`-component is the
  image under the top arrow.
* `AlgebraicGeometry.Stack.liftedQuotientStackToBase_obj_presented` and
  `AlgebraicGeometry.Stack.liftedAssociatedMap_obj_mk`: the structure arrow of Stacks 044R and the
  enlarged 1-morphism of Stacks 0458, on an object named by a `T`-point.
* `AlgebraicGeometry.Space.exists_baseChangeObjectSection`: a `T`-point of `U` and a `T`-point of
  `X'` with the same image in `X` are the two projections of a `T`-point of `U' = X' ×_X U`.

## Implementation notes

The structure arrow of Stacks 044R is the descent of the structure morphism of the object space
(`AlgebraicGeometry.Stack.quotientStackToBase`), and
`AlgebraicGeometry.Stack.quotientStackOfInvariant_obj_toQuotientStack` says that on an object
coming from the presentation the descent of an invariant morphism is that morphism itself — an
equality and not merely a 2-isomorphism, the target being fibred in sets. Composing with the
universe enlargement, which is `CategoryTheory.ULiftHom.up` on objects, gives the description
below.

## References

* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 044X](https://stacks.math.columbia.edu/tag/044X)
* [Stacks Project, Tag 0DTG](https://stacks.math.columbia.edu/tag/0DTG)
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Stack

universe u w

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- **The structure arrow of Stacks 044R on a presented object.** The object of `[U/R]` presented
by a `T`-point `u` of the object space is sent to the `T`-point of the base that `u` names. -/
theorem liftedQuotientStackToBase_obj_toQuotientStack
    (H : GroupoidInAlgebraicSpaces C S hS B) (z : (quotientPrestack H).obj) :
    (liftedQuotientStackToBase H).obj ((toQuotientStack H).obj z) =
      ULiftHom.objUp
        (⟨((quotientPrestackDown H).obj z).base,
          Discrete.mk (H.objectsToBase.hom.app (op ((quotientPrestackDown H).obj z).base)
            ((quotientPrestackDown H).obj z).fiber)⟩ :
          (fibredCategory C S hS B.obj).val.obj) :=
  congrArg ULiftHom.objUp
    ((quotientStackOfInvariant_obj_toQuotientStack H H.objectsToBase
        (H.target_over.trans H.source_over.symm) z).trans
      (pointwiseOfInvariant_obj H H.objectsToBase.hom
        (hom_comp_eq_of_invariant H (H.target_over.trans H.source_over.symm))
        ((quotientPrestackDown H).obj z)))

section BaseChange

variable (G : GroupoidInAlgebraicSpaces C S hS B) {X X' : AlgebraicSpaces C S hS}
  (XtoB : X ⟶ B) (X'toB : X' ⟶ B) (g : X' ⟶ X) (hg : g ≫ XtoB = X'toB)
  (φ : G.objects ⟶ X) (hφB : φ ≫ XtoB = G.objectsToBase)
  (hφ : Space.IsInvariant (Space.groupoidPreRelation G) φ.hom)

/-- **The `[U/R]`-component of the comparison 1-morphism of Stacks 0DTG** is the image of the
object under the top arrow of the square. -/
theorem baseChangeQuotientStackComparison_obj_x
    (z : (quotientStack (invariantBaseChangeGroupoid G XtoB g φ hφB hφ)).obj) :
    ((baseChangeQuotientStackComparison.{u, w} G XtoB X'toB g hg φ hφB hφ).obj z).x =
      (invariantBaseChangeQuotientStackMap (G := G) (XtoB := XtoB) (X'toB := X'toB)
        (g := g) (hg := hg) (φ := φ) (hφB := hφB) (hφ := hφ)).obj z := rfl

/-- **The `𝒮_{X'}`-component of the comparison 1-morphism of Stacks 0DTG** is the image of the
object under the left arrow of the square, the structure arrow of Stacks 044R for the base
change. -/
theorem baseChangeQuotientStackComparison_obj_y
    (z : (quotientStack (invariantBaseChangeGroupoid G XtoB g φ hφB hφ)).obj) :
    ((baseChangeQuotientStackComparison.{u, w} G XtoB X'toB g hg φ hφB hφ).obj z).y =
      (liftedQuotientStackToBase
        (invariantBaseChangeGroupoid G XtoB g φ hφB hφ)).obj z := rfl

/-- **The base of the comparison 1-morphism of Stacks 0DTG at an object** is the test object the
object lies over. -/
theorem baseChangeQuotientStackComparison_obj_base
    (z : (quotientStack (invariantBaseChangeGroupoid G XtoB g φ hφB hφ)).obj) :
    ((baseChangeQuotientStackComparison.{u, w} G XtoB X'toB g hg φ hφB hφ).obj z).base =
      (quotientStack (invariantBaseChangeGroupoid G XtoB g φ hφB hφ)).p.obj z := rfl

end BaseChange

/-- **The structure arrow of Stacks 044R on the object named by a `T`-point of the object
space.** This is `AlgebraicGeometry.Stack.liftedQuotientStackToBase_obj_toQuotientStack` with the
presented object written through the unlifted presentation, which is the form in which Stacks
044X (1) and Stacks 046Q produce it. -/
theorem liftedQuotientStackToBase_obj_presented
    (H : GroupoidInAlgebraicSpaces C S hS B) (V : BigFppfOver C S hS)
    (u : H.objects.obj.obj (op V)) :
    (liftedQuotientStackToBase H).obj ((pointwiseToQuotientStack H).obj ⟨V, u⟩) =
      ULiftHom.objUp (⟨V, Discrete.mk (H.objectsToBase.hom.app (op V) u)⟩ :
        (fibredCategory C S hS B.obj).val.obj) :=
  liftedQuotientStackToBase_obj_toQuotientStack.{u, u} H
    ((quotientPrestackEquivalence H).functor.obj ⟨V, u⟩)

/-- **The enlarged 1-morphism of Stacks 0458 on the object named by a `T`-point.** -/
theorem liftedAssociatedMap_obj_mk {X Y : AlgebraicSpaces C S hS} (a : X ⟶ Y)
    (V : BigFppfOver C S hS) (s : X.obj.obj (op V)) :
    (liftedAssociatedMap a).obj
        (ULiftHom.objUp (⟨V, Discrete.mk s⟩ : (fibredCategory C S hS X.obj).val.obj)) =
      ULiftHom.objUp (⟨V, Discrete.mk (a.hom.app (op V) s)⟩ :
        (fibredCategory C S hS Y.obj).val.obj) :=
  congrArg ULiftHom.objUp (associatedMap_obj C S hS a.hom ⟨V, Discrete.mk s⟩)

end AlgebraicGeometry.Stack

namespace AlgebraicGeometry.Space

universe u

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}

/-- **A `T`-point of `U` and a `T`-point of `X'` with the same image in `X` are the two
projections of a `T`-point of `U' = X' ×_X U`.** This is Stacks 02X2 on sections
(`AlgebraicGeometry.Space.exists_section_of_isPullback`) for the cartesian square on object
spaces recorded by `AlgebraicGeometry.Space.BaseChange`, and it is what produces the local
preimage in the fibre of `[U'/R']` out of a local preimage in the fibre of `[U/R]`. -/
theorem exists_baseChangeObjectSection {X X' : AlgebraicSpaces C S hS}
    (H : GroupoidInAlgebraicSpaces C S hS X) (g : X' ⟶ X) (V : BigFppfOver C S hS)
    (u : H.objects.obj.obj (op V)) (x' : X'.obj.obj (op V))
    (h : H.objectsToBase.hom.app (op V) u = g.hom.app (op V) x') :
    ∃ u' : (Space.baseChange H g).groupoid.objects.obj.obj (op V),
      (Space.baseChange H g).projection.mapObjects.app (op V) u' = u ∧
        (Space.baseChange H g).groupoid.objectsToBase.hom.app (op V) u' = x' :=
  Space.exists_section_of_isPullback C S hS (Space.baseChange H g).objects_isPullback u x' h

end AlgebraicGeometry.Space

end
