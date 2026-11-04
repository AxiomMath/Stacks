module

public import Mathlib.CategoryTheory.Limits.Types.Limits
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Presheaves

/-!
# Two-morphisms and the direct image of presheaves of sets

Stacks 06TM concerns presheaves of sets on categories fibred in groupoids. For a one-morphism
`f : 𝒳 ⟶ 𝒴` the direct image `{}_pf : PSh(𝒳) ⥤ PSh(𝒴)` is right Kan extension along the
opposite of the underlying functor of `f`. For presheaves of sets this right Kan extension
exists by instance search, so that the direct-image half of 06TM holds with no existence
hypothesis; this file states that half for presheaves of sets.

The existence is the source's construction of `{}_pf` by limits,
`({}_pf F)(y) = lim_{f(x) → y} F(x)`: the index category of this limit is the category
`StructuredArrow (op y) (homFunctorOp f)` of pairs `(x, f(x) → y)`, whose objects form a type
in universe `max u₁ v₁` and whose morphisms are morphisms of `𝒳`. Presheaves of sets are taken
valued in `Type (max u₁ v₁ w)`, which therefore has all these limits
(`CategoryTheory.Limits.Types.hasLimitsOfShape` together with the smallness of structured-arrow
categories), and Mathlib's pointwise right Kan extension then supplies every
`HasRightKanExtension` instance needed below by instance search: along `homFunctorOp f` for
each one-morphism `f`, and along composites of two such functors.

## Main definitions

* `CategoryTheory.CatFiberedInGroupoids.pushforwardIsoOfSets`: the isomorphism
  `{}_pt : {}_pf ≅ {}_pg` of direct images of presheaves of sets induced by a two-morphism
  `t : f ⟶ g`.

## Main results

* `CategoryTheory.CatFiberedInGroupoids.pushforwardIsoOfSets_hom`: `{}_pt` is the mate of
  `t^p : g^p ≅ f^p` for the adjunctions `(f^p, {}_pf)` and `(g^p, {}_pg)`.
* `CategoryTheory.CatFiberedInGroupoids.pushforwardIsoOfSets_trans`: compatibility with
  vertical composition of two-morphisms.
* `CategoryTheory.CatFiberedInGroupoids.pushforwardIsoOfSets_hcomp`: compatibility with
  horizontal composition of two-morphisms.

The restriction half of 06TM, `t^p : g^p ≅ f^p` with its pointwise description and its
compatibility with vertical and horizontal composition, holds for presheaves valued in any
category and is `CategoryTheory.CatFiberedInGroupoids.pullbackIso` and the lemmas following it.

## Implementation notes

The source works with categories that have a set of objects, and fixes the big fppf site
`(Sch/S)_{fppf}` as such a category; presheaves of sets are then valued in sets of arbitrary
size. The universe `max u₁ v₁ w` is the Lean counterpart: it contains the objects and the
morphisms of every category fibred in groupoids in the statement, which is exactly what the
limits defining `{}_pf` need. The statements are given over an arbitrary base category; the
source's big fppf site is a special case.

## References

* [Stacks Project, Tag 06TM](https://stacks.math.columbia.edu/tag/06TM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor

universe w v₀ v₁ u₀ u₁

namespace CategoryTheory.CatFiberedInGroupoids

variable {B : Type u₀} [Category.{v₀} B]
variable {𝒳 𝒴 : CatFiberedInGroupoids.{v₀, v₁, u₀, u₁} B}

variable {f g : 𝒳 ⟶ 𝒴} (t : f ⟶ g)

/-- **Stacks 06TM.** The canonical isomorphism `{}_pt : {}_pf ≅ {}_pg` of direct images of
presheaves of sets induced by a two-morphism `t : f ⟶ g`, namely the mate of the restriction
comparison `t^p : g^p ≅ f^p` for the adjunctions `(f^p, {}_pf)` and `(g^p, {}_pg)`. The direct
images exist by instance search: Mathlib's pointwise right Kan extension, computed by limits in
`Type (max u₁ v₁ w)`. -/
@[stacks 06TM "canonical isomorphism of direct images of presheaves of sets"]
noncomputable def pushforwardIsoOfSets :
    (homFunctorOp f).ran (H := Type (max u₁ v₁ w)) ≅ (homFunctorOp g).ran :=
  pushforwardIso (Type (max u₁ v₁ w)) t

/-- **Stacks 06TM.** The isomorphism `{}_pt` of direct images of presheaves of sets is
compatible with adjointness of `(f^p, {}_pf)` and `(g^p, {}_pg)`: it is the conjugate of
`t^p : g^p ≅ f^p` for the two adjunctions. -/
@[stacks 06TM "compatibility with adjointness, for presheaves of sets"]
theorem pushforwardIsoOfSets_hom :
    (pushforwardIsoOfSets.{w} t).hom =
      conjugateEquiv ((homFunctorOp f).ranAdjunction (Type (max u₁ v₁ w)))
        ((homFunctorOp g).ranAdjunction (Type (max u₁ v₁ w)))
        (pullbackIso (Type (max u₁ v₁ w)) t).hom :=
  pushforwardIso_hom _ t

/-- **Stacks 06TM.** Vertical composition of two-morphisms becomes composition of the induced
isomorphisms of direct images of presheaves of sets. -/
@[stacks 06TM "vertical composition on direct images of presheaves of sets"]
theorem pushforwardIsoOfSets_trans {h : 𝒳 ⟶ 𝒴} (s : g ⟶ h) :
    pushforwardIsoOfSets.{w} (t ≫ s) = pushforwardIsoOfSets.{w} t ≪≫ pushforwardIsoOfSets s :=
  pushforwardIso_trans _ t s

/-- **Stacks 06TM.** The isomorphism of direct images of presheaves of sets induced by a
horizontal composite of two-morphisms, after identifying direct images along composites with
successive direct images, is the horizontal composite of the two induced isomorphisms. -/
@[stacks 06TM "horizontal composition on direct images of presheaves of sets"]
theorem pushforwardIsoOfSets_hcomp {𝒵 : CatFiberedInGroupoids.{v₀, v₁, u₀, u₁} B}
    {h k : 𝒴 ⟶ 𝒵} (s : h ⟶ k) :
    pushforwardIsoOfSets.{w} (Bicategory.whiskerRight t h ≫ Bicategory.whiskerLeft g s) ≪≫
        ranCompIso (homFunctorOp g) (homFunctorOp k) (Type (max u₁ v₁ w)) =
      ranCompIso (homFunctorOp f) (homFunctorOp h) (Type (max u₁ v₁ w)) ≪≫
        isoWhiskerRight (pushforwardIsoOfSets.{w} t)
          ((homFunctorOp h).ran (H := Type (max u₁ v₁ w))) ≪≫
        isoWhiskerLeft ((homFunctorOp g).ran (H := Type (max u₁ v₁ w)))
          (pushforwardIsoOfSets.{w} s) :=
  pushforwardIso_hcomp _ t s

end CategoryTheory.CatFiberedInGroupoids

end
