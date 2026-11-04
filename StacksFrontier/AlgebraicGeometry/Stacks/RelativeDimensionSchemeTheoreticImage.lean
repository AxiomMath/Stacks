module

public import StacksFrontier.AlgebraicGeometry.Stacks.DottedArrowsClosedSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointsMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionStackMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismCancellation

/-!
# Replacing the target of a 1-morphism by a substack it factors through

The first step of the proof of **Stacks 0DS4** replaces the target `𝒳` of `f : 𝒯 ⟶ 𝒳` by the
scheme theoretic image `𝒵` of **Stacks 0CMI**, so that the relative dimension of Stacks 0DRL may
be computed over a stack that `f` dominates. The factorization is
`AlgebraicGeometry.Stack.substackLift`, whose composite with the inclusion of the substack is `f`
on the nose (`AlgebraicGeometry.Stack.substackLift_comp`), and that the relative dimension is
unchanged is `AlgebraicGeometry.Stack.relativeStackDimensionAt_comp_of_isMonomorphism`, the
inclusion `𝒵 ⟶ 𝒳` being a closed immersion and hence a monomorphism.

## Main results

* `AlgebraicGeometry.Stack.IsSchemeTheoreticImage.prop_obj`: a 1-morphism lands in its scheme
  theoretic image, which is what `AlgebraicGeometry.Stack.substackLift` asks for.
* `AlgebraicGeometry.Stack.isLocallyOfFiniteType_substackLift`: the factorization of
  a 1-morphism locally of finite type through a substack is locally of finite type.
* `AlgebraicGeometry.Stack.relativeStackDimensionAt_substackLift`: the relative
  dimension of Stacks 0DRL of `f` is that of its factorization through the substack, at every
  point of `|𝒯|`, when the inclusion of the substack is a monomorphism.

## Implementation notes

Local finite type of the factorization is *derived*, not carried: the composite of the
factorization with the inclusion is `f`, and **Stacks 06U9**,
`AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFiniteType_of_comp`, cancels the second
factor with no hypothesis on it.

Monomorphy of the inclusion is a hypothesis rather than a consequence of the substack being
closed: the two steps that supply it for the scheme theoretic image,
`AlgebraicGeometry.Stack.AlgebraicStacks.isImmersion_of_isClosedImmersion` and **Stacks 0504**
`AlgebraicGeometry.Stack.AlgebraicStacks.isMonomorphism_of_isImmersion`, are both proved, and
taking the conclusion of their composite as the hypothesis keeps this file independent of the
closedness of the substack — an open substack, or any other monomorphic one, is covered as well.

## References

* [Stacks Project, Tag 0504](https://stacks.math.columbia.edu/tag/0504)
* [Stacks Project, Tag 04ZW](https://stacks.math.columbia.edu/tag/04ZW)
* [Stacks Project, Tag 06U9](https://stacks.math.columbia.edu/tag/06U9)
* [Stacks Project, Tag 0CMI](https://stacks.math.columbia.edu/tag/0CMI)
* [Stacks Project, Tag 0DRL](https://stacks.math.columbia.edu/tag/0DRL)
* [Stacks Project, Tag 0DS4](https://stacks.math.columbia.edu/tag/0DS4)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A 1-morphism lands in its scheme theoretic image: the property cutting out the image holds at
the image of every object of the source, the image being a substack through which the 1-morphism
factors (`AlgebraicGeometry.Stack.factorsThroughSubstack_iff_forall`). -/
theorem IsSchemeTheoreticImage.prop_obj {𝒯 𝒳 : AlgebraicStacks.{u, w} B S hS} {f : 𝒯 ⟶ 𝒳}
    {P : ObjectProperty 𝒳.val.val.obj} (hP : IsSchemeTheoreticImage f P)
    (X : 𝒯.val.val.obj) : P (f.hom.hom.obj X) :=
  have : P.IsClosedUnderIsomorphisms := hP.1.1
  (factorsThroughSubstack_iff_forall f).1 hP.2.1 X

/-- **The factorization of a 1-morphism locally of finite type through a substack is locally of
finite type.** Its composite with the inclusion of the substack is the given 1-morphism, and
Stacks 06U9 cancels the inclusion. -/
theorem isLocallyOfFiniteType_substackLift
    {𝒯 𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒯 ⟶ 𝒳)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    {P : ObjectProperty 𝒳.val.val.obj}
    (hA : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P))
    (h : ∀ X : 𝒯.val.val.obj, P (f.hom.hom.obj X)) :
    AlgebraicStacks.IsLocallyOfFiniteType B S hS (substackLift B S hS f hA h) :=
  AlgebraicStacks.isLocallyOfFiniteType_of_comp B S hS (substackLift B S hS f hA h)
    (fullSubcategoryInclusion 𝒳 P hA) (by rwa [substackLift_comp])

/-- **The relative dimension of Stacks 0DRL is unchanged when the target is replaced by a
monomorphic substack the 1-morphism factors through.** Let `f : 𝒯 ⟶ 𝒳` be locally of finite type
with `𝒯` and `𝒳` locally Noetherian algebraic stacks over `S`, let `P` cut out a substack `𝒵`
whose inclusion is a monomorphism (Stacks 04ZW) and which is locally Noetherian, and suppose `f`
lands in `P`. Then the relative dimension of Stacks 0DRL of `f` at every `t ∈ |𝒯|` is that of the
factorization `𝒯 ⟶ 𝒵`.

For the scheme theoretic image of **Stacks 0CMI** this is the reduction with which the proof of
**Stacks 0DS4** begins: the inclusion of the image is a closed immersion, hence an immersion,
hence a monomorphism, so the fibre dimension of `f` may be read over the image instead of over
`𝒳`. -/
theorem relativeStackDimensionAt_substackLift
    {𝒯 𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒯 ⟶ 𝒳)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    {P : ObjectProperty 𝒳.val.val.obj}
    (hA : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P))
    (h : ∀ X : 𝒯.val.val.obj, P (f.hom.hom.obj X))
    (hi : AlgebraicStacks.IsMonomorphism B S hS (fullSubcategoryInclusion 𝒳 P hA))
    (h𝒯 : IsLocallyNoetherianStack.{u, w} B S hS 𝒯)
    (h𝒵 : IsLocallyNoetherianStack.{u, w} B S hS (fullSubcategoryAlgebraicStack 𝒳 P hA))
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (t : points B S hS 𝒯.val.val 𝒯.val.property) :
    relativeStackDimensionAt.{u, w} B S hS f hf h𝒯 h𝒳 t =
      relativeStackDimensionAt.{u, w} B S hS (substackLift B S hS f hA h)
        (isLocallyOfFiniteType_substackLift.{u, w} B S hS f hf hA h) h𝒯 h𝒵 t :=
  relativeStackDimensionAt_comp_of_isMonomorphism.{u, w} B S hS (substackLift B S hS f hA h)
    (fullSubcategoryInclusion 𝒳 P hA) hi
    (isLocallyOfFiniteType_substackLift.{u, w} B S hS f hf hA h) hf h𝒯 h𝒵 h𝒳 t

end AlgebraicGeometry.Stack

end
