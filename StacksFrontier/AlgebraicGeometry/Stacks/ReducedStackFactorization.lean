module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedStackClosedSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveBaseChange

/-!
# Factoring a morphism from a reduced algebraic stack through a closed substack

Let `𝒵 ⊆ 𝒳` be a closed substack of an algebraic stack over `S` and let `f : 𝒴 ⟶ 𝒳` be a
1-morphism whose source is reduced. Then `f` factors through `𝒵` if and only if the image of
`|f|` is contained in `|𝒵|`.

A closed substack is a property of the objects of `𝒳` satisfying
`AlgebraicGeometry.Stack.IsClosedSubstack`, and factoring through it is
`AlgebraicGeometry.Stack.FactorsThroughSubstack`, taken over the big fppf site of `S` and up to a
2-isomorphism. The preimage of a substack is `CategoryTheory.ObjectProperty.inverseImage` along
the underlying functor. The statements are given for an arbitrary proof that the full
subcategory cut out by the property is an algebraic stack.

## Main results

* `AlgebraicGeometry.Stack.isSurjective_fullSubcategoryInclusion_inverseImage`: the inclusion of
  the preimage of a closed substack is surjective on points as soon as the image of the point map
  of the 1-morphism lies in the points of the substack.
* `AlgebraicGeometry.Stack.factorsThroughSubstack_iff_range_pointsMap_subset`: a 1-morphism from a
  reduced algebraic stack factors through a closed substack if and only if its image on points
  lies in the points of the substack.

## References

* [Stacks Project, Tag 050A](https://stacks.math.columbia.edu/tag/050A)
* [Stacks Project, Tag 050B](https://stacks.math.columbia.edu/tag/050B)
* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 04YM](https://stacks.math.columbia.edu/tag/04YM)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The inclusion of a preimage substack is surjective on points when the point map lands in
the substack.** Let `f : 𝒴 ⟶ 𝒳` be a 1-morphism of algebraic stacks over `S` and let `P` cut out
a strictly full subcategory of `𝒳` which is an algebraic stack. If every point in the image of
`|f|` comes from a point of that subcategory, then every point of `𝒴` comes from a point of the
preimage of `P` under `f`. -/
theorem isSurjective_fullSubcategoryInclusion_inverseImage
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒴 ⟶ 𝒳)
    {P : ObjectProperty 𝒳.val.val.obj} [P.IsClosedUnderIsomorphisms]
    (hA : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P))
    (hsub : Set.range (AlgebraicStacks.pointsMap B S hS f) ⊆
      Set.range (AlgebraicStacks.pointsMap B S hS (fullSubcategoryInclusion 𝒳 P hA))) :
    IsSurjective B S hS (fullSubcategoryInclusion 𝒴 (P.inverseImage f.hom.hom.toFunctor)
      (isAlgebraicStack_inverseImage f P hA)) := by
  intro y
  obtain ⟨x, hx⟩ := hsub ⟨y, rfl⟩
  obtain ⟨p, hp, -⟩ := AlgebraicStacks.exists_point_of_isTwoFibreProduct B S hS
    (inverseImageSquare f P hA) (isTwoFibreProduct_inverseImageSquare f P hA) y x hx.symm
  exact ⟨p, hp⟩

/-- Let `𝒳` and `𝒴` be algebraic stacks over `S`, let `P` cut out a closed
substack of `𝒳` and let `𝒴` be reduced. A 1-morphism `f : 𝒴 ⟶ 𝒳` factors through the substack
if and only if the image of the induced map on points is contained in the points of the
substack. -/
@[stacks 050B]
theorem factorsThroughSubstack_iff_range_pointsMap_subset
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒴 ⟶ 𝒳)
    {P : ObjectProperty 𝒳.val.val.obj} (hP : IsClosedSubstack 𝒳 P)
    (hA : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P))
    (hred : IsReducedStack B S hS 𝒴) :
    FactorsThroughSubstack f P ↔
      Set.range (AlgebraicStacks.pointsMap B S hS f) ⊆
        Set.range (AlgebraicStacks.pointsMap B S hS (fullSubcategoryInclusion 𝒳 P hA)) := by
  have hiso : P.IsClosedUnderIsomorphisms := hP.1
  constructor
  · rintro ⟨g, ⟨e⟩⟩ q ⟨y, rfl⟩
    refine ⟨pointsMap B S hS 𝒴.val.val (Classical.choose 𝒴.property) (Classical.choose hA) g y,
      ?_⟩
    refine (pointsMap_comp B S hS 𝒴.val.val (Classical.choose 𝒴.property) (Classical.choose hA)
      (Classical.choose 𝒳.property) g (fullSubcategoryBasedInclusion 𝒳 P) y).trans ?_
    exact congrFun (pointsMap_eq_of_basedNatTrans B S hS 𝒴.val.val (Classical.choose 𝒴.property)
      (Classical.choose 𝒳.property) e.hom) y
  · intro hsub
    have htop : P.inverseImage f.hom.hom.toFunctor = ⊤ :=
      eq_top_of_isClosedSubstack_of_isReducedStack B S hS _
        (isClosedSubstack_inverseImage f hP)
        (isSurjective_fullSubcategoryInclusion_inverseImage B S hS f hA hsub) hred
    exact (factorsThroughSubstack_iff_forall f).2 fun X => (congrFun htop X).mpr trivial

end AlgebraicGeometry.Stack

end
