module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedStackClosedSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Thickening
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningComposition

/-!
# An algebraic stack is a thickening of its reduction (Stacks 0BPT)

**Stacks 0BPT** records three things about the reduction of an algebraic stack `𝒳'` over `S`.

1. `𝒳'` is a thickening of its reduction `𝒳'_red`.
2. If `𝒳 ⊆ 𝒳'` is a thickening of algebraic stacks, then `𝒳'_red = 𝒳_red ⊆ 𝒳`.
3. Consequently `𝒳 = 𝒳'_red` exactly when `𝒳` is a reduced algebraic stack.

## Main definitions

* `AlgebraicGeometry.Stack.StackReduction`: the reduction of an algebraic stack over `S`, in the
  sense of Properties of Stacks, Definition 050C — a reduced closed substack whose set of points
  is the whole set of points of the ambient stack, presented by its inclusion 1-morphism.
* `AlgebraicGeometry.Stack.stackReductionOfThickening`: **assertion (2)**, the reduction of the
  ambient stack of a thickening, read off the reduction of the thickening itself.

## Main results

* `AlgebraicGeometry.Stack.isThickening_stackReductionInclusion`: **assertion (1)**, the inclusion
  of the reduction is a thickening.
* `AlgebraicGeometry.Stack.isClosedSubstack_stackReductionEssImage`: **assertion (1)** in substack
  form, the reduction is realised as a closed substack of the ambient stack carrying every point
  of it.
* `AlgebraicGeometry.Stack.isReducedStack_iff_essImage_stackReduction_eq_top`: **assertion (3)**,
  the reduction of `𝒳` is the whole of `𝒳` exactly when `𝒳` is reduced.

## Implementation notes

The notion of Definition 050C is **not** in this library: neither the reduced induced structure of
Properties of Stacks, Lemma 0509 nor the reduction it is used to define has been formalised, so
there is no term `𝒳_red` to refer to. The definition is therefore carried here as data,
`AlgebraicGeometry.Stack.StackReduction`, bundling exactly what Definition 050C provides: an
algebraic stack over `S`, a closed immersion of it into `𝒳` in the sense of Stacks 04YL, the
statement that the induced map on the point sets of Stacks 04XG has image all of `|𝒳|`, and
reducedness of the source in the sense of `AlgebraicGeometry.Stack.IsReducedStack`. That structure
is substrate, not a formalisation of 050C itself, and it carries no tag; the three assertions of
0BPT are then statements about an arbitrary such presentation, which is the strongest form
available while the construction is missing. Nothing about existence or uniqueness of a reduction
is claimed or used.

Equality of substacks is equality of the object property cutting them out, as in
`AlgebraicGeometry.Stack.IsClosedSubstack` (**Stacks 04YM**, part (2)). So "`𝒳 = 𝒳'_red`" of
assertion (3) is read through assertion (2): the reduction of `𝒳'` *is* the reduction of `𝒳`,
included through `𝒳`, so `𝒳` is the reduction of `𝒳'` exactly when the substack of `𝒳` cut out by
its own reduction is all of `𝒳`. That substack is the essential image of the inclusion, by
**Stacks 0506**, and "all of `𝒳`" is the object property `⊤` — the same reading of "the substack
is the whole stack" that `AlgebraicGeometry.Stack.eq_top_of_isClosedSubstack_of_isReducedStack`
(**Stacks 050A**) uses.

The two directions of assertion (3) are the two halves of the content of 0BPT.

* A reduced stack is its own reduction. This is Stacks 050A applied to the closed substack cut out
  by the essential image of the inclusion of the reduction, whose inclusion carries every point
  because the inclusion of the reduction does and the two differ by an equivalence onto that
  substack (Stacks 0506).
* A stack whose reduction is all of it is reduced. The inclusion of the reduction is then fully
  faithful, because a closed immersion is a monomorphism, and essentially surjective, so it is an
  equivalence of the underlying categories; reducedness is the existential scheme criterion of
  **Stacks 04YF**, and its atlas transports along such a 1-morphism — surjectivity on points by
  functoriality of the point map, smoothness by
  `AlgebraicGeometry.Stack.isRelativelySmooth_comp_of_isEquivalence` applied to the right vertical
  1-morphism of a smooth diagram of **Stacks 06FM**.

Assertion (1) is where the source itself is content-free: the two clauses of
`AlgebraicGeometry.Stack.IsThickening` are the closed-immersion clause of Definition 050C and its
clause on point sets. Both forms of it are recorded, the morphism form and the substack form, and
only the second carries work.

## References

* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 04YF](https://stacks.math.columbia.edu/tag/04YF)
* [Stacks Project, Tag 04YM](https://stacks.math.columbia.edu/tag/04YM)
* [Stacks Project, Tag 050A](https://stacks.math.columbia.edu/tag/050A)
* [Stacks Project, Tag 050C](https://stacks.math.columbia.edu/tag/050C)
* [Stacks Project, Tag 0506](https://stacks.math.columbia.edu/tag/0506)
* [Stacks Project, Tag 0BPP](https://stacks.math.columbia.edu/tag/0BPP)
* [Stacks Project, Tag 0BPS](https://stacks.math.columbia.edu/tag/0BPS)
* [Stacks Project, Tag 0BPT](https://stacks.math.columbia.edu/tag/0BPT)
-/

@[expose] public section

open CategoryTheory Bicategory
open Stacks.Thickenings

namespace AlgebraicGeometry.Stack

universe u w

/-- The *reduction* of an algebraic stack `𝒳` over `S`, in the sense of Properties of Stacks,
Definition 050C: a reduced closed substack of `𝒳` whose set of points is all of `|𝒳|`, presented
by its inclusion 1-morphism rather than by an object property of `𝒳`.

This is the notion Definition 050C constructs from the reduced induced structure of Properties of
Stacks, Lemma 0509. Neither that construction nor its uniqueness is in this library, so the data
is carried as a hypothesis; see the implementation notes of this module. -/
structure StackReduction (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : AlgebraicStacks.{u, w} B S hS) where
  /-- The reduction, as an algebraic stack over `S`. -/
  reduction : AlgebraicStacks.{u, w} B S hS
  /-- Its inclusion into `𝒳`. -/
  inclusion : reduction ⟶ 𝒳
  /-- The inclusion is a closed immersion, in the sense of Stacks 04YL part (2). -/
  isClosedImmersion : AlgebraicStacks.IsClosedImmersion B S hS inclusion
  /-- The set of points of the reduction is all of the set of points of `𝒳`. -/
  pointsRange : Set.range (AlgebraicStacks.pointsMap B S hS inclusion) = Set.univ
  /-- The reduction is reduced. -/
  isReducedStack : IsReducedStack B S hS reduction

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS}

namespace StackReduction

/-- The inclusion of the reduction is surjective on points: its image is everything. -/
theorem isSurjective_inclusion (R : StackReduction B S hS 𝒳) :
    IsSurjective B S hS R.inclusion :=
  Set.range_eq_univ.mp R.pointsRange

/-- The inclusion of the reduction is an immersion, because a closed immersion of algebraic
stacks is one. -/
theorem isImmersion_inclusion (R : StackReduction B S hS 𝒳) :
    AlgebraicStacks.IsImmersion B S hS R.inclusion :=
  ⟨R.isClosedImmersion.1, fun U y hy F hF he =>
    Space.isImmersion_of_isClosedImmersion B S hS (R.isClosedImmersion.2 U y hy F hF he)⟩

end StackReduction

/-- **Stacks 0BPT, assertion (1).** An algebraic stack over `S` is a thickening of its reduction:
the inclusion of the reduction is a closed immersion and is surjective on points, which are the
two clauses of `AlgebraicGeometry.Stack.IsThickening` (**Stacks 0BPP**, part (1)).

Surjectivity on points is the clause of Definition 050C that the set of points of the reduction is
all of `|𝒳|`. -/
@[stacks 0BPT "assertion (1): an algebraic stack is a thickening of its reduction"]
theorem isThickening_stackReductionInclusion (R : StackReduction B S hS 𝒳) :
    IsThickening R.inclusion :=
  ⟨R.isClosedImmersion, R.isSurjective_inclusion⟩

/-- The closed substack of `𝒳` cut out by the reduction carries every point of `𝒳`.

By **Stacks 0506** the inclusion of the reduction factors as an equivalence onto the full
subcategory cut out by its essential image followed by the inclusion of that subcategory; the map
on points of Stacks 04XG is functorial and unchanged by a 2-morphism, so the inclusion of the
subcategory inherits surjectivity on points from the inclusion of the reduction. -/
theorem StackReduction.isSurjective_essImageInclusion (R : StackReduction B S hS 𝒳)
    (hP : IsAlgebraicStack.{u, w} B S hS
      (fullSubcategoryBased 𝒳
        (CatFiberedInGroupoids.homFunctor R.inclusion.hom).essImage)) :
    IsSurjective B S hS
      (fullSubcategoryInclusion 𝒳
        (CatFiberedInGroupoids.homFunctor R.inclusion.hom).essImage hP) := by
  obtain ⟨f, -, ⟨α⟩⟩ := AlgebraicStacks.exists_isEquivalence_to_essImage R.inclusion
    R.isImmersion_inclusion hP
  have hsurj : Function.Surjective (AlgebraicStacks.pointsMap B S hS R.inclusion) :=
    R.isSurjective_inclusion
  rw [← AlgebraicStacks.pointsMap_eq_of_hom₂ B S hS α.hom,
    AlgebraicStacks.pointsMap_comp] at hsurj
  exact Function.Surjective.of_comp hsurj

/-- **Stacks 0BPT, assertion (1), substack form.** The reduction of an algebraic stack `𝒳` over
`S` is realised as a closed substack of `𝒳` carrying every point of `𝒳`, which is what it means
for `𝒳` to be a thickening of it in the substack language of **Stacks 04YM**, part (2).

The substack is the essential image of the inclusion of the reduction, a closed substack by
**Stacks 0506**. -/
@[stacks 0BPT "assertion (1), substack form: the reduction is a closed substack with every point"]
theorem isClosedSubstack_stackReductionEssImage (R : StackReduction B S hS 𝒳) :
    ∃ hP : IsAlgebraicStack.{u, w} B S hS
        (fullSubcategoryBased 𝒳
          (CatFiberedInGroupoids.homFunctor R.inclusion.hom).essImage),
      AlgebraicStacks.IsClosedImmersion B S hS
          (fullSubcategoryInclusion 𝒳
            (CatFiberedInGroupoids.homFunctor R.inclusion.hom).essImage hP) ∧
        IsSurjective B S hS
          (fullSubcategoryInclusion 𝒳
            (CatFiberedInGroupoids.homFunctor R.inclusion.hom).essImage hP) :=
  ⟨AlgebraicStacks.isAlgebraicStack_essImage R.inclusion R.isImmersion_inclusion,
    AlgebraicStacks.isClosedImmersion_essImageInclusion R.inclusion R.isClosedImmersion
      R.isImmersion_inclusion _,
    R.isSurjective_essImageInclusion _⟩

/-- **Stacks 0BPT, assertion (2).** Let `𝒳 ⊆ 𝒳'` be a thickening of algebraic stacks over `S`.
Then the reduction of `𝒳` is a reduction of `𝒳'`, included through `𝒳`: this is the source's
`𝒳'_red = 𝒳_red ⊆ 𝒳`.

The inclusion is the composite of the inclusion of the reduction of `𝒳` with the given thickening,
which is again a thickening by **Stacks 0BPS**, and the source stack is untouched, so it is still
reduced. -/
@[stacks 0BPT "assertion (2): a thickening has the same reduction as its ambient stack"]
def stackReductionOfThickening
    [(Space.closedImmersionProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    (R : StackReduction B S hS 𝒳) (i : 𝒳 ⟶ 𝒳') (hi : IsThickening i) :
    StackReduction B S hS 𝒳' where
  reduction := R.reduction
  inclusion := R.inclusion ≫ i
  isClosedImmersion :=
    (isThickening_comp R.inclusion i (isThickening_stackReductionInclusion R) hi).1
  pointsRange := Set.range_eq_univ.mpr
    (isThickening_comp R.inclusion i (isThickening_stackReductionInclusion R) hi).2
  isReducedStack := R.isReducedStack

/-- The reduction of the ambient stack of a thickening is included through the thickening: its
inclusion factors as the inclusion of the reduction of the thickening followed by the thickening.
This is the `⊆ 𝒳` of assertion (2). -/
theorem stackReductionOfThickening_inclusion
    [(Space.closedImmersionProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    (R : StackReduction B S hS 𝒳) (i : 𝒳 ⟶ 𝒳') (hi : IsThickening i) :
    (stackReductionOfThickening R i hi).inclusion = R.inclusion ≫ i :=
  rfl

/-- The reduction of the ambient stack of a thickening is the reduction of the thickening. -/
theorem stackReductionOfThickening_reduction
    [(Space.closedImmersionProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    (R : StackReduction B S hS 𝒳) (i : 𝒳 ⟶ 𝒳') (hi : IsThickening i) :
    (stackReductionOfThickening R i hi).reduction = R.reduction :=
  rfl

/-- **Smoothness of a 1-morphism of algebraic stacks is unchanged by postcomposition with a
1-morphism whose underlying functor is an equivalence.** A smooth diagram of **Stacks 06FM** over
`a` becomes one over `a ≫ e` on postcomposing its right vertical 1-morphism with `e`: that keeps
the diagram 2-commutative, and relative smoothness survives by
`AlgebraicGeometry.Stack.isRelativelySmooth_comp_of_isEquivalence`. -/
private theorem isSmooth_comp_of_isEquivalence {𝒰 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS}
    (a : 𝒰 ⟶ 𝒴) (e : 𝒴 ⟶ 𝒵)
    (he : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor e.hom))
    (ha : AlgebraicStacks.IsSmooth B S hS a) :
    AlgebraicStacks.IsSmooth B S hS (a ≫ e) := by
  obtain ⟨U, V, hU, hV, p, q, h, ⟨η⟩, hp, hpsurj, hq, hPh⟩ := ha
  refine ⟨U, V, hU, hV, p, q ≫ e.hom, h, ⟨?_⟩, hp, hpsurj,
    isRelativelySmooth_comp_of_isEquivalence B S hS q e.hom he hq, hPh⟩
  exact (α_ (associatedMap B S hS h).1 q e.hom).symm ≪≫
    Bicategory.whiskerRightIso η e.hom ≪≫ α_ p a.hom e.hom

/-- **Reducedness of an algebraic stack over `S` transports along a 1-morphism whose underlying
functor is an equivalence and which is surjective on points.** Reducedness is the existential
scheme criterion of **Stacks 04YF**; the atlas is carried by the same scheme, with the atlas
1-morphism postcomposed with the given one, which stays surjective on points by functoriality of
the point map of Stacks 04XG and stays smooth by
`AlgebraicGeometry.Stack.isSmooth_comp_of_isEquivalence`. -/
theorem isReducedStack_of_isEquivalence_stackMorphism {𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS}
    (e : 𝒴 ⟶ 𝒵) (he : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor e.hom))
    (hesurj : IsSurjective B S hS e) (h𝒴 : IsReducedStack B S hS 𝒴) :
    IsReducedStack B S hS 𝒵 := by
  obtain ⟨U, a, hasurj, hasmooth, hU⟩ := h𝒴
  refine ⟨U, a ≫ e, ?_, isSmooth_comp_of_isEquivalence a e he hasmooth, hU⟩
  change Function.Surjective (AlgebraicStacks.pointsMap B S hS (a ≫ e))
  rw [AlgebraicStacks.pointsMap_comp]
  exact hesurj.comp hasurj

/-- **Stacks 0BPT, assertion (3).** Let `R` present the reduction of an algebraic stack `𝒳` over
`S`. Then the closed substack of `𝒳` cut out by that reduction is all of `𝒳` exactly when `𝒳` is a
reduced algebraic stack.

Read through assertion (2) this is the source's assertion (3): for a thickening `𝒳 ⊆ 𝒳'` the
reduction of `𝒳'` is the reduction of `𝒳`, so `𝒳 = 𝒳'_red` says precisely that the reduction of
`𝒳` is all of `𝒳`.

One direction is **Stacks 050A** at the closed substack cut out by the essential image of the
inclusion of the reduction, which carries every point of `𝒳`. For the other, a reduction whose
substack is all of `𝒳` has fully faithful and essentially surjective inclusion, so reducedness
transports from the reduction to `𝒳`. -/
@[stacks 0BPT "assertion (3): the reduction is the whole stack exactly when the stack is reduced"]
theorem isReducedStack_iff_essImage_stackReduction_eq_top (R : StackReduction B S hS 𝒳) :
    (CatFiberedInGroupoids.homFunctor R.inclusion.hom).essImage = ⊤ ↔
      IsReducedStack B S hS 𝒳 := by
  refine ⟨fun htop => ?_, eq_top_of_isClosedSubstack_of_isReducedStack B S hS _
    (AlgebraicStacks.isClosedSubstack_essImage R.inclusion R.isClosedImmersion)
    (R.isSurjective_essImageInclusion _)⟩
  obtain ⟨_, _⟩ := AlgebraicStacks.full_and_faithful_homFunctor_of_isImmersion R.inclusion
    R.isImmersion_inclusion
  have : (CatFiberedInGroupoids.homFunctor R.inclusion.hom).EssSurj :=
    ⟨fun Y => by rw [htop]; trivial⟩
  exact isReducedStack_of_isEquivalence_stackMorphism R.inclusion Functor.IsEquivalence.mk
    R.isSurjective_inclusion R.isReducedStack

end AlgebraicGeometry.Stack

end
