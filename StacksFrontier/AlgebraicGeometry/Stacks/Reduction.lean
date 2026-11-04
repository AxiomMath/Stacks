module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedClosedSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeTheoreticImagePointsClosure

/-!
# Algebraic stack structures on a closed set of points, and the reduction

Let `𝒳` be an algebraic stack over a scheme `S` and let `Z` be a closed subset of its space of
points. An *algebraic stack structure* on `Z` is a closed substack of `𝒳` whose set of points is
`Z`; among these there is at most one which is reduced, the *reduced induced structure*, and the
reduced induced structure on the whole of `|𝒳|` is the *reduction* `𝒳_red` of `𝒳`.

A substack of `𝒳` is a strictly full subcategory, so a structure on `Z` is a property of the
objects of `𝒳` and the three notions of this file are predicates on such a property. Nothing is
redefined here: the reduced induced structure is pinned by the uniqueness half of
**Stacks 0509**, `AlgebraicGeometry.Stack.eq_of_isReducedStack_of_range_pointsMap_eq`, and the
reduction is its value at the whole point set.

## Main definitions

* `AlgebraicGeometry.Stack.IsAlgebraicStackStructure`: a property of objects is an algebraic
  stack structure on a set of points when it cuts out a closed substack with that set of points.
* `AlgebraicGeometry.Stack.IsReducedInducedStackStructure`: such a structure which is moreover
  reduced.
* `AlgebraicGeometry.Stack.IsReduction`: a reduced induced structure on the whole point set.

## Main results

* `AlgebraicGeometry.Stack.IsAlgebraicStackStructure.isClosed`: a set of points carrying an
  algebraic stack structure is closed, so the restriction to closed subsets in the source costs
  nothing.
* `AlgebraicGeometry.Stack.IsReducedInducedStackStructure.unique`: the reduced induced structure
  on a set of points is unique, which is what makes the definite article of the source legitimate.
* `AlgebraicGeometry.Stack.IsReducedInducedStackStructure.le_of_isAlgebraicStackStructure`: it is
  the smallest algebraic stack structure on that set of points.
* `AlgebraicGeometry.Stack.IsReduction.eq_top_of_isReducedStack`: the reduction of a reduced
  algebraic stack is the whole of it.

## Implementation notes

The point set of a substack is the range of the map on points induced by its canonical inclusion,
and that inclusion is formed from a proof that the full subcategory is an algebraic stack. Both
predicates therefore quantify over such a proof. The quantifier is universal rather than
existential, which loses nothing: proofs of a `Prop` are definitionally equal, and the
closed-substack clause already supplies one, so the two readings agree wherever either is used —
the universal form applies without first destructing that clause, and it matches
`AlgebraicGeometry.Stack.eq_of_isReducedStack_of_range_pointsMap_eq` and
`AlgebraicGeometry.Stack.le_of_isReducedStack_of_range_pointsMap_subset`, which take the
algebraicity proof as an explicit argument.

Closedness of `Z` is a conclusion here, not a hypothesis: the range of the point map of a closed
immersion is closed, by **Stacks 0H20**. The source states the definition for a closed `Z`, and
`AlgebraicGeometry.Stack.IsAlgebraicStackStructure.isClosed` says that no generality is gained by
dropping the word.

The point topology is `AlgebraicGeometry.Stack.pointTopology` of **Stacks 04Y8**, which is not a
global instance; it is written out in the one statement that mentions `IsClosed`.

## Existence

The reduced induced structure and the reduction are predicates here, pinned down by
uniqueness, rather than constructions. Their existence is the existence half of **Stacks 0509**,
`AlgebraicGeometry.Stack.exists_isReducedInducedStackStructure`: every closed set of points
carries a reduced induced structure, and in particular every algebraic stack has a reduction.

## References

* [Stacks Project, Tag 050C](https://stacks.math.columbia.edu/tag/050C)
* [Stacks Project, Tag 0509](https://stacks.math.columbia.edu/tag/0509)
* [Stacks Project, Tag 050A](https://stacks.math.columbia.edu/tag/050A)
* [Stacks Project, Tag 050B](https://stacks.math.columbia.edu/tag/050B)
* [Stacks Project, Tag 0H20](https://stacks.math.columbia.edu/tag/0H20)
* [Stacks Project, Tag 047X](https://stacks.math.columbia.edu/tag/047X)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 050C, an algebraic stack structure on a closed set of points.** Let `𝒳` be an
algebraic stack over `S` and let `Z` be a set of points of `𝒳`. An *algebraic stack structure* on
`Z` is a closed substack of `𝒳` whose set of points is `Z`, that is, a property `P` of the
objects of `𝒳` cutting out a closed substack the canonical inclusion of which has range `Z` on
points. -/
@[stacks 050C "algebraic stack structure on a closed set of points"]
def IsAlgebraicStackStructure {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (Z : Set (AlgebraicStacks.points B S hS 𝒳)) (P : ObjectProperty 𝒳.val.val.obj) : Prop :=
  IsClosedSubstack 𝒳 P ∧
    ∀ hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P),
      Set.range (AlgebraicStacks.pointsMap B S hS (fullSubcategoryInclusion 𝒳 P hP)) = Z

/-- An algebraic stack structure on a set of points cuts out a closed substack. -/
theorem IsAlgebraicStackStructure.isClosedSubstack {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {Z : Set (AlgebraicStacks.points B S hS 𝒳)} {P : ObjectProperty 𝒳.val.val.obj}
    (h : IsAlgebraicStackStructure B S hS Z P) :
    IsClosedSubstack 𝒳 P :=
  h.1

/-- The set of points of an algebraic stack structure on `Z` is `Z`. -/
theorem IsAlgebraicStackStructure.range_pointsMap {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {Z : Set (AlgebraicStacks.points B S hS 𝒳)} {P : ObjectProperty 𝒳.val.val.obj}
    (h : IsAlgebraicStackStructure B S hS Z P)
    (hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P)) :
    Set.range (AlgebraicStacks.pointsMap B S hS (fullSubcategoryInclusion 𝒳 P hP)) = Z :=
  h.2 hP

/-- **A set of points carrying an algebraic stack structure is closed.** The inclusion of the
substack is a closed immersion, and a closed immersion of algebraic stacks is closed on points by
**Stacks 0H20**. -/
theorem IsAlgebraicStackStructure.isClosed {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {Z : Set (AlgebraicStacks.points B S hS 𝒳)} {P : ObjectProperty 𝒳.val.val.obj}
    (h : IsAlgebraicStackStructure B S hS Z P) :
    @IsClosed _ (pointTopology B S hS 𝒳.val) Z := by
  rw [← h.2 h.1.2.choose]
  exact isClosed_range_pointsMap_fullSubcategoryInclusion B S hS h.1.2.choose h.1.2.choose_spec

/-- **Stacks 050C, the reduced induced algebraic stack structure.** The *reduced induced
algebraic stack structure* on a set `Z` of points of `𝒳` is the algebraic stack structure on `Z`
which is reduced. There is at most one,
`AlgebraicGeometry.Stack.IsReducedInducedStackStructure.unique`, which is the content of the
uniqueness half of **Stacks 0509**. -/
@[stacks 050C "the reduced induced algebraic stack structure"]
def IsReducedInducedStackStructure {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (Z : Set (AlgebraicStacks.points B S hS 𝒳)) (P : ObjectProperty 𝒳.val.val.obj) : Prop :=
  IsAlgebraicStackStructure B S hS Z P ∧
    ∀ hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P),
      IsReducedStack B S hS (fullSubcategoryAlgebraicStack 𝒳 P hP)

/-- A reduced induced algebraic stack structure is an algebraic stack structure. -/
theorem IsReducedInducedStackStructure.isAlgebraicStackStructure
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {Z : Set (AlgebraicStacks.points B S hS 𝒳)}
    {P : ObjectProperty 𝒳.val.val.obj} (h : IsReducedInducedStackStructure B S hS Z P) :
    IsAlgebraicStackStructure B S hS Z P :=
  h.1

/-- **The reduced induced structure on a set of points is the smallest algebraic stack structure
on it.** It is contained in every closed substack whose points contain `Z`, by **Stacks 050B**;
in particular in every algebraic stack structure on `Z`. -/
theorem IsReducedInducedStackStructure.le_of_isAlgebraicStackStructure
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {Z : Set (AlgebraicStacks.points B S hS 𝒳)}
    {P Q : ObjectProperty 𝒳.val.val.obj} (hP : IsReducedInducedStackStructure B S hS Z P)
    (hQ : IsAlgebraicStackStructure B S hS Z Q) :
    P ≤ Q :=
  le_of_isReducedStack_of_range_pointsMap_subset B S hS hP.1.1.2.choose hQ.1 hQ.1.2.choose
    (hP.2 _) (((hP.1.2 _).trans (hQ.2 _).symm).subset)

/-- **Stacks 050C, uniqueness of the reduced induced structure.** Two reduced induced algebraic
stack structures on the same set of points are equal. This is the uniqueness half of
**Stacks 0509**, and it is what makes the definite article of the source legitimate. -/
@[stacks 050C "uniqueness of the reduced induced structure"]
theorem IsReducedInducedStackStructure.unique {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {Z : Set (AlgebraicStacks.points B S hS 𝒳)} {P Q : ObjectProperty 𝒳.val.val.obj}
    (hP : IsReducedInducedStackStructure B S hS Z P)
    (hQ : IsReducedInducedStackStructure B S hS Z Q) :
    P = Q :=
  eq_of_isReducedStack_of_range_pointsMap_eq B S hS hP.1.1 hQ.1.1 hP.1.1.2.choose
    hQ.1.1.2.choose (hP.2 _) (hQ.2 _) ((hP.1.2 _).trans (hQ.1.2 _).symm)

/-- **Stacks 050C, the reduction.** The *reduction* `𝒳_red` of an algebraic stack `𝒳` over `S` is
the reduced induced algebraic stack structure on the whole of its space of points. It is unique,
`AlgebraicGeometry.Stack.IsReduction.unique`. -/
@[stacks 050C "the reduction"]
def IsReduction {𝒳 : AlgebraicStacks.{u, w} B S hS} (P : ObjectProperty 𝒳.val.val.obj) : Prop :=
  IsReducedInducedStackStructure B S hS Set.univ P

/-- The reduction of an algebraic stack is unique. -/
theorem IsReduction.unique {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {P Q : ObjectProperty 𝒳.val.val.obj} (hP : IsReduction B S hS P)
    (hQ : IsReduction B S hS Q) :
    P = Q :=
  IsReducedInducedStackStructure.unique B S hS hP hQ

/-- The inclusion of the reduction is surjective on points. -/
theorem IsReduction.isSurjective {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {P : ObjectProperty 𝒳.val.val.obj} (h : IsReduction B S hS P)
    (hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P)) :
    IsSurjective B S hS (fullSubcategoryInclusion 𝒳 P hP) :=
  Set.range_eq_univ.1 (h.1.2 hP)

/-- **The reduction of a reduced algebraic stack is the whole of it.** The inclusion of the
reduction is surjective on points, so **Stacks 050A** applies. -/
theorem IsReduction.eq_top_of_isReducedStack {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {P : ObjectProperty 𝒳.val.val.obj} (h : IsReduction B S hS P)
    (hred : IsReducedStack B S hS 𝒳) :
    P = ⊤ :=
  eq_top_of_isClosedSubstack_of_isReducedStack B S hS P h.1.1
    (h.isSurjective B S hS h.1.1.2.choose) hred

end AlgebraicGeometry.Stack

end
