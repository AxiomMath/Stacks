module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalityFiniteness
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphismPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationEquivalenceInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEveryConverse
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap

/-!
# Base change of finite presentation for 1-morphisms of algebraic stacks (Stacks 06Q4)

**Stacks 06Q4** says that finite presentation and local finite presentation of 1-morphisms of
algebraic stacks over `S` are stable under base change.

The source proves it by combining the base-change remark **Stacks 06FQ** with the base-change
statement **Stacks 03XR** for morphisms of algebraic spaces, and that is the route taken here.
Stacks 06FQ turns a property of morphisms of algebraic spaces which is smooth local on the
source-and-target, and whose restriction to algebraic spaces is stable under base change, into a
property of 1-morphisms of algebraic stacks — through the *existential* smooth-diagram criterion
of **Stacks 06FM** — that is stable under base change along an arbitrary 2-fibre-product square.
Stacks 06Q2 part (1) is instead defined over the *universal* criterion, so the local assertion is
Stacks 06FQ read across the equivalence of conditions (1) and (2) of Stacks 06FM; that equivalence
is supplied by **Stacks 06FC** at local finite presentation, and the base-change instance
Stacks 06FQ asks for is Stacks 03XR on the nose, `AlgebraicGeometry.Stack.spaceProperty` being an
abbreviation.

The global assertion adds the other two conjuncts of Stacks 06Q2 part (2): quasi-compactness, which
base changes by **Stacks 050V**, and quasi-separatedness, which base changes by **Stacks 050F**.
Being of finite presentation therefore has one conjunct more than being of finite type, which is
why this is not a literal copy of the finite-type sibling
`AlgebraicGeometry.Stack.AlgebraicStacks.isFiniteType_baseChange` (Stacks 06FU).

No comparison 1-morphism is built: every ingredient takes a square that is merely *recognised* as a
2-fibre product, so there is nothing to transport along.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFinitePresentation_baseChange` and
  `...isFinitePresentation_baseChange`: **Stacks 06Q4**.

## Implementation notes

The source lemma asserts two independent propositions — the local one and the global one — so the
tag's covering set is two declarations and both keys are registered, exactly as for the finite-type
sibling **Stacks 06FU** in `StacksFrontier.AlgebraicGeometry.Stacks.FinitenessBaseChange`.

The quasi-separatedness statement **Stacks 050F** is phrased over a 2-commutative square of
the cospan in the other order and concludes about its *second* projection, so it is applied at
`CategoryTheory.Bicategory.TwoCommSq.swap`; exchanging the legs of a 2-fibre product again gives a
2-fibre product by `CategoryTheory.Bicategory.isTwoFibreProduct_swap`, and
`CategoryTheory.Bicategory.TwoCommSq.swap` carries `@[implicit_reducible]`, so the swapped second
projection is the given first projection with no transport.

The two declarations have the same leaf names as the statements for morphisms of *algebraic
spaces* would; the space-level facts consumed here are instead phrased as the instances
`AlgebraicGeometry.Space.isLocallyOfFinitePresentation_isStableUnderBaseChange` and
`AlgebraicGeometry.Space.isFinitePresentation_isStableUnderBaseChange`, so no namespace clash
arises.

## References

* [Stacks Project, Tag 03XR](https://stacks.math.columbia.edu/tag/03XR)
* [Stacks Project, Tag 050F](https://stacks.math.columbia.edu/tag/050F)
* [Stacks Project, Tag 050V](https://stacks.math.columbia.edu/tag/050V)
* [Stacks Project, Tag 06FC](https://stacks.math.columbia.edu/tag/06FC)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06FQ](https://stacks.math.columbia.edu/tag/06FQ)
* [Stacks Project, Tag 06Q2](https://stacks.math.columbia.edu/tag/06Q2)
* [Stacks Project, Tag 06Q4](https://stacks.math.columbia.edu/tag/06Q4)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 06Q4**, the local assertion. A base change of a 1-morphism of algebraic stacks over
`S` which is locally of finite presentation is locally of finite presentation: if `P` is a 2-fibre
product of the cospan `(g, f)` and `f` is locally of finite presentation, then the projection
`P.fst` is locally of finite presentation.

This is the base-change remark **Stacks 06FQ** at local finite presentation of morphisms of
algebraic spaces, transported across the equivalence of conditions (1) and (2) of **Stacks 06FM**,
since Stacks 06Q2 part (1) is the universal criterion where Stacks 06FQ concludes about the
existential one. Local finite presentation is smooth local on the source-and-target by
**Stacks 06FC** and stable under base change by **Stacks 03XR**. -/
@[stacks 06Q4 "locally of finite presentation"]
theorem isLocallyOfFinitePresentation_baseChange
    {𝒳 𝒴 𝒴' : Stack.AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴)
    (P : Bicategory.TwoCommSq g f)
    (hP : Bicategory.IsTwoFibreProduct P)
    (hf : IsLocallyOfFinitePresentation B S hS f) :
    IsLocallyOfFinitePresentation B S hS P.fst := by
  have : (Stack.spaceProperty B S hS
      (fun _ _ k => Space.IsLocallyOfFinitePresentation B S hS k)).IsStableUnderBaseChange :=
    Space.isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS
  have hiff := @Stack.hasPropertyOnEverySmoothDiagram_iff_some B S hS
    (fun _ _ h => Space.IsLocallyOfFinitePresentation B S hS h)
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS)
  exact (hiff P.pt.property 𝒴'.property P.fst.hom).2
    (Stack.hasPropertyOnSomeSmoothDiagram_baseChange B S hS
      (fun _ _ h => Space.IsLocallyOfFinitePresentation B S hS h)
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS) f g P hP
      ((hiff 𝒳.property 𝒴.property f.hom).1 hf))

/-- **Stacks 06Q4**, the global assertion. A base change of a 1-morphism of algebraic stacks over
`S` of finite presentation is of finite presentation.

Being of finite presentation is being locally of finite presentation together with being
quasi-compact and quasi-separated (Stacks 06Q2, part (2)); the first conjunct base changes by the
local assertion above, the second by **Stacks 050V** and the third by **Stacks 050F**. -/
@[stacks 06Q4 "finite presentation"]
theorem isFinitePresentation_baseChange {𝒳 𝒴 𝒴' : Stack.AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴)
    (P : Bicategory.TwoCommSq g f)
    (hP : Bicategory.IsTwoFibreProduct P)
    (hf : IsFinitePresentation B S hS f) :
    IsFinitePresentation B S hS P.fst :=
  ⟨isLocallyOfFinitePresentation_baseChange B S hS f g P hP hf.1,
    Stack.isQuasiCompactMorphism_baseChange B S hS f g P hP hf.2.1,
    isQuasiSeparated_baseChange_of_isTwoFibreProduct B S hS f g P.swap
      (Bicategory.isTwoFibreProduct_swap hP) hf.2.2⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

end
