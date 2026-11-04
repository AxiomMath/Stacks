module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalityFiniteness
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphismPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEveryConverse

/-!
# Base change of finiteness conditions on 1-morphisms of algebraic stacks (Stacks 06FU)

**Stacks 06FU** says that finite type and local finite type of 1-morphisms of algebraic stacks
over `S` are stable under base change.

The source proves it by combining the base-change remark **Stacks 06FQ** with the base-change
statement **Stacks 03XH** for morphisms of algebraic spaces, and that is the route taken here.
Stacks 06FQ turns a property of morphisms of algebraic spaces which is smooth local on the
source-and-target, and whose restriction to algebraic spaces is stable under base change, into a
property of 1-morphisms of algebraic stacks — through the *existential* smooth-diagram criterion
of **Stacks 06FM** — that is stable under base change along an arbitrary 2-fibre-product square.
Stacks 06FS part (1) is instead defined over the *universal* criterion, so the local assertion is
Stacks 06FQ read across the equivalence of conditions (1) and (2) of Stacks 06FM; that
equivalence is supplied by **Stacks 06FC** at local finite type, and the base-change instance
Stacks 06FQ asks for is Stacks 03XH on the nose, `AlgebraicGeometry.Stack.spaceProperty` being an
abbreviation.

The global assertion adds the second conjunct of Stacks 06FS part (2): quasi-compactness, which
base changes by **Stacks 050V**.

No comparison 1-morphism is built anywhere: both ingredients take a square that is merely
*recognised* as a 2-fibre product, so there is nothing to transport along.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFiniteType_baseChange` and
  `...isFiniteType_baseChange`: **Stacks 06FU**.

## Implementation notes

The source lemma asserts two independent propositions — the local one and the global one — so the
tag's covering set is two declarations and both keys are registered, exactly as for the
composition sibling **Stacks 06FT** in
`StacksFrontier.AlgebraicGeometry.Stacks.FinitenessComposition`.

The two declarations have the same leaf names as the statements for morphisms of *algebraic
spaces* would; the space-level fact consumed here is instead phrased as the instance
`AlgebraicGeometry.Space.isLocallyOfFiniteType_isStableUnderBaseChange`, so no namespace clash
arises. The sibling at smoothness is
`AlgebraicGeometry.Stack.AlgebraicStacks.isSmooth_baseChange` (Stacks 075W), which needs no
round trip because Stacks 075U is defined over the existential criterion.

## References

* [Stacks Project, Tag 03XH](https://stacks.math.columbia.edu/tag/03XH)
* [Stacks Project, Tag 050V](https://stacks.math.columbia.edu/tag/050V)
* [Stacks Project, Tag 06FC](https://stacks.math.columbia.edu/tag/06FC)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06FQ](https://stacks.math.columbia.edu/tag/06FQ)
* [Stacks Project, Tag 06FS](https://stacks.math.columbia.edu/tag/06FS)
* [Stacks Project, Tag 06FU](https://stacks.math.columbia.edu/tag/06FU)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 06FU**, the local assertion. A base change of a 1-morphism of algebraic stacks over
`S` which is locally of finite type is locally of finite type: if `P` is a 2-fibre product of the
cospan `(g, f)` and `f` is locally of finite type, then the projection `P.fst` is locally of
finite type.

This is the base-change remark **Stacks 06FQ** at local finite type of morphisms of algebraic
spaces, transported across the equivalence of conditions (1) and (2) of **Stacks 06FM**, since
Stacks 06FS part (1) is the universal criterion where Stacks 06FQ concludes about the existential
one. Local finite type is smooth local on the source-and-target by **Stacks 06FC** and stable
under base change by **Stacks 03XH**. -/
@[stacks 06FU "locally of finite type"]
theorem isLocallyOfFiniteType_baseChange {𝒳 𝒴 𝒴' : Stack.AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴)
    (P : Bicategory.TwoCommSq g f)
    (hP : Bicategory.IsTwoFibreProduct P)
    (hf : IsLocallyOfFiniteType B S hS f) :
    IsLocallyOfFiniteType B S hS P.fst :=
  let : (Stack.spaceProperty B S hS
      (fun _ _ k => Space.IsLocallyOfFiniteType B S hS k)).IsStableUnderBaseChange :=
    Space.isLocallyOfFiniteType_isStableUnderBaseChange B S hS
  (Stack.hasPropertyOnEverySmoothDiagram_iff_some B S hS
      (fun _ _ h => Space.IsLocallyOfFiniteType B S hS h)
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
      P.pt.property 𝒴'.property P.fst.hom).2
    (Stack.hasPropertyOnSomeSmoothDiagram_baseChange B S hS
      (fun _ _ h => Space.IsLocallyOfFiniteType B S hS h)
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS) f g P hP
      ((Stack.hasPropertyOnEverySmoothDiagram_iff_some B S hS
        (fun _ _ h => Space.IsLocallyOfFiniteType B S hS h)
        (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
        𝒳.property 𝒴.property f.hom).1 hf))

/-- **Stacks 06FU**, the global assertion. A base change of a finite type 1-morphism of algebraic
stacks over `S` is of finite type.

Being of finite type is being locally of finite type together with being quasi-compact
(Stacks 06FS, part (2)); the first conjunct base changes by the local assertion above and the
second by **Stacks 050V**. -/
@[stacks 06FU "finite type"]
theorem isFiniteType_baseChange {𝒳 𝒴 𝒴' : Stack.AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴)
    (P : Bicategory.TwoCommSq g f)
    (hP : Bicategory.IsTwoFibreProduct P)
    (hf : IsFiniteType B S hS f) :
    IsFiniteType B S hS P.fst :=
  ⟨isLocallyOfFiniteType_baseChange B S hS f g P hP hf.1,
    Stack.isQuasiCompactMorphism_baseChange B S hS f g P hP hf.2⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

end
