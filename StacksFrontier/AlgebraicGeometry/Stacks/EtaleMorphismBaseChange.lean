module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.LocalOnSourceAndTarget.EtaleSmoothExamples
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordFibreProductEtaleCover
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordPresentationExistence
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleDiagramOfSomeEtaleSmoothDiagram
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleMorphismPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphismSurjectiveDiagram
public import StacksFrontier.AlgebraicGeometry.Stacks.UnramifiedBaseChange

/-!
# Base change of étale 1-morphisms of algebraic stacks (Stacks 0CIN)

**Stacks 0CIN** says that a base change of an étale 1-morphism of algebraic stacks is étale: if
`f : 𝒳 ⟶ 𝒴` is étale in the sense of **Stacks 0CIL** and `g : 𝒴' ⟶ 𝒴` is arbitrary, then the
projection to `𝒴'` of any 2-fibre product of `(g, f)` is étale.

## Main results

* `Stack.hasPropertyOnEveryEtaleDiagram_isEtale_of_hasSurjectiveEtaleSmoothDiagram`:
  an étale 1-morphism admitting one diagram of the shape of condition (2) of **Stacks 0CIF** has
  étale top horizontal morphism on *every* étale diagram over it, smooth or not.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isEtale_baseChange`: **Stacks 0CIN**.

## Implementation notes

The source combines **Stacks 0CII** with the base change of étale morphisms of algebraic spaces
(**Stacks 0466**). The route taken here reaches the same conclusion for *every* 2-fibre product of
the cospan at once, rather than for the canonical one, and the two inputs are the same:

* the Deligne–Mumford conjunct is
  `AlgebraicGeometry.Stack.AlgebraicStacks.isDM_baseChange_of_isEtale` (**Stacks 050F**);
* for the étale-smooth diagram conjunct, the diagram that **Stacks 0CIA** supplies for the
  Deligne–Mumford `f` turns the universal étale-smooth test for `f` into the existential one, and
  `AlgebraicGeometry.Stack.hasPropertyOnEveryEtaleDiagram_of_hasPropertyOnSomeEtaleSmoothDiagram`
  turns that into the test over *every* étale diagram — the right-hand vertical 1-morphism need
  not be smooth, because étaleness of morphisms of algebraic spaces is stable under arbitrary base
  change (**Stacks 0466**) and étale-smooth local on the source-and-target (**Stacks 0CG3**).
  That test, unlike the étale-smooth one, is inherited by the projection of any 2-fibre product by
  pasting (`AlgebraicGeometry.Stack.hasPropertyOnEveryEtaleDiagram_baseChange`), and it contains
  the étale-smooth test.

## References

* [Stacks Project, Tag 0466](https://stacks.math.columbia.edu/tag/0466)
* [Stacks Project, Tag 050F](https://stacks.math.columbia.edu/tag/050F)
* [Stacks Project, Tag 0CG3](https://stacks.math.columbia.edu/tag/0CG3)
* [Stacks Project, Tag 0CIA](https://stacks.math.columbia.edu/tag/0CIA)
* [Stacks Project, Tag 0CIF](https://stacks.math.columbia.edu/tag/0CIF)
* [Stacks Project, Tag 0CII](https://stacks.math.columbia.edu/tag/0CII)
* [Stacks Project, Tag 0CIL](https://stacks.math.columbia.edu/tag/0CIL)
* [Stacks Project, Tag 0CIN](https://stacks.math.columbia.edu/tag/0CIN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An étale 1-morphism has étale top horizontal morphism on every étale diagram.** Let
`f : 𝒳 ⟶ 𝒴` be étale in the sense of **Stacks 0CIL** and suppose it admits one diagram of the
shape of condition (2) of **Stacks 0CIF**. Then for every algebraic space `V` with a 1-morphism
`V ⟶ 𝒴`, smooth or not, and every diagram over `f` with étale comparison to the 2-fibre
product, the top horizontal morphism of algebraic spaces is étale.

The given diagram turns the universal étale-smooth test for `f` into the existential one, and
`AlgebraicGeometry.Stack.hasPropertyOnEveryEtaleDiagram_of_hasPropertyOnSomeEtaleSmoothDiagram`
applies because étaleness is étale-smooth local on the source-and-target (**Stacks 0CG3**) and
stable under base change (**Stacks 0466**). -/
theorem hasPropertyOnEveryEtaleDiagram_isEtale_of_hasSurjectiveEtaleSmoothDiagram
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hex : HasSurjectiveEtaleSmoothDiagram B S hS f) (hf : IsEtale B S hS f) :
    HasPropertyOnEveryEtaleDiagram B S hS
      (fun {_ _} (g : _ ⟶ _) => Space.IsEtale B S hS g.hom :
        MorphismProperty (AlgebraicSpaces B S hS)) f :=
  hasPropertyOnEveryEtaleDiagram_of_hasPropertyOnSomeEtaleSmoothDiagram B S hS _
    (Space.isEtale_isEtaleSmoothLocalOnSourceAndTarget B S hS)
    (fun f hf b => Space.isEtale_of_isPullback B S hS _ _ f b
      (AlgebraicSpaces.isPullback_fiberProduct B S hS f b) hf)
    f (hasPropertyOnSomeEtaleSmoothDiagram_of_hasPropertyOnEveryEtaleSmoothDiagram B S hS _ f hex
      hf.2)

/-- **The étale-smooth conjunct of Stacks 0CIN, given one diagram for `f`.** Let `f : 𝒳 ⟶ 𝒴` be
étale and admit one diagram of the shape of condition (2) of **Stacks 0CIF**, and let `Q` be any
2-fibre product of `(g, f)`. Then the projection `Q.fst` is étale.

The Deligne–Mumford conjunct is **Stacks 050F**; for the other, `f` passes the test over every
étale diagram, that test passes to `Q.fst` by pasting, and it contains the étale-smooth one. -/
theorem isEtale_fst_of_hasSurjectiveEtaleSmoothDiagram
    {𝒳 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴)
    (Q : Bicategory.TwoCommSq g f) (hQ : Bicategory.IsTwoFibreProduct Q)
    (hex : HasSurjectiveEtaleSmoothDiagram B S hS f) (hf : IsEtale B S hS f) :
    IsEtale B S hS Q.fst :=
  ⟨AlgebraicStacks.isDM_baseChange_of_isEtale B S hS f g Q hQ hf,
    hasPropertyOnEveryEtaleSmoothDiagram_of_hasPropertyOnEveryEtaleDiagram B S hS _
      (hasPropertyOnEveryEtaleDiagram_baseChange B S hS _ f g Q hQ
        (hasPropertyOnEveryEtaleDiagram_isEtale_of_hasSurjectiveEtaleSmoothDiagram B S hS f hex
          hf))⟩

namespace AlgebraicStacks

/-- **Stacks 0CIN.** A base change of an étale 1-morphism of algebraic stacks over `S` is étale:
if `f : 𝒳 ⟶ 𝒴` is étale and `Q` is any 2-fibre product of a cospan `(g : 𝒴' ⟶ 𝒴, f)`, then
the projection `Q.fst : Q.pt ⟶ 𝒴'` is étale, both conjuncts of **Stacks 0CIL** included.

The diagram of condition (2) of **Stacks 0CIF** for the Deligne–Mumford `f` is cut out by the
surjective étale presentation of **Stacks 0CIA**, part (2), whose input, the substantial direction
of **Stacks 06N3**, is `AlgebraicGeometry.Stack.existsEtalePresentationOfIsAbsolutelyDM`. -/
@[stacks 0CIN]
theorem isEtale_baseChange {𝒳 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴)
    (Q : Bicategory.TwoCommSq g f) (hQ : Bicategory.IsTwoFibreProduct Q)
    (hf : IsEtale B S hS f) :
    IsEtale B S hS Q.fst :=
  isEtale_fst_of_hasSurjectiveEtaleSmoothDiagram B S hS f g Q hQ
    (hasSurjectiveEtaleSmoothDiagram_of_isDM_of_forward B S hS
      (existsEtalePresentationOfIsAbsolutelyDM.{u, w} B S hS B.contains_terminal) f hf.1) hf

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
