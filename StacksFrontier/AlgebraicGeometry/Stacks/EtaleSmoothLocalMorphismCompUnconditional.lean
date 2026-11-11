module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordPresentationExistence
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphismComp

/-!
# Composites of DM 1-morphisms with an étale-smooth local property (Stacks 0CIH)

Let `P` be a property of morphisms of algebraic spaces which is étale-smooth local on the
source-and-target (**Stacks 0CFZ**) and stable under composition. Then the property of
Deligne–Mumford 1-morphisms of algebraic stacks that **Stacks 0CIG** induces from `P` is stable
under composition.

The argument is the source's and is
`AlgebraicGeometry.Stack.hasEtaleSmoothLocalProperty_comp`. That theorem takes the forward
direction of **Stacks 06N3** as its argument `hForward`, through which **Stacks 0CIA** supplies
the surjective étale presentations of the two 2-fibre products the source chooses. Here that
argument is discharged by `AlgebraicGeometry.Stack.existsEtalePresentationOfIsAbsolutelyDM`,
the unconditional forward direction of Stacks 06N3, at the containment of the terminal scheme
in the site, which holds for every big fppf site
(`AlgebraicGeometry.BigFppfSite.contains_terminal`). Nothing is carried.

## Main results

* `AlgebraicGeometry.Stack.hasEtaleSmoothLocalProperty_comp_of_isEtaleSmoothLocal`:
  **Stacks 0CIH**.

## References

* [Stacks Project, Tag 06N3](https://stacks.math.columbia.edu/tag/06N3)
* [Stacks Project, Tag 0CIA](https://stacks.math.columbia.edu/tag/0CIA)
* [Stacks Project, Tag 0CIG](https://stacks.math.columbia.edu/tag/0CIG)
* [Stacks Project, Tag 0CIH](https://stacks.math.columbia.edu/tag/0CIH)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0CIH.** Let `P` be a property of morphisms of algebraic spaces over `S` which is
étale-smooth local on the source-and-target and stable under composition. Then the property of
Deligne–Mumford 1-morphisms of algebraic stacks over `S` which **Stacks 0CIG** induces from `P`
is stable under composition: if `f : 𝒳 ⟶ 𝒴` and `g : 𝒴 ⟶ 𝒵` are DM and have it, so does
`f ≫ g`.

This is `AlgebraicGeometry.Stack.hasEtaleSmoothLocalProperty_comp` with its argument `hForward`
discharged by the unconditional forward direction of **Stacks 06N3**,
`AlgebraicGeometry.Stack.existsEtalePresentationOfIsAbsolutelyDM`, at
`AlgebraicGeometry.BigFppfSite.contains_terminal`. -/
@[stacks 0CIH "P etale-smooth local on the source-and-target (Stacks 0CFZ) and stable under \
composition; the composite of two DM 1-morphisms having the property of Stacks 0CIG has it"]
theorem hasEtaleSmoothLocalProperty_comp_of_isEtaleSmoothLocal
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    (hP : Space.IsEtaleSmoothLocalOnSourceAndTarget B S hS P)
    (hcomp : ∀ {X Y Z : AlgebraicSpaces B S hS} (p : X ⟶ Y) (q : Y ⟶ Z), P p → P q → P (p ≫ q))
    {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hf : HasEtaleSmoothLocalProperty B S hS P f)
    (hg : HasEtaleSmoothLocalProperty B S hS P g) :
    HasEtaleSmoothLocalProperty B S hS P (f ≫ g) :=
  hasEtaleSmoothLocalProperty_comp B S hS P hP hcomp B.contains_terminal
    (existsEtalePresentationOfIsAbsolutelyDM.{u, w} B S hS B.contains_terminal) f g hf hg

end AlgebraicGeometry.Stack

end
