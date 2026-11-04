module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordPresentationExistence
public import StacksFrontier.AlgebraicGeometry.Stacks.UnramifiedMorphismPermanence

/-!
# Composition of unramified 1-morphisms of algebraic stacks (Stacks 0CIU)

**Stacks 0CIU** asserts that the composition of unramified 1-morphisms of algebraic stacks is
unramified. Unramifiedness of a 1-morphism of algebraic stacks is
`AlgebraicGeometry.Stack.IsUnramified` (**Stacks 0CIT**).

The proof is the source's: **Stacks 0CIH** read at unramifiedness of morphisms of algebraic
spaces, which is étale-smooth local on the source-and-target (the unramified entry of
**Stacks 0CG3**) and stable under composition (**Stacks 03ZI**). Both inputs of that transfer
theorem which `AlgebraicGeometry.Stack.isUnramified_comp` takes as hypotheses are
discharged here: the containment of the terminal scheme in the site is
`AlgebraicGeometry.BigFppfSite.contains_terminal`, and the substantial direction of
**Stacks 06N3**, which enters the source's argument through **Stacks 0CIA**, is
`AlgebraicGeometry.Stack.existsEtalePresentationOfIsAbsolutelyDM`.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isUnramified_comp`: **Stacks 0CIU**.

## References

* [Stacks Project, Tag 03ZI](https://stacks.math.columbia.edu/tag/03ZI)
* [Stacks Project, Tag 06N3](https://stacks.math.columbia.edu/tag/06N3)
* [Stacks Project, Tag 0CG3](https://stacks.math.columbia.edu/tag/0CG3)
* [Stacks Project, Tag 0CIA](https://stacks.math.columbia.edu/tag/0CIA)
* [Stacks Project, Tag 0CIH](https://stacks.math.columbia.edu/tag/0CIH)
* [Stacks Project, Tag 0CIT](https://stacks.math.columbia.edu/tag/0CIT)
* [Stacks Project, Tag 0CIU](https://stacks.math.columbia.edu/tag/0CIU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0CIU.** The composition of unramified 1-morphisms of algebraic stacks over `S` is
unramified: for `f : 𝒳 ⟶ 𝒴` and `g : 𝒴 ⟶ 𝒵` unramified, so is `f ≫ g`.

This is **Stacks 0CIH** at unramifiedness of morphisms of algebraic spaces, which is étale-smooth
local on the source-and-target by **Stacks 0CG3** and stable under composition by
**Stacks 03ZI**. -/
@[stacks 0CIU]
theorem isUnramified_comp
    {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hf : IsUnramified B S hS f) (hg : IsUnramified B S hS g) :
    IsUnramified B S hS (f ≫ g) :=
  Stack.isUnramified_comp.{u, w} B S hS B.contains_terminal
    (existsEtalePresentationOfIsAbsolutelyDM.{u, w} B S hS B.contains_terminal) f g hf hg

end AlgebraicGeometry.Stack.AlgebraicStacks

end
