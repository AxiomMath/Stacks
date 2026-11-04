module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.TrivialActionGerbe
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeFppfDescent
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverCompare
public import StacksFrontier.CategoryTheory.Sites.Gerbe.BaseEquivalence

/-!
# Gerbes are fppf-locally classifying stacks (Stacks 06QH)

**Stacks 06QH** is the equivalence, for a 1-morphism `π : 𝒳 ⟶ 𝒴` of algebraic stacks, of

1. `𝒳` is a gerbe over `𝒴`, and
2. there are an algebraic space `U`, a group algebraic space `G` flat and locally of finite
   presentation over `U`, and a surjective, flat and locally finitely presented morphism
   `U ⟶ 𝒴` such that `𝒳 ×_𝒴 U ≅ [U/G]` as objects over `U`, the quotient being taken for the
   trivial action of `G` on `U`.

This file proves the implication (2) ⟹ (1). The two inputs are **Stacks 06PF**
(`AlgebraicGeometry.Stack.isGerbeOver_quotientStackToBase_trivialAction`): the structure arrow
`[U/G] ⟶ U` makes `[U/G]` a gerbe over `U` for the trivial action; and **Stacks 06QF**
(`AlgebraicGeometry.Stack.AlgebraicStacks.isGerbeOver_of_snd_of_isSurjective_isFlat_isLfp`):
being a gerbe descends along a surjective, flat, locally finitely presented base change.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isGerbeOver_of_equivalenceOver_quotientStack`:
  **Stacks 06QH**, the implication (2) ⟹ (1).

## Implementation notes

The algebraic space `U` enters as an object of the category of algebraic spaces of Stacks 02X2
and is read as an algebraic stack through its fibred category of Stacks 0458, which is one by
`AlgebraicGeometry.Stack.isAlgebraicStack_fibredCategory`, so that `U ⟶ 𝒴` is an ordinary
1-morphism of algebraic stacks and no comparison of 2-categories is needed. The base change
`𝒳 ×_𝒴 U` is an arbitrary 2-fibre-product square over the cospan `(f, g)`, as in Stacks 06QE and
06QF, whose projection `snd` to `U` is the base change of `f`.

An isomorphism of objects over `U` is an equivalence in the 2-category of categories over the
fibred category of `U`, that is a `StacksRepresentableCFG.EquivalenceOver`. Composing its
structure functors with the structure functor of `U` turns it into an equivalence over the big
fppf site (`CategoryTheory.Functor.IsEquivalenceOver.compRight`), which is the form in which
**Stacks 06P0** transports the gerbe condition from `[U/G] ⟶ U` to the base change.

Flatness and local finite presentation of `G` over `U` are recorded, since they are part of
clause (2), but they are not used: they are what the converse implication produces, by way of
Stacks 06QG. Clause (2) also does not need `G` to act nontrivially — the quotient is for the
trivial action, whose action groupoid is the one of Stacks 0444 attached to the unique action of
`G` on the terminal object `U` of the slice over `U`.

## References

* [Stacks Project, Tag 06P0](https://stacks.math.columbia.edu/tag/06P0)
* [Stacks Project, Tag 06PF](https://stacks.math.columbia.edu/tag/06PF)
* [Stacks Project, Tag 06QF](https://stacks.math.columbia.edu/tag/06QF)
* [Stacks Project, Tag 06QH](https://stacks.math.columbia.edu/tag/06QH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

/-- An algebraic space over `S`, read as an object of the 2-category of algebraic stacks over
`S` by way of its fibred category of Stacks 0458, which is an algebraic stack. -/
abbrev ofAlgebraicSpace (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : AlgebraicSpaces B S hS) : Stack.AlgebraicStacks.{u, w} B S hS :=
  ⟨fibredCategory B S hS U.obj,
    isAlgebraicStack_fibredCategory.{u, w} B S hS U.obj U.property⟩

/-- Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`, let `U` be an algebraic space
over `S`, let `G` be a group algebraic space flat and locally of finite presentation over `U`,
and let `g : U ⟶ 𝒴` be surjective, flat and locally of finite presentation. If the base change
of `f` along `g` is isomorphic, as an object over `U`, to the quotient stack `[U/G]` of the
trivial action of `G` on `U`, then `f` makes `𝒳` a gerbe over `𝒴`. -/
@[stacks 06QH "(2) implies (1); the converse needs Stacks 06QG"]
theorem isGerbeOver_of_equivalenceOver_quotientStack
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (U : AlgebraicSpaces B S hS) (g : ofAlgebraicSpace.{u, w} B S hS U ⟶ 𝒴)
    (hgsurj : Stack.IsSurjective B S hS g) (hgflat : IsFlat B S hS g)
    (hglfp : IsLocallyOfFinitePresentation B S hS g)
    (G : Over U.obj) [GrpObj G] (hG : IsAlgebraicSpace B S hS G.left)
    (_hGflat : Space.IsFlat B S hS G.hom)
    (_hGlfp : Space.IsLocallyOfFinitePresentation B S hS G.hom)
    (A : Space.ActionGroupoidConstruction U G (𝟙_ (Over U.obj)) hG U.property)
    (P : Bicategory.TwoCommSq f g) (hP : Bicategory.IsTwoFibreProduct P)
    (e : StacksRepresentableCFG.EquivalenceOver
      (CatFiberedInGroupoids.homFunctor P.snd.hom)
      (quotientStackToBase A.groupoid).toFunctor) :
    IsGerbeOver B S hS f := by
  have hquot : CategoryTheory.IsGerbeOver (BigFppfOver.topology B S hS)
      (fibredCategory B S hS U.obj).val.p (quotientStackToBase A.groupoid).toFunctor :=
    isGerbeOver_quotientStackToBase_trivialAction U G hG A
  have hPgerbe : IsGerbeOver B S hS P.snd :=
    CategoryTheory.IsGerbeOver.of_isEquivalenceOver_base_symm e.hom.w
      (e.toFunctorIsEquivalenceOver.compRight (fibredCategory B S hS U.obj).val.p) hquot
  exact isGerbeOver_of_snd_of_isSurjective_isFlat_isLfp B S hS P hP hgsurj hgflat hglfp hPgerbe

end AlgebraicGeometry.Stack.AlgebraicStacks

end
