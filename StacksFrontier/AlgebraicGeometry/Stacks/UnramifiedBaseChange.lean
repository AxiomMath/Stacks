module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordEquivalenceInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtaleInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.UnderlyingTwoFibreProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.UnramifiedEtaleDiagram
public import StacksFrontier.AlgebraicGeometry.Stacks.UnramifiedEtaleDiagramForward
public import StacksFrontier.CategoryTheory.TwoFibreProduct.PastingFunctorial

/-!
# Base change of unramified 1-morphisms of algebraic stacks (Stacks 0CIV)

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` and `g : 𝒴' ⟶ 𝒴` an arbitrary
1-morphism. The étale diagram test of condition (2) of Stacks 0CIY is stable under base change,
and the base change `𝒴' ×_𝒴 𝒳 ⟶ 𝒴'` of an unramified `f` is unramified.

## Main results

* `AlgebraicGeometry.Stack.hasPropertyOnEveryEtaleDiagram_baseChange`: the étale diagram test of
  condition (2) of Stacks 0CIY is stable under base change, for an arbitrary property `P` of
  morphisms of algebraic spaces over `S`.
* `AlgebraicGeometry.Stack.isUnramifiedOnEveryEtaleDiagram_baseChange`: condition (2) of
  Stacks 0CIY is stable under base change.
* `AlgebraicGeometry.Stack.isUnramified_fst_of_isUnramifiedOnEveryEtaleDiagram`: the projection
  of a 2-fibre product is unramified when `f` satisfies condition (2) of Stacks 0CIY.
* `AlgebraicGeometry.Stack.isUnramified_baseChange_of_isUnramifiedOnEveryEtaleDiagram`:
  the base change of an unramified `f` is unramified.
* `AlgebraicGeometry.Stack.isUnramified_snd_of_isTwoFibreProduct`: the same for a 2-fibre product
  of `(f, g)`, whose projection to `𝒴'` is the second one.

## References

* [Stacks Project, Tag 0CIT](https://stacks.math.columbia.edu/tag/0CIT)
* [Stacks Project, Tag 0CIV](https://stacks.math.columbia.edu/tag/0CIV)
* [Stacks Project, Tag 0CIY](https://stacks.math.columbia.edu/tag/0CIY)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Let `f : 𝒳 ⟶ 𝒴` and `g : 𝒴' ⟶ 𝒴` be 1-morphisms of algebraic stacks over `S` and let `R` be
a 2-fibre product of `(g, f)`. If every étale diagram of algebraic spaces over `f` has top
horizontal morphism with `P`, then so does every étale diagram over the projection `R.fst`. -/
theorem hasPropertyOnEveryEtaleDiagram_baseChange
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    {𝒳 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴)
    (R : Bicategory.TwoCommSq g f) (hR : Bicategory.IsTwoFibreProduct R)
    (hf : HasPropertyOnEveryEtaleDiagram B S hS P f) :
    HasPropertyOnEveryEtaleDiagram B S hS P R.fst := by
  intro U V hU hV a b h η hk
  have hQc : Bicategory.IsTwoFibreProduct
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        b.hom R.underlying.fst) :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      b.hom R.underlying.fst
  set c := diagramCone B S hS R.fst.hom a.hom b.hom h η
  set k := Quotient.out (hQc.from c)
  exact hf U V hU hV (a ≫ R.snd) (b ≫ g) h (R.underlying.pasteFst c).iso
    (isRelativelyEtale_preHom_of_one B S hS
      (Bicategory.isTwoFibreProduct_pasteFst R.underlying
        (isTwoFibreProduct_underlying_algebraicStacks B S hS R hR) _ hQc)
      (Bicategory.TwoCommSq.PreHom.pasteFst R.underlying k) (hk _ hQc k))

/-- If `f : 𝒳 ⟶ 𝒴` satisfies condition (2) of Stacks 0CIY and `R` is a 2-fibre product of
`(g, f)`, then the projection `R.fst` satisfies condition (2) of Stacks 0CIY. -/
theorem isUnramifiedOnEveryEtaleDiagram_baseChange
    {𝒳 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴)
    (R : Bicategory.TwoCommSq g f) (hR : Bicategory.IsTwoFibreProduct R)
    (hf : IsUnramifiedOnEveryEtaleDiagram.{u, w} B S hS f) :
    IsUnramifiedOnEveryEtaleDiagram.{u, w} B S hS R.fst :=
  ⟨isDM_baseChange_of_isTwoFibreProduct B S hS f g R.swap
      (Bicategory.isTwoFibreProduct_swap hR) hf.1,
    hasPropertyOnEveryEtaleDiagram_baseChange B S hS _ f g R hR hf.2⟩

/-- If `f : 𝒳 ⟶ 𝒴` satisfies condition (2) of Stacks 0CIY and `R` is a 2-fibre product of
`(g, f)`, then the projection `R.fst` is unramified in the sense of Stacks 0CIT. -/
theorem isUnramified_fst_of_isUnramifiedOnEveryEtaleDiagram
    {𝒳 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (g : 𝒴' ⟶ 𝒴) (R : Bicategory.TwoCommSq g f) (hR : Bicategory.IsTwoFibreProduct R)
    (hf : IsUnramifiedOnEveryEtaleDiagram.{u, w} B S hS f) :
    IsUnramified B S hS R.fst :=
  isUnramified_of_isUnramifiedOnEveryEtaleDiagram B S hS
    (isUnramifiedOnEveryEtaleDiagram_baseChange.{u, w} B S hS f g R hR hf)

/-- A base change of an unramified 1-morphism of algebraic stacks over `S` is unramified: if
`f : 𝒳 ⟶ 𝒴` is unramified, `g : 𝒴' ⟶ 𝒴` is any 1-morphism and `R` is any 2-fibre product of
`(g, f)`, then the projection `R.fst : R.pt ⟶ 𝒴'` is unramified in the sense of Stacks 0CIT. -/
@[stacks 0CIV "f : X -> Y is unramified in the sense of Stacks 0CIT, g : Y' -> Y is any \
1-morphism of algebraic stacks over S and R is any 2-fibre product of (g, f); the base change \
R.fst : R.pt -> Y' is unramified in the sense of Stacks 0CIT"]
theorem isUnramified_baseChange_of_isUnramifiedOnEveryEtaleDiagram
    {𝒳 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (g : 𝒴' ⟶ 𝒴) (R : Bicategory.TwoCommSq g f) (hR : Bicategory.IsTwoFibreProduct R)
    (hf : IsUnramified B S hS f) :
    IsUnramified B S hS R.fst :=
  isUnramified_fst_of_isUnramifiedOnEveryEtaleDiagram.{u, w} B S hS f g R hR
    (isUnramifiedOnEveryEtaleDiagram_of_isUnramified B S hS hf)

/-- If `f : 𝒳 ⟶ 𝒴` is unramified, `g : 𝒴' ⟶ 𝒴` is any 1-morphism and `R` is any 2-fibre product
of `(f, g)`, then the projection `R.snd : R.pt ⟶ 𝒴'` is unramified in the sense of Stacks 0CIT. -/
@[stacks 0CIV "the same statement with the 2-fibre product written as a square of (f, g): for f \
unramified in the sense of Stacks 0CIT and any g, the second projection R.snd is unramified"]
theorem isUnramified_snd_of_isTwoFibreProduct
    {𝒳 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (g : 𝒴' ⟶ 𝒴) (R : Bicategory.TwoCommSq f g) (hR : Bicategory.IsTwoFibreProduct R)
    (hf : IsUnramified B S hS f) :
    IsUnramified B S hS R.snd :=
  isUnramified_baseChange_of_isUnramifiedOnEveryEtaleDiagram.{u, w} B S hS f g R.swap
    (Bicategory.isTwoFibreProduct_swap hR) hf

end AlgebraicGeometry.Stack

end
