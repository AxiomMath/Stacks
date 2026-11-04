module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalityFiniteness
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FppfDescentProperty

/-!
# Local finite type descends along an fppf cover of the target (Stacks 06U7)

**Stacks 06U7.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` and let
`W ⟶ 𝒴` be surjective, flat and locally of finite presentation, where `W` is an algebraic space
over `S`. If the base change `W ×_𝒴 𝒳 ⟶ W` of `f` is locally of finite type, then so is `f`.

Local finite type satisfies the two hypotheses of the general fppf descent of **Stacks 0DN6**:
it is smooth local on the source-and-target for morphisms of algebraic spaces, which is the
local-finite-type case of **Stacks 06FC**, and it is local on the target for the fppf
precoverage, which is **Stacks 041S** for the fpqc precoverage carried along
`AlgebraicGeometry.Space.fppfPrecoverage_le_fpqcPrecoverage`. Two conversions sit between that
descent and the statement, and both are the standard ones in this chapter. Stacks 06FS part (1)
is defined over the *universal* smooth-diagram criterion of **Stacks 06FM** while Stacks 0DN6 is
stated over the *existential* one, so the hypothesis and the conclusion are both moved across the
equivalence of conditions (1) and (2) of Stacks 06FM. And Stacks 0DN6 takes its hypothesis on the
first projection of the 2-fibre product of the cospan `(g, f)` where the source — and the
statements below — name the second projection of the cospan `(f, g)`; those are two apexes of one
cospan, so the passage between them is
`AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_fst_of_isTwoFibreProduct` applied to the
swapped square.

Nothing in that argument uses the cover being an algebraic space, so the workhorse here is the
general statement for an arbitrary 1-morphism of algebraic stacks — the exact twin of the local
finite presentation case **Stacks 06Q8**
(`AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFinitePresentation_of_baseChange`), which
the source does state for a 1-morphism of algebraic stacks. Stacks 06U7 is its instance at the
algebraic stack `AlgebraicGeometry.Stack.algebraicSpaceStack` of an algebraic space, which is the
form the source states and the form its consumers have, since what they hold is a presentation
of `𝒴`.

This is not the descent of **Stacks 06U8**
(`AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFiniteType_of_comp_of_fppf`): there the
surjective flat 1-morphism of finite presentation is the *first factor* of a composite and the
conclusion is about the second, which is fppf descent on the source rather than along a base
change.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFiniteType_of_baseChange`: local finite
  type descends along any surjective flat 1-morphism of algebraic stacks locally of finite
  presentation.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFiniteType_of_baseChange_algebraicSpace`:
  **Stacks 06U7**, that descent along a cover by an algebraic space.

## References

* [Stacks Project, Tag 041S](https://stacks.math.columbia.edu/tag/041S)
* [Stacks Project, Tag 06FC](https://stacks.math.columbia.edu/tag/06FC)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06FS](https://stacks.math.columbia.edu/tag/06FS)
* [Stacks Project, Tag 06Q8](https://stacks.math.columbia.edu/tag/06Q8)
* [Stacks Project, Tag 06U7](https://stacks.math.columbia.edu/tag/06U7)
* [Stacks Project, Tag 0DN6](https://stacks.math.columbia.edu/tag/0DN6)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` and let `g : 𝒵 ⟶ 𝒴` be
surjective, flat and locally of finite presentation. If the base change `𝒵 ×_𝒴 𝒳 ⟶ 𝒵` of `f`
along `g` is locally of finite type, then so is `f`.

This is the local finite type twin of **Stacks 06Q8** and the general form of **Stacks 06U7**,
which is its instance at a cover by an algebraic space. -/
theorem isLocallyOfFiniteType_of_baseChange
    {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴)
    (hgsurj : Stack.IsSurjective B S hS g)
    (hgflat : IsFlat B S hS g)
    (hglfp : IsLocallyOfFinitePresentation B S hS g)
    (hbase : IsLocallyOfFiniteType B S hS
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS f g).snd) :
    IsLocallyOfFiniteType B S hS f := by
  set P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    fun _ _ h => Space.IsLocallyOfFiniteType B S hS h with hPdef
  have hP : Space.IsSmoothLocalOnSourceAndTarget B S hS P :=
    Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS
  have hlocal : (Stack.spaceProperty B S hS P).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u + 1} B S hS) :=
    (Space.isLocallyOfFiniteType_isLocalAtTarget_fpqc.{u, u + 1} B S hS).of_le
      (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u + 1} B S hS)
  have hsome : Stack.HasPropertyOnSomeSmoothDiagram B S hS P
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom f.hom).fst :=
    Stack.hasPropertyOnSomeSmoothDiagram_fst_of_isTwoFibreProduct B S hS P
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom g.hom).swap
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom f.hom)
      (Bicategory.isTwoFibreProduct_swap
        (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
          f.hom g.hom))
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        g.hom f.hom)
      ((Stack.hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS P hP
        (Stack.twoFibreProductSquareAlgebraicStacks B S hS f g).pt.property 𝒵.property
        (Stack.twoFibreProductSquareAlgebraicStacks B S hS f g).snd.hom).1 hbase)
  refine (Stack.hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS P hP
    𝒳.property 𝒴.property f.hom).2 ?_
  exact Stack.hasProperty_of_baseChange.{u, u + 1, w} B S hS P hP f g hgsurj hgflat hglfp hsome

/-- **Stacks 06U7.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` and let
`g : W ⟶ 𝒴` be surjective, flat and locally of finite presentation, where `W` is an algebraic
space over `S`. If the base change `W ×_𝒴 𝒳 ⟶ W` of `f` along `g` is locally of finite type,
then so is `f`. -/
@[stacks 06U7]
theorem isLocallyOfFiniteType_of_baseChange_algebraicSpace
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hW : IsAlgebraicSpace B S hS W)
    (g : Stack.algebraicSpaceStack.{u, w} B S hS W hW ⟶ 𝒴)
    (hgsurj : Stack.IsSurjective B S hS g)
    (hgflat : IsFlat B S hS g)
    (hglfp : IsLocallyOfFinitePresentation B S hS g)
    (hbase : IsLocallyOfFiniteType B S hS
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS f g).snd) :
    IsLocallyOfFiniteType B S hS f :=
  isLocallyOfFiniteType_of_baseChange B S hS f g hgsurj hgflat hglfp hbase

end AlgebraicGeometry.Stack.AlgebraicStacks

end
