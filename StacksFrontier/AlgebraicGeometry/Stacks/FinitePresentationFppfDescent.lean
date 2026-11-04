module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalityFiniteness
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FppfDescentProperty

/-!
# Fppf descent of local finite presentation for algebraic stacks (Stacks 06Q8)

**Stacks 06Q8** says that if `𝒵 ⟶ 𝒴` is a surjective, flat, locally finitely presented
1-morphism of algebraic stacks over `S`, then a 1-morphism `f : 𝒳 ⟶ 𝒴` is locally of finite
presentation as soon as its base change `𝒵 ×_𝒴 𝒳 ⟶ 𝒵` is.

The source's proof is two sentences: local finite presentation satisfies the hypotheses of
**Stacks 0DN6**, being smooth local on the source-and-target and fppf local on the target. Both
are available here. Smooth locality on the source-and-target is `AlgebraicGeometry.Space.`
`isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation`, the local-finite-presentation case
of **Stacks 06FC**; locality at the target is **Stacks 041T**, which is proved for the fpqc
precoverage and carried to the fppf one along
`AlgebraicGeometry.Space.fppfPrecoverage_le_fpqcPrecoverage`.

Two conversions are needed on top of that, and both are the standard ones in this chapter.
Stacks 06Q2 part (1) is defined over the *universal* smooth-diagram criterion while Stacks 0DN6
is stated over the *existential* one, so the hypothesis and the conclusion are both moved across
the equivalence of conditions (1) and (2) of **Stacks 06FM**. And Stacks 0DN6 takes its
hypothesis on the first projection of the 2-fibre product of the cospan `(g, f)` where the
source — and this statement — name the second projection of the cospan `(f, g)`; those are two
apexes of one cospan, so the passage between them is
`AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_fst_of_isTwoFibreProduct` applied to the
swapped square.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFinitePresentation_of_baseChange`:
  **Stacks 06Q8**.

## References

* [Stacks Project, Tag 06Q8](https://stacks.math.columbia.edu/tag/06Q8)
* [Stacks Project, Tag 0DN6](https://stacks.math.columbia.edu/tag/0DN6)
* [Stacks Project, Tag 041T](https://stacks.math.columbia.edu/tag/041T)
* [Stacks Project, Tag 06FC](https://stacks.math.columbia.edu/tag/06FC)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 06Q8.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` and let
`g : 𝒵 ⟶ 𝒴` be surjective, flat and locally of finite presentation. If the base change
`𝒵 ×_𝒴 𝒳 ⟶ 𝒵` of `f` along `g` is locally of finite presentation, then so is `f`. -/
@[stacks 06Q8]
theorem isLocallyOfFinitePresentation_of_baseChange
    {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴)
    (hgs : Stack.IsSurjective B S hS g)
    (hgflat : IsFlat B S hS g)
    (hglfp : IsLocallyOfFinitePresentation B S hS g)
    (hbase : IsLocallyOfFinitePresentation B S hS
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS f g).snd) :
    IsLocallyOfFinitePresentation B S hS f := by
  set P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    fun _ _ h => Space.IsLocallyOfFinitePresentation B S hS h with hPdef
  have hP : Space.IsSmoothLocalOnSourceAndTarget B S hS P :=
    Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS
  have hlocal : (Stack.spaceProperty B S hS P).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u + 1} B S hS) :=
    MorphismProperty.IsLocalAtTarget.of_le
      (Space.fppfPrecoverage_le_fpqcPrecoverage B S hS)
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
  exact Stack.hasProperty_of_baseChange.{u, u + 1, w} B S hS P hP f g hgs hgflat hglfp hsome

end AlgebraicGeometry.Stack.AlgebraicStacks

end
