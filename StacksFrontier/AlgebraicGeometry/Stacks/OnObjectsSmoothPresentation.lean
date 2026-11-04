module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFormallySmooth
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.FormallySmoothOnObjects
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.LimitPreservingFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaProductsToDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothPresentationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveOnObjectsRelative

/-!
# From the three properties on objects to a smooth presentation

Let `𝒴` be a stack in groupoids over the big fppf site of a scheme `S` whose diagonal is
representable by algebraic spaces, and let `v : (Sch/U)_{fppf} ⟶ 𝒴` be a scheme-valued point
of `𝒴` which is limit preserving on objects, formally smooth on objects and surjective on
objects. Then `𝒴` is an algebraic stack.

This is the closing step of the proof of **Stacks 06DC**, Artin's theorem on representability of
flat groupoids. That proof produces a cover of `𝒴` in exactly this shape — the three conditions
"on objects" rather than smoothness and surjectivity — and converts it into a presentation using
**Stacks 06CX**, **Stacks 06D3**, **Stacks 06D7** and the infinitesimal lifting criterion
**Stacks 04AM**. Here that conversion is carried out once, for an arbitrary scheme-valued point.

## Main results

* `AlgebraicGeometry.Stack.isAlgebraicStack_of_onObjects_schemePoint`: the conversion, for a
  scheme-valued point of a stack with a diagonal representable by algebraic spaces.

## Implementation notes

The point of stating this for a *scheme-valued* point, rather than for a 1-morphism from an
algebraic stack as the source of Stacks 06DC does, is that it needs no hypothesis of
representability on the 1-morphism and no further input beyond the four tags above.
Representability of `v` by algebraic spaces is not assumed: it follows from the diagonal of `𝒴`
by **Stacks 045G**, the implication from condition (1) to condition (3), so the three conditions
on objects can be traded for the corresponding relative properties of **Stacks 03YK** by the
three equivalences 06CX, 06D3 and 06D7. Local finite presentation and formal smoothness then
give smoothness through the direction of Stacks 04AM that needs no representability hypothesis,
`AlgebraicGeometry.Space.isSmooth_of_isLocallyOfFinitePresentation_of_formallySmooth`, and
`AlgebraicGeometry.Stack.isAlgebraicStack_of_smoothPresentation_of_hasRepresentableDiagonal`
assembles the clauses of Stacks 026O.

Going the other way — from an algebraic stack covering `𝒴` to a scheme-valued point of `𝒴` with
the three conditions on objects, which is what the composition step of Stacks 06DC does — would
need the atlas of the covering stack to be formally smooth on objects, hence its smooth relative
base changes to be formally smooth. For base changes that are merely algebraic spaces that is
the implication of Stacks 04AM which this library carries as the unproved
`AlgebraicGeometry.Space.FormallySmoothEtaleDescent`, so that step is not available here.

## References

* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 026O](https://stacks.math.columbia.edu/tag/026O)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 06CX](https://stacks.math.columbia.edu/tag/06CX)
* [Stacks Project, Tag 06D3](https://stacks.math.columbia.edu/tag/06D3)
* [Stacks Project, Tag 06D7](https://stacks.math.columbia.edu/tag/06D7)
* [Stacks Project, Tag 06DC](https://stacks.math.columbia.edu/tag/06DC)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The closing step of the proof of Stacks 06DC.** A stack in groupoids over the big fppf
site of `S` whose diagonal is representable by algebraic spaces and which has a scheme-valued
point that is limit preserving on objects, formally smooth on objects and surjective on objects
is an algebraic stack.

The three conditions on objects become the relative properties of Stacks 03YK at local finite
presentation, formal smoothness and surjectivity by **Stacks 06CX**, **Stacks 06D3** and
**Stacks 06D7** — all three equivalences need `v` to be representable by algebraic spaces, which
is **Stacks 045G** from the diagonal — and the first two combine into relative smoothness by
**Stacks 04AM**. -/
theorem isAlgebraicStack_of_onObjects_schemePoint
    {𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (h𝒴 : 𝒴.val.p.IsStack (BigFppfOver.topology B S hS))
    (hdiag : HasRepresentableDiagonal B S hS 𝒴)
    (U : BigFppfOver B S hS) (v : schemeFibredCategory B S hS U ⟶ 𝒴)
    (hlim : BigFppfOver.IsLimitPreservingOnObjects.{u, u, u} B S hS
      (schemeFibredCategory B S hS U) 𝒴 v)
    (hsmooth : IsFormallySmoothOnObjects B S hS (schemeFibredCategory B S hS U) 𝒴 v)
    (hsurj : IsSurjectiveOnObjects B S hS (schemeFibredCategory B S hS U).val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor v)) :
    IsAlgebraicStack.{u, w} B S hS 𝒴.val := by
  have hv : IsRepresentableByAlgebraicSpaces B S hS v.hom :=
    (isAlgebraicSpaceIsomPresheaf_iff_isRepresentableFromSchemes B S hS 𝒴).mp
      ((hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS 𝒴).mp hdiag) U v.hom
  have hlfp := (isLimitPreservingOnObjects_iff_isLocallyOfFinitePresentation
    B S hS (schemeFibredCategory B S hS U) 𝒴 v hv).mp hlim
  have hfs := (BigFppfOver.isFormallySmoothOnObjects_iff_isRelativelyFormallySmooth
    B S hS v hv).mp hsmooth
  have hrsurj : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (Space.surjectiveMorphismProperty B S hS) v hv :=
    (isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u + 1} B S hS v hv).mp hsurj
  exact isAlgebraicStack_of_smoothPresentation_of_hasRepresentableDiagonal.{u, w} B S hS v h𝒴
    hdiag (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U) hv hrsurj
    (fun V y hy F hF he =>
      Space.isSmooth_of_isLocallyOfFinitePresentation_of_formallySmooth
        (hlfp V y hy F hF he) (hfs V y hy F hF he))

end AlgebraicGeometry.Stack

end
