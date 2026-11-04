module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothMorphismProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatPresentationRepresentableDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyComp
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityComp
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDeligneMumford

/-!
# A smooth surjective presentation by an algebraic space makes a stack algebraic

Let `v : 𝒰 ⟶ 𝒳` be a 1-morphism of stacks in groupoids over the big fppf site of a scheme `S`
with `𝒰` representable by an algebraic space and `v` representable by algebraic spaces,
surjective and smooth. **Stacks 05UL** says that `𝒳` is then an algebraic stack.

Of the four clauses of **Stacks 026O** the first two are the hypotheses on `𝒳`. The diagonal
clause is **Stacks 05XW**, applied to `v`, which is flat and locally of finite presentation
because it is smooth (Stacks 03ZF and Stacks 04AJ). The presentation clause needs a *scheme*
atlas: a surjective smooth scheme atlas of `𝒰` exists because `𝒰` is itself an algebraic stack
(Stacks 026O for a representable category), and its composite with `v` is representable,
surjective and smooth by **Stacks 0301** and **Stacks 045B**.

## Main results

* `AlgebraicGeometry.Stack.isAlgebraicStack_of_smoothPresentation`: **Stacks 05UL**.
* `AlgebraicGeometry.Stack.isAlgebraicStack_of_smoothPresentation_of_hasRepresentableDiagonal`:
  the same conclusion from a diagonal already known to be representable by algebraic spaces,
  which needs no bootstrap theorem.

## Implementation notes

The stack condition on `𝒳` is taken in the sieve-indexed rendering
`CategoryTheory.Functor.IsStack` of Stacks 026F rather than the family-indexed
`CategoryTheory.Functor.IsStackInGroupoids` of Stacks 02ZI, and that choice is what makes the
proof short. The two renderings are the conditions (1) and (3) of Stacks 02ZJ; of the two
implications between them only `CategoryTheory.Functor.IsStack.isStackInGroupoids`, from the
sieve-indexed one to the family-indexed one at every descent universe, is available in this
library — the converse is not, and is not applicable at the index universe `u + 1` in which the
fppf covering families of the big site live (see the module docstring of
`StacksFrontier/AlgebraicGeometry/Stacks/RepresentableStackInSetoids.lean`). Both renderings are
renderings of the source's single notion "`𝒳` is a stack", so either may be assumed; but from
the sieve-indexed one both conjuncts of the stack clause of
`AlgebraicGeometry.Stack.IsAlgebraicStack` are immediate, at an arbitrary descent universe `w`,
and Stacks 05XW consumes it as it stands. Assuming the family-indexed one instead would leave
the first conjunct to be recovered through the unavailable implication, which is the only thing
the quotient-stack detour of the source — identify `𝒳` with `[U/R]` for the groupoid of the
presentation and read the stack condition off the quotient — is there to do.

The source also assumes `𝒰` to be a stack in groupoids; as in Stacks 05XW that is not needed,
being a consequence of its representability by an algebraic space (Stacks 04SZ).

## References

* [Stacks Project, Tag 026O](https://stacks.math.columbia.edu/tag/026O)
* [Stacks Project, Tag 0301](https://stacks.math.columbia.edu/tag/0301)
* [Stacks Project, Tag 03ZF](https://stacks.math.columbia.edu/tag/03ZF)
* [Stacks Project, Tag 045B](https://stacks.math.columbia.edu/tag/045B)
* [Stacks Project, Tag 04AJ](https://stacks.math.columbia.edu/tag/04AJ)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 05UL](https://stacks.math.columbia.edu/tag/05UL)
* [Stacks Project, Tag 05XW](https://stacks.math.columbia.edu/tag/05XW)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒰 𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}

/-- **Stacks 05UL.** A stack in groupoids over the big fppf site of `S` which receives a
1-morphism from a category representable by an algebraic space that is representable by
algebraic spaces, surjective and smooth is an algebraic stack. -/
@[stacks 05UL]
theorem isAlgebraicStack_of_smoothPresentation (v : 𝒰 ⟶ 𝒳)
    (h𝒳 : 𝒳.val.p.IsStack (BigFppfOver.topology B S hS))
    (h𝒰 : IsRepresentableByAlgebraicSpace B S hS 𝒰)
    (hv : IsRepresentableByAlgebraicSpaces B S hS v.hom)
    (hsurj : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (Space.surjectiveMorphismProperty B S hS) v hv)
    (hsmooth : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (Space.smoothMorphismProperty B S hS) v hv) :
    IsAlgebraicStack.{u, w} B S hS 𝒳.val := by
  refine ⟨𝒳.isFiberedInGroupoids,
    ⟨h𝒳, h𝒳.isStackInGroupoids 𝒳.isFiberedInGroupoids⟩, ?_, ?_⟩
  · exact hasRepresentableDiagonal_of_flatPresentation.{u, u + 1, u + 1} B S hS v h𝒳 h𝒰 hv hsurj
      (fun V y hy F hF he => Space.isFlat_of_isSmooth B S hS _ (hsmooth V y hy F hF he))
      (fun V y hy F hF he =>
        Space.isLocallyOfFinitePresentation_of_isSmooth B S hS (hsmooth V y hy F hF he))
  · obtain ⟨hUfib, hUstk, hUdiag, hUatlas⟩ :=
      isAlgebraicStack_of_isRepresentableByAlgebraicSpace.{u, w} B S hS 𝒰 h𝒰
    obtain ⟨U, g, hg, hgprop⟩ := hUatlas
    let gCat : schemeFibredCategory B S hS U ⟶ 𝒰 := Bicategory.InducedBicategory.mkHom g
    have hgCat : IsRepresentableByAlgebraicSpaces B S hS gCat.hom := hg
    have hcomp : IsRepresentableByAlgebraicSpaces B S hS (gCat ≫ v).hom :=
      isRepresentableByAlgebraicSpaces_comp B S hS gCat v hgCat hv
    have hgsurj : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
        (Space.surjectiveMorphismProperty B S hS) gCat hgCat :=
      fun V y hy F hF he => (hgprop V y hy F hF he).1
    have hgsmooth : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
        (Space.smoothMorphismProperty B S hS) gCat hgCat :=
      fun V y hy F hF he => (hgprop V y hy F hF he).2
    refine ⟨U, (gCat ≫ v).hom, hcomp, fun V y hy F hF he => ⟨?_, ?_⟩⟩
    · exact hasRelativeProperty_comp B S hS (Space.surjectiveMorphismProperty B S hS)
        gCat v hgCat hv hgsurj hsurj V y hy F hF he
    · exact hasRelativeProperty_comp B S hS (Space.smoothMorphismProperty B S hS)
        gCat v hgCat hv hgsmooth hsmooth V y hy F hF he

/-- **Stacks 05UL for a stack whose diagonal is already known to be representable by algebraic
spaces.** A stack in groupoids over the big fppf site of `S` with a diagonal representable by
algebraic spaces which receives a 1-morphism from a category representable by an algebraic space
that is representable by algebraic spaces, surjective and smooth is an algebraic stack.

Of the four clauses of Stacks 026O only the presentation clause is proved here, and it needs no
bootstrap theorem: the source `𝒰` is an algebraic stack because it is representable by an
algebraic space (Stacks 026O for a representable category), so it has a surjective smooth scheme
atlas, and the composite of that atlas with `v` is representable, surjective and smooth by
Stacks 0301 and Stacks 045B. It is the diagonal clause alone that
`AlgebraicGeometry.Stack.isAlgebraicStack_of_smoothPresentation` obtains from Stacks 05XW. -/
theorem isAlgebraicStack_of_smoothPresentation_of_hasRepresentableDiagonal (v : 𝒰 ⟶ 𝒳)
    (h𝒳 : 𝒳.val.p.IsStack (BigFppfOver.topology B S hS))
    (hdiag : HasRepresentableDiagonal B S hS 𝒳)
    (h𝒰 : IsRepresentableByAlgebraicSpace B S hS 𝒰)
    (hv : IsRepresentableByAlgebraicSpaces B S hS v.hom)
    (hsurj : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (Space.surjectiveMorphismProperty B S hS) v hv)
    (hsmooth : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (Space.smoothMorphismProperty B S hS) v hv) :
    IsAlgebraicStack.{u, w} B S hS 𝒳.val := by
  refine ⟨𝒳.isFiberedInGroupoids,
    ⟨h𝒳, h𝒳.isStackInGroupoids 𝒳.isFiberedInGroupoids⟩, hdiag, ?_⟩
  obtain ⟨hUfib, hUstk, hUdiag, hUatlas⟩ :=
    isAlgebraicStack_of_isRepresentableByAlgebraicSpace.{u, w} B S hS 𝒰 h𝒰
  obtain ⟨U, g, hg, hgprop⟩ := hUatlas
  let gCat : schemeFibredCategory B S hS U ⟶ 𝒰 := Bicategory.InducedBicategory.mkHom g
  have hgCat : IsRepresentableByAlgebraicSpaces B S hS gCat.hom := hg
  have hcomp : IsRepresentableByAlgebraicSpaces B S hS (gCat ≫ v).hom :=
    isRepresentableByAlgebraicSpaces_comp B S hS gCat v hgCat hv
  have hgsurj : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (Space.surjectiveMorphismProperty B S hS) gCat hgCat :=
    fun V y hy F hF he => (hgprop V y hy F hF he).1
  have hgsmooth : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (Space.smoothMorphismProperty B S hS) gCat hgCat :=
    fun V y hy F hF he => (hgprop V y hy F hF he).2
  refine ⟨U, (gCat ≫ v).hom, hcomp, fun V y hy F hF he => ⟨?_, ?_⟩⟩
  · exact hasRelativeProperty_comp B S hS (Space.surjectiveMorphismProperty B S hS)
      gCat v hgCat hv hgsurj hsurj V y hy F hF he
  · exact hasRelativeProperty_comp B S hS (Space.smoothMorphismProperty B S hS)
      gCat v hgCat hv hgsmooth hsmooth V y hy F hF he

end AlgebraicGeometry.Stack

end
