module

public import StacksFrontier.AlgebraicGeometry.Stacks.PresentationBaseChangeSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyBaseChange

/-!
# The base change of the atlas of a presentation is smooth and surjective

Let `S` be a scheme of a big fppf site, let `𝒳` be an algebraic stack over `S` and let
`P = ((U, R, s, t, c), [U/R] ≃ 𝒳)` be a presentation of it. Let `𝒵 ⟶ [U/R]` be any 1-morphism and
let a 2-fibre product square over the cospan `(𝒵 ⟶ [U/R], π : 𝒮_U ⟶ [U/R])` be given. Then its
projection to `𝒵` is representable by algebraic spaces, smooth and surjective.

## Main results

All in the namespace `AlgebraicGeometry.Stack.GroupoidPresentation`.

* `isRepresentableByAlgebraicSpaces_baseChangedProjection`: **Stacks 0302** for the base-changed
  atlas.
* `isRelativelySmooth_baseChangedProjection`: it is smooth in the sense of Stacks 04XB.
* `isRelativelySurjective_baseChangedProjection`: it is surjective in the sense of Stacks 04XB.

## Implementation notes

The base change is taken along a 1-morphism into the quotient stack `[U/R]`, not into `𝒳`:
`𝒮_U` and `[U/R]` are both `CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1}`, a universe
assignment Stacks 045C accepts for its three categories, so no universe lifting is needed.

The three universe arguments of Stacks 045C and of Stacks 0302 are given explicitly, since the
elaborator cannot solve `max u ?v =?= u + 1` for `?v`.

`AlgebraicGeometry.Stack.IsRelativelySmooth` bundles representability with the relative property
at `AlgebraicGeometry.Space.smoothMorphismProperty`. Surjectivity is stated as the relative
property alone, as in `AlgebraicGeometry.Stack.QuotientAtlas.isRelativelySurjective`.

## References

* [Stacks Project, Tag 0302](https://stacks.math.columbia.edu/tag/0302)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 04X0](https://stacks.math.columbia.edu/tag/04X0)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04Y6](https://stacks.math.columbia.edu/tag/04Y6)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.GroupoidPresentation

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
variable {𝒵 : CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver B S hS)}

/-- **Stacks 0302 for the base-changed atlas of a presentation.** The projection to `𝒵` of a
2-fibre product of a 1-morphism `𝒵 ⟶ [U/R]` with the canonical atlas `π : 𝒮_U ⟶ [U/R]` is
representable by algebraic spaces. -/
theorem isRepresentableByAlgebraicSpaces_baseChangedProjection
    (P : GroupoidPresentation B S hS 𝒳.val) (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (gt : 𝒵 ⟶ quotientStackCFG B S hS P.groupoid)
    (Q : Bicategory.TwoCommSq gt (quotientStackProjectionHom P.groupoid))
    (hQ : Bicategory.IsTwoFibreProduct Q) :
    IsRepresentableByAlgebraicSpaces B S hS Q.fst.hom :=
  isRepresentableByAlgebraicSpaces_baseChange.{u, u + 1, u} B S hS _ _ _
    (quotientStackProjectionHom P.groupoid) gt Q hQ
    (isRepresentableByAlgebraicSpaces_projection P h𝒳)

/-- **The base change of the atlas of a presentation is smooth.** The projection to `𝒵` of a
2-fibre product of a 1-morphism `𝒵 ⟶ [U/R]` with the canonical atlas `π : 𝒮_U ⟶ [U/R]` is
smooth. -/
theorem isRelativelySmooth_baseChangedProjection
    (P : GroupoidPresentation B S hS 𝒳.val) (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (gt : 𝒵 ⟶ quotientStackCFG B S hS P.groupoid)
    (Q : Bicategory.TwoCommSq gt (quotientStackProjectionHom P.groupoid))
    (hQ : Bicategory.IsTwoFibreProduct Q) :
    IsRelativelySmooth B S hS Q.fst :=
  ⟨isRepresentableByAlgebraicSpaces_baseChangedProjection P h𝒳 gt Q hQ,
    hasRelativeProperty_baseChange.{u, u + 1, u, u} B S hS
      (Space.smoothMorphismProperty B S hS)
      _ _ _ (quotientStackProjectionHom P.groupoid) gt Q hQ
      (isRepresentableByAlgebraicSpaces_projection P h𝒳)
      (isRelativelySmooth_projection P h𝒳).2⟩

/-- **The base change of the atlas of a presentation is surjective.** The projection to `𝒵` of a
2-fibre product of a 1-morphism `𝒵 ⟶ [U/R]` with the canonical atlas `π : 𝒮_U ⟶ [U/R]` is
surjective. -/
theorem isRelativelySurjective_baseChangedProjection
    (P : GroupoidPresentation B S hS 𝒳.val) (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (gt : 𝒵 ⟶ quotientStackCFG B S hS P.groupoid)
    (Q : Bicategory.TwoCommSq gt (quotientStackProjectionHom P.groupoid))
    (hQ : Bicategory.IsTwoFibreProduct Q) :
    HasRelativeProperty B S hS (Space.surjectiveMorphismProperty B S hS) Q.fst
      (isRepresentableByAlgebraicSpaces_baseChangedProjection P h𝒳 gt Q hQ) :=
  hasRelativeProperty_baseChange.{u, u + 1, u, u} B S hS
    (Space.surjectiveMorphismProperty B S hS)
    _ _ _ (quotientStackProjectionHom P.groupoid) gt Q hQ
    (isRepresentableByAlgebraicSpaces_projection P h𝒳)
    (isRelativelySurjective_projection P h𝒳)

end AlgebraicGeometry.Stack.GroupoidPresentation

end
