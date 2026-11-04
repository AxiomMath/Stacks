module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.QuotientAtlasPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackEquivalenceUniverses
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalEquivalenceInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackProjectionRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothGroupoidQuotientAtlas

/-!
# The atlas of a presentation of an algebraic stack is smooth and surjective

Let `S` be a scheme of a big fppf site, let `𝒳` be an algebraic stack over `S` and let
`P = ((U, R, s, t, c), [U/R] ≃ 𝒳)` be a presentation of it in the sense of Stacks 04TI. Then the
canonical projection `π : 𝒮_U ⟶ [U/R]` of Stacks 044R is representable by algebraic spaces,
smooth and surjective.

The three conclusions are those of **Stacks 04WZ** and **Stacks 04X0**. What this module adds is
that for a groupoid which *presents an algebraic stack* they need no hypothesis beyond the
algebraicity of `𝒳`, whereas the general statements of those two tags are only available in this
library on the bootstrap theorem Stacks 04S6, part (3), which it does not prove.

## Main results

* `AlgebraicGeometry.Stack.GroupoidPresentation.hasRepresentableDiagonal_quotientStackCFG`:
  the quotient stack of the presenting groupoid has representable diagonal, condition (1) of
  Stacks 045G.
* `AlgebraicGeometry.Stack.GroupoidPresentation.isRepresentableByAlgebraicSpaces_projection`:
  the conclusion of **Stacks 04WZ** for `π`, with nothing carried.
* `AlgebraicGeometry.Stack.GroupoidPresentation.quotientAtlasPresentation`: the Stacks 04M9 datum
  `AlgebraicGeometry.Stack.QuotientAtlas.Presentation` for the presenting groupoid, discharged.
* `AlgebraicGeometry.Stack.GroupoidPresentation.isRelativelySmooth_projection` and
  `AlgebraicGeometry.Stack.GroupoidPresentation.isRelativelySurjective_projection`: the two
  conclusions of **Stacks 04X0** for `π`, with nothing carried.

## Implementation notes

**The two conclusions.** The library's Stacks 04X0,
`AlgebraicGeometry.Stack.QuotientAtlas.isRelativelySmooth` and
`AlgebraicGeometry.Stack.QuotientAtlas.isRelativelySurjective`, holds for every smooth groupoid,
so the two conclusions here are its instances at the presenting groupoid. What this file adds is
a second route to the representability of `π` which needs no bootstrap: its target has a
representable diagonal, so `π` is representable by
`AlgebraicGeometry.Stack.representable_quotientStackProjection_of_hasRepresentableDiagonal` —
the implication (1) ⟹ (7) of Stacks 045G — and the diagonal of `[U/R]` is representable because
`𝒳`'s is and the two are equivalent over the site. That route gives
`AlgebraicGeometry.Stack.GroupoidPresentation.quotientAtlasPresentation`.

**Why the diagonal is transported through condition (3) of Stacks 045G.** The direct transport
`AlgebraicGeometry.Stack.hasRepresentableDiagonal_iff_of_equivalence` asks the two categories to
share their object and morphism universes, and `[U/R]` is a stackification, so its morphisms live
one universe above `𝒳`'s. Condition (3) — every 1-morphism from a scheme-represented category is
representable by algebraic spaces — is carried across equivalences in independent universes by
`AlgebraicGeometry.Stack.isRepresentableFromSchemes_of_equivalenceOver`, and the two conditions
are interchangeable by `...hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf` composed
with `...isAlgebraicSpaceIsomPresheaf_iff_isRepresentableFromSchemes`. That round trip is what
the proof below does.

The index universe of the algebraicity hypothesis is free: only its diagonal clause is used, and
that clause does not mention it.

## References

* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 04M9](https://stacks.math.columbia.edu/tag/04M9)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 04TI](https://stacks.math.columbia.edu/tag/04TI)
* [Stacks Project, Tag 04WZ](https://stacks.math.columbia.edu/tag/04WZ)
* [Stacks Project, Tag 04X0](https://stacks.math.columbia.edu/tag/04X0)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.GroupoidPresentation

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}

/-- Condition (1) of Stacks 045G is equivalent to its condition (3). -/
private theorem hasRepresentableDiagonal_iff_isRepresentableFromSchemes
    (𝒴 : CatFiberedInGroupoids.{u, _, u + 1, _} (BigFppfOver B S hS)) :
    HasRepresentableDiagonal B S hS 𝒴 ↔ IsRepresentableFromSchemes B S hS 𝒴 :=
  (hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS 𝒴).trans
    (isAlgebraicSpaceIsomPresheaf_iff_isRepresentableFromSchemes B S hS 𝒴)

/-- **The quotient stack of a presenting groupoid has representable diagonal.** If the smooth
groupoid `(U, R, s, t, c)` presents the algebraic stack `𝒳`, then `[U/R]` satisfies condition (1)
of Stacks 045G, because `𝒳` does and the two are equivalent over the site.

The transport runs through condition (3) of Stacks 045G, which is the form of the condition that
tolerates the universe gap between a stack and a stackification of it; see the implementation
notes. -/
theorem hasRepresentableDiagonal_quotientStackCFG
    (P : GroupoidPresentation B S hS 𝒳.val) (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val) :
    HasRepresentableDiagonal B S hS (quotientStackCFG B S hS P.groupoid) := by
  have hd𝒳 : HasRepresentableDiagonal B S hS 𝒳 := by
    rw [hasRepresentableDiagonal_iff]
    exact h𝒳.2.2.1
  exact (hasRepresentableDiagonal_iff_isRepresentableFromSchemes _).mpr
    (isRepresentableFromSchemes_of_equivalenceOver B S hS
      P.equivalence.toBasedEquivalence.symm
      ((hasRepresentableDiagonal_iff_isRepresentableFromSchemes _).mp hd𝒳))

/-- **The conclusion of Stacks 04WZ for the atlas of a presentation.** The canonical projection
`π : 𝒮_U ⟶ [U/R]` of Stacks 044R out of the object space of a groupoid presenting an algebraic
stack is representable by algebraic spaces.

This is the implication (1) ⟹ (7) of Stacks 045G applied to the representable diagonal of
`[U/R]`, so the bootstrap theorem Stacks 04S6 is not used. -/
theorem isRepresentableByAlgebraicSpaces_projection
    (P : GroupoidPresentation B S hS 𝒳.val) (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val) :
    IsRepresentableByAlgebraicSpaces B S hS (quotientStackProjectionHom P.groupoid).hom :=
  isRepresentableByAlgebraicSpaces_quotientStackProjectionHom_of_hasRepresentableDiagonal
    B S hS P.groupoid (hasRepresentableDiagonal_quotientStackCFG P h𝒳)

/-- **The Stacks 04M9 datum for the groupoid of a presentation, discharged.** The identification
of the canonical 2-fibre product of `π : 𝒮_U ⟶ [U/R]` with itself as the arrow space of the
groupoid, in the 2-category of categories fibred in groupoids — the hypothesis every consumer of
Stacks 04X0 and Stacks 06FH takes. Its one undischarged field, the representability of `π`, is
`AlgebraicGeometry.Stack.GroupoidPresentation.isRepresentableByAlgebraicSpaces_projection`. -/
noncomputable def quotientAtlasPresentation
    (P : GroupoidPresentation B S hS 𝒳.val) (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val) :
    QuotientAtlas.Presentation P.groupoid :=
  QuotientAtlas.presentation P.groupoid (isRepresentableByAlgebraicSpaces_projection P h𝒳)

/-- **The conclusion of Stacks 04X0, smoothness, for the atlas of a presentation.** The canonical
projection `π : 𝒮_U ⟶ [U/R]` out of the object space of a groupoid presenting an algebraic stack
is smooth in the sense of Stacks 04XB.

Smoothness of the groupoid is the `smooth` field of the presentation; nothing else is carried. -/
theorem isRelativelySmooth_projection
    (P : GroupoidPresentation B S hS 𝒳.val) (_h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val) :
    IsRelativelySmooth B S hS (quotientStackProjectionHom P.groupoid) :=
  QuotientAtlas.isRelativelySmooth P.smooth

/-- **The conclusion of Stacks 04X0, surjectivity, for the atlas of a presentation.** The
canonical projection `π : 𝒮_U ⟶ [U/R]` out of the object space of a groupoid presenting an
algebraic stack is surjective in the sense of Stacks 04XB.

No smoothness is needed for this half; the identity arrow at a point of the object space is a
preimage of that point. -/
theorem isRelativelySurjective_projection
    (P : GroupoidPresentation B S hS 𝒳.val) (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val) :
    HasRelativeProperty.{u, u + 1, u + 1, u} B S hS
      (Space.surjectiveMorphismProperty B S hS)
      (quotientStackProjectionHom P.groupoid)
      (isRepresentableByAlgebraicSpaces_projection P h𝒳) :=
  QuotientAtlas.isRelativelySurjective

end AlgebraicGeometry.Stack.GroupoidPresentation

end
