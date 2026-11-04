module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.QuotientAtlasFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.QuotientAtlasPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.SmoothGroupoid
public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackRepresentableDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeSmooth

/-!
# The atlas of the quotient stack of a smooth groupoid is smooth and surjective

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `B` over a
scheme `S` of a big fppf site, and let `π : S_U ⟶ [U/R]` be the canonical projection of
Stacks 044R. **Stacks 04X0** says that if `G` is smooth (Stacks 04TH: its source and target maps
are smooth morphisms of algebraic spaces) then `π` is smooth and surjective.

Both adjectives are read in the sense of Stacks 04XB: `π` is representable by algebraic spaces,
and the property is tested on every algebraic space representing a base change of `π` along a
scheme-valued point of `[U/R]`. Smoothness in that sense is
`AlgebraicGeometry.Stack.IsRelativelySmooth`, and surjectivity is the relative property of
Stacks 03YK at `AlgebraicGeometry.Space.surjectiveMorphismProperty`.

## Main results

* `AlgebraicGeometry.Stack.QuotientAtlas.isRelativelySmooth`: the smoothness half of
  **Stacks 04X0**.
* `AlgebraicGeometry.Stack.QuotientAtlas.isRelativelySurjective`: the surjectivity half of
  **Stacks 04X0**.
* `AlgebraicGeometry.Stack.QuotientAtlas.isRelativelySmooth_isSurjective_of_bootstrap04S6`:
  **Stacks 04X0**, both halves together.

## Implementation notes

Both halves are `AlgebraicGeometry.Stack.QuotientAtlas.hasRelativeProperty` — descent along `π`
reduces a relative property of `π` to the same property of the source map `s` — read at the two
properties in question. Smoothness of `s` is the hypothesis, and surjectivity of `s` needs no
hypothesis at all, because the identity arrow at a point of the object space is a preimage of
that point: that is
`AlgebraicGeometry.Stack.QuotientAtlas.isSurjective_source`, the counterpart of the source's
remark that the groupoid identity `e : U ⟶ R` is a section of `s`. The surjectivity half is
therefore literally the surjectivity clause of Stacks 06FH,
`AlgebraicGeometry.Stack.QuotientAtlas.isSurjective`, and is
re-exported here rather than reproved.

Only smoothness of the source map is used; groupoid inversion identifies `s` with `t`, so the
smoothness hypothesis on `t` that Stacks 04TH carries plays no part. The hypothesis is
nevertheless taken in the packaged form `AlgebraicGeometry.GroupoidInAlgebraicSpaces.IsSmooth`,
which is how the source states it.

**What is built.** Both proofs build an
`AlgebraicGeometry.Stack.QuotientAtlas.Presentation`, which bundles the representability of `π`
that the source takes from Stacks 04WZ together with the identification of the 2-fibre product of
`π` with itself that the source takes from **Stacks 04M9**. The second of those is built for every
groupoid in algebraic spaces: `AlgebraicGeometry.Stack.QuotientAtlas.presentation` assembles a
`Presentation` from Stacks 04M9 and from the representability of `π` alone.

Representability of `π` the source takes from Stacks 04WZ and Stacks 045G, and Stacks 04WZ
rests, through Stacks 04TB and Stacks 04SK, on the bootstrap theorem Stacks 04S6 part (3): its
form here is `AlgebraicGeometry.Stack.representable_quotientStackProjectionHom`, from which the
presentation is built.

## References

* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 04M9](https://stacks.math.columbia.edu/tag/04M9)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 04TH](https://stacks.math.columbia.edu/tag/04TH)
* [Stacks Project, Tag 04WZ](https://stacks.math.columbia.edu/tag/04WZ)
* [Stacks Project, Tag 04X0](https://stacks.math.columbia.edu/tag/04X0)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 06FH](https://stacks.math.columbia.edu/tag/06FH)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.QuotientAtlas

universe u

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- **Stacks 04X0, smoothness of the projection.** Let `G = (U, R, s, t, c)` be a smooth
groupoid in algebraic spaces over `S`. Then the canonical projection `π : S_U ⟶ [U/R]` of
Stacks 044R is smooth in the sense of Stacks 04XB: it is representable by algebraic spaces, and
every algebraic space representing a base change of it along a scheme-valued point of `[U/R]` has
smooth structural morphism.

Only smoothness of the source map `s` is used. The 2-cartesian square of Stacks 04M9 is
`AlgebraicGeometry.Stack.QuotientAtlas.presentation`, built from the representability of the
projection, `AlgebraicGeometry.Stack.representable_quotientStackProjectionHom`. -/
@[stacks 04X0 "smoothness"]
theorem isRelativelySmooth {G : GroupoidInAlgebraicSpaces C S hS B}
    (hG : GroupoidInAlgebraicSpaces.IsSmooth C S hS G) :
    IsRelativelySmooth C S hS (quotientStackProjectionHom G) :=
  ⟨representable_quotientStackProjectionHom G,
    hasRelativeProperty.{u, u} (presentation G (representable_quotientStackProjectionHom G))
      (Space.smoothMorphismProperty C S hS) hG.1⟩

/-- **Stacks 04X0, surjectivity of the projection.** Let `G = (U, R, s, t, c)` be a groupoid
in algebraic spaces over `S`. Then the canonical projection `π : S_U ⟶ [U/R]` of
Stacks 044R is surjective in the sense of Stacks 04XB: every algebraic space representing a base
change of it along a scheme-valued point of `[U/R]` has surjective structural morphism.

No smoothness is needed: the source map of a groupoid is surjective because the identity arrow at
a point of the object space is a preimage of that point. -/
@[stacks 04X0 "surjectivity"]
theorem isRelativelySurjective {G : GroupoidInAlgebraicSpaces C S hS B} :
    HasRelativeProperty.{u, u + 1, u + 1, u} C S hS
      (Space.surjectiveMorphismProperty C S hS)
      (quotientStackProjectionHom G) (representable_quotientStackProjectionHom G) :=
  isSurjective.{u, u} (presentation G (representable_quotientStackProjectionHom G))

/-- **Stacks 04X0.** Let `G = (U, R, s, t, c)` be a smooth groupoid in algebraic spaces over
`S`. Then the canonical projection `π : S_U ⟶ [U/R]` of Stacks 044R is smooth and surjective in
the sense of Stacks 04XB: it is representable by algebraic spaces, and every algebraic space
representing a base change of it along a scheme-valued point of `[U/R]` has smooth and surjective
structural morphism.

Representability is `AlgebraicGeometry.Stack.representable_quotientStackProjectionHom` (Stacks
04WZ and 045G); everything else is built, the 2-cartesian square of Stacks 04M9 by
`AlgebraicGeometry.Stack.QuotientAtlas.presentation`. -/
@[stacks 04X0]
theorem isRelativelySmooth_isSurjective_of_bootstrap04S6 {G : GroupoidInAlgebraicSpaces C S hS B}
    (hG : GroupoidInAlgebraicSpaces.IsSmooth C S hS G) :
    IsRelativelySmooth C S hS (quotientStackProjectionHom G) ∧
      HasRelativeProperty.{u, u + 1, u + 1, u} C S hS
        (Space.surjectiveMorphismProperty C S hS)
        (quotientStackProjectionHom G) (representable_quotientStackProjectionHom G) :=
  ⟨isRelativelySmooth hG, isRelativelySurjective⟩

end AlgebraicGeometry.Stack.QuotientAtlas

end
