module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackProjection
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStack
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteria
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaAlgebraicSpaceSources
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaProductsToDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaRepresentableProducts
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaRepresentableSources
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaSchemePoints
public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackProjectionLocalEssSurj

/-!
# Representability of the projection to a quotient stack

Let `G` be a groupoid in algebraic spaces `(U, R, s, t, c)` over an algebraic space `B` over a
scheme `S` of a big fppf site, and let `π : S_U ⟶ [U/R]` be the canonical projection from the
object-space fibration to the quotient stack (**Stacks 044R**,
`AlgebraicGeometry.Stack.quotientStackProjection`). This module shows that `π` is representable
by algebraic spaces as soon as the quotient stack has representable diagonal.

The source map's flatness and finiteness play no part here; they bear on the *properties* of `π`,
not on its representability.

## Main results

* `AlgebraicGeometry.Stack.isRepresentableFromAlgebraicSpaces_of_hasRepresentableDiagonal`:
  the implication (1) ⟹ (7) of the diagonal criteria — a category fibred in groupoids with
  representable diagonal receives every 1-morphism from a category fibred in groupoids
  representable by an algebraic space representably.
* `AlgebraicGeometry.Stack.quotientStackCFG`: the quotient stack packaged as a category fibred
  in groupoids.
* `AlgebraicGeometry.Stack.representable_quotientStackProjection_of_hasRepresentableDiagonal`:
  the projection to the quotient stack is representable by algebraic spaces once the quotient
  stack has representable diagonal.

## Implementation notes

The first result is the composite of the six equivalences of the diagonal criteria,
beginning at `AlgebraicGeometry.Stack.hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf`
and ending at the equivalence of conditions (6) and (7).
Conditions (6) and (8) carry two universe parameters for the second of the two categories fibred
in groupoids which conditions (5) and (7) do not mention; the chain instantiates them at `u` and
`u + 1`, any choice doing equally well because the chain enters and leaves (6) by equivalences
holding at every choice.

The second result is the first applied to the object-space fibration, which is representable by
the object space itself (`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_fibredCategory`,
**Stacks 04SV**), and to the projection.

No `@[stacks]` attribute is placed on any of the three declarations.

The diagonal criteria of **Stacks 045G** already carry their sites, one on each of the seven
equivalences, and the first result below is a composite of six of them rather than new
content, so a site here would be a second site for content already covered.

**Stacks 06FH** asserts that the projection is flat, locally of finite presentation and
surjective; representability of the projection is what makes those three assertions expressible
and is the first of the four declarations the tag covers. The result below is *hypothesis-borne
on the representable diagonal*, which is not a hypothesis of Stacks 06FH — there it is a
consequence of **Stacks 04WZ**, the statement that the diagonal of a quotient stack is
representable by algebraic spaces, which is not yet available in this development. So the
statement below is weaker than the tag's and carries no `06FH` site. Once Stacks 04WZ is
available the unconditional form is this result applied to it.
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w v₁ w₁

variable (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)

/-- Condition (1) of the diagonal criteria implies condition (7): if the diagonal of `𝒳` is
representable by algebraic spaces, then every 1-morphism to `𝒳` from a category fibred in
groupoids representable by an algebraic space is representable by algebraic spaces.

This is the composite of the six equivalences (1) ↔ (2) ↔ ⋯ ↔ (7). -/
theorem isRepresentableFromAlgebraicSpaces_of_hasRepresentableDiagonal
    (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver C S hS))
    (hdiag : HasRepresentableDiagonal C S hS 𝒳) :
    IsRepresentableFromAlgebraicSpaces.{u, v, w, v₁, w₁} C S hS 𝒳 :=
  (hasAlgebraicSpaceRepresentableProducts_iff_isRepresentableFromAlgebraicSpaces.{u,
      v, w, v₁, w₁, u, u + 1} C S hS 𝒳).mp
    ((representableFromCategories_iff_algebraicSpaceProducts.{u, v, w, v₁, w₁, u, u + 1}
        C S hS 𝒳).mp
      ((hasAlgebraicSpaceSchemePointProducts_iff_isRepresentableFromRepresentableCategories.{u,
          v, w, v₁, w₁} C S hS 𝒳).mp
        ((isRepresentableFromSchemes_iff_hasAlgebraicSpaceSchemePointProducts C S hS 𝒳).mp
          ((isAlgebraicSpaceIsomPresheaf_iff_isRepresentableFromSchemes C S hS 𝒳).mp
            ((hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf C S hS 𝒳).mp hdiag)))))

variable {B : AlgebraicSpaces C S hS}

/-- The quotient stack of a groupoid in algebraic spaces, packaged as a category fibred in
groupoids over the big fppf site. -/
noncomputable def quotientStackCFG (G : GroupoidInAlgebraicSpaces C S hS B) :
    CatFiberedInGroupoids (BigFppfOver C S hS) :=
  CatFiberedInGroupoids.mk (quotientStack G) (isFiberedInGroupoids_quotientStack G)

/-- The canonical projection from the object-space fibration of a groupoid in algebraic spaces
to its quotient stack is representable by algebraic spaces, provided the quotient stack has
representable diagonal.

The object-space fibration is representable by the object space, so this is condition (7) of the
diagonal criteria applied to the projection. -/
theorem representable_quotientStackProjection_of_hasRepresentableDiagonal
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (hdiag : HasRepresentableDiagonal C S hS (quotientStackCFG C S hS G)) :
    IsRepresentableByAlgebraicSpaces C S hS (quotientStackProjection G) :=
  isRepresentableFromAlgebraicSpaces_of_hasRepresentableDiagonal.{u, u + 1, u + 1, u, u + 1}
    C S hS (quotientStackCFG C S hS G) hdiag
    (fibredCategory C S hS G.objects.obj)
    (isRepresentableByAlgebraicSpace_fibredCategory C S hS G.objects.obj G.objects.property)
    (quotientStackProjection G)

/-- The bundled projection `quotientStackProjectionHom` is representable by algebraic spaces once
the quotient stack has representable diagonal.

This is the junction between the two halves of the question. The unbundled projection
`quotientStackProjection` is a 1-morphism of based categories at *different* hom universes —
`BasedCategory.{u, u + 1}` to `BasedCategory.{u + 1, u + 1}` — which
`IsRepresentableByAlgebraicSpaces` accepts, being universe-heterogeneous in its source and
target, taking the two at independent universes. `HasRelativeProperty`, by
contrast, pins both sides to one `BasedCategory.{v, w}`, so the relative properties of the
projection are stated for `quotientStackProjectionHom`, whose source has had its hom universe
lifted. `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_quotientStackProjectionHom`
carries representability across that lift; this result composes it with the diagonal criteria, so
that the representability witness every relative property of the projection needs is available
from the representable diagonal alone. -/
theorem isRepresentableByAlgebraicSpaces_quotientStackProjectionHom_of_hasRepresentableDiagonal
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (hdiag : HasRepresentableDiagonal C S hS (quotientStackCFG C S hS G)) :
    IsRepresentableByAlgebraicSpaces C S hS (quotientStackProjectionHom G).hom :=
  isRepresentableByAlgebraicSpaces_quotientStackProjectionHom G
    (representable_quotientStackProjection_of_hasRepresentableDiagonal C S hS G hdiag)

end AlgebraicGeometry.Stack

end
