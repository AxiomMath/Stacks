module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.FullFaithfulness
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.RestrictionComparison

/-!
# The quotient stack of a restriction maps fully faithfully (Stacks 046S for a restriction)

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `B` over a
scheme `S` of a big fppf site, and let `g : U' ⟶ U` be any morphism of algebraic spaces. The
restriction `G|_{U'}` of Stacks 044B comes with a canonical morphism of groupoids to `G`, and
Stacks 046S says that the induced 1-morphism `[U'/R'] ⟶ [U/R]` of quotient stacks (Stacks 046Q)
is fully faithful exactly when the square

```
  R' ⟶ R
  ↓     ↓
U'×U' ⟶ U×U
```

is cartesian. For a restriction it is, by construction and with no hypothesis: that is what
being the restriction means.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isPullback_restrictionSourceTarget`: the square
  above is cartesian, for the chosen restriction of Stacks 044B along an arbitrary `g`.
* `AlgebraicGeometry.Stack.fullyFaithful_quotientStackMap_restrict`: **Stacks 046S** at that
  square — the induced 1-morphism `[U'/R'] ⟶ [U/R]` is fully faithful.

## Implementation notes

The cartesian square is `CategoryTheory.Limits.isPullback_prodLift_of_isPullback` of
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.RestrictionComparison`, read in the
category of presheaves on the big fppf site rather than in the slice over the base, which is
where Stacks 046S states its hypothesis. The three cartesian squares it consumes are the
defining squares of the three chosen presheaf fibre products out of which
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.restrictionArrows` is built, each flipped: the
generic lemma names the two endpoint fibre products in the order `(U' ×_{g, U, t} R)` and
`(R ×_{s, U, g} U')` and produces `prod.lift t s`, whereas Stacks 046S asks for
`prod.lift s t`, so the two are fed in with their roles exchanged. The third projection of the
conclusion is the composite through the *other* endpoint fibre product, and is identified with
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.restrictionArrowsToArrows` by the defining
compatibility of the outer fibre product.

Nothing here is tagged for Stacks 044B or 046Q; the one source statement used is Stacks 046S,
whose library form is `AlgebraicGeometry.Stack.fullyFaithful_quotientStackMap_iff_isPullback`,
and restating it at one instance does not claim the tag again.

## References

* [Stacks Project, Tag 044B](https://stacks.math.columbia.edu/tag/044B)
* [Stacks Project, Tag 044D](https://stacks.math.columbia.edu/tag/044D)
* [Stacks Project, Tag 046Q](https://stacks.math.columbia.edu/tag/046Q)
* [Stacks Project, Tag 046S](https://stacks.math.columbia.edu/tag/046S)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B)
  {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects)

/-- **The arrow space of a restriction is the fibre product of `U' × U'` with `R` over `U × U`.**
For an arbitrary morphism `g : U' ⟶ U` to the object space of a groupoid in algebraic spaces,
the square formed by the projection of the restricted arrows to the arrows of `G`, the pair
(source, target) of the restriction, the pair (source, target) of `G` and the self-product of
`g` is cartesian in the category of presheaves on the big fppf site of `S`.

This is Stacks 044D read with the plain product of presheaves in place of the fibre product over
the base, which is the form the hypothesis of Stacks 046S takes. -/
theorem isPullback_restrictionSourceTarget :
    IsPullback (restrictionArrowsToArrows G g).hom
      (prod.lift (restrictionSource G g).hom (restrictionTarget G g).hom)
      (prod.lift G.source.hom G.target.hom) (prod.map g.hom g.hom) := by
  have hp : IsPullback
      (pullback.snd (pullback.snd g.hom G.target.hom) (pullback.fst G.source.hom g.hom))
      (pullback.fst (pullback.snd g.hom G.target.hom) (pullback.fst G.source.hom g.hom))
      (pullback.fst G.source.hom g.hom) (pullback.snd g.hom G.target.hom) :=
    (IsPullback.of_hasPullback _ _).flip
  have key := isPullback_prodLift_of_isPullback (IsPullback.of_hasPullback G.source.hom g.hom).flip
    (IsPullback.of_hasPullback g.hom G.target.hom).flip hp
  rw [hp.w] at key
  exact key.flip

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

namespace AlgebraicGeometry.Stack

open GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B)
  {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects)

/-- **Stacks 046S for a restriction.** The 1-morphism `[U'/R'] ⟶ [U/R]` of Stacks 046Q induced
by the canonical morphism from the restriction of a groupoid in algebraic spaces along an
arbitrary morphism `g : U' ⟶ U` to the groupoid itself is fully faithful.

Its hypothesis, that the source–target square of the morphism of groupoids be cartesian, is
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.isPullback_restrictionSourceTarget`, which holds
for every restriction with no hypothesis on `g`. -/
theorem fullyFaithful_quotientStackMap_restrict :
    Nonempty (quotientStackMap (G.restrict g).hom).toFunctor.FullyFaithful :=
  (fullyFaithful_quotientStackMap_iff_isPullback (G.restrict g).hom).mpr
    (isPullback_restrictionSourceTarget G g)

end AlgebraicGeometry.Stack

end
