module

public import
  StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.RestrictionCoverings
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverCompare

/-!
# An isomorphism of groupoids induces an equivalence of quotient stacks

Let `(U, R, s, t, c)` and `(U', R', s', t', c')` be groupoids in algebraic spaces over an
algebraic space `B` over a scheme `S` of a big fppf site, and let `e` be an isomorphism between
them, i.e. a morphism whose maps on objects and on arrows are both invertible. Then the induced
1-morphism `[e] : [U/R] ⟶ [U'/R']` of quotient stacks of **Stacks 046Q** is an equivalence of
categories over the big fppf site.

## Main results

* `AlgebraicGeometry.Stack.nonempty_isEquivalenceOver_quotientStackMap_of_iso`: the induced
  1-morphism of quotient stacks is an equivalence over the site, as a
  `CategoryTheory.Functor.IsEquivalenceOver`.
* `AlgebraicGeometry.Stack.nonempty_equivalenceOver_quotientStack_of_iso`: the two quotient
  stacks are equivalent over the site, as a
  `CategoryTheory.StacksRepresentableCFG.EquivalenceOver`.

## Implementation notes

The proof is the criterion of **Stacks 046T**,
`AlgebraicGeometry.Stack.quotientStackMap_isEquivalenceOver_iff`, whose two clauses are both
immediate for an isomorphism.

The first clause asks that the square formed by the map on arrows and the two source–target maps
be cartesian. Its two horizontal maps are the map on arrows and the self-product of the map on
objects, and both are invertible — the first by
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.Iso.isIso_mapArrows`, the second by
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.Iso.isIso_mapObjects` and
`CategoryTheory.Limits.isIso_prod` — so the square is cartesian as soon as it commutes, by
`CategoryTheory.IsPullback.of_horiz_isIso`. Commutation is the pair of clauses
`Deformation.GroupoidInFunctors.Hom.map_source` and `map_target`, read on the two components of
the product through `CategoryTheory.Limits.prod.hom_ext`.

The second clause asks that the saturation map `U ×_{e, U', t'} R' ⟶ R' ⟶ U'` be a surjection of
fppf sheaves. An invertible map of presheaves is surjective on sections, hence locally
surjective (`CategoryTheory.Presheaf.isLocallySurjective_of_iso`), so this is the first of the
three sufficient conditions recorded with Stacks 046T,
`AlgebraicGeometry.Space.isLocallySurjective_source_pullback_snd`, applied to the map on objects.
That condition is stated with the presheaf pullback, which is the chosen fibre product of
algebraic spaces of the criterion on the nose.

`CategoryTheory.Functor.IsEquivalenceOver` does not record that its forward functor lies over the
site; the strict commutation is `(quotientStackMap e.hom).w`, and the two together give the
`CategoryTheory.StacksRepresentableCFG.EquivalenceOver` of the second result through
`CategoryTheory.StacksRepresentableCFG.EquivalenceOver.ofFunctorIsEquivalenceOver`.

## References

* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 046Q](https://stacks.math.columbia.edu/tag/046Q)
* [Stacks Project, Tag 046T](https://stacks.math.columbia.edu/tag/046T)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- The source–target square of an isomorphism of groupoids in algebraic spaces is cartesian:
both of its horizontal maps are invertible, and it commutes because the morphism of groupoids
preserves sources and targets. This is condition (1) of **Stacks 046T** for an isomorphism. -/
theorem isPullback_mapArrows_of_iso {G H : GroupoidInAlgebraicSpaces C S hS B}
    (e : GroupoidInAlgebraicSpaces.Iso G H) :
    IsPullback e.hom.toGroupoidHom.mapArrows
      (prod.lift G.toGroupoidInFunctors.source G.toGroupoidInFunctors.target)
      (prod.lift H.toGroupoidInFunctors.source H.toGroupoidInFunctors.target)
      (prod.map e.hom.toGroupoidHom.mapObjects e.hom.toGroupoidHom.mapObjects) := by
  have := e.isIso_mapObjects
  have := e.isIso_mapArrows
  refine IsPullback.of_horiz_isIso ⟨?_⟩
  refine prod.hom_ext ?_ ?_ <;>
    simp only [prod.comp_lift, prod.lift_map, prod.lift_fst, prod.lift_snd] <;> ext T a
  · exact e.hom.toGroupoidHom.map_source T a
  · exact e.hom.toGroupoidHom.map_target T a

/-- The saturation map of an isomorphism of groupoids in algebraic spaces is a surjection of fppf
sheaves. This is condition (2) of **Stacks 046T** for an isomorphism. -/
theorem isLocallySurjective_saturation_of_iso {G H : GroupoidInAlgebraicSpaces C S hS B}
    (e : GroupoidInAlgebraicSpaces.Iso G H) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS)
      ((GroupoidInAlgebraicSpaces.fiberProductSnd
          (ObjectProperty.homMk e.hom.toGroupoidHom.mapObjects : G.objects ⟶ H.objects)
          H.target ≫ H.source).hom) := by
  have := e.isIso_mapObjects
  exact Space.isLocallySurjective_source_pullback_snd e.hom inferInstance

/-- An isomorphism of groupoids in algebraic spaces induces an equivalence of quotient
stacks over the big fppf site. -/
theorem nonempty_isEquivalenceOver_quotientStackMap_of_iso
    {G H : GroupoidInAlgebraicSpaces C S hS B} (e : GroupoidInAlgebraicSpaces.Iso G H) :
    Nonempty (Functor.IsEquivalenceOver (quotientStack G).p (quotientStack H).p
      (quotientStackMap e.hom).toFunctor) :=
  (quotientStackMap_isEquivalenceOver_iff e.hom).mpr
    ⟨isPullback_mapArrows_of_iso e, isLocallySurjective_saturation_of_iso e⟩

/-- An isomorphism of groupoids in algebraic spaces makes the two quotient stacks equivalent over
the big fppf site, in the form that the representability criteria of **Stacks 04SV** and
**Stacks 02ZW** quantify over. -/
theorem nonempty_equivalenceOver_quotientStack_of_iso
    {G H : GroupoidInAlgebraicSpaces C S hS B} (e : GroupoidInAlgebraicSpaces.Iso G H) :
    Nonempty (StacksRepresentableCFG.EquivalenceOver (quotientStack G).p (quotientStack H).p) :=
  (nonempty_isEquivalenceOver_quotientStackMap_of_iso e).map
    (StacksRepresentableCFG.EquivalenceOver.ofFunctorIsEquivalenceOver
      (quotientStackMap e.hom).w)

end AlgebraicGeometry.Stack

end
