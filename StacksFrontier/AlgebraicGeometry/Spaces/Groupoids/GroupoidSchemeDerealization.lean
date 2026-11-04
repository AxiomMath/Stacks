module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSchemeDerealization.SpaceRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSchemeDerealization.RestrictionIdentityInverse
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSchemeDerealization.RestrictionComposablePairs
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSchemeDerealization.RestrictionCompRealization

/-!
# De-realizing an algebraic space of a big fppf site as a scheme

A scheme over `S` which a big fppf site over `S` contains represents an algebraic space over
`S`, and a groupoid scheme whose object scheme, arrow scheme and scheme of composable pairs the
site contains is realized as a groupoid in algebraic spaces by
`Stacks.Groupoids.GroupoidScheme.realization`.  This file goes the other way: an algebraic space
whose underlying presheaf is representable *is* the space represented by a scheme over `S` which
the site contains, a morphism from such a space to a represented space comes from a morphism of
schemes over `S`, and the arrow space of the restriction of a realization along a represented
morphism is the space represented by the arrow scheme of the restriction of the groupoid scheme.

## Main definitions

* `AlgebraicGeometry.schemeSpace` and `AlgebraicGeometry.schemeSpaceMap`: the
  algebraic space over `S` represented by a scheme over `S` which the site contains, and the
  morphism of algebraic spaces represented by a morphism of such schemes.
* `AlgebraicGeometry.Space.representingScheme` and
  `AlgebraicGeometry.Space.representingSchemeIso`: the scheme over `S` representing a
  representable presheaf on the site over `S`, and the identification of the two.
* `AlgebraicGeometry.Space.derealize`: the morphism of schemes over `S` underlying a morphism
  from a representable presheaf to a represented one.
* `Stacks.Groupoids.GroupoidScheme.restrictionArrowsRealizationIso`: the identification of the
  space represented by the arrow scheme of the restriction of a groupoid scheme with the
  iterated fibre product which is the arrow space of the restriction of its realization.
* `Stacks.Groupoids.GroupoidScheme.restrictionComposablePairs` and
  `Stacks.Groupoids.GroupoidScheme.composablePairsRealizationIso`: the scheme of composable
  pairs of arrows of the restriction of a groupoid scheme — the fibre product of its source and
  its target, on which its composition is defined — and the identification of the space it
  represents with the space of composable pairs of the restriction of the realization.
* `Stacks.Groupoids.GroupoidScheme.restrictionAmbientComp` and
  `Stacks.Groupoids.GroupoidScheme.restrictionComposition`: the composite in `G` of the two
  underlying arrows of a composable pair of a restriction, and the composition of the
  restriction itself, at the scheme level.
* `Stacks.Groupoids.GroupoidScheme.restrictionIdentity`: the identity arrow of a restriction at
  the scheme level, with `restrictionIdentity_comp_source`, `_comp_target` and
  `_comp_arrowsToArrows` computing it and
  `Stacks.Groupoids.GroupoidScheme.eq_restrictionIdentity_of_spec` saying those three identities
  determine it — which is what identifies the otherwise opaque `identity` field of the groupoid
  scheme that `AlgebraicGeometry.GroupoidScheme.restrict` produces by `Classical.choice`.
* `Stacks.Groupoids.GroupoidScheme.restrictionInverse`: the inverse of a restriction at the
  scheme level — the inverse in `G` of the underlying arrow, with the two endpoint lifts
  exchanged — with `restrictionInverse_comp_source`, `_comp_target` and `_comp_arrowsToArrows`
  computing it and `Stacks.Groupoids.GroupoidScheme.eq_restrictionInverse_of_spec` saying those
  three identities determine it, identifying `restrict`'s opaque `inverse` field.
* `Stacks.Groupoids.GroupoidScheme.restrictionIdentityPair_comp_restrictionComposition`: the
  identity arrow of a restriction is **idempotent**.  Together with its source and target this
  is everything needed to recognise it across the de-realization, because the pointwise identity
  of a groupoid in functors is characterised among arrows with equal source and target by being
  idempotent — `Deformation.GroupoidInFunctors.identity_eq_of_idempotent`.
* `Stacks.Groupoids.GroupoidScheme.restrictionInversePair_comp_restrictionComposition`: the
  inverse of an arrow of a restriction **composes with that arrow to the identity at its
  source**.  Together with `restrictionInverse_comp_source` and `_comp_target`, which exchange
  the two endpoints, this is what recognises the inverse across the de-realization, by the same
  route as the identity.

## Main results

* `AlgebraicGeometry.Space.schemeSiteObject_siteToOver_obj` and
  `AlgebraicGeometry.Space.schemeSiteMap_siteToOver_map`: an object, respectively a morphism, of
  the big fppf site over `S` is the scheme over `S`, respectively the morphism of schemes over
  `S`, that it determines, regarded in the site.
* `AlgebraicGeometry.Space.isEtale_schemeSpaceMap_iff`,
  `AlgebraicGeometry.Space.isSeparated_schemeSpaceMap_iff` and
  `AlgebraicGeometry.Space.isFinite_schemeSpaceMap_iff` and
  `AlgebraicGeometry.Space.isOpenImmersion_schemeSpaceMap_iff`: a morphism of schemes over `S`
  is étale, respectively separated, finite, or an open immersion, exactly when the morphism of
  algebraic spaces it represents is.
* `AlgebraicGeometry.Space.schemeSiteMap_pullback_hom_ext`: two morphisms of the site into a
  fibre product of schemes over `S` which the site contains agree as soon as their composites
  with the two projections agree.
* `AlgebraicGeometry.Space.schemeSiteMap_yoneda_injective`: two morphisms of schemes over `S`
  between schemes which the site contains agree as soon as the morphisms of presheaves they
  represent agree.
* `AlgebraicGeometry.Space.pullback_app_ext`: two sections of a pullback of presheaves of types
  agree as soon as their images under the two projections agree.
* `AlgebraicGeometry.Space.isPullback_comp_iso`: a cartesian square stays cartesian after
  composing each leg of its cospan with an isomorphism.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.restrictionCompositionData_underlying_eq`: the
  arrow underlying the composite of a composable pair of a restriction is the composite, in the
  ambient groupoid, of the two underlying arrows.
* `Deformation.GroupoidInFunctors.compose_source` and
  `Deformation.GroupoidInFunctors.compose_target`: the source of a composite is the source of
  the arrow composed first, and its target the target of the arrow composed last.  The
  repository had neither; both are read off the subtype that
  `Deformation.GroupoidInFunctors.evaluationArrowEquiv` lands in.
* `Deformation.GroupoidInFunctors.left_inverse_unique`: **left inverses in a groupoid in
  functors are unique** — two arrows composing with a given arrow to the identity at its source
  are equal.  Stated in terms of `compose` and `identity` only, which is what makes it provable:
  going through `Deformation.inverseArrow` instead drags in `Groupoid.inv` and the transport of
  the source and target indices along `Hom.map_source`/`Hom.map_target`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.restriction_arrow_ext`: **a section of the arrow
  space of a restriction is its source, its target and its underlying arrow of the ambient
  groupoid** — the space-level counterpart of
  `AlgebraicGeometry.GroupoidScheme.restriction_hom_ext`.  It comes from the restriction's
  `evaluation_fullyFaithful` field alone, so unlike the alternatives it needs no access to the
  restriction's composition, which the `Restriction` structure does not expose.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.restriction_identity_eq`: the identity of a
  restriction, recognised by having equal source and target and the ambient identity as its
  underlying arrow.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.restriction_left_inverse_unique`: the inverse of
  an arrow of a restriction, recognised by its endpoints and by its underlying arrow composing
  with that of the given arrow to the ambient identity.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.restrictionArrowsCompIso`: **restricting along a
  morphism precomposed with an isomorphism.**  The arrow space of the restriction along
  `E.hom ≫ g` is canonically isomorphic to the arrow space of the restriction along `g`, with
  `restrictionArrowsCompIso_hom_comp_arrowsToArrows`, `_hom_comp_source` and `_hom_comp_target`
  carrying the projection to the ambient arrows and the two endpoint lifts across — the latter
  two up to `E`, since the lifts live in the two different spaces.  This is what lets the output
  of a de-realization be used at all: de-realizing a representable algebraic space produces a
  scheme together with an *isomorphism* onto that space, so a restriction taken along a morphism
  out of the space must be compared with the restriction along the corresponding morphism out of
  the scheme.
* `Stacks.Groupoids.GroupoidScheme.restrictionComp_realization_eq`: **the comparison of the two
  compositions of a restriction**, which the rest of this file's de-realization is phrased
  around.  Its three clauses are
  `Stacks.Groupoids.GroupoidScheme.restrictionComp_realization_comp_source`, `_comp_target` and
  `_comp_arrowsToArrows`.
* `Stacks.Groupoids.GroupoidScheme.restrictionComp_realization_comp_source` and
  `Stacks.Groupoids.GroupoidScheme.restrictionComp_realization_comp_target`: the source and the
  target of the space-level composite of a composable pair, read through the two
  identifications, are those of the arrow composed first and of the arrow composed last.
* `Stacks.Groupoids.GroupoidScheme.restrictionComposition_comp_source`,
  `Stacks.Groupoids.GroupoidScheme.restrictionComposition_comp_target` and
  `Stacks.Groupoids.GroupoidScheme.restrictionComposition_comp_arrowsToArrows`: the source, the
  target and the underlying arrow of `G` of the composite of a composable pair, and
  `Stacks.Groupoids.GroupoidScheme.eq_restrictionComposition_of_spec`: those three identities
  determine the composition of a restriction.
* `AlgebraicGeometry.Space.derealize_spec`: the morphism of presheaves represented by
  `AlgebraicGeometry.Space.derealize` is the given one, read through the identification of its
  source with its representing scheme.
* `Stacks.Groupoids.GroupoidScheme.restrictionArrows_realizationMap_obj`: the arrow space of the
  restriction of a realization is that iterated fibre product.
* `Stacks.Groupoids.GroupoidScheme.restrictionArrowsRealizationIso_hom_comp_source`,
  `Stacks.Groupoids.GroupoidScheme.restrictionArrowsRealizationIso_hom_comp_target` and
  `Stacks.Groupoids.GroupoidScheme.restrictionArrowsRealizationIso_hom_comp_arrowsToArrows`:
  that identification carries the source, the target and the projection to the ambient arrow
  space of the restricted realization to the Yoneda images of those of the restricted groupoid
  scheme.
* `Stacks.Groupoids.GroupoidScheme.exists_etale_scheme_of_isRepresentable`: an algebraic space
  with representable underlying presheaf, étale over the object space of a realization, is the
  space represented by a scheme over `S` which is étale over the object scheme.

## Implementation notes

De-realization of objects and of morphisms is definitional rather than constructed: an object of
the big fppf site over `S` is a scheme of the site together with a morphism to `S`, which is what
`AlgebraicGeometry.Space.schemeSiteObject` builds, so
`AlgebraicGeometry.Space.schemeSiteObject_siteToOver_obj` and
`AlgebraicGeometry.Space.schemeSiteMap_siteToOver_map` hold by reflexivity.  What
representability of a presheaf then supplies is the scheme itself, through
`CategoryTheory.Functor.reprX`.

The arrow space of the restriction of a groupoid in algebraic spaces is an iterated fibre
product, and the arrow scheme of the restriction of a groupoid scheme is the same iterated fibre
product taken in schemes over `S`.  The identification of the two is assembled from three
applications of `AlgebraicGeometry.Space.yonedaSchemePullbackIso`: the outer square of the
scheme-level iterated fibre product is carried by Yoneda to a cartesian square of presheaves,
whose cospan is identified with the cospan of the space-level iterated fibre product by the two
inner applications.  Both are then cartesian squares on the same cospan, so their vertices agree
by `CategoryTheory.IsPullback.isoIsPullback`.

The composition of the restricted groupoid IS compared here, by
`Stacks.Groupoids.GroupoidScheme.restrictionComp_realization_eq`.  A groupoid in algebraic spaces
carries its groupoid structure as a pointwise condition rather than as structure morphisms, so
that comparison — of `AlgebraicGeometry.GroupoidInAlgebraicSpaces.restrictionComp` with the
composition supplied by `AlgebraicGeometry.GroupoidScheme.restrict` — is a separate statement,
and it needs three ingredients.

Its domain is de-realized by
`Stacks.Groupoids.GroupoidScheme.composablePairsRealizationIso`, built from
`AlgebraicGeometry.Space.yonedaSchemePullbackIso` exactly as the arrow identification is.  The
scheme-level composition is pinned down: `Stacks.Groupoids.GroupoidScheme.restrictionComposition`
is constructed explicitly, its source, target and underlying arrow of `G` are computed by
`Stacks.Groupoids.GroupoidScheme.restrictionComposition_comp_source`, `_comp_target` and
`_comp_arrowsToArrows`, and
`Stacks.Groupoids.GroupoidScheme.eq_restrictionComposition_of_spec` says those three identities
determine it — this is `AlgebraicGeometry.GroupoidScheme.restriction_hom_ext`, that a generalized
point of the arrow scheme of a restriction is its source, its target and its underlying arrow.
And the space-level `restrictionComp`, read through the two identifications, satisfies those same
three identities: `Stacks.Groupoids.GroupoidScheme.restrictionComp_realization_comp_source` and
`_comp_target` come from the fields `hom_source` and `hom_target` of
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.RestrictionCompositionData`, and
`_comp_arrowsToArrows` from `hom_comp`.

That third clause is the one that needs `underlying`, which
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.RestrictionCompositionData` characterises only
section by section.  It is given a morphism-level form by
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.restrictionCompositionData_underlying_eq`:
`underlying` is `restrictionUnderlyingLift` followed by the ambient composition.  That lemma is
stated for an ARBITRARY groupoid in algebraic spaces rather than for a realization, which is what
makes it provable — for a realization the two sides carry
`yoneda.obj (schemeSiteObject C hS hR)` and `(G.realization ...).arrows.obj`, equal only by `rfl`
through `Stacks.Groupoids.GroupoidScheme.realization_arrows`, and no rewrite survives that.  Its
own proof is the only element-level argument in the file: both sides are sections of the ambient
space of composable pairs, so `AlgebraicGeometry.Space.pullback_app_ext` reduces the equality to
the two underlying arrows.  With it, the clause itself is ordinary morphism-level work:
`Stacks.Groupoids.GroupoidScheme.realization_comp` expands the ambient composition, and
`pullback.hom_ext` reduces what remains to
`Stacks.Groupoids.GroupoidScheme.composablePairsRealizationIso_comp_underlyingFst`/`Snd` against
`restrictionAmbientLift_comp_fst`/`_snd` and
`AlgebraicGeometry.Space.yonedaSchemePullbackIso_hom_fst`/`_snd`.  The comparison is then
assembled by de-realizing the space-level composition with
`AlgebraicGeometry.Space.schemeSiteMap_yoneda_injective` and feeding the three clauses to
`eq_restrictionComposition_of_spec`.

Five facts about this layer, each of which cost a pass to find.  `rw` and `simp only` are
unusable wherever a term's type is defeq but not syntactically equal to the one the goal carries
— the `realization_arrows` and `restrictionArrows` unfoldings above, and the `restrictionSource`/
`restrictionTarget`/`restrictionArrowsToArrows` definitions, which unfold `restrictionArrows`
inside the types and leave terms that are not type-correct at `implicit` transparency, after
which even `pullback.lift_fst_assoc` silently fails to match.  `calc` is unusable for the same
reason, with a different symptom: it reports `failed to synthesize Trans Eq Eq ?m`, because its
two `Eq`s sit at those different types; chains of `refine (...).trans ?_` do the same work and
tolerate defeq, but `_` for an inferable argument inside one of them reintroduces the same error
as an unsolved metavariable.  `simpa only [Iso.inv_hom_id_assoc]` will not collapse
`iso.inv ≫ iso.hom ≫ f`; `AlgebraicGeometry.Space.yonedaSchemePullbackIso` compatibilities are
turned round with `Iso.inv_comp_eq` instead.  `simp only [CategoryTheory.hom_comp]` does not fire
on the `(f ≫ g).hom` of a morphism of `AlgebraicGeometry.AlgebraicSpaces`; an explicit type
ascription plus `congrArg (fun f => f.hom)` does.  And an app equation is extracted as
`congrArg (fun k => k z) (NatTrans.congr_app h T)` — in one step
`congrArg (fun k => k.app T z) h` leaves `k`'s type a metavariable so `k.app T` stays a `⟶` and
will not apply to `z`, `ConcreteCategory.congr_hom` finds no `ConcreteCategory (Type u) ?m`
instance, and `congrFun` cannot see through `⟶`.

## References

* [Stacks Project, Tag 0231](https://stacks.math.columbia.edu/tag/0231)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 044B](https://stacks.math.columbia.edu/tag/044B)
-/
