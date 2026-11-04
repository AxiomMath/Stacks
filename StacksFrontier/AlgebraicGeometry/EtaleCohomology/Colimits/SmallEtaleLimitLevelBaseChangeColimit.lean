module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleLimitLevelCrossing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleLimitColimitMainstreamSite

/-!
# Stacks 0EYN, second half, in the base-change vocabulary of Stacks 09YQ

`Stacks.EtaleCohomology.AffineLimitCohomology.restrictionIsColimitAb_limitToEtaleSite` states
`F = colim_i p_i^{-1}p_{i, *}F` for an abelian sheaf on Mathlib's small étale site of a limit
`X = lim X_i` of schemes with affine transition morphisms, with the restrictions taken along the
canonical functors `toLimitSmall i` of the system of sites of [Stacks, Tag 0EYL], composed with
the two bounded-site crossings. The statements of [Stacks, Tag 09YQ] are about something else:
the restrictions along **base change of the projection `X → X_i` of the limit cone**, on Mathlib's
small étale sites throughout.

The two agree only up to isomorphism —
`Stacks.EtaleCohomology.AffineLimitCohomology.levelCrossingIso` — because a level of the system
of [Stacks, Tag 0EYL] is a category of *chosen* pullback models and base change on Mathlib's site
is the *chosen* fibre product, so the comparison is `CategoryTheory.IsPullback.isoPullback` and
no equality is available. This file carries the universal property across that isomorphism.

## Main results

* `Stacks.EtaleCohomology.AffineLimitCohomology.restrictionIsColimitAb_levelBaseChange` —
  **[Stacks, Tag 0EYN], second half, with the restrictions taken along base change along the
  projections of the limit cone**: for every abelian sheaf `F` on Mathlib's small étale site of
  `X = lim X_i`, every family of maps out of the restrictions of `F` along
  `Stacks.EtaleCohomology.AffineLimitCohomology.levelBaseChangeCrossing`, compatible with
  `levelBaseChangeCrossing_transition`, is the restriction of a unique map of sheaves out of `F`.

## Implementation notes

**Nothing here is a new descent argument.** The transport is
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.RestrictionIsColimit'.ofIso`,
which asks only for the isomorphisms of the legs: the transition datum of the transported
predicate is *defined* by conjugating the old one, so no coherence hypothesis arises. That the
conjugated datum is exactly
`Stacks.EtaleCohomology.AffineLimitCohomology.levelBaseChangeCrossing_transition` is a
definitional match — that declaration is itself the conjugate of the on-the-nose cocone identity
`levelCrossing_transition` by `levelCrossingIso` at the two levels.

**Why the consumer takes an isomorphism at all.**
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.RestrictionIsColimit'` used to
take its transition datum as an *equality* of functors, which is what the strict colimit of sites
of [Stacks, Tag 0A34] provides and what no base-change reading of it can. Taking an isomorphism
is a generalisation and not a weakening: the equality case is recovered by
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.compTransitionIso`, i.e.
`CategoryTheory.eqToIso`, and every statement that used to produce or consume the predicate does
so unchanged.

**This is not yet the degree-zero statement of [Stacks, Tag 09YQ].** What it provides is the
*first* of the things that statement needs — the legs in the base-change vocabulary.

The passage from a universal property of this shape to
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.IsColimitPresentation`, which is stated with
*inverse image* along `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.conePi` rather than with
restriction, is no longer missing: the two are adjoint, and
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.isColimitPresentation_directImageSystem_iff`
identifies the predicate at the system of direct images with
`Stacks.EtaleCohomology.LimitHigherDirectImage.IsDirectImageDescent`, a statement in which only
restrictions along base change occur. Neither is the crossing of the level sites: restriction of
abelian sheaves from Mathlib's small étale site of `X_i` to a level is an equivalence, by
`Stacks.EtaleCohomology.AffineLimitCohomology.isEquivalence_levelEtaleRestrictionAb`.

Still missing: the identification of the two transition data —
`levelBaseChangeCrossing_transition` here against
`Stacks.EtaleCohomology.coneDirectImageCompAb` there, a coherence of the chosen fibre products of
[Stacks, Tag 0EYL]; the reindexing of the levels by `Iᵒᵖ`, which has to go through
`(affineEtaleSiteColimit …).indexEquiv` rather than through an equality, `affineEtaleSiteColimit`
being `@[no_expose]` and its body not exposable, the levels being chosen fibre products and
`CategoryTheory.Limits.pullback` reducing only through Mathlib's
`@[no_expose] CategoryTheory.Limits.getLimitCone`; the identification of the coefficients
`AddCommGrpCat` here with the sheaves of sets at which
`Stacks.EtaleCohomology.QcSeparatedColimit.sectionOver_colimit_of_qcqs_etale_object` proves the
degree-zero Čech descent, of which the *inverse image* half is no longer missing —
`Stacks.EtaleCohomology.etaleForgetInverseImageIso` and
`Stacks.EtaleCohomology.etaleForgetInverseImageSections` in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/SmallEtaleCoefficientCrossing.lean` carry
it, and what is still missing at the coefficients is the *universal property*, whose factorisation
clause the comparison does not cross because the set-valued predicate quantifies it over sheaves
of sets; and the legs `Stacks.EtaleCohomology.etaleCohomologyMapTo` through
`CategoryTheory.Sheaf.H.equiv₀`.

## References

* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 0EYN](https://stacks.math.columbia.edu/tag/0EYN)
* [Stacks Project, Tag 0EYL](https://stacks.math.columbia.edu/tag/0EYL)
* [Stacks Project, Tag 0A34](https://stacks.math.columbia.edu/tag/0A34)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace Stacks.EtaleCohomology.AffineLimitCohomology

open AlgebraicGeometry CategoryTheory.Sites.InverseSystem

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : Iᵒᵖ ⥤ AlgebraicGeometry.Scheme.{max u v}) (c : Cone D)
  (B : AlgebraicGeometry.BigEtaleSite.{max u v})
  (hD : ∀ i, B.Contains (D.obj i)) (hX : B.Contains c.pt)
  (hc : IsLimit c)
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]

/-- **[Stacks, Tag 0EYN], second half, on Mathlib's small étale site of a limit of schemes, with
the levels read by BASE CHANGE along the projections of the cone, for sheaves of ABELIAN
GROUPS.** Let `(X_i)` be an inverse system of schemes with affine transition morphisms over a
nonempty directed index, all of them objects of a big étale site `B`, let `X = lim X_i` and let
`F` be an abelian sheaf on Mathlib's small étale site of `X`. Then

`F = colim_i p_i^{-1} p_{i, *} F`,

in the form the inverse-system machinery proves it, and with every restriction taken along
`Stacks.EtaleCohomology.AffineLimitCohomology.levelBaseChangeCrossing` — the level of
[Stacks, Tag 0EYL] read on the small étale site of `X_i` and then base changed along
`p_i : X ⟶ X_i`: every family of maps out of those restrictions of `F`, compatible with
`levelBaseChangeCrossing_transition`, is the restriction of a **unique** map of sheaves out
of `F`.

This is `Stacks.EtaleCohomology.AffineLimitCohomology.restrictionIsColimitAb_limitToEtaleSite`
carried across `Stacks.EtaleCohomology.AffineLimitCohomology.levelCrossingIso` by
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.RestrictionIsColimit'.ofIso`.
Nothing is assumed: the isomorphism of the legs is the one [Stacks, Tag 0EYL] supplies as data
through its field `toLimit_isPullback`, and the transition datum of the conclusion is the
conjugate of the system's own on-the-nose cocone identity, which is how
`levelBaseChangeCrossing_transition` is defined. -/
theorem restrictionIsColimitAb_levelBaseChange
    (F : Sheaf (c.pt).smallEtaleTopology AddCommGrpCat.{max u v + 1}) :
    InverseSystemOfFiniteSites.RestrictionIsColimit'
      (c.pt).smallEtaleTopology AddCommGrpCat.{max u v + 1} (sys D c B hD hX hc)
      (levelBaseChangeCrossing D c B hD hX hc)
      (levelBaseChangeCrossing_transition D c B hD hX hc) F :=
  InverseSystemOfFiniteSites.RestrictionIsColimit'.ofIso
    (c.pt).smallEtaleTopology AddCommGrpCat.{max u v + 1}
    (InverseSystemOfFiniteSites.compTransitionIso
      (limitToSmallEtale D c B hX ⋙ AlgebraicGeometry.SmallEtale.toEtaleSite B c.pt hX)
      (sys D c B hD hX hc) (toLimitSmall D c B hD hX hc)
      (toLimitSmall_transition D c B hD hX hc))
    (levelCrossingIso D c B hD hX hc)
    (restrictionIsColimitAb_limitToEtaleSite D c B hD hX hc F)

end Stacks.EtaleCohomology.AffineLimitCohomology

end
