module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleLimitLevelBaseChangeColimit

/-!
# The level side of the site crossing of Stacks 09YQ, at abelian coefficients

`Stacks.EtaleCohomology.AffineLimitCohomology.restrictionIsColimitAb_levelBaseChange` — the second
half of [Stacks, Tag 0EYN] on Mathlib's small étale site of a limit of schemes, with the
restrictions taken along base change along the projections of the cone — is stated with legs
`Stacks.EtaleCohomology.AffineLimitCohomology.levelBaseChangeCrossing` whose source is a *level*
of `Stacks.EtaleCohomology.affineEtaleSiteColimit`, a category of chosen pullback models of the
small **affine** étale site of [Stacks, Tag 021B]. The statements of [Stacks, Tag 09YQ] are about
abelian sheaves on *Mathlib's* small étale sites `AlgebraicGeometry.Scheme.smallEtaleTopology` of
the `X_i`. This file carries the level side of that crossing at those coefficients: restriction of
abelian sheaves from Mathlib's small étale site of `X_i` to the level is an **equivalence**.

Nothing new is proved about sites. The crossing is a composite of three dense-subsite inclusions,
each of which is already proved, and the only thing supplied here is the composition at the
coefficients
`AddCommGrpCat.{max u v + 1}`:

* the level equivalence, `Stacks.EtaleCohomology.affineEtaleSiteColimit_levelEquiv_isDenseSubsite`,
  which is coefficient-free;
* the inclusion of the small affine étale site, [Stacks, Tag 04HR], in the form
  `Stacks.EtaleCohomology.BaseChangeAlgebraSystem.isDenseSubsite_smallAffineEtaleInclusion`;
* the embedding of the size-bounded site of [Stacks, Tag 021B] into Mathlib's,
  `AlgebraicGeometry.SmallEtale.isDenseSubsite_toEtaleSite`.

The tree already carries the first two of these composed **for sheaves of sets** in
`Type (max u v + 1)`, as
`Stacks.EtaleCohomology.affineEtaleSiteColimit_levelToSmallEtale_sheafEquiv`; the abelian form is
not a transport of that statement but the same composition at another coefficient category, and
what it needs afresh is only that `AddCommGrpCat.{max u v + 1}` has limits of the shapes
Mathlib's `CategoryTheory.Functor.IsDenseSubsite.instIsEquivalence` asks for, which typeclass
inference supplies.

## Main results

* `Stacks.EtaleCohomology.AffineLimitCohomology.isEquivalence_levelRestrictionAb` — **the abelian
  counterpart of `affineEtaleSiteColimit_levelToSmallEtale_sheafEquiv`**: restriction of abelian
  sheaves along `Stacks.EtaleCohomology.QcSeparatedColimit.levelToSmallEtale`, from the
  size-bounded small étale site of `X_i` of [Stacks, Tag 021B] to the level, is an equivalence.
* `Stacks.EtaleCohomology.AffineLimitCohomology.isContinuous_levelToEtaleSite` — the level
  crossing continued into Mathlib's small étale site is a morphism of sites.
* `Stacks.EtaleCohomology.AffineLimitCohomology.isEquivalence_levelEtaleRestrictionAb` — **the
  whole level-side crossing at abelian coefficients**: restriction of abelian sheaves from
  Mathlib's small étale site of `X_i` to the level of [Stacks, Tag 0EYL] is an equivalence.
* `Stacks.EtaleCohomology.AffineLimitCohomology.hom_ext_of_levelRestrictionAb` — the form a
  descent argument consumes: **a map of abelian sheaves on Mathlib's small étale site of `X_i` is
  determined by its values on the objects coming from the level.**
* `Stacks.EtaleCohomology.AffineLimitCohomology.exists_level_of_index` — the reindexing: **every
  index of the inverse system of schemes is the index of a level, up to a canonical isomorphism
  of schemes over the cone.**

## Implementation notes

**Why the instances are supplied by hand.** `Functor.IsDenseSubsite.instIsEquivalence` requires
`[∀ X, Limits.HasLimitsOfShape (StructuredArrow X G.op) A]`, which holds for
`AddCommGrpCat.{max u v + 1}` and for `Type (max u v + 1)` but not for an arbitrary coefficient
category; stated at a variable `A` with no hypotheses the instance is not found, and that is the
whole reason this file is at `AddCommGrpCat.{max u v + 1}` rather than at an arbitrary `A`. The
continuity instances are not global — `(sys …).J i` is the topology of a level, which typeclass
inference cannot see through — so each is introduced from the named theorem, by `letI` in
a statement and by `have` in a tactic proof, as
`Stacks.EtaleCohomology.AffineLimitCohomology.levelRestrictionIso` already does.

**What this leaves.** With this and the adjunction bridge
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.isColimitPresentation_directImageSystem_iff`,
the only thing still separating `restrictionIsColimitAb_levelBaseChange` from the degree-zero
statement of [Stacks, Tag 09YQ] at abelian coefficients is the identification of the two
transition data — `levelBaseChangeCrossing_transition`, the conjugate of the system's own
on-the-nose cocone identity by `levelCrossingIso`, against
`Stacks.EtaleCohomology.coneDirectImageCompAb`, the associativity of fibre products — together
with the reindexing along `(affineEtaleSiteColimit …).indexEquiv`, which cannot be an equality:
`affineEtaleSiteColimit` is `@[no_expose]` and its body can never be exposed, since the levels are
*chosen* fibre products and `CategoryTheory.Limits.pullback` reduces only through Mathlib's
`@[no_expose] CategoryTheory.Limits.getLimitCone`. The reindexing has to go through `indexEquiv`
itself, whose counit is an isomorphism of `Iᵒᵖ` and hence an isomorphism `X_{levelIndex n} ≅ X_i`
of schemes.

## References

* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 0EYN](https://stacks.math.columbia.edu/tag/0EYN)
* [Stacks Project, Tag 0EYL](https://stacks.math.columbia.edu/tag/0EYL)
* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
* [Stacks Project, Tag 04HR](https://stacks.math.columbia.edu/tag/04HR)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace Stacks.EtaleCohomology.AffineLimitCohomology

open AlgebraicGeometry CategoryTheory.Sites.InverseSystem
open Stacks.EtaleCohomology.QcSeparatedColimit (levelIndex levelToSmallEtale)

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : Iᵒᵖ ⥤ AlgebraicGeometry.Scheme.{max u v}) (c : Cone D)
  (B : AlgebraicGeometry.BigEtaleSite.{max u v})
  (hD : ∀ i, B.Contains (D.obj i)) (hX : B.Contains c.pt)
  (hc : IsLimit c)
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]

/-- **Restriction of ABELIAN sheaves from the size-bounded small étale site of `X_i` to a level of
[Stacks, Tag 0EYL] is an equivalence.** This is
`Stacks.EtaleCohomology.affineEtaleSiteColimit_levelToSmallEtale_sheafEquiv`, which the tree
carries for sheaves of sets in `Type (max u v + 1)`, at the coefficients
`AddCommGrpCat.{max u v + 1}`.

Both factors are dense-subsite inclusions: the level equivalence by
`Stacks.EtaleCohomology.affineEtaleSiteColimit_levelEquiv_isDenseSubsite`, which says nothing
about coefficients, and the inclusion of the small affine étale site by [Stacks, Tag 04HR], in the
form `Stacks.EtaleCohomology.BaseChangeAlgebraSystem.isDenseSubsite_smallAffineEtaleInclusion`.

It says that reading an abelian sheaf of a level as the restriction of an abelian sheaf on the
small étale site of `X_i` is no restriction on it: every one of them is isomorphic to such a
restriction, and every map of them to a map of those. -/
theorem isEquivalence_levelRestrictionAb (i : (sys D c B hD hX hc).I) :
    letI := QcSeparatedColimit.isContinuous_levelToSmallEtale D c B hD hX hc i
    ((levelToSmallEtale D c B hD hX hc i).sheafPushforwardContinuous
        AddCommGrpCat.{max u v + 1} ((sys D c B hD hX hc).J i)
        (AlgebraicGeometry.SmallEtale.topology B
          (D.obj (levelIndex D c B hD hX hc i)) (hD _))).IsEquivalence := by
  have := affineEtaleSiteColimit_levelEquiv_isDenseSubsite D c B hD hX hc i
  have := BaseChangeAlgebraSystem.isDenseSubsite_smallAffineEtaleInclusion B
    (D.obj (levelIndex D c B hD hX hc i)) (hD _)
  exact Functor.isEquivalence_of_iso (Functor.sheafPushforwardContinuousComp
    ((affineEtaleSiteColimit D c B hD hX hc).levelEquiv i).functor
    (AlgebraicGeometry.SmallAffineEtale.inclusion B _ (hD _)) _ _
    (AlgebraicGeometry.SmallAffineEtale.topology B _ (hD _)) _)

/-- **The level crossing continued into Mathlib's small étale site of `X_i` is a morphism of
sites.** The composite of
`Stacks.EtaleCohomology.QcSeparatedColimit.isContinuous_levelToSmallEtale` with
`AlgebraicGeometry.SmallEtale.isContinuous_toEtaleSite`. -/
theorem isContinuous_levelToEtaleSite (i : (sys D c B hD hX hc).I) :
    (levelToSmallEtale D c B hD hX hc i ⋙
      AlgebraicGeometry.SmallEtale.toEtaleSite B
        (D.obj (levelIndex D c B hD hX hc i)) (hD _)).IsContinuous
      ((sys D c B hD hX hc).J i)
      (AlgebraicGeometry.Scheme.smallEtaleTopology
        (D.obj (levelIndex D c B hD hX hc i))) :=
  let := QcSeparatedColimit.isContinuous_levelToSmallEtale D c B hD hX hc i
  let := AlgebraicGeometry.SmallEtale.isContinuous_toEtaleSite B
    (D.obj (levelIndex D c B hD hX hc i)) (hD _)
  Functor.isContinuous_comp _ _ _
    (AlgebraicGeometry.SmallEtale.topology B
      (D.obj (levelIndex D c B hD hX hc i)) (hD _)) _

/-- **The level side of the site crossing of [Stacks, Tag 09YQ], at abelian coefficients:
restriction of abelian sheaves from MATHLIB's small étale site of `X_i` to a level of
[Stacks, Tag 0EYL] is an equivalence.**

It is `Stacks.EtaleCohomology.AffineLimitCohomology.isEquivalence_levelRestrictionAb` followed by
the size cutoff of [Stacks, Tag 021B], which is a dense subsite of Mathlib's small étale site by
`AlgebraicGeometry.SmallEtale.isDenseSubsite_toEtaleSite`; so the whole crossing is a composite of
three dense-subsite restrictions and nothing is assumed.

This is the coefficient at which the development of [Stacks, Tag 09YQ] runs — the degree-zero
Čech descent `Stacks.EtaleCohomology.QcSeparatedColimit.sectionOver_colimit_of_qcqs_etale_object`
is at sheaves of sets, but its abelian consumers, among them
`Stacks.EtaleCohomology.AffineLimitCohomology.restrictionIsColimitAb_levelBaseChange`, are at
`AddCommGrpCat.{max u v + 1}`. -/
theorem isEquivalence_levelEtaleRestrictionAb (i : (sys D c B hD hX hc).I) :
    letI := isContinuous_levelToEtaleSite D c B hD hX hc i
    ((levelToSmallEtale D c B hD hX hc i ⋙
        AlgebraicGeometry.SmallEtale.toEtaleSite B
          (D.obj (levelIndex D c B hD hX hc i)) (hD _)).sheafPushforwardContinuous
        AddCommGrpCat.{max u v + 1} ((sys D c B hD hX hc).J i)
        (AlgebraicGeometry.Scheme.smallEtaleTopology
          (D.obj (levelIndex D c B hD hX hc i)))).IsEquivalence := by
  have := QcSeparatedColimit.isContinuous_levelToSmallEtale D c B hD hX hc i
  have := AlgebraicGeometry.SmallEtale.isContinuous_toEtaleSite B
    (D.obj (levelIndex D c B hD hX hc i)) (hD _)
  have := isEquivalence_levelRestrictionAb D c B hD hX hc i
  exact Functor.isEquivalence_of_iso (Functor.sheafPushforwardContinuousComp _ _ _ _
    (AlgebraicGeometry.SmallEtale.topology B (D.obj (levelIndex D c B hD hX hc i)) (hD _)) _)

/-- **A map of abelian sheaves on Mathlib's small étale site of `X_i` is determined by its values
on the objects coming from a level of [Stacks, Tag 0EYL].** This is the faithfulness half of
`Stacks.EtaleCohomology.AffineLimitCohomology.isEquivalence_levelEtaleRestrictionAb`, in the form
a descent argument consumes it: a family of maps indexed by the levels determines at most one map
of direct images, so the uniqueness clause of
`Stacks.EtaleCohomology.AffineLimitCohomology.restrictionIsColimitAb_levelBaseChange` can be read
back on Mathlib's sites. -/
theorem hom_ext_of_levelRestrictionAb (i : (sys D c B hD hX hc).I)
    {F G : Sheaf (AlgebraicGeometry.Scheme.smallEtaleTopology
      (D.obj (levelIndex D c B hD hX hc i))) AddCommGrpCat.{max u v + 1}} (φ ψ : F ⟶ G)
    (h : ∀ V : (sys D c B hD hX hc).C i,
      φ.hom.app (op ((levelToSmallEtale D c B hD hX hc i ⋙
          AlgebraicGeometry.SmallEtale.toEtaleSite B
            (D.obj (levelIndex D c B hD hX hc i)) (hD _)).obj V)) =
        ψ.hom.app (op ((levelToSmallEtale D c B hD hX hc i ⋙
          AlgebraicGeometry.SmallEtale.toEtaleSite B
            (D.obj (levelIndex D c B hD hX hc i)) (hD _)).obj V))) :
    φ = ψ := by
  have := isContinuous_levelToEtaleSite D c B hD hX hc i
  have := isEquivalence_levelEtaleRestrictionAb D c B hD hX hc i
  exact ((levelToSmallEtale D c B hD hX hc i ⋙
    AlgebraicGeometry.SmallEtale.toEtaleSite B
      (D.obj (levelIndex D c B hD hX hc i)) (hD _)).sheafPushforwardContinuous
    AddCommGrpCat.{max u v + 1} ((sys D c B hD hX hc).J i)
    (AlgebraicGeometry.Scheme.smallEtaleTopology
      (D.obj (levelIndex D c B hD hX hc i)))).map_injective
    (Sheaf.hom_ext (NatTrans.ext (funext fun V => h V.unop)))

/-- **Every index of the inverse system of schemes is the index of a level of [Stacks, Tag 0EYL],
up to a canonical isomorphism of schemes over the cone.** For `i : Iᵒᵖ` the level
`(affineEtaleSiteColimit …).indexEquiv.inverse.obj i` has
`Stacks.EtaleCohomology.QcSeparatedColimit.levelIndex` isomorphic to `i`, and the isomorphism
commutes with the projections of the cone.

This is the reindexing that a statement indexed by the levels needs in order to become one
indexed by `Iᵒᵖ`, and it cannot be improved to an equality: `(affineEtaleSiteColimit …).system.I`
*is* `Iᵒᵖ` and `indexEquiv` *is* `CategoryTheory.Equivalence.refl`, but
`affineEtaleSiteColimit` carries `@[no_expose]` and its body cannot be exposed — the levels are
*chosen* fibre products, and `CategoryTheory.Limits.pullback` reduces only through Mathlib's
`@[no_expose] CategoryTheory.Limits.getLimitCone`, so an exported `rfl` through it is rejected.
Going through `indexEquiv` instead costs only this isomorphism, `Iᵒᵖ` being thin: an isomorphism
of the index gives an isomorphism `X_{levelIndex n} ≅ X_i` of schemes, and
`CategoryTheory.Limits.Cone.w` makes it commute with the projections, so base change along
`c.π.app (levelIndex n)` and along `c.π.app i` agree up to it. -/
theorem exists_level_of_index (i : Iᵒᵖ) :
    ∃ (n : (sys D c B hD hX hc).I) (e : D.obj (levelIndex D c B hD hX hc n) ≅ D.obj i),
      c.π.app (levelIndex D c B hD hX hc n) ≫ e.hom = c.π.app i :=
  ⟨(affineEtaleSiteColimit D c B hD hX hc).indexEquiv.inverse.obj i,
    D.mapIso ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.counitIso.app i), c.w _⟩

end Stacks.EtaleCohomology.AffineLimitCohomology

end
