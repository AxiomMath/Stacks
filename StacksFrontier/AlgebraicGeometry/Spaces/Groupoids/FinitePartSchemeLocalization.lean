module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FiniteTypeLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSchemeEtaleLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.Groupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.RestrictedSubgroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.WithSectionScheme

/-!
# Étale localization of a groupoid by a scheme, separated over the object space

Stacks 04RW produces, in the quasi-splitting situation of Stacks 04RV, an algebraic space `U'`
with an étale morphism `U' ⟶ U` over which the restriction of the groupoid is quasi-split.
Stacks 04RY improves this under the extra hypotheses that the source and target are flat and
locally of finite presentation: then `U'` can be taken to be a *scheme* and `U' ⟶ U` to be
*separated* étale.

The `U'` of the proof of Stacks 04RW is the finite part `(R_s/U, e)_fin` of Stacks 04RU, which
under the extra hypotheses is a scheme separated over `U` by Stacks 04RI and Stacks 04RR, and
the restriction of the groupoid along its projection carries the open finite subgroupoid of
Stacks 04RU, clause (3), hence is quasi-split at every point.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.exists_etale_separated_scheme_quasiSplitting`:
  for a groupoid in algebraic spaces whose object space is a scheme, a scheme `U'` separated and
  étale over `U` over which the restricted groupoid is quasi-split at every point.
* `Stacks.Groupoids.GroupoidScheme.exists_etale_separated_scheme_quasiSplitting`: the same for a
  groupoid scheme in the quasi-splitting situation of Stacks 04RV, obtained by realizing it as a
  groupoid in algebraic spaces.

Neither result is Stacks 04RY itself: neither exhibits the point `u'` of `U'` over `u` with
`κ(u) = κ(u')` (and without it the statements hold with `U'` empty).  Stacks 04RY, with that
point, is
`Stacks.Groupoids.GroupoidScheme.exists_quasiSplit_separated_scheme_of_quasiSplittingSituation`
in `StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasiSplittingEtaleScheme`.

## Implementation notes

That `U' ⟶ U` is separated is read off the identification of `U'` with `(R_s/U, e)_fin` recorded
by `AlgebraicGeometry.Space.FinitePartGroupoid.objectProjection_spec`: that identification writes
the projection as an isomorphism followed by the composite of the inclusion
`(R_s/U, e)_fin ⟶ (R_s/U)_fin` with the projection of the finite part, and both factors of the
composite are separated — the first because a subfunctor inclusion is a monomorphism, the second
by Stacks 04RI, part (1).

The conclusion is quasi-splitting at every point of `U'`, which is stronger than quasi-splitting
at a single point but does not exhibit a point of `U'` above the chosen point `u` of `U` with
`κ(u) = κ(u')`; the source obtains that point by decomposing the fibre of `R` over `κ(u)` using
the quasi-finiteness of `s` at `e(u)` from Stacks 04RV, which nothing here consumes.  That point
is constructed in
`Stacks.Groupoids.GroupoidScheme.exists_quasiSplit_separated_scheme_of_quasiSplittingSituation`,
which is where `@[stacks 04RY]` sits.

## References

* [Stacks Project, Tag 04RI](https://stacks.math.columbia.edu/tag/04RI)
* [Stacks Project, Tag 04RR](https://stacks.math.columbia.edu/tag/04RR)
* [Stacks Project, Tag 04RU](https://stacks.math.columbia.edu/tag/04RU)
* [Stacks Project, Tag 04RV](https://stacks.math.columbia.edu/tag/04RV)
* [Stacks Project, Tag 04RW](https://stacks.math.columbia.edu/tag/04RW)
* [Stacks Project, Tag 04RY](https://stacks.math.columbia.edu/tag/04RY)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- The scheme-and-separatedness part of Stacks 04RY, for a groupoid in algebraic spaces whose
object space is a scheme; the point `u'` over `u` with `κ(u) = κ(u')` is not part of this
statement (Stacks 04RY itself is
`Stacks.Groupoids.GroupoidScheme.exists_quasiSplit_separated_scheme_of_quasiSplittingSituation`).

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over `B` whose source and target are
separated, whose source is flat and locally of finite presentation, whose target is locally of
finite type and whose object space `U` is a scheme.  Then there is an algebraic space `U'` which
is a *scheme*, a *separated* étale morphism `g : U' ⟶ U`, and `R|_{U'}` is quasi-split at every
point of `U'`. -/
theorem exists_etale_separated_scheme_quasiSplitting
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (hsep : Space.IsSeparated C S hS G.source.hom)
    (htsep : Space.IsSeparated C S hS G.target.hom)
    (hflat : Space.IsFlat C S hS G.source.hom)
    (hfp : Space.IsLocallyOfFinitePresentation C S hS G.source.hom)
    (htlft : Space.IsLocallyOfFiniteType C S hS G.target.hom)
    (hU : G.objects.obj.IsRepresentable) :
    ∃ (U' : AlgebraicSpaces C S hS) (g : U' ⟶ G.objects),
      U'.obj.IsRepresentable ∧
      Space.IsEtale C S hS g.hom ∧
      Space.IsSeparated C S hS g.hom ∧
      ∀ u' : Space.points C S hS (restrict G g).groupoid.objects.obj,
        IsQuasiSplitAt (restrict G g).groupoid u' := by
  have hslft : Space.IsLocallyOfFiniteType C S hS G.source.hom :=
    Space.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation C S hS hfp
  obtain ⟨F⟩ := Space.nonempty_finitePartGroupoid G hsep htsep hslft htlft
  have hsub : Nonempty (OpenFiniteSubgroupoid (restrict G F.objectProjection).groupoid) := by
    have h := nonempty_openFiniteSubgroupoid_restrict G F.groupoid F.hom.toGroupoidHom
      F.universalOpen (by rw [F.universalOpen_base]; exact F.objectProjection_eq)
      (by rw [F.universalOpen_base]; exact F.objectProjection_etale)
      F.arrows_eq F.source_eq F.arrowProjection_eq
    rwa [F.universalOpen_base] at h
  refine ⟨F.groupoid.objects, F.objectProjection, ?_, F.objectProjection_etale, ?_,
    fun u' => isQuasiSplitAt_of_openFiniteSubgroupoid _ (Classical.choice hsub) u'⟩
  · have hrep : (Space.finitePartWithSection C S hS G.source F.unit
        F.unit_source).toSubfunctor.toFunctor.IsRepresentable :=
      Space.isRepresentable_finitePartWithSection C S hS G.source F.unit F.unit_source
        hsep hflat hfp hU
    exact Functor.IsRepresentable.mk'
      ((Space.finitePartWithSection C S hS G.source F.unit
        F.unit_source).toSubfunctor.toFunctor.reprW ≪≫ F.objectsEquiv.symm)
  · rw [F.objectProjection_spec]
    exact Space.isSeparated_comp C S hS _ _
      (Space.isSeparated_of_isIso C S hS F.objectsEquiv.hom)
      (Space.isSeparated_ι_comp_baseMap_finitePartWithSection C S hS G.source F.unit
        F.unit_source hsep hflat hfp)

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

namespace Stacks.Groupoids.GroupoidScheme

open AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {S : Scheme.{u}}

/-- The functor to schemes takes a morphism of schemes over `S` regarded in the site back to the
underlying morphism of schemes. -/
private theorem toScheme_map_schemeSiteMap (C : AlgebraicGeometry.BigFppfSite.{u})
    (hS : C.Contains S) {X Y : Over S} (hX : C.Contains X.left) (hY : C.Contains Y.left)
    (f : X ⟶ Y) :
    (AlgebraicGeometry.BigFppfOver.toScheme C S hS).map
      (AlgebraicGeometry.Space.schemeSiteMap C hS hX hY f) = f.left :=
  congrArg (fun m : X ⟶ Y => m.left)
    (AlgebraicGeometry.Space.siteToOver_map_schemeSiteMap C hS hX hY f)

/-- The scheme-and-separatedness part of Stacks 04RY, in the quasi-splitting situation of
Stacks 04RV; the point `u'` over `u` with `κ(u) = κ(u')` is not part of this statement (Stacks
04RY itself is
`Stacks.Groupoids.GroupoidScheme.exists_quasiSplit_separated_scheme_of_quasiSplittingSituation`).

In Situation 04RV, assume in addition that the source of the groupoid scheme is flat and locally
of finite presentation.  Then there is a *scheme* `U'`, a *separated* étale morphism
`g : U' ⟶ U`, and `R|_{U'}` is quasi-split at every point of `U'`.

Only the flatness and local finite presentation of the *source* are used; the tag assumes them of
the target as well, so the hypotheses here are weaker than the tag's.  Separatedness and local
finiteness of type of the source and of the target come from Situation 04RV itself. -/
theorem exists_etale_separated_scheme_quasiSplitting
    (D : AlgebraicGeometry.Space.QuasiSplittingSituation.{u})
    (C : AlgebraicGeometry.BigFppfSite.{u}) (hS : C.Contains D.S)
    (hU : C.Contains D.groupoid.objects.left)
    (hR : C.Contains D.groupoid.arrows.left)
    (hP : C.Contains (pullback D.groupoid.source D.groupoid.target).left)
    (hflat : AlgebraicGeometry.Flat D.groupoid.source.left)
    (hfp : AlgebraicGeometry.LocallyOfFinitePresentation D.groupoid.source.left) :
    ∃ (U' : AlgebraicGeometry.AlgebraicSpaces C D.S hS)
      (g : U' ⟶ (D.groupoid.realization C hS hU hR hP).objects),
      U'.obj.IsRepresentable ∧
      AlgebraicGeometry.Space.IsEtale C D.S hS g.hom ∧
      AlgebraicGeometry.Space.IsSeparated C D.S hS g.hom ∧
      ∀ u' : AlgebraicGeometry.Space.points C D.S hS
          (restrict (D.groupoid.realization C hS hU hR hP) g).groupoid.objects.obj,
        IsQuasiSplitAt (restrict (D.groupoid.realization C hS hU hR hP) g).groupoid u' := by
  have hmap := toScheme_map_schemeSiteMap C hS hR hU D.groupoid.source
  have hmapt := toScheme_map_schemeSiteMap C hS hR hU D.groupoid.target
  have hs := D.groupoid.realization_source C hS hU hR hP
  have ht := D.groupoid.realization_target C hS hU hR hP
  have hsep' : AlgebraicGeometry.Space.IsSeparated C D.S hS
      (D.groupoid.realization C hS hU hR hP).source.hom := by
    rw [hs]
    exact (AlgebraicGeometry.Space.isSeparated_yoneda_map_iff C D.S hS _).2
      (hmap ▸ D.sourceSeparated)
  have htsep' : AlgebraicGeometry.Space.IsSeparated C D.S hS
      (D.groupoid.realization C hS hU hR hP).target.hom := by
    rw [ht]
    exact (AlgebraicGeometry.Space.isSeparated_yoneda_map_iff C D.S hS _).2
      (hmapt ▸ D.targetSeparated)
  have hflat' : AlgebraicGeometry.Space.IsFlat C D.S hS
      (D.groupoid.realization C hS hU hR hP).source.hom := by
    rw [hs]
    exact AlgebraicGeometry.Space.isFlat_yoneda_map C D.S hS _ (hmap ▸ hflat)
  have hfp' : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation C D.S hS
      (D.groupoid.realization C hS hU hR hP).source.hom := by
    rw [hs]
    exact AlgebraicGeometry.Space.isLocallyOfFinitePresentation_yoneda_map C D.S hS _
      (hmap ▸ hfp)
  have htlft' : AlgebraicGeometry.Space.IsLocallyOfFiniteType C D.S hS
      (D.groupoid.realization C hS hU hR hP).target.hom := by
    rw [ht]
    exact (AlgebraicGeometry.Space.holdsOnEveryEtaleChart_yoneda_map_iff C D.S hS
      AlgebraicGeometry.LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget _).2
      (hmapt ▸ D.targetLocallyOfFiniteType)
  have hUrep : (D.groupoid.realization C hS hU hR hP).objects.obj.IsRepresentable :=
    inferInstanceAs
      (yoneda.obj (AlgebraicGeometry.Space.schemeSiteObject C hS hU)).IsRepresentable
  exact AlgebraicGeometry.GroupoidInAlgebraicSpaces.exists_etale_separated_scheme_quasiSplitting
    (D.groupoid.realization C hS hU hR hP) hsep' htsep' hflat' hfp' htlft' hUrep

end Stacks.Groupoids.GroupoidScheme

end
