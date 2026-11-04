module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.EtaleLocalizationArrowContainment
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.EtaleLocalizationSplittingCriterion

/-!
# Discharging the finite-part hypotheses of the étale localization statements

Three statements of the étale localization of a groupoid scheme are carried in this library in a
*conditional* form, with the finite part of Stacks 04RU hypothesised:

* `Stacks.Groupoids.GroupoidScheme.exists_etale_quasiSplitting` assumes
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.FinitePartSubgroupoid`;
* `Stacks.Groupoids.GroupoidScheme.exists_etale_strongSplitting` (Stacks 03FM) and
  `Stacks.Groupoids.GroupoidScheme.exists_etale_splitting` (Stacks 0DTC) assume
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.TargetLocusSubgroupoid` together with the
  auxiliary hypotheses `hlift` and `hQ`.

This file discharges the first of those hypotheses and, for Stacks 03FM, produces the
unconditional statement in the shape the conditional one has.

## Main definitions

* `AlgebraicGeometry.Space.FinitePartUniversalOpen.toFinitePartSubgroupoid`: the finite part of
  Stacks 04RU, read as the input which the conditional étale localization consumes.
* `AlgebraicGeometry.Space.finitePartSubgroupoid`: that input, built for any groupoid in
  algebraic spaces whose source and target are separated and locally of finite type — so the
  finite-part hypothesis of the conditional statements is *not* an assumption at all.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.pointsMap_eqToHom_restrict_objects`: pushing a
  point of `U'` forward along the identification of `U'` with the object space of the
  restriction `R|_{U'}` changes nothing.  This is the comparison between the two spellings of
  the point `u'` used by the statements below.
* `Stacks.Groupoids.GroupoidScheme.exists_etale_quasiSplitting_unconditional`: the
  quasi-splitting of `R|_{U'}` at every point of `U'`, with no finite-part hypothesis.
* `Stacks.Groupoids.GroupoidScheme.exists_etale_strongSplitting_unconditional`: **Stacks 03FM**
  with no finite-part hypothesis, no `hlift` and no `hQ`.
* `Stacks.Groupoids.GroupoidScheme.exists_etale_splitting_of_strongSplittingSituation`: the
  conclusion of Stacks 0DTC in the *strong* splitting situation of Stacks 04RL.  This is **not**
  Stacks 0DTC, whose standing hypotheses are those of Stacks 0DTB and are strictly weaker; see
  the implementation notes.

## Implementation notes

### Why `TargetLocusSubgroupoid` is not constructed

`AlgebraicGeometry.GroupoidInAlgebraicSpaces.TargetLocusSubgroupoid` asks, beyond the data of
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.FinitePartSubgroupoid`, for an open subspace `Q` of
the object space `U` with `mem_arrows_iff`: a section of the arrow space of `R|_{U'}` lies in the
subgroupoid *exactly* when its target in `R` is a section of `Q`.  The finite part does not
satisfy this, and no choice of `Q` can repair it, because membership of an arrow of `R|_{U'}` in
the universal open `Z_univ` depends on the *section of `U'`* which is its source — on the open
`Z_x` of the fibre which that section names — and not only on its target in `U`.

The simplest witness is a finite constant group acting on the spectrum of a field.  Take
`U = Spec k`, `R = (ℤ/2) × U` with `s = t` the projection.  A section of the finite part over a
connected test object is an open of the two-element fibre containing the unit, so there are two:
`U'` has two points `x₁` (the unit alone) and `x₂` (everything), and `Z_univ` contains the
identity arrow at `x₁` but not the non-identity arrow at `x₂`… while every arrow of `R|_{U'}` has
the same target in `U = Spec k`, whose only open subspaces are `∅` and `U`.  So `mem_arrows_iff`
forces `Z_univ` to contain either all eight arrows of `R|_{U'}` or none, and it contains three.

Consequently `Stacks.Groupoids.GroupoidScheme.exists_etale_strongSplitting` and
`Stacks.Groupoids.GroupoidScheme.exists_etale_splitting` cannot be discharged through their own
hypotheses; the unconditional Stacks 03FM below is obtained instead from
`AlgebraicGeometry.Space.exists_stronglySplit_of_strongSplittingSituation`, which proves the tag
directly, and is stated in the same shape as the conditional theorem so that the two can be
compared.

### What Stacks 0DTC still needs

The conclusion of Stacks 0DTC is reached here only under the standing hypotheses of Stacks 04RL,
by `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isSplitAt_of_isStronglySplitAt`, and Stacks 0DTC
is not a consequence of that: by
`AlgebraicGeometry.Space.StrongSplittingSituation.toSplittingSituation` the situation of Stacks
04RL implies that of Stacks 0DTB and not conversely, so the implication proved here has
hypotheses strictly stronger than the tag's.

What the tag needs, and what is missing, is the fibre-level input of the splitting situation.
The whole development of
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/EtaleLocalizationArrowContainment.lean` runs on
an open `W` of the scheme-theoretic fibre `F_u = R ×_{s, U} Spec κ(u)` satisfying
`∀ x, x ∈ W ↔ t (ι x) = u`, which is what
`AlgebraicGeometry.Space.StrongSplittingSituation.exists_fiberOpens_stabilizer` supplies.  In the
splitting situation of Stacks 0DTB the available open is the one of
`AlgebraicGeometry.Space.SplittingSituation.exists_fiberOpens_stabilizer`, whose support is the
image of the fibre of the stabilizer *group scheme* over `u`; that is in general a proper subset
of the arrows with both endpoints `u`, which is exactly why Stacks 0DTB is the weaker standing
hypothesis.  Two things therefore have to be redone for it and are not done anywhere in this
library: the membership criterion
`AlgebraicGeometry.Space.exists_lift_fibrePair_iff` for the stabilizer-supported open, and the
containment of the stabilizer of `R|_{U'}` over `u'` in `Z_univ` replacing
`AlgebraicGeometry.Space.contains_arrows_fibreValuedPoint`.

## References

* [Stacks Project, Tag 03FM](https://stacks.math.columbia.edu/tag/03FM)
* [Stacks Project, Tag 04RK](https://stacks.math.columbia.edu/tag/04RK)
* [Stacks Project, Tag 04RL](https://stacks.math.columbia.edu/tag/04RL)
* [Stacks Project, Tag 04RU](https://stacks.math.columbia.edu/tag/04RU)
* [Stacks Project, Tag 04RV](https://stacks.math.columbia.edu/tag/04RV)
* [Stacks Project, Tag 04RW](https://stacks.math.columbia.edu/tag/04RW)
* [Stacks Project, Tag 0DTB](https://stacks.math.columbia.edu/tag/0DTB)
* [Stacks Project, Tag 0DTC](https://stacks.math.columbia.edu/tag/0DTC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- Reading a point of `U'` as a point of the object space of the restriction `R|_{U'}`, along
the identification `AlgebraicGeometry.GroupoidInAlgebraicSpaces.Restriction.objects_eq` of the
two spaces, changes nothing.

The two forms in which the point `u'` of Stacks 03FM is stated — as a point of `U'` and as a
point of the object space of `R|_{U'}` — differ by exactly this transport. -/
theorem pointsMap_eqToHom_restrict_objects (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects)
    (p : Space.points C S hS U'.obj) :
    Space.pointsMap C S hS U'.obj
        (eqToHom (restrict G g).objects_eq.symm).hom p = p :=
  congrFun (Space.pointsMap_id C S hS U'.obj) p

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

namespace AlgebraicGeometry.Space.FinitePartUniversalOpen

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} {G : GroupoidInAlgebraicSpaces C S hS B}

/-- The finite part of Stacks 04RU, read as the input which the conditional form of the étale
localization consumes: its object space with its étale projection, together with the universal
open read as an open finite subgroupoid of the restriction along that projection. -/
def toFinitePartSubgroupoid (F : FinitePartUniversalOpen G) :
    GroupoidInAlgebraicSpaces.FinitePartSubgroupoid G where
  objects := F.objects
  objectProjection := F.objectProjection
  objectProjection_etale := F.objectProjection_etale
  restrictedSubgroupoid := F.restrictedSubgroupoid

end AlgebraicGeometry.Space.FinitePartUniversalOpen

namespace AlgebraicGeometry

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- **The finite-part hypothesis of the conditional étale localization is not an assumption.**
For a groupoid in algebraic spaces whose source and target are separated and locally of finite
type, the finite part of Stacks 04RU supplies an algebraic space with an étale morphism to the
object space together with an open finite subgroupoid of the restriction along it. -/
def Space.finitePartSubgroupoid (G : GroupoidInAlgebraicSpaces C S hS B)
    (hs_sep : Space.IsSeparated C S hS G.source.hom)
    (ht_sep : Space.IsSeparated C S hS G.target.hom)
    (hs_lft : Space.IsLocallyOfFiniteType C S hS G.source.hom)
    (ht_lft : Space.IsLocallyOfFiniteType C S hS G.target.hom) :
    GroupoidInAlgebraicSpaces.FinitePartSubgroupoid G :=
  (Space.finitePartUniversalOpen G hs_sep ht_sep hs_lft ht_lft).toFinitePartSubgroupoid

end AlgebraicGeometry

namespace Stacks.Groupoids.GroupoidScheme

open AlgebraicGeometry AlgebraicGeometry.GroupoidInAlgebraicSpaces

/-- In the quasi-splitting situation of Stacks 04RV there is an algebraic space `U'`, an étale
morphism `g : U' ⟶ U` of algebraic spaces, and the restriction `R|_{U'}` is quasi-split at every
point of `U'`.

No point of `U'` above `u` is exhibited, so the conclusion is satisfied by the empty `U'` as
well; the étale neighbourhood carrying the point `u'` over `u` with `κ(u)`-valued section is
`Stacks.Groupoids.GroupoidScheme.exists_quasiSplit_of_quasiSplittingSituation`. -/
theorem exists_etale_quasiSplitting_unconditional
    (D : AlgebraicGeometry.Space.QuasiSplittingSituation.{u})
    (C : BigFppfSite.{u}) (hS : C.Contains D.S)
    (hU : C.Contains D.groupoid.objects.left)
    (hR : C.Contains D.groupoid.arrows.left)
    (hP : C.Contains (pullback D.groupoid.source D.groupoid.target).left) :
    ∃ (U' : AlgebraicSpaces C D.S hS)
      (g : U' ⟶ (D.groupoid.realization C hS hU hR hP).objects),
      AlgebraicGeometry.Space.IsEtale C D.S hS g.hom ∧
      ∀ u' : AlgebraicGeometry.Space.points C D.S hS
          (restrict (D.groupoid.realization C hS hU hR hP) g).groupoid.objects.obj,
        IsQuasiSplitAt (restrict (D.groupoid.realization C hS hU hR hP) g).groupoid u' :=
  exists_etale_quasiSplitting D C hS hU hR hP
    (AlgebraicGeometry.Space.finitePartSubgroupoid _
      (AlgebraicGeometry.Space.isSeparated_realization_source D.groupoid C hS hU hR hP)
      (AlgebraicGeometry.Space.isSeparated_realization_target D.groupoid C hS hU hR hP)
      (AlgebraicGeometry.Space.isLocallyOfFiniteType_realization_source
        D.groupoid C hS hU hR hP)
      (AlgebraicGeometry.Space.isLocallyOfFiniteType_realization_target
        D.groupoid C hS hU hR hP))

/-- **Stacks Project, Tag 03FM**, unconditionally.

In the strong splitting situation of Stacks 04RL there are an algebraic space `U'`, an étale
morphism `U' ⟶ U` and a point `Spec κ(u) ⟶ U'` lying over `u` at which `R|_{U'}` is strongly
split.

This is the statement of `Stacks.Groupoids.GroupoidScheme.exists_etale_strongSplitting` with the
three hypotheses `F`, `hlift` and `hQ` removed: `U'`, the étale morphism and the point are all
produced.  Only the standing hypotheses of Stacks 04RL and the requirements that the big fppf
site contain the base, object, arrow and composable-pair schemes and `Spec κ(u)` remain.

The content is `AlgebraicGeometry.Space.exists_stronglySplit_of_strongSplittingSituation`; this
restatement differs from it only in spelling the point `u'` as a point of the object space of
`R|_{U'}` rather than of `U'`, which by
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.pointsMap_eqToHom_restrict_objects` is the same
point. -/
theorem exists_etale_strongSplitting_unconditional
    (D : AlgebraicGeometry.Space.StrongSplittingSituation.{u})
    (C : BigFppfSite.{u}) (hS : C.Contains D.S)
    (hU : C.Contains D.groupoid.objects.left)
    (hR : C.Contains D.groupoid.arrows.left)
    (hP : C.Contains (pullback D.groupoid.source D.groupoid.target).left)
    (hK : C.Contains (Spec (D.groupoid.objects.left.residueField D.u))) :
    ∃ (U' : AlgebraicSpaces C D.S hS)
      (g : U' ⟶ (D.groupoid.realization C hS hU hR hP).objects),
      AlgebraicGeometry.Space.IsEtale C D.S hS g.hom ∧
      ∃ v : U'.obj.obj (Opposite.op
          (AlgebraicGeometry.Space.residueFieldSiteObject C hS
            (X := D.groupoid.objects) D.u hK)),
        (AlgebraicGeometry.Space.yonedaSchemePointEquiv C hS hU
            (Opposite.op (AlgebraicGeometry.Space.residueFieldSiteObject C hS
              (X := D.groupoid.objects) D.u hK))
            (g.hom.app _ v)).left =
              D.groupoid.objects.left.fromSpecResidueField D.u ∧
        IsStronglySplitAt (restrict (D.groupoid.realization C hS hU hR hP) g).groupoid
          (AlgebraicGeometry.Space.pointsMap C D.S hS U'.obj
            (eqToHom (restrict (D.groupoid.realization C hS hU hR hP) g).objects_eq.symm).hom
            (AlgebraicGeometry.Space.FieldValuedPoint.class C D.S hS U'.obj
              { carrier := D.groupoid.objects.left.residueField D.u
                contained := hK
                toBase := D.groupoid.objects.left.fromSpecResidueField D.u ≫
                  D.groupoid.objects.hom
                value := v })) := by
  obtain ⟨U', g, hg, v, hv, hsplit⟩ :=
    AlgebraicGeometry.Space.exists_stronglySplit_of_strongSplittingSituation
      D C hS hU hR hP hK
  exact ⟨U', g, hg, v, hv, by rwa [pointsMap_eqToHom_restrict_objects]⟩

/-- **The conclusion of Stacks Project, Tag 0DTC, in the strong splitting situation of Stacks
04RL** — *not* Stacks 0DTC, whose standing hypotheses are those of Stacks 0DTB.

In the strong splitting situation there are an algebraic space `U'`, an étale morphism `U' ⟶ U`
and a point `Spec κ(u) ⟶ U'` lying over `u` at which `R|_{U'}` is *split*.

This is the statement of `Stacks.Groupoids.GroupoidScheme.exists_etale_splitting` with `F`,
`hlift` and `hQ` removed and with the splitting situation of Stacks 0DTB replaced by the strong
splitting situation of Stacks 04RL.  The replacement is a strengthening of the hypotheses, by
`AlgebraicGeometry.Space.StrongSplittingSituation.toSplittingSituation` and the remark on it, so
this is strictly weaker than the tag; what the tag needs beyond it is set out in the
implementation notes of this file. -/
theorem exists_etale_splitting_of_strongSplittingSituation
    (D : AlgebraicGeometry.Space.StrongSplittingSituation.{u})
    (C : BigFppfSite.{u}) (hS : C.Contains D.S)
    (hU : C.Contains D.groupoid.objects.left)
    (hR : C.Contains D.groupoid.arrows.left)
    (hP : C.Contains (pullback D.groupoid.source D.groupoid.target).left)
    (hK : C.Contains (Spec (D.groupoid.objects.left.residueField D.u))) :
    ∃ (U' : AlgebraicSpaces C D.S hS)
      (g : U' ⟶ (D.groupoid.realization C hS hU hR hP).objects),
      AlgebraicGeometry.Space.IsEtale C D.S hS g.hom ∧
      ∃ v : U'.obj.obj (Opposite.op
          (AlgebraicGeometry.Space.residueFieldSiteObject C hS
            (X := D.groupoid.objects) D.u hK)),
        (AlgebraicGeometry.Space.yonedaSchemePointEquiv C hS hU
            (Opposite.op (AlgebraicGeometry.Space.residueFieldSiteObject C hS
              (X := D.groupoid.objects) D.u hK))
            (g.hom.app _ v)).left =
              D.groupoid.objects.left.fromSpecResidueField D.u ∧
        IsSplitAt (restrict (D.groupoid.realization C hS hU hR hP) g).groupoid
          (AlgebraicGeometry.Space.pointsMap C D.S hS U'.obj
            (eqToHom (restrict (D.groupoid.realization C hS hU hR hP) g).objects_eq.symm).hom
            (AlgebraicGeometry.Space.FieldValuedPoint.class C D.S hS U'.obj
              { carrier := D.groupoid.objects.left.residueField D.u
                contained := hK
                toBase := D.groupoid.objects.left.fromSpecResidueField D.u ≫
                  D.groupoid.objects.hom
                value := v })) := by
  obtain ⟨U', g, hg, v, hv, hsplit⟩ :=
    exists_etale_strongSplitting_unconditional D C hS hU hR hP hK
  exact ⟨U', g, hg, v, hv, isSplitAt_of_isStronglySplitAt hsplit⟩

end Stacks.Groupoids.GroupoidScheme

end
