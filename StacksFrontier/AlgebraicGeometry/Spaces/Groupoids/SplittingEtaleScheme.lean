module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.EtaleLocalizationStabilizerContainment
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSchemeDerealization
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.WithSectionScheme

/-!
# A splitting on a separated étale neighbourhood which is a scheme

Let `(U, R, s, t, c)` be a groupoid scheme over `S` in the splitting situation of Stacks 0DTB at
a point `u ∈ U`, and suppose in addition that `s` is flat and locally of finite presentation.
Then the étale neighbourhood `U' = (R_s/U, e)_{fin}` of Stacks 0DTC is a *scheme* and its
projection `g : U' ⟶ U` is *separated* as well as étale, while `R' = R|_{U'}` is still split
over the point of `U'` above `u` whose residue field is `κ(u)`.  This is **Stacks 0DTD**.

The neighbourhood, its point and the splitting are those of Stacks 0DTC, available as
`Stacks.Groupoids.GroupoidScheme.exists_split_of_splittingSituation`; what Stacks 0DTD adds is
that `U'` is a scheme and that `g` is separated.  Both come from the identification of `U'` with
the finite part containing the unit, recorded by
`AlgebraicGeometry.Space.FinitePartUniversalOpen.objectsEquiv` and
`AlgebraicGeometry.Space.FinitePartUniversalOpen.objectProjection_spec`: the finite part of a
separated, flat morphism locally of finite presentation over a scheme is a scheme by Stacks 04RI
part (2) and Stacks 04RR part (4), and its projection is separated by Stacks 04RI part (1)
together with Stacks 04RR part (1).

## Main results

* `Stacks.Groupoids.GroupoidScheme.exists_etale_separated_scheme_split`: **Stacks 0DTD**.

## Implementation notes

This is the exact analogue, for Situation 0DTB and plain splitting, of
`Stacks.Groupoids.GroupoidScheme.nonempty_etaleStrongSplitting`, which is Stacks 04RX for
Situation 04RL and strong splitting; the two differ only in which point of `U'` and which
splitting are produced, and the scheme-ness and separatedness arguments are literally the same
because the neighbourhood `(R_s/U, e)_{fin}` is the same in both.

The neighbourhood is produced as an algebraic space asserted to be representable, and the
splitting is the one of Stacks 04RK (2) read for the restriction of the *realization* of the
groupoid scheme, exactly as in
`Stacks.Groupoids.GroupoidScheme.exists_split_of_splittingSituation` for Stacks 0DTC.  The
scheme-level notion `Stacks.Groupoids.GroupoidScheme.Splitting` is not used: a groupoid in
algebraic spaces carries its groupoid structure as a pointwise condition rather than as
structure morphisms, so the composition of the restriction of a realization is not comparable to
the composition supplied by `AlgebraicGeometry.GroupoidScheme.restrict`.

The point of `U'` above `u` is recorded as Stacks 0DTC records it, as a section over
`Spec κ(u)` whose image under `g` is the canonical morphism `Spec κ(u) ⟶ U`.  For a
representable `U'` such a section is a morphism of schemes `Spec κ(u) ⟶ U'`, hence by
`AlgebraicGeometry.Scheme.SpecToEquivOfField` a point `u'` of `U'` above `u` together with a
retraction `κ(u') ⟶ κ(u)` of the residue field map of `g` at `u'`; a retraction of a
homomorphism of fields forces it to be an isomorphism by
`AlgebraicGeometry.Scheme.Hom.isIso_residueFieldMap_of_retraction`, which is the residue-field
clause `κ(u) = κ(u')` of the tag.  So the section formulation is exactly the tag's clause: the
two data determine each other.

Only flatness and local finite presentation of the *source* are assumed; the tag asks them of
the target as well, so the hypotheses here are weaker than the tag's.  Separatedness and local
finiteness of type of the source and of the target, the finiteness of the fibre of the
stabilizer over `u` and the quasi-finiteness of `s` along it are the standing hypotheses of
Situation 0DTB, carried by `AlgebraicGeometry.Space.SplittingSituation`.  The containments `hS`,
`hU`, `hR`, `hP` and `hK` say that the big fppf site contains the base, object, arrow and
composable-pair schemes and `Spec κ(u)`, which is this library's standing ambient requirement.

## References

* [Stacks Project, Tag 04RI](https://stacks.math.columbia.edu/tag/04RI)
* [Stacks Project, Tag 04RK](https://stacks.math.columbia.edu/tag/04RK)
* [Stacks Project, Tag 04RR](https://stacks.math.columbia.edu/tag/04RR)
* [Stacks Project, Tag 04RU](https://stacks.math.columbia.edu/tag/04RU)
* [Stacks Project, Tag 04RX](https://stacks.math.columbia.edu/tag/04RX)
* [Stacks Project, Tag 0DTB](https://stacks.math.columbia.edu/tag/0DTB)
* [Stacks Project, Tag 0DTC](https://stacks.math.columbia.edu/tag/0DTC)
* [Stacks Project, Tag 0DTD](https://stacks.math.columbia.edu/tag/0DTD)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Groupoids.GroupoidScheme

open AlgebraicGeometry.Space AlgebraicGeometry.GroupoidInAlgebraicSpaces in
/-- **Stacks Project, Tag 0DTD.**

In the splitting situation of Stacks 0DTB, with the source in addition flat and locally of finite
presentation, there are a scheme `U'`, a separated étale morphism `g : U' ⟶ U`, and a point `u'`
of `U'` over `u` with `κ(u) = κ(u')`, such that the restriction `R' = R|_{U'}` is split over
`u'`.

The neighbourhood is `U' = (R_s/U, e)_{fin}`, the finite part of Stacks 04RU containing the
unit, with its étale projection; it is a scheme by Stacks 04RI part (2) and Stacks 04RR part
(4), and the projection is separated by Stacks 04RI part (1) and Stacks 04RR part (1).  The
point and the splitting are those of Stacks 0DTC, the point being recorded as a section over
`Spec κ(u)` whose image under `g` is the canonical morphism `Spec κ(u) ⟶ U`. -/
@[stacks 0DTD "in Situation 0DTB with the source flat and locally of finite presentation: U' is
a SCHEME (asserted as representability of the neighbourhood), U' ⟶ U is SEPARATED as well as
étale, and R|_{U'} is SPLIT over a Spec κ(u)-valued point of U' lying over u. The neighbourhood,
its point and the splitting are Stacks 0DTC, which this library proves as
`Stacks.Groupoids.GroupoidScheme.exists_split_of_splittingSituation`; the scheme-ness and the
separatedness are Stacks 04RI and Stacks 04RR applied to the finite part (R_s/U, e)_fin, through
its identification with the neighbourhood recorded by
`AlgebraicGeometry.Space.FinitePartUniversalOpen.objectsEquiv` and `objectProjection_spec`.
Splitting is Stacks 04RK part (2) for the restriction of the REALIZATION of the groupoid scheme,
as in this library's Stacks 0DTC and Stacks 04RX; the scheme-level
`Stacks.Groupoids.GroupoidScheme.Splitting` is not used, the composition of the restricted
realization not being compared with the composition of
`AlgebraicGeometry.GroupoidScheme.restrict`. The residue-field clause κ(u) = κ(u') is the
section over Spec κ(u): a section of a representable U' is a point u' of U' over u together with
a retraction of the residue field map at u', and a retraction forces that map to be an
isomorphism by `AlgebraicGeometry.Scheme.Hom.isIso_residueFieldMap_of_retraction`. Only flatness
and local finite presentation of the SOURCE are assumed, where the tag asks them of the target
too, so the hypotheses are weaker than the tag's. Beyond Situation 0DTB the remaining hypotheses
are that the big fppf site contains the base, object, arrow and composable-pair schemes and
Spec κ(u), this library's standing ambient requirement"]
theorem exists_etale_separated_scheme_split
    (D : AlgebraicGeometry.Space.SplittingSituation.{u})
    (C : AlgebraicGeometry.BigFppfSite.{u}) (hS : C.Contains D.S)
    (hU : C.Contains D.groupoid.objects.left)
    (hR : C.Contains D.groupoid.arrows.left)
    (hP : C.Contains (pullback D.groupoid.source D.groupoid.target).left)
    (hK : C.Contains (Spec (D.groupoid.objects.left.residueField D.u)))
    (hflat : AlgebraicGeometry.Flat D.groupoid.source.left)
    (hfp : AlgebraicGeometry.LocallyOfFinitePresentation D.groupoid.source.left) :
    ∃ (U' : AlgebraicGeometry.AlgebraicSpaces C D.S hS)
      (g : U' ⟶ (D.groupoid.realization C hS hU hR hP).objects),
      U'.obj.IsRepresentable ∧
      AlgebraicGeometry.Space.IsEtale C D.S hS g.hom ∧
      AlgebraicGeometry.Space.IsSeparated C D.S hS g.hom ∧
      ∃ v : U'.obj.obj (Opposite.op
          (schemeSiteObject C hS (X := residueOver D.groupoid D.u) hK)),
        (yonedaSchemePointEquiv C hS hU (Opposite.op
            (schemeSiteObject C hS (X := residueOver D.groupoid D.u) hK))
            (g.hom.app _ v)).left =
          D.groupoid.objects.left.fromSpecResidueField D.u ∧
        IsSplitAt
          (restrict (D.groupoid.realization C hS hU hR hP) g).groupoid
          ((residueSectionValuedPoint D.groupoid C hS D.u hK U' v).class C D.S hS U'.obj) := by
  obtain ⟨W, hWstab, -, -, hWfin⟩ := D.exists_fiberOpens_stabilizer
  have hsep' : IsSeparated C D.S hS (D.groupoid.realization C hS hU hR hP).source.hom :=
    isSeparated_realization_source D.groupoid C hS hU hR hP
  have hflat' : AlgebraicGeometry.Space.IsFlat C D.S hS
      (D.groupoid.realization C hS hU hR hP).source.hom := by
    rw [D.groupoid.realization_source C hS hU hR hP]
    exact isFlat_yoneda_map C D.S hS _ hflat
  have hfp' : IsLocallyOfFinitePresentation C D.S hS
      (D.groupoid.realization C hS hU hR hP).source.hom := by
    rw [D.groupoid.realization_source C hS hU hR hP]
    exact isLocallyOfFinitePresentation_yoneda_map C D.S hS _ hfp
  have hUrep : (D.groupoid.realization C hS hU hR hP).objects.obj.IsRepresentable :=
    inferInstanceAs (yoneda.obj (schemeSiteObject C hS hU)).IsRepresentable
  set F := realizationFinitePart D.groupoid C hS hU hR hP
  refine ⟨F.objects, F.objectProjection, ?_, F.objectProjection_etale, ?_,
    etaleLocalStabilizerFibrePoint D.groupoid C hS hU hR D.u hK hP W hWfin hWstab F,
    lies_over_stabilizerFibrePoint D.groupoid C hS hU hR D.u hK hP W hWfin hWstab F,
    isSplitAt_stabilizerFibreValuedPoint D.groupoid C hS hU hR D.u hK hP W hWfin hWstab F⟩
  · have := isRepresentable_finitePartWithSection C D.S hS _ F.unit F.unit_source
      hsep' hflat' hfp' hUrep
    exact Functor.IsRepresentable.mk'
      ((finitePartWithSection C D.S hS (D.groupoid.realization C hS hU hR hP).source
        F.unit F.unit_source).toSubfunctor.toFunctor.reprW ≪≫ F.objectsEquiv.symm)
  · rw [F.objectProjection_spec]
    exact isSeparated_comp C D.S hS _ _ (isSeparated_of_isIso C D.S hS F.objectsEquiv.hom)
      (isSeparated_ι_comp_baseMap_finitePartWithSection C D.S hS _ F.unit F.unit_source
        hsep' hflat' hfp')

end Stacks.Groupoids.GroupoidScheme

end
