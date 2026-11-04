module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.EtaleLocalizationArrowContainment
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSchemeDerealization
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.WithSectionScheme

/-!
# A strong splitting on a separated étale neighbourhood which is a scheme

Let `(U, R, s, t, c)` be a groupoid scheme over `S` in the strong splitting situation of
Stacks 04RL at a point `u ∈ U`, and suppose in addition that `s` is flat and locally of finite
presentation.  Then the étale neighbourhood `U' = (R_s/U, e)_{fin}` of Stacks 03FM is a *scheme*
and its projection `g : U' ⟶ U` is *separated* as well as étale, while `R' = R|_{U'}` is still
strongly split over the point of `U'` above `u` whose residue field is `κ(u)`.  This is
**Stacks 04RX**.

The neighbourhood, its point and the splitting are those of Stacks 03FM, available as
`AlgebraicGeometry.Space.exists_stronglySplit_of_strongSplittingSituation`; what Stacks 04RX adds
is that `U'` is a scheme and that `g` is separated.  Both come from the identification of `U'`
with the finite part containing the unit, recorded by
`AlgebraicGeometry.Space.FinitePartUniversalOpen.objectsEquiv` and
`AlgebraicGeometry.Space.FinitePartUniversalOpen.objectProjection_spec`: the finite part of a
separated, flat morphism locally of finite presentation over a scheme is a scheme by
Stacks 04RI part (2) and Stacks 04RR part (4), and its projection is separated by Stacks 04RI
part (1) together with Stacks 04RR part (1).

## Main results

* `AlgebraicGeometry.Scheme.Hom.isIso_residueFieldMap_of_retraction`: if the residue field map
  of a morphism of schemes at a point admits a retraction, it is an isomorphism.  This is why a
  `Spec κ(u)`-valued point of `U'` lying over `u` is a point `u'` of `U'` with `κ(u) = κ(u')`.
* `Stacks.Groupoids.GroupoidScheme.nonempty_etaleStrongSplitting`: **Stacks 04RX**.

## Implementation notes

The neighbourhood is produced as an algebraic space asserted to be representable, and the
splitting is the one of Stacks 04RK read for the restriction of the *realization* of the
groupoid scheme, exactly as in
`AlgebraicGeometry.Space.exists_stronglySplit_of_strongSplittingSituation` for Stacks 03FM and
in `Stacks.Groupoids.GroupoidScheme.exists_etale_separated_scheme_quasiSplitting` for
Stacks 04RY.  The scheme-level notion
`Stacks.Groupoids.GroupoidScheme.StrongSplitting` is not used: a groupoid in algebraic spaces
carries its groupoid structure as a pointwise condition rather than as structure morphisms, so
the composition of the restriction of a realization is not comparable to the composition
supplied by `AlgebraicGeometry.GroupoidScheme.restrict` — the comparison of the two
compositions is the one piece the de-realization of
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSchemeDerealization` leaves open, its
arrow spaces being already identified by
`Stacks.Groupoids.GroupoidScheme.restrictionArrowsRealizationIso`.

The point of `U'` above `u` is recorded as Stacks 03FM records it, as a section over
`Spec κ(u)` whose image under `g` is the canonical morphism `Spec κ(u) ⟶ U`.  For a
representable `U'` such a section is a morphism of schemes `Spec κ(u) ⟶ U'`, hence by
`AlgebraicGeometry.Scheme.SpecToEquivOfField` a point `u'` of `U'` above `u` together with a
retraction `κ(u') ⟶ κ(u)` of the residue field map of `g` at `u'`; a retraction of a
homomorphism of fields forces it to be an isomorphism, which is the residue-field clause
`κ(u) = κ(u')` of the tag.

Only flatness and local finite presentation of the *source* are assumed; the tag asks them of
the target as well, so the hypotheses here are weaker than the tag's.  Separatedness and local
finiteness of type of the source and of the target, the finiteness of the stabilizer of `u` and
the quasi-finiteness of `s` along it are the standing hypotheses of Situation 04RL, carried by
`AlgebraicGeometry.Space.StrongSplittingSituation`.  The containments `hS`, `hU`, `hR`, `hP` and
`hK` say that the big fppf site contains the base, object, arrow and composable-pair schemes and
`Spec κ(u)`, which is this library's standing ambient requirement.

## References

* [Stacks Project, Tag 03FM](https://stacks.math.columbia.edu/tag/03FM)
* [Stacks Project, Tag 04RI](https://stacks.math.columbia.edu/tag/04RI)
* [Stacks Project, Tag 04RK](https://stacks.math.columbia.edu/tag/04RK)
* [Stacks Project, Tag 04RL](https://stacks.math.columbia.edu/tag/04RL)
* [Stacks Project, Tag 04RR](https://stacks.math.columbia.edu/tag/04RR)
* [Stacks Project, Tag 04RU](https://stacks.math.columbia.edu/tag/04RU)
* [Stacks Project, Tag 04RX](https://stacks.math.columbia.edu/tag/04RX)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- If the residue field map of a morphism of schemes at a point admits a retraction, then it is
an isomorphism.

The retraction is surjective because it is a retraction, and injective because its source is a
field; hence it is bijective, so an isomorphism, and the map it retracts is its inverse. -/
theorem isIso_residueFieldMap_of_retraction {X Y : Scheme.{u}} (f : X ⟶ Y) (p : X)
    (σ : X.residueField p ⟶ Y.residueField (f.base p))
    (hσ : f.residueFieldMap p ≫ σ = 𝟙 (Y.residueField (f.base p))) :
    IsIso (f.residueFieldMap p) := by
  have hinj : Function.Injective σ := RingHom.injective (CommRingCat.Hom.hom σ)
  have hsurj : Function.Surjective σ := by
    have h : Function.Surjective fun x : Y.residueField (f.base p) =>
        σ (f.residueFieldMap p x) := by
      refine fun x => ⟨x, ?_⟩
      have h' := congrArg
        (fun k : Y.residueField (f.base p) ⟶ Y.residueField (f.base p) => k x) hσ
      simpa using h'
    exact Function.Surjective.of_comp h
  have hiso : IsIso σ := (ConcreteCategory.isIso_iff_bijective σ).2 ⟨hinj, hsurj⟩
  have : IsIso (f.residueFieldMap p ≫ σ) := by
    rw [hσ]
    infer_instance
  exact IsIso.of_isIso_comp_right (f.residueFieldMap p) σ

end AlgebraicGeometry.Scheme.Hom

namespace Stacks.Groupoids.GroupoidScheme

open AlgebraicGeometry.Space AlgebraicGeometry.GroupoidInAlgebraicSpaces in
/-- **Stacks Project, Tag 04RX.**

In the strong splitting situation of Stacks 04RL, with the source in addition flat and locally
of finite presentation, there are a scheme `U'`, a separated étale morphism `g : U' ⟶ U`, and a
point `u'` of `U'` over `u` with `κ(u) = κ(u')`, such that the restriction `R' = R|_{U'}` is
strongly split over `u'`.

The neighbourhood is `U' = (R_s/U, e)_{fin}`, the finite part of Stacks 04RU containing the
unit, with its étale projection; it is a scheme by Stacks 04RI part (2) and Stacks 04RR part
(4), and the projection is separated by Stacks 04RI part (1) and Stacks 04RR part (1).  The
point and the strong splitting are those of Stacks 03FM, the point being recorded as a section
over `Spec κ(u)` whose image under `g` is the canonical morphism `Spec κ(u) ⟶ U`. -/
@[stacks 04RX "in Situation 04RL with the source flat and locally of finite presentation: U' is
a SCHEME (asserted as representability of the neighbourhood), U' ⟶ U is SEPARATED as well as
étale, and R|_{U'} is strongly split over a Spec κ(u)-valued point of U' lying over u. The
neighbourhood, its point and the splitting are Stacks 03FM, which this library proves as
`AlgebraicGeometry.Space.exists_stronglySplit_of_strongSplittingSituation`; the scheme-ness and
the separatedness are Stacks 04RI and Stacks 04RR applied to the finite part (R_s/U, e)_fin,
through its identification with the neighbourhood recorded by
`AlgebraicGeometry.Space.FinitePartUniversalOpen.objectsEquiv` and `objectProjection_spec`.
Strong splitting is Stacks 04RK part (1) for the restriction of the REALIZATION of the groupoid
scheme, as in this library's Stacks 03FM and Stacks 04RY; the scheme-level
`Stacks.Groupoids.GroupoidScheme.StrongSplitting` is not used, the composition of the restricted
realization not being compared with the composition of
`AlgebraicGeometry.GroupoidScheme.restrict`. Only flatness and local finite presentation of the
SOURCE are assumed, where the tag asks them of the target too, so the hypotheses are weaker than
the tag's. Beyond Situation 04RL the remaining hypotheses are that the big fppf site contains
the base, object, arrow and composable-pair schemes and Spec κ(u), this library's standing
ambient requirement"]
theorem nonempty_etaleStrongSplitting
    (D : AlgebraicGeometry.Space.StrongSplittingSituation.{u})
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
        IsStronglySplitAt
          (restrict (D.groupoid.realization C hS hU hR hP) g).groupoid
          ((residueSectionValuedPoint D.groupoid C hS D.u hK U' v).class C D.S hS U'.obj) := by
  obtain ⟨W, hW, -, hWfin⟩ := D.exists_fiberOpens_stabilizer
  have hsep' : IsSeparated C D.S hS (D.groupoid.realization C hS hU hR hP).source.hom :=
    isSeparated_realization_source D.groupoid C hS hU hR hP
  have hflat' : AlgebraicGeometry.Space.IsFlat C D.S hS
      (D.groupoid.realization C hS hU hR hP).source.hom :=
    isFlat_yoneda_map C D.S hS _ hflat
  have hfp' : IsLocallyOfFinitePresentation C D.S hS
      (D.groupoid.realization C hS hU hR hP).source.hom :=
    isLocallyOfFinitePresentation_yoneda_map C D.S hS _ hfp
  have hUrep : (D.groupoid.realization C hS hU hR hP).objects.obj.IsRepresentable :=
    inferInstanceAs (yoneda.obj (schemeSiteObject C hS hU)).IsRepresentable
  refine ⟨(realizationFinitePart D.groupoid C hS hU hR hP).objects,
    (realizationFinitePart D.groupoid C hS hU hR hP).objectProjection, ?_,
    (realizationFinitePart D.groupoid C hS hU hR hP).objectProjection_etale, ?_,
    etaleLocalFibrePoint D.groupoid C hS hU hR D.u hK hP
      (realizationFinitePart D.groupoid C hS hU hR hP) W hW hWfin,
    lies_over_fibrePoint D.groupoid C hS hU hR D.u hK hP
      (realizationFinitePart D.groupoid C hS hU hR hP) W hW hWfin,
    isStronglySplitAt_fibreValuedPoint D.groupoid C hS hU hR D.u hK hP
      (realizationFinitePart D.groupoid C hS hU hR hP) W hW hWfin⟩
  · have hrep : (finitePartWithSection C D.S hS
        (D.groupoid.realization C hS hU hR hP).source
        (realizationFinitePart D.groupoid C hS hU hR hP).unit
        (realizationFinitePart D.groupoid C hS hU hR
          hP).unit_source).toSubfunctor.toFunctor.IsRepresentable :=
      isRepresentable_finitePartWithSection C D.S hS _
        (realizationFinitePart D.groupoid C hS hU hR hP).unit
        (realizationFinitePart D.groupoid C hS hU hR hP).unit_source hsep' hflat' hfp' hUrep
    exact Functor.IsRepresentable.mk'
      ((finitePartWithSection C D.S hS (D.groupoid.realization C hS hU hR hP).source
        (realizationFinitePart D.groupoid C hS hU hR hP).unit
        (realizationFinitePart D.groupoid C hS hU hR hP).unit_source).toSubfunctor.toFunctor.reprW
        ≪≫ (realizationFinitePart D.groupoid C hS hU hR hP).objectsEquiv.symm)
  · rw [(realizationFinitePart D.groupoid C hS hU hR hP).objectProjection_spec]
    exact isSeparated_comp C D.S hS _ _
      (isSeparated_of_isIso C D.S hS
        (realizationFinitePart D.groupoid C hS hU hR hP).objectsEquiv.hom)
      (isSeparated_ι_comp_baseMap_finitePartWithSection C D.S hS _
        (realizationFinitePart D.groupoid C hS hU hR hP).unit
        (realizationFinitePart D.groupoid C hS hU hR hP).unit_source hsep' hflat' hfp')

end Stacks.Groupoids.GroupoidScheme

end
