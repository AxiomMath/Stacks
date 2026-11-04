module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasiSplittingEtaleLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.StrongSplittingDerealizationPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.StrongSplittingEtaleScheme

/-!
# A quasi-splitting on a separated étale neighbourhood which is a scheme

Let `(U, R, s, t, c)` be a groupoid scheme over `S` in the quasi-splitting situation of
Stacks 04RV at a point `u ∈ U`, and suppose in addition that `s` is flat and locally of finite
presentation.  Then the étale neighbourhood `U' = (R_s/U, e)_{fin}` of Stacks 04RW is a *scheme*
and its projection `g : U' ⟶ U` is *separated* as well as étale, while `R' = R|_{U'}` is still
quasi-split over the point of `U'` above `u` whose residue field is `κ(u)`.  This is
**Stacks 04RY**.

## Main results

* `AlgebraicGeometry.Scheme.Hom.exists_isIso_residueFieldMap_of_specResidueFieldSection`: a
  morphism of schemes with a section over `Spec κ(y)` has a point above `y` with residue field
  `κ(y)`.
* `AlgebraicGeometry.Space.exists_isIso_residueFieldMap_of_residueSection`: the same, read for a
  `Spec κ(u)`-valued section of an algebraic space on a scheme representing it.
* `Stacks.Groupoids.GroupoidScheme.exists_quasiSplit_separated_scheme_of_quasiSplittingSituation`:
  **Stacks 04RY**.

## Implementation notes

The neighbourhood, its point and the quasi-splitting are those of Stacks 04RW; what is added
here is that `U'` is a scheme and that `g` is separated.  Both come from the identification of
`U'` with the finite part containing the unit: the finite part of a separated, flat morphism
locally of finite presentation over a scheme is a scheme by Stacks 04RI part (2) and Stacks
04RR part (4), and its projection is separated by Stacks 04RI part (1) together with Stacks
04RR part (1).

The neighbourhood is produced as an algebraic space asserted to be representable, so the point
`u'` of the tag is recorded twice: as the `Spec κ(u)`-valued section `v` of `U'` over the
canonical morphism `Spec κ(u) ⟶ U`, and — on any scheme `X'` representing `U'`, with any
morphism of schemes `X' ⟶ U` inducing `g` — as an honest point `u'` of `X'` over `u` at which
the residue field map of that morphism is an isomorphism, which is the equality `κ(u) = κ(u')`.
A morphism `Spec κ(u) ⟶ X'` over `u` is a point of `X'` over `u` together with a retraction of
the residue field map there, and a retraction of a homomorphism of fields forces it to be an
isomorphism.

Only flatness and local finite presentation of the *source* are assumed; the tag asks them of
the target as well, so the hypotheses here are weaker than the tag's.  Separatedness and local
finiteness of type of the source and of the target and the quasi-finiteness of `s` at `e(u)`
are the standing hypotheses of Situation 04RV, carried by
`AlgebraicGeometry.Space.QuasiSplittingSituation`.  The containments `hS`, `hU`, `hR`, `hP` and
`hK` say that the big fppf site contains the base, object, arrow and composable-pair schemes and
`Spec κ(u)`, which is this library's standing ambient requirement.

## References

* [Stacks Project, Tag 04RI](https://stacks.math.columbia.edu/tag/04RI)
* [Stacks Project, Tag 04RK](https://stacks.math.columbia.edu/tag/04RK)
* [Stacks Project, Tag 04RR](https://stacks.math.columbia.edu/tag/04RR)
* [Stacks Project, Tag 04RU](https://stacks.math.columbia.edu/tag/04RU)
* [Stacks Project, Tag 04RV](https://stacks.math.columbia.edu/tag/04RV)
* [Stacks Project, Tag 04RW](https://stacks.math.columbia.edu/tag/04RW)
* [Stacks Project, Tag 04RY](https://stacks.math.columbia.edu/tag/04RY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A morphism of schemes admitting a section over the spectrum of the residue field at a point
of the target has a point above that point with the same residue field. -/
alias exists_isIso_residueFieldMap_of_specResidueFieldSection :=
  exists_isIso_residueFieldMap_of_specResidueField

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Space

/-- A `Spec κ(u)`-valued section of an algebraic space over the canonical morphism
`Spec κ(u) ⟶ U`, read on a scheme representing that space, gives a point of the scheme above
`u` whose residue field is `κ(u)`. -/
theorem exists_isIso_residueFieldMap_of_residueSection
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
    (C : BigFppfSite.{u}) (hS : C.Contains S) (hU : C.Contains G.objects.left)
    (u : G.objects.left) (hK : C.Contains (Spec (G.objects.left.residueField u)))
    (U' : AlgebraicGeometry.AlgebraicSpaces C S hS)
    (g : U'.obj ⟶ yoneda.obj (schemeSiteObject C hS hU))
    (v : U'.obj.obj (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK)))
    (hv : (yonedaSchemePointEquiv C hS hU
        (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK)) (g.app _ v)).left =
      G.objects.left.fromSpecResidueField u)
    (X' : BigFppfOver C S hS) (ε : U'.obj ≅ yoneda.obj X')
    (gS : X' ⟶ schemeSiteObject C hS hU) (hgS : yoneda.map gS = ε.inv ≫ g) :
    ∃ x : (BigFppfOver.toScheme C S hS).obj X',
      ((BigFppfOver.toScheme C S hS).map gS).base x = u ∧
      IsIso (((BigFppfOver.toScheme C S hS).map gS).residueFieldMap x) := by
  have hkey : yoneda.preimage (yonedaEquiv.symm v ≫ ε.hom) ≫ gS =
      g.app (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK)) v := by
    refine yoneda.map_injective ?_
    rw [yoneda.map_comp, Functor.map_preimage, hgS, Category.assoc, Iso.hom_inv_id_assoc]
    refine yonedaEquiv.injective ?_
    rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map, Equiv.apply_symm_apply]
  have hw : (BigFppfOver.toScheme C S hS).map
        (yoneda.preimage (yonedaEquiv.symm v ≫ ε.hom)) ≫
      (BigFppfOver.toScheme C S hS).map gS =
      G.objects.left.fromSpecResidueField u := by
    rw [← Functor.map_comp, hkey]
    exact hv
  exact Scheme.Hom.exists_isIso_residueFieldMap_of_specResidueFieldSection _ u _ hw

end AlgebraicGeometry.Space

namespace Stacks.Groupoids.GroupoidScheme

open AlgebraicGeometry.Space AlgebraicGeometry.GroupoidInAlgebraicSpaces in
/-- **Stacks Project, Tag 04RY.**

In the quasi-splitting situation of Stacks 04RV, with the source in addition flat and locally
of finite presentation, there are a scheme `U'`, a separated étale morphism `g : U' ⟶ U`, and a
point `u'` of `U'` over `u` with `κ(u) = κ(u')`, such that `R' = R|_{U'}` is quasi-split over
`u'`. -/
@[stacks 04RY "ALL FOUR ASSERTIONS PRODUCED, in Situation 04RV with the source flat and \
locally of finite presentation: U' is a SCHEME (delivered as representability of the \
neighbourhood), U' -> U is SEPARATED as well as etale, there is a point u' of U' over u with \
k(u) = k(u') -- recorded both as a Spec k(u)-valued section v of U' over the canonical \
Spec k(u) -> U, and, on any scheme X' representing U' with any morphism of schemes X' -> U \
inducing g, as a point u' of X' with image u at which the residue field map is an ISOMORPHISM \
-- and R|_{U'} is QUASI-SPLIT over u'. Each of the four is constructed, none of them an input. \
The neighbourhood, the point and the quasi-splitting are Tag 04RW, proved in \
StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/QuasiSplittingEtaleLocalization.lean; the \
scheme-ness and the separatedness are Tags 04RI and 04RR applied to the finite part \
(R_s/U, e)_fin. Flatness and local finite presentation are required of the SOURCE alone, where \
the tag requires them of the target too, so these hypotheses are WEAKER than the tag's. Beyond \
Situation 04RV the remaining requirements are that the big fppf site contains the base, object, \
arrow and composable-pair schemes and Spec k(u), this library's standing ambient requirement"]
theorem exists_quasiSplit_separated_scheme_of_quasiSplittingSituation
    (D : AlgebraicGeometry.Space.QuasiSplittingSituation.{u})
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
        IsQuasiSplitAt
          (restrict (D.groupoid.realization C hS hU hR hP) g).groupoid
          ((residueSectionValuedPoint D.groupoid C hS D.u hK U' v).class C D.S hS U'.obj) ∧
        ∀ (X' : AlgebraicGeometry.BigFppfOver C D.S hS) (ε : U'.obj ≅ yoneda.obj X')
          (gS : X' ⟶ schemeSiteObject C hS hU), yoneda.map gS = ε.inv ≫ g.hom →
          ∃ u' : (AlgebraicGeometry.BigFppfOver.toScheme C D.S hS).obj X',
            ((AlgebraicGeometry.BigFppfOver.toScheme C D.S hS).map gS).base u' = D.u ∧
            IsIso (((AlgebraicGeometry.BigFppfOver.toScheme C D.S hS).map
              gS).residueFieldMap u') := by
  obtain ⟨W, hWid, hWfin⟩ := D.exists_fiberOpens_identity
  have hsep' : IsSeparated C D.S hS (D.groupoid.realization C hS hU hR hP).source.hom :=
    isSeparated_realization_source D.groupoid C hS hU hR hP
  have hflat' : AlgebraicGeometry.Space.IsFlat C D.S hS
      (D.groupoid.realization C hS hU hR hP).source.hom := by
    rw [D.groupoid.realization_source C hS hU hR hP]
    refine isFlat_yoneda_map C D.S hS _ ?_
    rw [toScheme_map_schemeSiteMap_eq]
    exact hflat
  have hfp' : IsLocallyOfFinitePresentation C D.S hS
      (D.groupoid.realization C hS hU hR hP).source.hom := by
    rw [D.groupoid.realization_source C hS hU hR hP]
    refine isLocallyOfFinitePresentation_yoneda_map C D.S hS _ ?_
    rw [toScheme_map_schemeSiteMap_eq]
    exact hfp
  have hUrep : (D.groupoid.realization C hS hU hR hP).objects.obj.IsRepresentable :=
    inferInstanceAs (yoneda.obj (schemeSiteObject C hS hU)).IsRepresentable
  have hmem := unitFibrePoint_mem_identity D.groupoid C hS hU hR D.u hK hP
    (realizationFinitePart D.groupoid C hS hU hR hP) W hWid
  have hlies := lies_over_fibrePointOfMem D.groupoid C hS hU hR D.u hK hP
    (realizationFinitePart D.groupoid C hS hU hR hP) W hmem hWfin
  refine ⟨(realizationFinitePart D.groupoid C hS hU hR hP).objects,
    (realizationFinitePart D.groupoid C hS hU hR hP).objectProjection, ?_,
    (realizationFinitePart D.groupoid C hS hU hR hP).objectProjection_etale, ?_,
    etaleLocalFibrePointOfMem D.groupoid C hS hU hR D.u hK hP
      (realizationFinitePart D.groupoid C hS hU hR hP) W hmem hWfin, hlies,
    isQuasiSplitAt_of_openFiniteSubgroupoid _
      (realizationFinitePart D.groupoid C hS hU hR hP).restrictedSubgroupoid _,
    fun X' ε gS hgS => exists_isIso_residueFieldMap_of_residueSection D.groupoid C hS hU D.u hK
      (realizationFinitePart D.groupoid C hS hU hR hP).objects
      (realizationFinitePart D.groupoid C hS hU hR hP).objectProjection.hom _ hlies
      X' ε gS hgS⟩
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
