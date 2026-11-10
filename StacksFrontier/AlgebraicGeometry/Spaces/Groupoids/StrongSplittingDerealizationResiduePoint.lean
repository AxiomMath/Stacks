module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.StrongSplittingDerealizationSubgroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.StrongSplittingDerealizationTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.SitePullbackContainment

/-!
# A strong splitting on a separated étale neighbourhood, de-realized

Let `(U, R, s, t, c)` be a groupoid scheme over `S` in the strong splitting situation of
Stacks 04RL at a point `u ∈ U`, with `s` flat and locally of finite presentation.  Stacks 04RX
produces a representable algebraic space `U'` étale and separated over the object space of the
realization of `R`, a section of `U'` over `Spec κ(u)` lying over the canonical morphism
`Spec κ(u) ⟶ U`, and a strong splitting of the restriction of the realization along `U' ⟶ U`.
This file turns that output into data about *schemes*: a scheme `Y` over `S`, a separated étale
`q : Y ⟶ U`, a point `y` of `Y` above `u` with `κ(u) = κ(y)`, and a strong splitting of every
groupoid scheme realizing `R|_Y` over the point of its object scheme carried by `y`.

The point of `Y` is the image of the closed point under the morphism `Spec κ(u) ⟶ Y` that the
section determines, and the content of the de-realization is that this point and the
field-valued point of `U'` recorded by Stacks 04RX describe one another: the section of `U'` is
the image of a section of the presheaf represented by `Y`, and the point of `|U'|` it defines is
the image of the point of `|Y|` defined by that section.

## Main results

* `Stacks.Groupoids.GroupoidScheme.pointsMap_derealizeResiduePoint_eq_class`: the point of `|Y|`
  given by the de-realized morphism `Spec κ(u) ⟶ Y` is carried by the identification of the
  presheaf represented by `Y` with `U'` to the field-valued point of `U'` recorded by
  Stacks 04RX.
* `Stacks.Groupoids.GroupoidScheme.pointsMap_derealizedObjectPoint_eq`: the de-realized point of
  the object space of a realization of `R|_Y`, transported along the identification of `Y` with
  `U'`, is that same field-valued point.
* `Stacks.Groupoids.GroupoidScheme.isIso_residueFieldMap_restriction_mapObjects`: the point of
  the object scheme of a realization of `R|_Y` carried by `y` lies over `u` and has residue field
  `κ(u)`.
* `Stacks.Groupoids.GroupoidScheme.isStronglySplitAt_of_derealize`: a strong splitting of the
  restriction of the realization along `U' ⟶ U` de-realizes to a strong splitting of every
  groupoid scheme realizing `R|_Y` over the point carried by `y`.
* `Stacks.Groupoids.GroupoidScheme.exists_etale_separated_scheme_isStronglySplitAt`: the output
  of Stacks 04RX read entirely at the level of schemes.

## References

* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 04RK](https://stacks.math.columbia.edu/tag/04RK)
* [Stacks Project, Tag 04RL](https://stacks.math.columbia.edu/tag/04RL)
* [Stacks Project, Tag 04RX](https://stacks.math.columbia.edu/tag/04RX)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.BigFppfSite

-- A big fppf site containing two schemes over `S` contains their fibre product over any
-- third one -- Stacks 000R part (1), read for the size cutoff of the site -- is
-- `AlgebraicGeometry.BigFppfSite.contains_pullback_left` in
-- `StacksFrontier/AlgebraicGeometry/Spaces/SitePullbackContainment.lean`, proved there from
-- `contains_of_mono` and `contains_prod_left`.  It is not restated here.

end AlgebraicGeometry.BigFppfSite

namespace Stacks.Groupoids.GroupoidScheme

open AlgebraicGeometry.Space

variable {S : Scheme.{u}} (G : GroupoidScheme S) (C : BigFppfSite.{u}) (hS : C.Contains S)
  (hU : C.Contains G.objects.left) (hR : C.Contains G.arrows.left)
  (hP : C.Contains (pullback G.source G.target).left)
  {Y : Over S} (hY : C.Contains Y.left) (q : Y ⟶ G.objects) (u : G.objects.left)
  (hK : C.Contains (Spec (G.objects.left.residueField u)))
  {U' : AlgebraicSpaces C S hS} (e : yoneda.obj (schemeSiteObject C hS hY) ≅ U'.obj)
  (v : U'.obj.obj (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK)))

/-! ### Comparing the two descriptions of the point

The point of `Y` above `u` with residue field `κ(u)` is the image of the closed point under the
de-realized morphism `Spec κ(u) ⟶ Y`, by
`Stacks.Groupoids.GroupoidScheme.isIso_residueFieldMap_derealizeResiduePoint`; what remains is to
identify the point of `|U'|` it determines with the field-valued point recorded by
Stacks 04RX. -/

/-- The field-valued point of the presheaf represented by `Y` carried by a section of `U'` over
the spectrum of the residue field at `u`: the same data, with the section pulled back along the
identification of the two presheaves. -/
private def derealizeResidueValuedPoint :
    FieldValuedPoint C S hS (yoneda.obj (schemeSiteObject C hS hY)) where
  carrier := G.objects.left.residueField u
  contained := hK
  toBase := G.objects.left.fromSpecResidueField u ≫ G.objects.hom
  value := e.inv.app (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK)) v

/-- The scheme point underlying that field-valued point is the image of the closed point under
the de-realized morphism `Spec κ(u) ⟶ Y`. -/
private theorem schemePoint_derealizeResidueValuedPoint :
    schemePoint C S hS (schemeSiteObject C hS hY)
        (derealizeResidueValuedPoint G C hS hY u hK e v) =
      (derealizeResiduePoint G C hS hY e u hK v).left.base
        (IsLocalRing.closedPoint (G.objects.left.residueField u)) := rfl

/-- Pushing that field-valued point forward along the identification of the two presheaves gives
the field-valued point of `U'` recorded by Stacks 04RX. -/
private theorem pointsMap_class_derealizeResidueValuedPoint :
    pointsMap C S hS (yoneda.obj (schemeSiteObject C hS hY)) e.hom
        ((derealizeResidueValuedPoint G C hS hY u hK e v).class C S hS
          (yoneda.obj (schemeSiteObject C hS hY))) =
      (residueSectionValuedPoint G C hS u hK U' v).class C S hS U'.obj := by
  refine congrArg (fun w => FieldValuedPoint.class C S hS U'.obj
    { carrier := G.objects.left.residueField u, contained := hK,
      toBase := G.objects.left.fromSpecResidueField u ≫ G.objects.hom, value := w }) ?_
  exact congrArg (fun k => k v) (NatTrans.congr_app e.inv_hom_id
    (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK)))

/-- **The two descriptions of the point agree.**  The point of `|Y|` given by the image of the
closed point under the de-realized morphism `Spec κ(u) ⟶ Y` is carried by the identification of
the presheaf represented by `Y` with `U'` to the field-valued point of `U'` recorded by
Stacks 04RX. -/
theorem pointsMap_derealizeResiduePoint_eq_class (y : Y.left)
    (hy : y = (derealizeResiduePoint G C hS hY e u hK v).left.base
      (IsLocalRing.closedPoint (G.objects.left.residueField u))) :
    pointsMap C S hS (yoneda.obj (schemeSiteObject C hS hY)) e.hom
        ((pointsEquivScheme C S hS (schemeSiteObject C hS hY)).symm y) =
      (residueSectionValuedPoint G C hS u hK U' v).class C S hS U'.obj := by
  subst hy
  refine Eq.trans ?_ (pointsMap_class_derealizeResidueValuedPoint G C hS hY u hK e v)
  refine congrArg (pointsMap C S hS (yoneda.obj (schemeSiteObject C hS hY)) e.hom) ?_
  refine (congrArg (pointsEquivScheme C S hS (schemeSiteObject C hS hY)).symm
    (schemePoint_derealizeResidueValuedPoint G C hS hY u hK e v).symm).trans ?_
  refine (Equiv.symm_apply_eq _).2 ?_
  exact (pointsToScheme_class C S hS (schemeSiteObject C hS hY)
    (derealizeResidueValuedPoint G C hS hY u hK e v)).symm

/-- **The de-realized point of the object space of a realization of the restriction.**  It is
carried, by the comparison of the object spaces of the two restrictions, to the field-valued
point of `U'` recorded by Stacks 04RX.

The two transports along the equalities of object spaces which the two realizations record are
the identity on the presheaves they compare, so only the identification of the presheaf
represented by `Y` with `U'` remains. -/
theorem pointsMap_derealizedObjectPoint_eq
    (g : U' ⟶ (G.realization C hS hU hR hP).objects)
    (R : GroupoidInAlgebraicSpaces.Restriction (G.realization C hS hU hR hP) g)
    (Rs : GroupoidInAlgebraicSpaces.Restriction (G.realization C hS hU hR hP)
      (realizationMap G C hS hU hR hP hY q))
    (Gr : AlgebraicGeometry.GroupoidScheme.Restriction G q) (y : Y.left)
    (hy : y = (derealizeResiduePoint G C hS hY e u hK v).left.base
      (IsLocalRing.closedPoint (G.objects.left.residueField u))) :
    pointsMap C S hS Rs.groupoid.objects.obj
        (eqToHom Rs.objects_eq ≫ (derealizeSpaceIso C hS hY e).hom ≫
          eqToHom R.objects_eq.symm).hom
        (derealizedObjectPoint G C hS hU hR hP hY q Rs Gr
          ((eqToHom Gr.objects_eq.symm).left.base y)) =
      pointsMap C S hS U'.obj (eqToHom R.objects_eq.symm).hom
        ((residueSectionValuedPoint G C hS u hK U' v).class C S hS U'.obj) := by
  have hhom : (eqToHom Rs.objects_eq ≫ (derealizeSpaceIso C hS hY e).hom ≫
        eqToHom R.objects_eq.symm).hom =
      (eqToHom Rs.objects_eq).hom ≫ e.hom ≫ (eqToHom R.objects_eq.symm).hom := rfl
  have hid : eqToHom (restrictionObjectsObj_eq G C hS hU hR hP hY q Rs).symm ≫
      (eqToHom Rs.objects_eq).hom = 𝟙 (yoneda.obj (schemeSiteObject C hS hY)) := by
    rw [hom_eqToHom C hS Rs.objects_eq, eqToHom_trans, eqToHom_refl]
  have hpt : pointsMap C S hS Rs.groupoid.objects.obj (eqToHom Rs.objects_eq).hom
      (derealizedObjectPoint G C hS hU hR hP hY q Rs Gr
        ((eqToHom Gr.objects_eq.symm).left.base y)) =
      (pointsEquivScheme C S hS (schemeSiteObject C hS hY)).symm y := by
    change pointsMap C S hS Rs.groupoid.objects.obj (eqToHom Rs.objects_eq).hom
      (pointsMap C S hS (yoneda.obj (schemeSiteObject C hS hY))
        (eqToHom (restrictionObjectsObj_eq G C hS hU hR hP hY q Rs).symm)
        ((pointsEquivScheme C S hS (schemeSiteObject C hS hY)).symm
          ((eqToHom Gr.objects_eq).left.base
            ((eqToHom Gr.objects_eq.symm).left.base y)))) = _
    rw [← pointsMap_comp_apply, hid, pointsMap_id, over_eqToHom_apply_symm]
    rfl
  rw [hhom, pointsMap_comp_apply, pointsMap_comp_apply, hpt,
    pointsMap_derealizeResiduePoint_eq_class G C hS hY u hK e v y hy]

/-! ### The de-realized strong splitting -/

/-- **A strong splitting de-realized to the scheme level.**  A strong splitting of a realization
of the restriction of the realization of `R` along a morphism from `U'`, at the field-valued
point of `U'` recorded by Stacks 04RX, is a strong splitting of every groupoid scheme realizing
`R|_Y` over the point of its object scheme carried by `y`.

The splitting is first transported along the identification of `U'` with the presheaf
represented by `Y`, by
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.nonempty_strongSplitting_of_eq`, and then
de-realized by
`Stacks.Groupoids.GroupoidScheme.isStronglySplitAt_of_contains_arrows`. -/
theorem isStronglySplitAt_of_derealize
    (hA : C.Contains (pullback q G.target).left)
    (hB : C.Contains (pullback G.source q).left)
    (hRA : C.Contains (AlgebraicGeometry.restrictionArrows G q).left)
    (hCP : C.Contains (restrictionComposablePairs G q).left)
    (g : U' ⟶ (G.realization C hS hU hR hP).objects)
    (he : e.hom ≫ g.hom = yoneda.map (schemeSiteMap C hS hY hU q))
    (hsplit : GroupoidInAlgebraicSpaces.IsStronglySplitAt
      (GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP) g).groupoid
      ((residueSectionValuedPoint G C hS u hK U' v).class C S hS U'.obj))
    (Gr : AlgebraicGeometry.GroupoidScheme.Restriction G q) (y : Y.left)
    (hy : y = (derealizeResiduePoint G C hS hY e u hK v).left.base
      (IsLocalRing.closedPoint (G.objects.left.residueField u))) :
    IsStronglySplitAt Gr.groupoid ((eqToHom Gr.objects_eq.symm).left.base y) := by
  obtain ⟨Q⟩ := hsplit
  have hfix : ∀ w : Space.points C S hS U'.obj,
      pointsMap C S hS U'.obj
        (eqToHom (GroupoidInAlgebraicSpaces.restrict
          (G.realization C hS hU hR hP) g).objects_eq.symm).hom w = w :=
    fun w => congrFun (pointsMap_id C S hS U'.obj) w
  obtain ⟨Q'⟩ := GroupoidInAlgebraicSpaces.nonempty_strongSplitting_of_eq
    (derealizeSpaceIso C hS hY e)
    (GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP) g) Q
    (realizationMap G C hS hU hR hP hY q)
    (derealizeSpaceIso_hom_comp G C hS hU hR hP hY q e g he)
    (GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP)
      (realizationMap G C hS hU hR hP hY q))
    (derealizedObjectPoint G C hS hU hR hP hY q
      (GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP)
        (realizationMap G C hS hU hR hP hY q)) Gr
      ((eqToHom Gr.objects_eq.symm).left.base y))
    ((pointsMap_derealizedObjectPoint_eq G C hS hU hR hP hY q u hK e v g _ _ Gr y hy).trans
      (hfix _))
  exact isStronglySplitAt_of_contains_arrows G C hS hU hR hP hY q hA hB hRA _
    Q'.toOpenFiniteSubgroupoid hCP Gr _ Q'.contains_arrows

/-! ### The output of Stacks 04RX at the level of schemes -/

/-- The morphism to the ambient object scheme of a realization of a restriction takes the point
carried by a point `y` of the scheme being restricted to, to the image of `y`, and has
isomorphic residue field map there whenever the restricting morphism does at `y`. -/
theorem isIso_residueFieldMap_restriction_mapObjects
    (Gr : AlgebraicGeometry.GroupoidScheme.Restriction G q) (y : Y.left)
    (hyu : q.left.base y = u) (hyiso : IsIso (q.left.residueFieldMap y)) :
    Gr.hom.mapObjects.left.base ((eqToHom Gr.objects_eq.symm).left.base y) = u ∧
      IsIso (Gr.hom.mapObjects.left.residueFieldMap
        ((eqToHom Gr.objects_eq.symm).left.base y)) := by
  have hiso : IsIso (eqToHom Gr.objects_eq).left :=
    inferInstanceAs (IsIso ((Over.forget S).map (eqToHom Gr.objects_eq)))
  have hbase : (eqToHom Gr.objects_eq).left.base
      ((eqToHom Gr.objects_eq.symm).left.base y) = y :=
    over_eqToHom_apply_symm Gr.objects_eq y
  refine ⟨?_, ?_⟩
  · rw [Gr.mapObjects_eq, Over.comp_left, Scheme.Hom.comp_apply, hbase]
    exact hyu
  · rw [Gr.mapObjects_eq, Over.comp_left, Scheme.residueFieldMap_comp]
    have h1 : IsIso (q.left.residueFieldMap ((eqToHom Gr.objects_eq).left.base
        ((eqToHom Gr.objects_eq.symm).left.base y))) := by
      rw [hbase]
      exact hyiso
    have h2 : IsIso ((eqToHom Gr.objects_eq).left.residueFieldMap
      ((eqToHom Gr.objects_eq.symm).left.base y)) := inferInstance
    exact IsIso.comp_isIso' h1 h2

/-- **The output of Stacks 04RX, at the level of schemes.**  In the strong splitting situation of
Stacks 04RL, with the source flat and locally of finite presentation, there are a scheme `Y` over
`S`, a separated étale morphism `q : Y ⟶ U`, and a point `y` of `Y` above `u` with
`κ(u) = κ(y)`, such that every groupoid scheme realizing the restriction `R|_Y` is strongly split
over the point of its object scheme carried by `y`.

The neighbourhood, its étaleness and its separatedness are the de-realization, by
`Stacks.Groupoids.GroupoidScheme.exists_etale_scheme_of_isRepresentable` and
`Stacks.Groupoids.GroupoidScheme.isSeparated_derealize`, of the algebraic space produced by
`Stacks.Groupoids.GroupoidScheme.nonempty_etaleStrongSplitting`; the point and its residue field
are `Stacks.Groupoids.GroupoidScheme.isIso_residueFieldMap_derealizeResiduePoint`, and the
splitting is `Stacks.Groupoids.GroupoidScheme.isStronglySplitAt_of_derealize`.  The site
containments for the fibre products of the restriction follow from those for `U`, `R` and `Y` by
`AlgebraicGeometry.BigFppfSite.contains_pullback_left`. -/
theorem exists_etale_separated_scheme_isStronglySplitAt
    (D : AlgebraicGeometry.Space.StrongSplittingSituation.{u})
    (C : BigFppfSite.{u}) (hS : C.Contains D.S)
    (hU : C.Contains D.groupoid.objects.left) (hR : C.Contains D.groupoid.arrows.left)
    (hP : C.Contains (pullback D.groupoid.source D.groupoid.target).left)
    (hK : C.Contains (Spec (D.groupoid.objects.left.residueField D.u)))
    (hflat : AlgebraicGeometry.Flat D.groupoid.source.left)
    (hfp : AlgebraicGeometry.LocallyOfFinitePresentation D.groupoid.source.left) :
    ∃ (Y : Over D.S) (q : Y ⟶ D.groupoid.objects) (y : Y.left),
      AlgebraicGeometry.IsSeparated q.left ∧ AlgebraicGeometry.Etale q.left ∧
      q.left.base y = D.u ∧ IsIso (q.left.residueFieldMap y) ∧
      ∀ Gr : AlgebraicGeometry.GroupoidScheme.Restriction D.groupoid q,
        IsStronglySplitAt Gr.groupoid ((eqToHom Gr.objects_eq.symm).left.base y) := by
  obtain ⟨U', g, hrep, hetale, hsep, v, hv, hsplit⟩ :=
    nonempty_etaleStrongSplitting D C hS hU hR hP hK hflat hfp
  obtain ⟨Y, hY, q, e, hqet, he⟩ :=
    exists_etale_scheme_of_isRepresentable D.groupoid C hS hU hR hP U' hrep g hetale
  have hA : C.Contains (pullback q D.groupoid.target).left :=
    C.contains_pullback_left q D.groupoid.target hY hR
  have hB : C.Contains (pullback D.groupoid.source q).left :=
    C.contains_pullback_left D.groupoid.source q hR hY
  have hRA : C.Contains (AlgebraicGeometry.restrictionArrows D.groupoid q).left :=
    C.contains_pullback_left (pullback.snd q D.groupoid.target)
      (pullback.fst D.groupoid.source q) hA hB
  have hCP : C.Contains (restrictionComposablePairs D.groupoid q).left :=
    C.contains_pullback_left (AlgebraicGeometry.restrictionSource D.groupoid q)
      (AlgebraicGeometry.restrictionTarget D.groupoid q) hRA hRA
  obtain ⟨hyu, hyiso⟩ := isIso_residueFieldMap_derealizeResiduePoint D.groupoid C hS hU hY q
    e g.hom he D.u hK v hv
  exact ⟨Y, q, _, isSeparated_derealize D.groupoid C hS hU hY q e g.hom he hsep, hqet,
    hyu, hyiso, fun Gr => isStronglySplitAt_of_derealize D.groupoid C hS hU hR hP hY q D.u hK
      e v hA hB hRA hCP g he hsplit Gr _ rfl⟩

end Stacks.Groupoids.GroupoidScheme

end

end
