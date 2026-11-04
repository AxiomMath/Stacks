module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.Translation
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.UnibranchArrows
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentModules

/-!
# Geometric unibranchness of an arrow space at the identity arrow

Let `(U, R, s, t, c)` be a groupoid in algebraic spaces and let `r : U ⟶ R` be a family of
arrows whose source and target are isomorphisms of the object space.  Left translation by `r`
is an automorphism of `R` carrying the identity arrow at the source of `r` to `r` itself (Tag
06E3), so `R` is geometrically unibranch at the point of `r` as soon as it is geometrically
unibranch at the point of that identity arrow.

When the object space is the spectrum of a field `k'` of the site, the object space has a single
point, so the identity arrow in question is the identity arrow at the tautological point and the
hypothesis is a single condition.  Applied to the restriction of a groupoid along an
algebraically closed field extension this is the second reduction in the proof of [Stacks
Project, Tag 06E4]: it weakens the hypothesis of
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.isGeometricallyUnibranch_arrows_of_restrictions`
from all arrows with invertible source and target to the identity alone.

## Main definitions

* `AlgebraicGeometry.Space.FieldValuedPoint.class_eq_class_of_dominates` records that a
  field-valued point and a restriction of it along a morphism of site objects have the same
  class.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.extensionRestriction`: the restriction of a
  groupoid over a field along an extension of that field, as a groupoid in algebraic spaces.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.extensionTautologicalPoint`: the field-valued
  point of its object space given by the identity section.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.restrictionArrowFamily`: the family of arrows of
  the restriction determined by a single arrow over the extension field.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.restrictionIdentityArrow` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.restrictionIdentityArrowPoint`: the identity
  arrow of the restriction and the point of the restricted arrow space it determines.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.identityArrow_comp_translationByArrow`: Tag 06E3
  as an equation of morphisms — translation by `r`, precomposed with the identity arrow at the
  source of `r`, is `r`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isGeometricallyUnibranchAt_of_identityArrow`: the
  transport of geometric unibranchness from the identity arrow at the source of `r` to `r`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isGeometricallyUnibranchAt_restriction_of_identity`:
  the same for the restriction of a groupoid over a field along a field extension, where the
  identity arrow is the one at the tautological point.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isGeometricallyUnibranch_arrows_of_identityArrows`:
  the first two reductions of Tag 06E4 combined — geometric unibranchness of the arrow space of
  the groupoid follows from geometric unibranchness of the arrow space of each restriction along
  an algebraically closed extension at the point of its identity arrow alone.

## Implementation notes

The arrow `r` of the source is an arrow *over the extension field*, i.e. a section of the
restricted arrow space over the spectrum of that field, which is the form in which Tag 06E2
produces it.  The object space of the restriction is the algebraic space represented by that
spectrum, so Yoneda turns the section into the family of arrows
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.restrictionArrowFamily` that
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.translationByArrow` consumes; the two invertibility
hypotheses transfer because the Yoneda image of an isomorphism is one.

The restricted groupoid is the one produced by
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.restrict`, whose comparison equalities are `rfl`:
its object space *is* the algebraic space of the extension field spectrum and its arrow space
*is* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.restrictionArrows`, so no transport along
`eqToHom` is needed anywhere below.

That the identity arrow may be taken at the tautological point, rather than at the source of
`r`, is the statement that the two points of the object space agree.  It holds because the
section of any field-valued point of the algebraic space of the spectrum of a field is itself a
morphism of site objects pulling the identity section back to that section, so the two points
have the same class.

## References

* [Stacks Project, Tag 06E3](https://stacks.math.columbia.edu/tag/06E3)
* [Stacks Project, Tag 06E4](https://stacks.math.columbia.edu/tag/06E4)
* [Stacks Project, Tag 06K5](https://stacks.math.columbia.edu/tag/06K5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)

/-- A field-valued point whose section is the restriction of the section of another along a
morphism of site objects has the same class as that other: the first point is already a common
extension of the two. -/
theorem FieldValuedPoint.class_eq_class_of_dominates
    {F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (p q : FieldValuedPoint C S hS F)
    (h : FieldValuedPoint.Dominates C S hS F p q) :
    p.class C S hS F = q.class C S hS F :=
  FieldValuedPoint.class_eq_class_of_hasCommonExtension C S hS F
    ⟨p, FieldValuedPoint.dominates_refl C S hS F p, h⟩

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

section Translation

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- **Stacks 06E3, as an equation of morphisms.**  Left translation by a family `r` of arrows
whose source is an isomorphism, precomposed with the identity arrow at the source of `r`, is `r`
itself. -/
@[stacks 06E3 "image of the identity, as an equation of morphisms"]
theorem identityArrow_comp_translationByArrow (H : GroupoidInAlgebraicSpaces C S hS B)
    (r : H.objects ⟶ H.arrows) [IsIso (r ≫ H.source)] :
    ((r ≫ H.source) ≫ identityArrow H) ≫ translationByArrow H r = r := by
  apply ObjectProperty.hom_ext
  ext T x
  show (translationByArrow H r).hom.app T
      ((identityArrow H).hom.app T ((r ≫ H.source).hom.app T x)) = r.hom.app T x
  rw [identityArrow_hom_app]
  exact translationByArrow_identity H r T x

/-- Left translation by `r` carries the point of the identity arrow at the source of `r` to the
point of `r`. -/
theorem pointsMap_translationByArrow_identityArrow (H : GroupoidInAlgebraicSpaces C S hS B)
    (r : H.objects ⟶ H.arrows) [IsIso (r ≫ H.source)]
    (x : Space.points C S hS H.objects.obj) :
    Space.pointsMap C S hS H.arrows.obj (translationByArrow H r).hom
        (Space.pointsMap C S hS H.objects.obj
          ((r ≫ H.source) ≫ identityArrow H).hom x) =
      Space.pointsMap C S hS H.objects.obj r.hom x := by
  have hhom : ((r ≫ H.source) ≫ identityArrow H).hom ≫ (translationByArrow H r).hom =
      r.hom :=
    congrArg (fun f : H.objects ⟶ H.arrows => f.hom)
      (identityArrow_comp_translationByArrow H r)
  rw [← hhom, Space.pointsMap_comp]
  rfl

/-- If the arrow space of a groupoid in algebraic spaces is geometrically unibranch at the point
of the identity arrow at the source of a family `r` of arrows whose source and target are both
isomorphisms, then it is geometrically unibranch at the point of `r`: left translation by `r` is
an automorphism of the arrow space taking the one point to the other. -/
theorem isGeometricallyUnibranchAt_of_identityArrow (H : GroupoidInAlgebraicSpaces C S hS B)
    (r : H.objects ⟶ H.arrows) [IsIso (r ≫ H.source)] [IsIso (r ≫ H.target)]
    (x : Space.points C S hS H.objects.obj)
    (hid : Space.IsGeometricallyUnibranchAt C S hS H.arrows.obj
      (Space.pointsMap C S hS H.objects.obj
        ((r ≫ H.source) ≫ identityArrow H).hom x)) :
    Space.IsGeometricallyUnibranchAt C S hS H.arrows.obj
      (Space.pointsMap C S hS H.objects.obj r.hom x) := by
  have : IsIso (translationByArrow H r).hom :=
    (ObjectProperty.isIso_hom_iff _).mpr (translationByArrow_isIso H r)
  rw [← pointsMap_translationByArrow_identityArrow H r x]
  exact Space.isGeometricallyUnibranchAt_of_isIso C S hS H.arrows.property H.arrows.property
    (translationByArrow H r).hom _ hid

end Translation

section Restriction

variable {S : Scheme.{u}} (C : BigFppfSite.{u}) (hS : C.Contains S)
  {k : Type u} [Field k] (hk : C.Contains (Spec (.of k)))
  (structureMap : Spec (.of k) ⟶ S)
  {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B)
  (hU : G.objects = Space.fieldSpace C hS hk structureMap)

/-- The restriction of `G` along an extension field, as a groupoid in algebraic spaces: its
object space is the algebraic space of the spectrum of the extension field and its arrow space
is `AlgebraicGeometry.GroupoidInAlgebraicSpaces.restrictionArrows`. -/
noncomputable abbrev extensionRestriction {k' : Type u} [Field k']
    (hk' : C.Contains (Spec (.of k'))) (i : k →+* k') :
    GroupoidInAlgebraicSpaces C S hS B :=
  (restrict G (Space.restrictionObjectMap C hS hk hk' structureMap i G hU)).groupoid

/-- The tautological field-valued point of the object space of the restriction of `G` along an
extension field: the identity section of the spectrum of that field. -/
noncomputable def extensionTautologicalPoint {k' : Type u} [Field k']
    (hk' : C.Contains (Spec (.of k'))) (i : k →+* k') :
    Space.FieldValuedPoint C S hS
      (extensionRestriction C hS hk structureMap G hU hk' i).objects.obj where
  carrier := k'
  contained := hk'
  toBase := Scheme.Spec.map (CommRingCat.ofHom i).op ≫ structureMap
  value := 𝟙 (extensionSiteObject C hS structureMap hk' i)

/-- The family of arrows of the restriction of `G` along an extension field determined by a
single arrow over that field: the morphism out of the object space which Yoneda associates with
the section. -/
noncomputable def restrictionArrowFamily {k' : Type u} [Field k']
    (hk' : C.Contains (Spec (.of k'))) (i : k →+* k')
    (r : (restrictionArrows G
      (Space.restrictionObjectMap C hS hk hk' structureMap i G hU)).obj.obj
        (Opposite.op (extensionSiteObject C hS structureMap hk' i))) :
    (extensionRestriction C hS hk structureMap G hU hk' i).objects ⟶
      (extensionRestriction C hS hk structureMap G hU hk' i).arrows :=
  ObjectProperty.homMk (yonedaEquiv.symm r)

/-- The family of arrows determined by `r` takes the identity section to `r`. -/
theorem restrictionArrowFamily_hom_app_id {k' : Type u} [Field k']
    (hk' : C.Contains (Spec (.of k'))) (i : k →+* k')
    (r : (restrictionArrows G
      (Space.restrictionObjectMap C hS hk hk' structureMap i G hU)).obj.obj
        (Opposite.op (extensionSiteObject C hS structureMap hk' i))) :
    (restrictionArrowFamily C hS hk structureMap G hU hk' i r).hom.app
        (Opposite.op (extensionSiteObject C hS structureMap hk' i))
        (𝟙 (extensionSiteObject C hS structureMap hk' i)) = r :=
  (yonedaEquiv_apply (yonedaEquiv.symm r)).symm.trans (Equiv.apply_symm_apply _ _)

/-- Precomposing a morphism into a representable presheaf with the section determined by `x` is
the Yoneda image of its value at `x`. -/
private theorem yonedaEquiv_symm_comp_eq_yoneda_map {E : Type*} [Category E]
    {F : Eᵒᵖ ⥤ Type _} {X Y : E} (f : F ⟶ yoneda.obj Y) (x : F.obj (Opposite.op X)) :
    yonedaEquiv.symm x ≫ f = yoneda.map (f.app (Opposite.op X) x : X ⟶ Y) := by
  rw [yonedaEquiv_symm_naturality_right]
  exact yonedaEquiv.symm_apply_eq.mpr (yonedaEquiv_yoneda_map _).symm

/-- The composite of the family of arrows determined by `r` with the source of the restriction
is the Yoneda image of the source of `r`. -/
theorem restrictionArrowFamily_hom_comp_source {k' : Type u} [Field k']
    (hk' : C.Contains (Spec (.of k'))) (i : k →+* k')
    (r : (restrictionArrows G
      (Space.restrictionObjectMap C hS hk hk' structureMap i G hU)).obj.obj
        (Opposite.op (extensionSiteObject C hS structureMap hk' i))) :
    (restrictionArrowFamily C hS hk structureMap G hU hk' i r ≫
        (extensionRestriction C hS hk structureMap G hU hk' i).source).hom =
      yoneda.map ((restrictionSource G
          (Space.restrictionObjectMap C hS hk hk' structureMap i G hU)).hom.app
        (Opposite.op (extensionSiteObject C hS structureMap hk' i)) r) := by
  exact yonedaEquiv_symm_comp_eq_yoneda_map _ r

/-- The composite of the family of arrows determined by `r` with the target of the restriction
is the Yoneda image of the target of `r`. -/
theorem restrictionArrowFamily_hom_comp_target {k' : Type u} [Field k']
    (hk' : C.Contains (Spec (.of k'))) (i : k →+* k')
    (r : (restrictionArrows G
      (Space.restrictionObjectMap C hS hk hk' structureMap i G hU)).obj.obj
        (Opposite.op (extensionSiteObject C hS structureMap hk' i))) :
    (restrictionArrowFamily C hS hk structureMap G hU hk' i r ≫
        (extensionRestriction C hS hk structureMap G hU hk' i).target).hom =
      yoneda.map ((restrictionTarget G
          (Space.restrictionObjectMap C hS hk hk' structureMap i G hU)).hom.app
        (Opposite.op (extensionSiteObject C hS structureMap hk' i)) r) := by
  exact yonedaEquiv_symm_comp_eq_yoneda_map _ r

/-- The identity arrow of the restriction of `G` along an extension field, read as a section of
the restricted arrow space over the spectrum of that field. -/
noncomputable def restrictionIdentityArrow {k' : Type u} [Field k']
    (hk' : C.Contains (Spec (.of k'))) (i : k →+* k') :
    (restrictionArrows G
      (Space.restrictionObjectMap C hS hk hk' structureMap i G hU)).obj.obj
        (Opposite.op (extensionSiteObject C hS structureMap hk' i)) :=
  (identityArrow (extensionRestriction C hS hk structureMap G hU hk' i)).hom.app
    (Opposite.op (extensionSiteObject C hS structureMap hk' i))
    (𝟙 (extensionSiteObject C hS structureMap hk' i))

/-- The point of the restricted arrow space carried by the identity arrow of the restriction. -/
noncomputable def restrictionIdentityArrowPoint {k' : Type u} [Field k']
    (hk' : C.Contains (Spec (.of k'))) (i : k →+* k') :
    Space.points C S hS (restrictionArrows G
      (Space.restrictionObjectMap C hS hk hk' structureMap i G hU)).obj :=
  restrictionArrowPoint C hS hk structureMap G hU hk' i
    (restrictionIdentityArrow C hS hk structureMap G hU hk' i)

/-- The image of the tautological point of the object space of the restriction under a family of
arrows is the point of the restricted arrow space carried by the value of that family on the
identity section. -/
theorem pointsMap_extensionTautologicalPoint {k' : Type u} [Field k']
    (hk' : C.Contains (Spec (.of k'))) (i : k →+* k')
    (f : (extensionRestriction C hS hk structureMap G hU hk' i).objects ⟶
      (extensionRestriction C hS hk structureMap G hU hk' i).arrows) :
    Space.pointsMap C S hS
        (extensionRestriction C hS hk structureMap G hU hk' i).objects.obj f.hom
        ((extensionTautologicalPoint C hS hk structureMap G hU hk' i).class C S hS
          (extensionRestriction C hS hk structureMap G hU hk' i).objects.obj) =
      restrictionArrowPoint C hS hk structureMap G hU hk' i
        (f.hom.app (Opposite.op (extensionSiteObject C hS structureMap hk' i))
          (𝟙 (extensionSiteObject C hS structureMap hk' i))) :=
  rfl

/-- An endomorphism of the object space of the restriction fixes the class of the tautological
point: the object space is the algebraic space of the spectrum of a field, which has a single
point. -/
theorem pointsMap_extensionTautologicalPoint_endo {k' : Type u} [Field k']
    (hk' : C.Contains (Spec (.of k'))) (i : k →+* k')
    (f : (extensionRestriction C hS hk structureMap G hU hk' i).objects ⟶
      (extensionRestriction C hS hk structureMap G hU hk' i).objects) :
    Space.pointsMap C S hS
        (extensionRestriction C hS hk structureMap G hU hk' i).objects.obj f.hom
        ((extensionTautologicalPoint C hS hk structureMap G hU hk' i).class C S hS
          (extensionRestriction C hS hk structureMap G hU hk' i).objects.obj) =
      (extensionTautologicalPoint C hS hk structureMap G hU hk' i).class C S hS
        (extensionRestriction C hS hk structureMap G hU hk' i).objects.obj := by
  rw [Space.pointsMap_class]
  let f' : extensionSiteObject C hS structureMap hk' i ⟶
      extensionSiteObject C hS structureMap hk' i :=
    f.hom.app (Opposite.op (extensionSiteObject C hS structureMap hk' i))
      (𝟙 (extensionSiteObject C hS structureMap hk' i))
  exact Space.FieldValuedPoint.class_eq_class_of_dominates C S hS _ _ ⟨f', Category.comp_id f'⟩

/-- **The second reduction of Stacks 06E4 (Tag 06E3).**  Let `G` be a groupoid in algebraic
spaces whose object space is the spectrum of a field `k`, and let `k'/k` be a field extension
whose spectrum lies in the site.  If the arrow space of the restriction of `G` along
`Spec k' ⟶ Spec k` is geometrically unibranch at the point of its identity arrow, then it is
geometrically unibranch at the point of every arrow over `Spec k'` whose source and target are
automorphisms of `Spec k'`. -/
theorem isGeometricallyUnibranchAt_restriction_of_identity {k' : Type u} [Field k']
    (hk' : C.Contains (Spec (.of k'))) (i : k →+* k')
    (r : (restrictionArrows G
      (Space.restrictionObjectMap C hS hk hk' structureMap i G hU)).obj.obj
        (Opposite.op (extensionSiteObject C hS structureMap hk' i)))
    (hsrc : IsIso ((restrictionSource G
        (Space.restrictionObjectMap C hS hk hk' structureMap i G hU)).hom.app
      (Opposite.op (extensionSiteObject C hS structureMap hk' i)) r))
    (htgt : IsIso ((restrictionTarget G
        (Space.restrictionObjectMap C hS hk hk' structureMap i G hU)).hom.app
      (Opposite.op (extensionSiteObject C hS structureMap hk' i)) r))
    (hid : Space.IsGeometricallyUnibranchAt C S hS
      (restrictionArrows G
        (Space.restrictionObjectMap C hS hk hk' structureMap i G hU)).obj
      (restrictionIdentityArrowPoint C hS hk structureMap G hU hk' i)) :
    Space.IsGeometricallyUnibranchAt C S hS
      (restrictionArrows G
        (Space.restrictionObjectMap C hS hk hk' structureMap i G hU)).obj
      (restrictionArrowPoint C hS hk structureMap G hU hk' i r) := by
  have hiso₁ : IsIso (restrictionArrowFamily C hS hk structureMap G hU hk' i r ≫
      (extensionRestriction C hS hk structureMap G hU hk' i).source) :=
    (ObjectProperty.isIso_hom_iff _).mp
      (by
        rw [restrictionArrowFamily_hom_comp_source]
        exact (yoneda.mapIso (@asIso _ _ _ _ _ hsrc)).isIso_hom)
  have hiso₂ : IsIso (restrictionArrowFamily C hS hk structureMap G hU hk' i r ≫
      (extensionRestriction C hS hk structureMap G hU hk' i).target) :=
    (ObjectProperty.isIso_hom_iff _).mp
      (by
        rw [restrictionArrowFamily_hom_comp_target]
        exact (yoneda.mapIso (@asIso _ _ _ _ _ htgt)).isIso_hom)
  have hsplit : ((restrictionArrowFamily C hS hk structureMap G hU hk' i r ≫
        (extensionRestriction C hS hk structureMap G hU hk' i).source) ≫
      identityArrow (extensionRestriction C hS hk structureMap G hU hk' i)).hom =
        (restrictionArrowFamily C hS hk structureMap G hU hk' i r ≫
            (extensionRestriction C hS hk structureMap G hU hk' i).source).hom ≫
          (identityArrow (extensionRestriction C hS hk structureMap G hU hk' i)).hom :=
    rfl
  have hidpt : Space.pointsMap C S hS
      (extensionRestriction C hS hk structureMap G hU hk' i).objects.obj
      ((restrictionArrowFamily C hS hk structureMap G hU hk' i r ≫
          (extensionRestriction C hS hk structureMap G hU hk' i).source) ≫
        identityArrow (extensionRestriction C hS hk structureMap G hU hk' i)).hom
      ((extensionTautologicalPoint C hS hk structureMap G hU hk' i).class C S hS
        (extensionRestriction C hS hk structureMap G hU hk' i).objects.obj) =
        restrictionIdentityArrowPoint C hS hk structureMap G hU hk' i := by
    rw [hsplit, Space.pointsMap_comp, Function.comp_apply,
      pointsMap_extensionTautologicalPoint_endo]
    exact pointsMap_extensionTautologicalPoint C hS hk structureMap G hU hk' i
      (identityArrow (extensionRestriction C hS hk structureMap G hU hk' i))
  have hmain := isGeometricallyUnibranchAt_of_identityArrow
    (extensionRestriction C hS hk structureMap G hU hk' i)
    (restrictionArrowFamily C hS hk structureMap G hU hk' i r)
    ((extensionTautologicalPoint C hS hk structureMap G hU hk' i).class C S hS
      (extensionRestriction C hS hk structureMap G hU hk' i).objects.obj)
    (by rwa [hidpt])
  rwa [pointsMap_extensionTautologicalPoint, restrictionArrowFamily_hom_app_id] at hmain

/-- **The first two reductions of Stacks 06E4.**  Let `G` be a groupoid in algebraic spaces
whose object space is the spectrum of a field `k`.  Suppose that for every algebraically closed
field extension `k'/k` whose spectrum lies in the site, the arrow space of the restriction of
`G` along `Spec k' ⟶ Spec k` is geometrically unibranch at the point of its identity arrow.
Then the arrow space of `G` is geometrically unibranch.

This combines the reduction to the restrictions
(`AlgebraicGeometry.GroupoidInAlgebraicSpaces.isGeometricallyUnibranch_arrows_of_restrictions`,
Tags 06E2, 06E1 and 06DQ) with the reduction to the identity arrow (Tag 06E3).

No `@[stacks 06E4]` attribute is claimed: the hypothesis is geometric unibranchness of the
restricted arrow space at the identity arrow, which is the local computation of the last two
paragraphs of the source proof and so is the hard part of the tag itself. -/
theorem isGeometricallyUnibranch_arrows_of_identityArrows
    (hres : ∀ (k' : Type u) (_ : Field k') (_ : IsAlgClosed k') (i : k →+* k')
      (hk' : C.Contains (Spec (.of k'))),
      Space.IsGeometricallyUnibranchAt C S hS
        (restrictionArrows G
          (Space.restrictionObjectMap C hS hk hk' structureMap i G hU)).obj
        (restrictionIdentityArrowPoint C hS hk structureMap G hU hk' i)) :
    Space.IsGeometricallyUnibranch C S hS G.arrows.obj :=
  isGeometricallyUnibranch_arrows_of_restrictions C hS hk structureMap G hU
    fun k' field' alg' i hk' r hsrc htgt =>
      isGeometricallyUnibranchAt_restriction_of_identity C hS hk structureMap G hU
        hk' i r hsrc htgt (hres k' field' alg' i hk')

end Restriction

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
