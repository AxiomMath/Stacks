module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedProper
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed

/-!
# Points of a universe lift

Let `S` be a scheme contained in a big fppf site `B`. A presheaf `F` on the big fppf site of
`S` with values in `Type u`, the universe of the schemes, has a point space
`AlgebraicGeometry.Space.points` carrying `AlgebraicGeometry.Space.pointTopology`, and its
universe lift `F ⋙ CategoryTheory.uliftFunctor.{w}` has a point space
`AlgebraicGeometry.Space.pointsULift` carrying `AlgebraicGeometry.Space.pointTopologyULift`.
This file identifies the two, and uses the identification to carry closedness and universal
closedness of a morphism of presheaves of `Type u` to its universe lift.

## Main definitions

* `AlgebraicGeometry.Space.fieldValuedPointULiftEquiv`: a field-valued point of the universe
  lift of `F` is a field-valued point of `F`.
* `AlgebraicGeometry.Space.pointsULiftEquiv` and
  `AlgebraicGeometry.Space.pointsHomeomorphPointsULift`: the induced bijection and
  homeomorphism of point spaces.

## Main results

* `AlgebraicGeometry.Space.pointsMapULift_whiskerRight_pointsULiftEquiv`: the identification
  is natural in `F`.
* `AlgebraicGeometry.Space.isClosedMorphismULift_whiskerRight_iff`: the universe lift of a
  morphism of presheaves of `Type u` is closed exactly when the morphism is closed.
* `AlgebraicGeometry.Space.universallyClosedULift_whiskerRight_of_universallyClosed`: the
  universe lift of a universally closed morphism of presheaves of `Type u` is universally
  closed.

## Implementation notes

A field-valued point of a presheaf is a field of `Type u` whose spectrum lies in the site, a
structure map to `S`, and a section of the presheaf over the resulting object of the site.
Only the section changes when the value universe grows, and it changes by a universe lift, so
the two kinds of field-valued point differ by `ULift.up` on one field; having a common
field-valued extension is the same condition on either side because `ULift.up` is injective.
That gives the bijection of point spaces, and it is a homeomorphism because the test objects
of the two topologies also correspond: a morphism
`CategoryTheory.uliftYoneda.{w}.obj U ⟶ F ⋙ CategoryTheory.uliftFunctor.{w}` is the universe
lift of a morphism `CategoryTheory.yoneda.obj U ⟶ F`, the lifting functor being fully
faithful, and the scheme point underlying a field-valued point of a universe-lifted
represented presheaf is read off the `ULift.down` of its section.

Universal closedness quantifies over all algebraic spaces mapping to the target, so for the
universe lift the test objects are the algebraic spaces with values in `Type (max w u)`;
these are universe lifts up to isomorphism by
`AlgebraicGeometry.Space.exists_uliftFunctor_iso_of_isAlgebraicSpaceULift`, which reduces the
condition to closedness of the universe lift of a base change in the value universe of the
site.

## References

* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03HI](https://stacks.math.columbia.edu/tag/03HI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Field-valued points of a universe lift -/

section FieldValuedPoints

variable (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- A field-valued point of the universe lift of a presheaf of `Type u` is a field-valued
point of the presheaf: the field of definition, its containment in the site and the structure
map to the base are unchanged, and the section is a universe lift. -/
def fieldValuedPointULiftEquiv :
    FieldValuedPoint B S hS F ≃
      FieldValuedPointULift.{w} B S hS (F ⋙ uliftFunctor.{w}) where
  toFun p :=
    { carrier := p.carrier, field := p.field, contained := p.contained, toBase := p.toBase
      value := ULift.up p.value }
  invFun p :=
    { carrier := p.carrier, field := p.field, contained := p.contained, toBase := p.toBase
      value := p.value.down }
  left_inv _ := rfl
  right_inv _ := rfl

/-- Domination of field-valued points is the same condition on a presheaf of `Type u` and on
its universe lift: the morphism of field spectra witnessing it is the same, and the equality
of sections it asks for is the equality of their universe lifts. -/
theorem dominates_fieldValuedPointULiftEquiv_iff (p q : FieldValuedPoint B S hS F) :
    FieldValuedPointULift.Dominates B S hS (F ⋙ uliftFunctor.{w})
        (fieldValuedPointULiftEquiv.{w} B S hS F p)
        (fieldValuedPointULiftEquiv.{w} B S hS F q) ↔
      FieldValuedPoint.Dominates B S hS F p q :=
  ⟨fun ⟨f, hf⟩ ↦ ⟨f, congrArg ULift.down hf⟩, fun ⟨f, hf⟩ ↦ ⟨f, congrArg ULift.up hf⟩⟩

/-- Having a common field-valued extension is the same condition on a presheaf of `Type u`
and on its universe lift, the field-valued points of the two corresponding. -/
theorem hasCommonExtension_fieldValuedPointULiftEquiv_iff (p q : FieldValuedPoint B S hS F) :
    FieldValuedPoint.HasCommonExtension B S hS F p q ↔
      FieldValuedPointULift.HasCommonExtension B S hS (F ⋙ uliftFunctor.{w})
        (fieldValuedPointULiftEquiv.{w} B S hS F p)
        (fieldValuedPointULiftEquiv.{w} B S hS F q) := by
  constructor
  · rintro ⟨r, hp, hq⟩
    exact ⟨fieldValuedPointULiftEquiv.{w} B S hS F r,
      (dominates_fieldValuedPointULiftEquiv_iff.{w} B S hS F r p).mpr hp,
      (dominates_fieldValuedPointULiftEquiv_iff.{w} B S hS F r q).mpr hq⟩
  · rintro ⟨r, hp, hq⟩
    exact ⟨(fieldValuedPointULiftEquiv.{w} B S hS F).symm r,
      (dominates_fieldValuedPointULiftEquiv_iff.{w} B S hS F _ p).mp hp,
      (dominates_fieldValuedPointULiftEquiv_iff.{w} B S hS F _ q).mp hq⟩

/-- The points of the universe lift of a presheaf of `Type u` are the points of the
presheaf. -/
def pointsULiftEquiv :
    points B S hS F ≃ pointsULift.{w} B S hS (F ⋙ uliftFunctor.{w}) :=
  Quot.congr (fieldValuedPointULiftEquiv.{w} B S hS F)
    (hasCommonExtension_fieldValuedPointULiftEquiv_iff.{w} B S hS F)

/-- The equivalence `pointsULiftEquiv` sends the class of a field-valued point to the class of
the corresponding field-valued point of the universe lift. -/
@[simp]
theorem pointsULiftEquiv_class (p : FieldValuedPoint B S hS F) :
    pointsULiftEquiv.{w} B S hS F (p.class B S hS F) =
      (fieldValuedPointULiftEquiv.{w} B S hS F p).class B S hS
        (F ⋙ uliftFunctor.{w}) := rfl

end FieldValuedPoints

/-- The identification of the points of a presheaf of `Type u` with those of its universe
lift is natural in the presheaf: either way round, a morphism acts on the section of a
field-valued point. -/
theorem pointsMapULift_whiskerRight_pointsULiftEquiv
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G) :
    pointsMapULift B S hS (F ⋙ uliftFunctor.{w})
          (Functor.whiskerRight a uliftFunctor.{w}) ∘ pointsULiftEquiv.{w} B S hS F =
      pointsULiftEquiv.{w} B S hS G ∘ pointsMap B S hS F a := by
  funext x
  induction x using Quot.ind
  rfl

/-! ### The point topologies agree -/

section Topology

/-- The scheme point underlying a field-valued point of a universe-lifted represented
presheaf is the scheme point underlying the corresponding field-valued point of the
represented presheaf. -/
theorem schemePointULift_fieldValuedPointULiftEquiv (U : BigFppfOver B S hS)
    (p : FieldValuedPoint B S hS (yoneda.obj U)) :
    schemePointULift.{w} B S hS U
        (fieldValuedPointULiftEquiv.{w} B S hS (yoneda.obj U) p) =
      schemePoint B S hS U p := rfl

/-- The scheme-valued points of a universe-lifted presheaf test the same sets of points as
the scheme-valued points of the presheaf: the preimage of a set of points of the universe
lift along the universe lift of a scheme-valued point is cut out by an open subset of the
representing scheme exactly when its preimage along that scheme-valued point is. -/
theorem isSchemeOpenULift_pointsMapULift_iff
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (U : BigFppfOver B S hS)
    (a : yoneda.obj U ⟶ F) (W : Set (pointsULift.{w} B S hS (F ⋙ uliftFunctor.{w}))) :
    IsSchemeOpenULift.{w} B S hS U
        (pointsMapULift B S hS ((uliftYoneda.{w}).obj U)
          (Functor.whiskerRight a uliftFunctor.{w}) ⁻¹' W) ↔
      IsSchemeOpen B S hS U
        (pointsMap B S hS (yoneda.obj U) a ⁻¹' (pointsULiftEquiv.{w} B S hS F ⁻¹' W)) := by
  constructor
  · rintro ⟨V, hV, hmem⟩
    exact ⟨V, hV, fun p ↦ hmem (fieldValuedPointULiftEquiv.{w} B S hS (yoneda.obj U) p)⟩
  · rintro ⟨V, hV, hmem⟩
    exact ⟨V, hV, fun p ↦
      hmem ((fieldValuedPointULiftEquiv.{w} B S hS (yoneda.obj U)).symm p)⟩

/-- A set of points of the universe lift of a presheaf of `Type u` is open exactly when the
corresponding set of points of the presheaf is: the test objects of the two topologies
correspond, the lifting functor being fully faithful. -/
theorem isOpen_pointTopologyULift_comp_uliftFunctor_iff
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (W : Set (pointsULift.{w} B S hS (F ⋙ uliftFunctor.{w}))) :
    @IsOpen _ (pointTopologyULift.{w} B S hS (F ⋙ uliftFunctor.{w})) W ↔
      @IsOpen _ (pointTopology B S hS F) (pointsULiftEquiv.{w} B S hS F ⁻¹' W) := by
  let H := (Functor.whiskeringRight (BigFppfOver B S hS)ᵒᵖ (Type u)
    (Type (max w u))).obj uliftFunctor.{w}
  rw [isOpen_pointTopologyULift_iff, isOpen_pointTopology_iff]
  constructor
  · intro h U a
    exact (isSchemeOpenULift_pointsMapULift_iff.{w} B S hS U a W).mp
      (h U (Functor.whiskerRight a uliftFunctor.{w}))
  · intro h U α
    obtain ⟨a, rfl⟩ := H.map_surjective α
    exact (isSchemeOpenULift_pointsMapULift_iff.{w} B S hS U a W).mpr (h U a)

attribute [local instance] pointTopology pointTopologyULift

/-- The point space of the universe lift of a presheaf of `Type u` is the point space of the
presheaf. -/
def pointsHomeomorphPointsULift (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    points B S hS F ≃ₜ pointsULift.{w} B S hS (F ⋙ uliftFunctor.{w}) where
  toEquiv := pointsULiftEquiv.{w} B S hS F
  continuous_toFun := continuous_def.mpr fun W hW ↦
    (isOpen_pointTopologyULift_comp_uliftFunctor_iff.{w} B S hS W).mp hW
  continuous_invFun := by
    rw [continuous_def]
    intro V hV
    rw [show (pointsULiftEquiv.{w} B S hS F).invFun =
      ⇑(pointsULiftEquiv.{w} B S hS F).symm from rfl]
    refine (isOpen_pointTopologyULift_comp_uliftFunctor_iff.{w} B S hS _).mpr ?_
    rwa [← Set.preimage_comp, Equiv.symm_comp_self, Set.preimage_id]

/-! ### Closedness and universal closedness of a universe lift -/

/-- The universe lift of a morphism of presheaves of `Type u` is closed exactly when the
morphism is closed: the two maps on points agree under the homeomorphism of point spaces. -/
theorem isClosedMorphismULift_whiskerRight_iff
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (q : F ⟶ G) :
    IsClosedMorphismULift.{w} B S hS (Functor.whiskerRight q uliftFunctor.{w}) ↔
      IsClosedMorphism B S hS q := by
  have hnat (x : points B S hS F) :
      pointsMapULift B S hS (F ⋙ uliftFunctor.{w})
          (Functor.whiskerRight q uliftFunctor.{w}) (pointsULiftEquiv.{w} B S hS F x) =
        pointsULiftEquiv.{w} B S hS G (pointsMap B S hS F q x) :=
    congrFun (pointsMapULift_whiskerRight_pointsULiftEquiv.{w} B S hS q) x
  constructor
  · intro h
    have h' : IsClosedMap (pointsMapULift B S hS (F ⋙ uliftFunctor.{w})
      (Functor.whiskerRight q uliftFunctor.{w})) := h
    have heq : pointsMap B S hS F q =
        (pointsULiftEquiv.{w} B S hS G).symm ∘
          (pointsMapULift B S hS (F ⋙ uliftFunctor.{w})
            (Functor.whiskerRight q uliftFunctor.{w}) ∘
              pointsULiftEquiv.{w} B S hS F) := by
      funext x
      rw [Function.comp_apply, Function.comp_apply, hnat x, Equiv.symm_apply_apply]
    change IsClosedMap (pointsMap B S hS F q)
    rw [heq]
    exact (pointsHomeomorphPointsULift.{w} B S hS G).symm.isClosedMap.comp
      (h'.comp (pointsHomeomorphPointsULift.{w} B S hS F).isClosedMap)
  · intro h
    have h' : IsClosedMap (pointsMap B S hS F q) := h
    have heq : pointsMapULift B S hS (F ⋙ uliftFunctor.{w})
          (Functor.whiskerRight q uliftFunctor.{w}) =
        (pointsULiftEquiv.{w} B S hS G ∘ pointsMap B S hS F q) ∘
          (pointsULiftEquiv.{w} B S hS F).symm := by
      funext y
      rw [Function.comp_apply, Function.comp_apply,
        ← hnat ((pointsULiftEquiv.{w} B S hS F).symm y), Equiv.apply_symm_apply]
    change IsClosedMap (pointsMapULift B S hS (F ⋙ uliftFunctor.{w})
      (Functor.whiskerRight q uliftFunctor.{w}))
    rw [heq]
    exact ((pointsHomeomorphPointsULift.{w} B S hS G).isClosedMap.comp h').comp
      (pointsHomeomorphPointsULift.{w} B S hS F).symm.isClosedMap

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks of universe-lifted presheaves on the big fppf site
/-- The universe lift of a universally closed morphism of presheaves of `Type u` is
universally closed: an algebraic space over `S` with values in `Type (max w u)` is isomorphic
to the universe lift of a presheaf of `Type u`, so a base change of the lift along a morphism
from it is isomorphic to the universe lift of a base change of the morphism, whose map on
points is closed by hypothesis. -/
theorem universallyClosedULift_whiskerRight_of_universallyClosed
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (q : F ⟶ G)
    (hq : UniversallyClosed B S hS q) :
    UniversallyClosedULift.{w} B S hS (Functor.whiskerRight q uliftFunctor.{w}) := by
  let H := (Functor.whiskeringRight (BigFppfOver B S hS)ᵒᵖ (Type u)
    (Type (max w u))).obj uliftFunctor.{w}
  intro Z hZalg g
  obtain ⟨Z', ⟨e⟩⟩ := exists_uliftFunctor_iso_of_isAlgebraicSpaceULift B S hS hZalg
  obtain ⟨g', hmap⟩ :
      ∃ g' : Z' ⟶ G, Functor.whiskerRight g' uliftFunctor.{w} = e.hom ≫ g :=
    H.map_surjective (e.hom ≫ g)
  have hZ'alg : IsAlgebraicSpace B S hS Z' :=
    (isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS Z').mp
      (isAlgebraicSpaceULift_of_iso B S hS e.symm hZalg)
  have hclosed : IsClosedMap (pointsMapULift B S hS
      (pullback g' q ⋙ uliftFunctor.{w})
      (Functor.whiskerRight (pullback.fst g' q) uliftFunctor.{w})) :=
    (isClosedMorphismULift_whiskerRight_iff.{w} B S hS (pullback.fst g' q)).mpr
      (hq Z' hZ'alg g')
  have hcomp : IsClosedMap (pointsMapULift B S hS
      (pullback g' q ⋙ uliftFunctor.{w})
      (Functor.whiskerRight (pullback.fst g' q) uliftFunctor.{w} ≫ e.hom)) := by
    rw [pointsMapULift_comp]
    exact (isClosedMap_pointsMapULift_of_isIso B S hS e.hom).comp hclosed
  have hR : IsPullback e.hom (Functor.whiskerRight g' uliftFunctor.{w}) g
      (𝟙 (G ⋙ uliftFunctor.{w})) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, hmap]⟩
  have hpb : IsPullback
      (Functor.whiskerRight (pullback.fst g' q) uliftFunctor.{w} ≫ e.hom)
      (Functor.whiskerRight (pullback.snd g' q) uliftFunctor.{w}) g
      (Functor.whiskerRight q uliftFunctor.{w}) := by
    simpa using (isPullback_whiskerRight.{w} B S hS
      (IsPullback.of_hasPullback g' q)).paste_horiz hR
  have heq : hpb.isoPullback.inv ≫
      (Functor.whiskerRight (pullback.fst g' q) uliftFunctor.{w} ≫ e.hom) =
      pullback.fst g (Functor.whiskerRight q uliftFunctor.{w}) :=
    (Iso.inv_comp_eq hpb.isoPullback).mpr hpb.isoPullback_hom_fst.symm
  exact isClosedMap_pointsMapULift_of_comp_isIso B S hS hpb.isoPullback.inv heq hcomp

end Topology

end AlgebraicGeometry.Space

end
