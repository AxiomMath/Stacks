module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyClosed

/-!
# Universal closedness from a family of étale charts

Universal closedness of a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` can be
tested along a single surjective étale chart of the target, and it can be tested along the
members of a Zariski covering of the target. This file records the common generalisation of
the two tests: it is enough to have *any* family `φ i : h_{V i} ⟶ Y` of étale morphisms from
representable presheaves whose images cover the points of `Y`, and to know that the base
change of `f` along each member is universally closed. Neither individual member need be
surjective, and the index type is arbitrary.

## Main results

* `AlgebraicGeometry.Space.universallyClosed_of_etale_covering_family`: if a family of étale
  morphisms to `Y` from presheaves represented by objects of the site covers the points of
  `Y`, and the base change of `f` along each member is universally closed, then `f` is
  universally closed.

## Implementation notes

The proof is the one of `AlgebraicGeometry.Space.universallyClosed_of_isZariskiCover` with
the open immersions of a Zariski covering replaced by the étale charts of the family. For a
test morphism `g : Z ⟶ Y` out of an algebraic space one base changes the whole family along
`g`: each `Z ×_Y h_{V i} ⟶ Z` is again étale, since representable étaleness is stable under
base change, hence open on points by Tag 03IR; the base changes jointly cover the points of
`Z` because the `φ i` cover the points of `Y` and the comparison map to the fibre product of
point sets is surjective (Tag 03H4); and the base change of `Z ×_Y X ⟶ Z` along the `i`-th
member is a base change of `h_{V i} ×_Y X ⟶ h_{V i}`, hence closed by hypothesis. The
descent of closedness through such a family of cartesian squares is the topological lemma
`AlgebraicGeometry.Space.isClosedMap_of_isOpenMap_family_cartesian`.

The étale hypothesis is stated with `AlgebraicGeometry.Space.IsEtale`; inside the proof it is
converted to the representable-étale property of `CategoryTheory.MorphismProperty.presheaf`,
which is what is stable under base change, by `AlgebraicGeometry.Space.presheaf_etale_of_isEtale`
and `AlgebraicGeometry.Space.isEtale_of_presheaf_etale`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### The test along a covering family of étale charts -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks of presheaves on the big fppf site over `S` is slow
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance hasPullbacks_presheaf_UniversallyClosedEtaleFamily :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- Shortcut for the limit of a cospan of presheaves on the big fppf site over `S`. -/
local instance (priority := high) hasPullback_presheaf_UniversallyClosedEtaleFamily
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- If a family of étale charts of `Y`, indexed by any type, covers the points of `Y`, and the
base change of `f` along each member is universally closed, then `f` is universally closed.

This is the common generalisation of the étale-atlas test
`AlgebraicGeometry.Space.universallyClosed_of_etale_atlas`, which is the case of a one-member
family whose single member is surjective, and of the Zariski-local test
`AlgebraicGeometry.Space.universallyClosed_of_isZariskiCover`, whose members are the open
immersions of a Zariski covering. -/
theorem universallyClosed_of_etale_covering_family
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) {I : Type*}
    (V : I → BigFppfOver B S hS) (φ : ∀ i, yoneda.obj (V i) ⟶ Y)
    (hetale : ∀ i, IsEtale B S hS (φ i))
    (hcov : ∀ y : points B S hS Y, ∃ i, y ∈ Set.range (pointsMap B S hS (yoneda.obj (V i))
      (φ i)))
    (h : ∀ i, UniversallyClosed B S hS (pullback.fst (φ i) f)) :
    UniversallyClosed B S hS f := by
  have hbc : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  intro Z hZ g
  have hZi (i : I) : IsAlgebraicSpace B S hS (pullback g (φ i)) :=
    isAlgebraicSpace_pullback B S hS g (φ i) hZ (isAlgebraicSpace_yoneda B S hS (V i)) hY
  -- each base change of a member of the family is again étale
  have hietale (i : I) : IsEtale B S hS (pullback.fst g (φ i)) :=
    isEtale_of_presheaf_etale B S hS (hbc.of_isPullback
      (IsPullback.of_hasPullback g (φ i)).flip (presheaf_etale_of_isEtale B S hS (hetale i)))
  refine isClosedMap_of_isOpenMap_family_cartesian
    (pointsMap B S hS (pullback g f) (pullback.fst g f))
    (fun i ↦ pointsMap B S hS (pullback (pullback.fst g (φ i)) (pullback.fst g f))
      (pullback.snd (pullback.fst g (φ i)) (pullback.fst g f)))
    (fun i ↦ pointsMap B S hS (pullback (pullback.fst g (φ i)) (pullback.fst g f))
      (pullback.fst (pullback.fst g (φ i)) (pullback.fst g f)))
    (fun i ↦ pointsMap B S hS (pullback g (φ i)) (pullback.fst g (φ i)))
    (fun _ d ↦ pointsMap_apply_comm B S hS pullback.condition.symm d)
    (fun i c w hcw ↦ exists_points_of_isPullback B S hS
      (IsPullback.of_hasPullback (pullback.fst g (φ i)) (pullback.fst g f)).flip c w hcw)
    (fun _ ↦ continuous_pointsMap B S hS _)
    (fun i ↦ isOpenMap_pointsMap_of_isEtale B S hS (pullback.fst g (φ i)) (hZi i) hZ
      (hietale i))
    (fun z ↦ ?_)
    (fun i ↦ isClosedMorphism_pullback_fst_of_comm B S hS f g (φ i)
      (pullback.fst g (φ i)) (pullback.snd g (φ i)) pullback.condition
      (h i (pullback g (φ i)) (hZi i) (pullback.snd g (φ i))))
  -- the base changes of the members jointly cover the points of the test space
  obtain ⟨i, y, hy⟩ := hcov (pointsMap B S hS Z g z)
  obtain ⟨w, hw, -⟩ := exists_points_of_isPullback B S hS
    (IsPullback.of_hasPullback g (φ i)) z y hy.symm
  exact ⟨i, w, hw⟩

end AlgebraicGeometry.Space
