module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionProper

/-!
# The points of a represented presheaf are the points of the representing scheme

Let `S` be a scheme contained in a big fppf site `B`. For an object `U` of the big fppf site
over `S` the canonical map `AlgebraicGeometry.Space.pointsToScheme` from the points of the
presheaf represented by `U` to the points of the scheme underlying `U` is a bijection, and
clause (1) of Stacks 03BX says that it identifies the point topology with the topology of
the scheme. This file records that identification as a homeomorphism; the consequence that a
morphism of the site is a closed map on points exactly when the underlying morphism of schemes
is a closed map is `AlgebraicGeometry.Space.isClosedMap_pointsMap_yoneda_iff`, proved with the
point topology in `StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable`.

That consequence is then transported to a *representable* morphism of presheaves: closedness
on the points of the presheaf fibre product gives closedness of the morphism of schemes
representing the base change. This is the step through which a point-set hypothesis on
algebraic spaces — the form in which Stacks 03HI states closedness — becomes a hypothesis
about schemes.

## Main results

* `AlgebraicGeometry.Space.pointsHomeomorphOfIso`: an isomorphism of presheaves is a
  homeomorphism on points.
* `AlgebraicGeometry.Space.schemePointsHomeomorph`: Stacks 03BX, clause (1), as a
  homeomorphism.
* `AlgebraicGeometry.Space.isClosedMap_map_relativelyRepresentable_snd`: closedness on the
  points of a presheaf fibre product gives closedness of the representing morphism of schemes.

## Implementation notes

`AlgebraicGeometry.Space.pointTopology` is a plain definition rather than an instance, so it
is made a local instance here, and every point space below carries `pointTopology`.

Nothing here needs an algebraic space hypothesis, because `pointTopology` is defined for an
arbitrary presheaf on the big fppf site of `S`. The Stacks text states these facts for
algebraic spaces only because its topology is produced by the existence statement of Stacks
03BX, whose quantifier ranges over algebraic spaces.

The homeomorphism is the bijection `AlgebraicGeometry.Space.pointsEquivScheme` of
Stacks 03BX (1); both continuities come from
`AlgebraicGeometry.Space.isOpen_yoneda_iff_isSchemeOpen` together with
`AlgebraicGeometry.Space.isSchemeOpen_iff_preimage`, which say exactly that the open sets of
the point topology are the preimages of the open sets of the scheme.

## References

* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03HI](https://stacks.math.columbia.edu/tag/03HI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An isomorphism of presheaves on the big fppf site of `S` induces a homeomorphism of point
spaces: the two induced maps on points are mutually inverse, and every morphism of presheaves
is continuous on points by clause (2) of Stacks 03BX. -/
noncomputable def pointsHomeomorphOfIso {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ G) :
    points B S hS F ≃ₜ points B S hS G where
  toFun := pointsMap B S hS F e.hom
  invFun := pointsMap B S hS G e.inv
  left_inv x := by
    rw [show pointsMap B S hS G e.inv (pointsMap B S hS F e.hom x) =
      (pointsMap B S hS G e.inv ∘ pointsMap B S hS F e.hom) x from rfl,
      ← pointsMap_comp, e.hom_inv_id, pointsMap_id, id_eq]
  right_inv x := by
    rw [show pointsMap B S hS F e.hom (pointsMap B S hS G e.inv x) =
      (pointsMap B S hS F e.hom ∘ pointsMap B S hS G e.inv) x from rfl,
      ← pointsMap_comp, e.inv_hom_id, pointsMap_id, id_eq]
  continuous_toFun := continuous_pointsMap B S hS e.hom
  continuous_invFun := continuous_pointsMap B S hS e.inv

/-- The homeomorphism induced by an isomorphism of presheaves is the map on points induced by
the forward morphism. -/
@[simp]
theorem pointsHomeomorphOfIso_apply {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ G)
    (x : points B S hS F) :
    pointsHomeomorphOfIso B S hS e x = pointsMap B S hS F e.hom x := rfl

/-- The points of a represented presheaf, with the point topology, are homeomorphic to the
points of the representing scheme (Stacks 03BX, clause (1)). -/
noncomputable def schemePointsHomeomorph (U : BigFppfOver B S hS) :
    points B S hS (yoneda.obj U) ≃ₜ (BigFppfOver.toScheme B S hS).obj U :=
  (pointsEquivScheme B S hS U).toHomeomorphOfContinuousOpen
    (by
      rw [continuous_def]
      intro V hV
      rw [isOpen_yoneda_iff_isSchemeOpen, isSchemeOpen_iff_preimage]
      exact ⟨V, hV, rfl⟩)
    (by
      intro W hW
      rw [isOpen_yoneda_iff_isSchemeOpen, isSchemeOpen_iff_preimage] at hW
      obtain ⟨V, hV, rfl⟩ := hW
      have himg : (pointsEquivScheme B S hS U) ''
          (pointsToScheme B S hS U ⁻¹' V) = V :=
        (pointsEquivScheme B S hS U).image_preimage V
      rwa [himg])

/-- The homeomorphism `schemePointsHomeomorph` is the canonical map from points of the
represented presheaf to points of the scheme. -/
@[simp]
theorem schemePointsHomeomorph_apply (U : BigFppfOver B S hS)
    (x : points B S hS (yoneda.obj U)) :
    schemePointsHomeomorph B S hS U x = pointsToScheme B S hS U x := rfl

/-- Closedness on the points of the presheaf fibre product `h_U ×_Y X` gives closedness of
the morphism of schemes representing that base change.

The comparison is the uniqueness isomorphism between the chosen representation
`CategoryTheory.Functor.relativelyRepresentable.pullback` of the base change and the presheaf
fibre product. -/
theorem isClosedMap_map_relativelyRepresentable_snd
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) {U : BigFppfOver B S hS}
    (g : yoneda.obj U ⟶ Y)
    (hclosed : IsClosedMap (pointsMap B S hS (pullback g f) (pullback.fst g f))) :
    IsClosedMap ((BigFppfOver.toScheme B S hS).map (hf.snd g)) := by
  let e : yoneda.obj (hf.pullback g) ≅ pullback g f :=
    (hf.isPullback g).isoPullback ≪≫ pullbackSymmetry f g
  have he : e.hom ≫ pullback.fst g f = yoneda.map (hf.snd g) := by
    simp only [e, Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_fst,
      IsPullback.isoPullback_hom_snd]
  have hmap : pointsMap B S hS (yoneda.obj (hf.pullback g)) (yoneda.map (hf.snd g)) =
      pointsMap B S hS (pullback g f) (pullback.fst g f) ∘
        pointsMap B S hS (yoneda.obj (hf.pullback g)) e.hom := by
    rw [← pointsMap_comp, he]
  refine (isClosedMap_pointsMap_yoneda_iff B S hS (hf.snd g)).1 ?_
  rw [hmap]
  exact hclosed.comp (pointsHomeomorphOfIso B S hS e).isClosedMap

end AlgebraicGeometry.Space

end
