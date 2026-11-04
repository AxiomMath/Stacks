module

public import StacksFrontier.AlgebraicGeometry.Stacks.PresentationAtlasRelation
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionGroupoid

/-!
# The source and target of the self-intersection of an atlas are those of its groupoid

Let `S` be a scheme of a big fppf site, let `𝒳` be a category fibred in groupoids over the big
fppf site of `S` and let `P = ((U, R, s, t, c), [U/R] ≃ 𝒳)` be a presentation of `𝒳` in the sense
of Stacks 04TI, with atlas `a : 𝒮_U ⟶ 𝒳`
(`AlgebraicGeometry.Stack.GroupoidPresentation.atlasMap`).

For a chosen equivalence over the site between the self-intersection `𝒮_U ×_{a, 𝒳, a} 𝒮_U` and
`𝒮_R`, the two structure morphisms of the self-intersection groupoid built from it are the source
and the target of `P`'s own groupoid.

## Main definitions

* `AlgebraicGeometry.Stack.GroupoidPresentation.atlasObjectEquivalence`: the identity
  equivalence between the object space of the presentation and the category of elements of `U`.
* `AlgebraicGeometry.Stack.GroupoidPresentation.atlasRelationToBaseSwap`: the comparison out of
  the self-intersection of the atlas with its two factors exchanged.
* `AlgebraicGeometry.Stack.GroupoidPresentation.atlasRelationEquivalence`: a chosen equivalence
  over the site of `𝒮_U ×_{a, 𝒳, a} 𝒮_U` with `𝒮_R`.

## Main results

* `AlgebraicGeometry.Stack.GroupoidPresentation.sectionOfObj_atlasRelationArrow_y` and
  `...sectionOfObj_atlasRelationArrow_x`: the two components of the triple naming an arrow `r`
  of `R` name the source and the target of `r`.
* `AlgebraicGeometry.Stack.GroupoidPresentation.relationSourceMap_atlasRelationEquivalence` and
  `...relationTargetMap_atlasRelationEquivalence`: the source and the target of the
  self-intersection groupoid of the atlas are the source and the target of `P`'s own groupoid.

## Implementation notes

In the self-intersection, `AlgebraicGeometry.Stack.SelfIntersection.relationSourceMap` reads off
the second component of a triple `(x, y, φ : a x ≅ a y)` and `...relationTargetMap` the first,
while the comparison `AlgebraicGeometry.Stack.GroupoidPresentation.arrowToAtlasRelationBase` sends
an arrow `r` of `R` to a triple with first component `s r` and second `t r`. The comparison out of
the relation is therefore composed with `CategoryTheory.TwoFibreProductOver.swap`
(`AlgebraicGeometry.Stack.GroupoidPresentation.atlasRelationToBaseSwap`).

The chosen equivalence is a composite of three, each produced by
`StacksRepresentableCFG.equivalenceOverOfIsEquivalence`, whose forward 1-morphism is the given
comparison on the nose, so that `CategoryTheory.PresheafOfCategories.sectionOfObj` can be computed
along it.

## References

* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 04M9](https://stacks.math.columbia.edu/tag/04M9)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04T4](https://stacks.math.columbia.edu/tag/04T4)
* [Stacks Project, Tag 04TI](https://stacks.math.columbia.edu/tag/04TI)
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Stack.GroupoidPresentation

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}

attribute [local implicit_reducible] liftedObjectSpace liftedSpace liftedFibredCategory

variable (P : GroupoidPresentation B S hS 𝒳.val)

/-- The equivalence over the site between the object space of a presentation, read at the
morphism universe of the stack, and the category of elements of the sheaf of points of `U`: the
identity. -/
noncomputable abbrev atlasObjectEquivalence :
    StacksRepresentableCFG.EquivalenceOver (objectStack P).val.p
      (presheafOfCategories (P.groupoid.objects.obj ⋙ typeToCat)).p :=
  StacksRepresentableCFG.EquivalenceOver.refl _

/-- The comparison out of the relation of the atlas, with its two factors exchanged: it sends a
triple `(x, y, φ)` to `(y, x, φ⁻¹)` with the morphism universe of both factors enlarged. -/
noncomputable def atlasRelationToBaseSwap :
    (SelfIntersection.relation B S hS (objectStack P) 𝒳 (atlasMap P).hom).val.obj ⥤
      TwoFibreProductOver (liftedFibredCategory P.groupoid.objects).p
        (liftedFibredCategory P.groupoid.objects).p 𝒳.val.p
        ((liftedQuotientStackProjection P.groupoid).toFunctor ⋙ P.basedFunctor.toFunctor)
        ((liftedQuotientStackProjection P.groupoid).toFunctor ⋙ P.basedFunctor.toFunctor) :=
  atlasRelationToBase P ⋙
    TwoFibreProductOver.swap (liftedFibredCategory P.groupoid.objects).p
      (liftedFibredCategory P.groupoid.objects).p 𝒳.val.p
      ((liftedQuotientStackProjection P.groupoid).toFunctor ⋙ P.basedFunctor.toFunctor)
      ((liftedQuotientStackProjection P.groupoid).toFunctor ⋙ P.basedFunctor.toFunctor)

/-- The exchanged comparison is strictly over the big fppf site of `S`. -/
theorem atlasRelationToBaseSwap_comp_projection :
    atlasRelationToBaseSwap P ⋙ atlasRelationBaseProjection P =
      (SelfIntersection.relation B S hS (objectStack P) 𝒳 (atlasMap P).hom).val.p :=
  atlasRelationToBase_comp_projection P

/-- The exchanged comparison is an equivalence. -/
theorem isEquivalence_atlasRelationToBaseSwap :
    (atlasRelationToBaseSwap P).IsEquivalence := by
  have := isEquivalence_atlasRelationToBase P
  exact inferInstanceAs ((atlasRelationToBase P ⋙
    TwoFibreProductOver.swap (liftedFibredCategory P.groupoid.objects).p
      (liftedFibredCategory P.groupoid.objects).p 𝒳.val.p
      ((liftedQuotientStackProjection P.groupoid).toFunctor ⋙ P.basedFunctor.toFunctor)
      ((liftedQuotientStackProjection P.groupoid).toFunctor ⋙
        P.basedFunctor.toFunctor)).IsEquivalence)

/-- The first component of the exchanged comparison is the universe lift of the *second*
component. -/
theorem atlasRelationToBaseSwap_obj_x
    (ρ : (SelfIntersection.relation B S hS (objectStack P) 𝒳 (atlasMap P).hom).val.obj) :
    ((atlasRelationToBaseSwap P).obj ρ).x =
      (liftedFibredCategoryUp P.groupoid.objects).toFunctor.obj ρ.y := rfl

/-- The second component of the exchanged comparison is the universe lift of the *first*
component. -/
theorem atlasRelationToBaseSwap_obj_y
    (ρ : (SelfIntersection.relation B S hS (objectStack P) 𝒳 (atlasMap P).hom).val.obj) :
    ((atlasRelationToBaseSwap P).obj ρ).y =
      (liftedFibredCategoryUp P.groupoid.objects).toFunctor.obj ρ.x := rfl

/-- The chosen equivalence over the site of the self-intersection of the atlas with the apex
`𝒮_U^+ ×_𝒳 𝒮_U^+`, with the two factors exchanged. Its forward 1-morphism is
`AlgebraicGeometry.Stack.GroupoidPresentation.atlasRelationToBaseSwap` on the nose. -/
noncomputable def atlasRelationBaseEquivalence :
    StacksRepresentableCFG.EquivalenceOver
      (SelfIntersection.relation B S hS (objectStack P) 𝒳 (atlasMap P).hom).val.p
      (atlasRelationBaseProjection P) :=
  StacksRepresentableCFG.equivalenceOverOfIsEquivalence
    (SelfIntersection.relation B S hS (objectStack P) 𝒳 (atlasMap P).hom).isFiberedInGroupoids
    (isFiberedInGroupoids_atlasRelationBaseProjection P)
    (atlasRelationToBaseSwap P) (atlasRelationToBaseSwap_comp_projection P)
    (isEquivalence_atlasRelationToBaseSwap P)

/-- The chosen equivalence over the site of the universe-enlarged arrow space with the apex
`𝒮_U^+ ×_𝒳 𝒮_U^+`. Its forward 1-morphism is
`AlgebraicGeometry.Stack.GroupoidPresentation.arrowToAtlasRelationBase` on the nose. -/
noncomputable def atlasArrowBaseEquivalence :
    StacksRepresentableCFG.EquivalenceOver (liftedFibredCategory P.groupoid.arrows).p
      (atlasRelationBaseProjection P) :=
  StacksRepresentableCFG.equivalenceOverOfIsEquivalence
    (isFiberedInGroupoids_liftedArrows P)
    (isFiberedInGroupoids_atlasRelationBaseProjection P)
    (arrowToAtlasRelationBase P) (arrowToAtlasRelationBase_comp_projection P)
    (isEquivalence_arrowToAtlasRelationBase P)

/-- The chosen equivalence over the site of the arrow space with its universe enlargement. Its
forward 1-morphism is the universe lift `CategoryTheory.ULiftHom.up`, the identity on objects. -/
noncomputable def atlasArrowLiftEquivalence :
    StacksRepresentableCFG.EquivalenceOver
      (presheafOfCategories (P.groupoid.arrows.obj ⋙ typeToCat)).p
      (liftedFibredCategory P.groupoid.arrows).p :=
  StacksRepresentableCFG.equivalenceOverOfIsEquivalence
    (fibredCategory B S hS P.groupoid.arrows.obj).property
    (isFiberedInGroupoids_liftedArrows P)
    (liftedFibredCategoryUp P.groupoid.arrows).toFunctor
    (liftedFibredCategoryUp P.groupoid.arrows).w
    (isEquivalence_liftedFibredCategoryUp P.groupoid.arrows)

/-- The chosen equivalence over the big fppf site of `S` between the self-intersection
`𝒮_U ×_{a, 𝒳, a} 𝒮_U` of the atlas and the category of elements of the sheaf of points of the
arrow space `R`. -/
noncomputable def atlasRelationEquivalence :
    StacksRepresentableCFG.EquivalenceOver
      (SelfIntersection.relation B S hS (objectStack P) 𝒳 (atlasMap P).hom).val.p
      (presheafOfCategories (P.groupoid.arrows.obj ⋙ typeToCat)).p :=
  (atlasRelationBaseEquivalence P).trans
    ((atlasArrowBaseEquivalence P).symm.trans (atlasArrowLiftEquivalence P).symm)

section Arrow

variable {W : BigFppfOver B S hS} (r : P.groupoid.arrows.obj.obj (op W))

/-- The triple of the self-intersection of the atlas which names a given arrow `r` of `R` over a
test object: the image of `r` under the backward 1-morphism of the chosen equivalence. -/
noncomputable abbrev atlasRelationArrow :
    (SelfIntersection.relation B S hS (objectStack P) 𝒳 (atlasMap P).hom).val.obj :=
  (atlasRelationEquivalence P).inv.functor.obj ⟨W, Discrete.mk r⟩

/-- The triple naming `r` lies over the same test object as `r`. -/
theorem atlasRelationArrow_over :
    (SelfIntersection.relation B S hS (objectStack P) 𝒳 (atlasMap P).hom).val.p.obj
      (atlasRelationArrow P r) = W :=
  Functor.congr_obj (atlasRelationEquivalence P).inv.w
    (⟨W, Discrete.mk r⟩ : (presheafOfCategories (P.groupoid.arrows.obj ⋙ typeToCat)).obj)

/-- The triple naming `r` does name `r`. -/
theorem sectionOfObj_atlasRelationArrow :
    PresheafOfCategories.sectionOfObj (atlasRelationEquivalence P) (atlasRelationArrow P r)
        (atlasRelationArrow_over P r) = r :=
  PresheafOfCategories.sectionOfObj_inv_obj (atlasRelationEquivalence P) ⟨W, Discrete.mk r⟩

/-- The image under the comparison of Stacks 04M9 of the universe lift of `r`: the triple
`(s r, t r, τ_r)`. -/
noncomputable abbrev atlasRelationArrowImage :
    TwoFibreProductOver (liftedFibredCategory P.groupoid.objects).p
      (liftedFibredCategory P.groupoid.objects).p 𝒳.val.p
      ((liftedQuotientStackProjection P.groupoid).toFunctor ⋙ P.basedFunctor.toFunctor)
      ((liftedQuotientStackProjection P.groupoid).toFunctor ⋙ P.basedFunctor.toFunctor) :=
  (arrowToAtlasRelationBase P).obj ⟨W, Discrete.mk r⟩

/-- That image lies over the test object of `r`. -/
theorem atlasRelationArrowImage_over :
    (atlasRelationBaseProjection P).obj (atlasRelationArrowImage P r) = W :=
  Functor.congr_obj (arrowToAtlasRelationBase_comp_projection P)
    (⟨W, Discrete.mk r⟩ : (liftedFibredCategory P.groupoid.arrows).obj)

/-- The first component of that image, the source of `r`, lies over the test object of `r`. -/
theorem atlasRelationArrowImage_obj_x_over :
    (objectStack P).val.p.obj (atlasRelationArrowImage P r).x = W := by
  rw [arrowToAtlasRelationBase_obj_x]
  rfl

/-- The second component of that image, the target of `r`, lies over the test object of `r`. -/
theorem atlasRelationArrowImage_obj_y_over :
    (objectStack P).val.p.obj (atlasRelationArrowImage P r).y = W := by
  rw [arrowToAtlasRelationBase_obj_y]
  rfl

/-- The morphism from the image of the triple naming `r` under the exchanged comparison to
`(s r, t r, τ_r)` given by the counit of the chosen equivalence out of the relation. -/
noncomputable abbrev atlasRelationArrowCounit :
    (atlasRelationToBaseSwap P).obj (atlasRelationArrow P r) ⟶ atlasRelationArrowImage P r :=
  (atlasRelationBaseEquivalence P).counitIso.hom.app (atlasRelationArrowImage P r)

/-- The counit comparison lies over the identity of the test object. -/
theorem isHomLift_atlasRelationArrowCounit :
    (atlasRelationBaseProjection P).IsHomLift (𝟙 W) (atlasRelationArrowCounit P r) := by
  have h := (atlasRelationBaseEquivalence P).isHomLift_counitIso_hom_app
    (atlasRelationArrowImage P r)
  rwa [atlasRelationArrowImage_over P r] at h

/-- The first component of the counit comparison, read in the object space of `P` at the morphism
universe of the site: a morphism from the second component of the triple naming `r` to the source
of `r`. -/
noncomputable abbrev atlasRelationArrowCounitFst :
    (atlasRelationArrow P r).y ⟶ (atlasRelationArrowImage P r).x :=
  (liftedFibredCategoryDown P.groupoid.objects).toFunctor.map
    (atlasRelationArrowCounit P r).a

/-- The second component of the counit comparison: a morphism from the first component of the
triple naming `r` to the target of `r`. -/
noncomputable abbrev atlasRelationArrowCounitSnd :
    (atlasRelationArrow P r).x ⟶ (atlasRelationArrowImage P r).y :=
  (liftedFibredCategoryDown P.groupoid.objects).toFunctor.map
    (atlasRelationArrowCounit P r).b

/-- The first component of the counit comparison lies over the identity of the test object. -/
theorem isHomLift_atlasRelationArrowCounitFst :
    (objectStack P).val.p.IsHomLift (𝟙 W) (atlasRelationArrowCounitFst P r) :=
  Functor.isHomLift_map_of_comp_eq_general (liftedFibredCategoryDown P.groupoid.objects).w
    (𝟙 W) (atlasRelationArrowCounit P r).a
    (TwoFibreProductOver.isHomLift_a (atlasRelationArrowCounit P r) (𝟙 W)
      (isHomLift_atlasRelationArrowCounit P r))

/-- The second component of the counit comparison lies over the identity of the test object. -/
theorem isHomLift_atlasRelationArrowCounitSnd :
    (objectStack P).val.p.IsHomLift (𝟙 W) (atlasRelationArrowCounitSnd P r) :=
  Functor.isHomLift_map_of_comp_eq_general (liftedFibredCategoryDown P.groupoid.objects).w
    (𝟙 W) (atlasRelationArrowCounit P r).b
    (TwoFibreProductOver.isHomLift_b (atlasRelationArrowCounit P r) (𝟙 W)
      (isHomLift_atlasRelationArrowCounit P r))

/-- An object with a vertical morphism to the point `v` of the object space names `v`. -/
private theorem sectionOfObj_atlasObjectEquivalence_of_hom {X Y : (objectStack P).val.obj}
    (hX : (objectStack P).val.p.obj X = W) (hY : (objectStack P).val.p.obj Y = W) (f : X ⟶ Y)
    (hf : (objectStack P).val.p.IsHomLift (𝟙 W) f) (v : P.groupoid.objects.obj.obj (op W))
    (hYv : Y = ⟨W, Discrete.mk v⟩) :
    PresheafOfCategories.sectionOfObj (atlasObjectEquivalence P) X hX = v :=
  ((PresheafOfCategories.sectionOfObj_eq_of_hom (atlasObjectEquivalence P) hX hY f hf).trans
    (PresheafOfCategories.sectionOfObj_eq_of_obj_eq (atlasObjectEquivalence P)
      (atlasObjectEquivalence P) _
      (⟨W, Discrete.mk v⟩ : (presheafOfCategories (P.groupoid.objects.obj ⋙ typeToCat)).obj)
      _ rfl hYv)).trans
  (PresheafOfCategories.sectionOfObj_refl _)

/-- The second component of the triple naming `r` names the source of `r`. -/
theorem sectionOfObj_atlasRelationArrow_y :
    PresheafOfCategories.sectionOfObj (atlasObjectEquivalence P) (atlasRelationArrow P r).y
        (SelfIntersection.relation_obj_y (atlasRelationArrow_over P r)) =
      P.groupoid.source.hom.app (op W) r :=
  sectionOfObj_atlasObjectEquivalence_of_hom P _ (atlasRelationArrowImage_obj_x_over P r)
    (atlasRelationArrowCounitFst P r) (isHomLift_atlasRelationArrowCounitFst P r) _
    (arrowToAtlasRelationBase_obj_x P W r)

/-- The first component of the triple naming `r` names the target of `r`. -/
theorem sectionOfObj_atlasRelationArrow_x :
    PresheafOfCategories.sectionOfObj (atlasObjectEquivalence P) (atlasRelationArrow P r).x
        (SelfIntersection.relation_obj_x (atlasRelationArrow_over P r)) =
      P.groupoid.target.hom.app (op W) r :=
  sectionOfObj_atlasObjectEquivalence_of_hom P _ (atlasRelationArrowImage_obj_y_over P r)
    (atlasRelationArrowCounitSnd P r) (isHomLift_atlasRelationArrowCounitSnd P r) _
    (arrowToAtlasRelationBase_obj_y P W r)

/-- The source morphism of the self-intersection groupoid of the atlas sends a section `r` of `R`
to the source of `r`. -/
theorem relationSourceMap_app_atlasRelationEquivalence :
    (SelfIntersection.relationSourceMap (atlasObjectEquivalence P)
          (atlasRelationEquivalence P)).app (op W) r =
      P.groupoid.source.hom.app (op W) r :=
  ((congrArg ((SelfIntersection.relationSourceMap (atlasObjectEquivalence P)
      (atlasRelationEquivalence P)).app (op W)) (sectionOfObj_atlasRelationArrow P r).symm).trans
    (SelfIntersection.relationSourceMap_sectionOfObj (atlasObjectEquivalence P)
      (atlasRelationEquivalence P) (atlasRelationArrow P r) (atlasRelationArrow_over P r))).trans
    (sectionOfObj_atlasRelationArrow_y P r)

/-- The target morphism of the self-intersection groupoid of the atlas sends a section `r` of `R`
to the target of `r`. -/
theorem relationTargetMap_app_atlasRelationEquivalence :
    (SelfIntersection.relationTargetMap (atlasObjectEquivalence P)
          (atlasRelationEquivalence P)).app (op W) r =
      P.groupoid.target.hom.app (op W) r :=
  ((congrArg ((SelfIntersection.relationTargetMap (atlasObjectEquivalence P)
      (atlasRelationEquivalence P)).app (op W)) (sectionOfObj_atlasRelationArrow P r).symm).trans
    (SelfIntersection.relationTargetMap_sectionOfObj (atlasObjectEquivalence P)
      (atlasRelationEquivalence P) (atlasRelationArrow P r) (atlasRelationArrow_over P r))).trans
    (sectionOfObj_atlasRelationArrow_x P r)

end Arrow

/-- The source of the self-intersection groupoid of the atlas is the source of the presenting
groupoid. -/
theorem relationSourceMap_atlasRelationEquivalence :
    SelfIntersection.relationSourceMap (atlasObjectEquivalence P) (atlasRelationEquivalence P) =
      P.groupoid.source.hom :=
  natTrans_eq_of_forall_sectionOfObj B S hS
    (SelfIntersection.relation B S hS (objectStack P) 𝒳 (atlasMap P).hom)
    P.groupoid.arrows.obj P.groupoid.objects.obj
    (atlasRelationEquivalence P) _ _
    (fun _ _ _ => relationSourceMap_app_atlasRelationEquivalence P _)

/-- The target of the self-intersection groupoid of the atlas is the target of the presenting
groupoid. -/
theorem relationTargetMap_atlasRelationEquivalence :
    SelfIntersection.relationTargetMap (atlasObjectEquivalence P) (atlasRelationEquivalence P) =
      P.groupoid.target.hom :=
  natTrans_eq_of_forall_sectionOfObj B S hS
    (SelfIntersection.relation B S hS (objectStack P) 𝒳 (atlasMap P).hom)
    P.groupoid.arrows.obj P.groupoid.objects.obj
    (atlasRelationEquivalence P) _ _
    (fun _ _ _ => relationTargetMap_app_atlasRelationEquivalence P _)

/-- The object space of a presentation, read at the morphism universe of the stack, is fibred in
setoids over the site. -/
theorem isFiberedInSetoids_objectStack : (objectStack P).val.p.IsFiberedInSetoids :=
  SelfIntersection.isFiberedInSetoids_source (U := P.groupoid.objects)
    (atlasObjectEquivalence P)

/-- The self-intersection groupoid in algebraic spaces of the atlas of a presentation. Its object
and arrow spaces are those of the presentation itself, on the nose, and so are its source and
target. -/
noncomputable def atlasSelfIntersectionGroupoid :
    GroupoidInAlgebraicSpaces B S hS (Space.terminalSpace B S hS) :=
  SelfIntersection.selfIntersectionGroupoid (U := P.groupoid.objects) (R := P.groupoid.arrows)
    (atlasObjectEquivalence P) (atlasRelationEquivalence P) (isFiberedInSetoids_objectStack P)

/-- The object space of the self-intersection groupoid of the atlas is the object space of the
presentation. -/
@[simp] theorem atlasSelfIntersectionGroupoid_objects :
    (atlasSelfIntersectionGroupoid P).objects = P.groupoid.objects := rfl

/-- The arrow space of the self-intersection groupoid of the atlas is the arrow space of the
presentation. -/
@[simp] theorem atlasSelfIntersectionGroupoid_arrows :
    (atlasSelfIntersectionGroupoid P).arrows = P.groupoid.arrows := rfl

/-- The source of the self-intersection groupoid of the atlas is the source of the presentation,
as a morphism of algebraic spaces over `S`. -/
theorem atlasSelfIntersectionGroupoid_source :
    (atlasSelfIntersectionGroupoid P).source = P.groupoid.source :=
  congrArg ObjectProperty.homMk (relationSourceMap_atlasRelationEquivalence P)

/-- The target of the self-intersection groupoid of the atlas is the target of the presentation,
as a morphism of algebraic spaces over `S`. -/
theorem atlasSelfIntersectionGroupoid_target :
    (atlasSelfIntersectionGroupoid P).target = P.groupoid.target :=
  congrArg ObjectProperty.homMk (relationTargetMap_atlasRelationEquivalence P)

end AlgebraicGeometry.Stack.GroupoidPresentation

end
