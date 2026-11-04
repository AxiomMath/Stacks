module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.TwoFibreProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.PresentationAtlasSmallUniverse
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersection
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFirstFactor

/-!
# The arrow space of a presentation represents the relation of its atlas

Let `S` be a scheme of a big fppf site, let `𝒳` be a category fibred in groupoids over the big
fppf site of `S` and let `P = ((U, R, s, t, c), [U/R] ≃ 𝒳)` be a presentation of `𝒳` in the sense
of Stacks 04TI. Write `a : 𝒮_U ⟶ 𝒳` for its atlas at the morphism universe of `𝒳`
(`AlgebraicGeometry.Stack.GroupoidPresentation.atlasMap`). This module identifies the
self-intersection of that atlas with the arrow space:

    𝒮_U ×_{a, 𝒳, a} 𝒮_U  ≃  𝒮_R   over the big fppf site of `S`.

This is **Stacks 04M9** read at the atlas rather than at the canonical projection
`π : 𝒮_U ⟶ [U/R]`, which is where every consumer that base changes a presentation needs it: the
hypothesis `eR` of Stacks 04T4 (4) and of Stacks 04T5 is an equivalence over the site of exactly
this self-intersection with a chosen representing algebraic space, and for the atlas of a
presentation the chosen space can be `R` itself.

## Main definitions

* `AlgebraicGeometry.Stack.GroupoidPresentation.atlasRelationBaseProjection`: the structure
  functor of `𝒮_U^+ ×_𝒳 𝒮_U^+`, the self-intersection of the *presenting* 1-morphism
  `𝒮_U^+ ⟶ 𝒳` of Stacks 044R — the universe-enlarged object space on both factors. It is the
  apex both comparisons below land in.
* `AlgebraicGeometry.Stack.GroupoidPresentation.arrowToAtlasRelationBase`: the comparison from
  `𝒮_R^+`, the universe-enlarged arrow space, sending an arrow `r` to the triple `(s r, t r, τ)`
  with `τ` the 2-arrow of Stacks 044S at `r` carried into `𝒳`.
* `AlgebraicGeometry.Stack.GroupoidPresentation.atlasRelationToBase`: the comparison from
  `𝒮_U ×_{a, 𝒳, a} 𝒮_U`, which enlarges the universe of the two factors and changes nothing else.
  Its two halves, one factor at a time, are
  `AlgebraicGeometry.Stack.GroupoidPresentation.atlasRelationLift` and
  `...atlasRelationBaseLift`, through the mixed product
  `...atlasRelationMixedProjection`.

## Main results

* `AlgebraicGeometry.Stack.GroupoidPresentation.isEquivalence_arrowToAtlasRelationBase` and
  `...isEquivalence_atlasRelationToBase`: both comparisons are equivalences of the underlying
  categories, and both are strictly over the site
  (`...arrowToAtlasRelationBase_comp_projection`, `...atlasRelationToBase_comp_projection`).
* `AlgebraicGeometry.Stack.GroupoidPresentation.arrowToAtlasRelationBase_obj_x` and `...obj_y`,
  `...atlasRelationToBase_obj_x` and `...obj_y`: the two components of each comparison.
* `AlgebraicGeometry.Stack.GroupoidPresentation.nonempty_equivalenceOver_relation_atlasMap`:
  **the identification** — the self-intersection of the atlas is equivalent over the big fppf
  site of `S` to the fibred category of the arrow space.

## Implementation notes

**Why a span and not a single 1-morphism.** The two sides of the identification are 2-fibre
products of two different cospans: one of `π : 𝒮_U^+ ⟶ [U/R]` with itself, the other of
`a : 𝒮_U ⟶ 𝒳` with itself. Four replacements separate them, and each is available as a
1-morphism only in one direction:

* `CategoryTheory.TwoFibreProductOver.mapBase` along the presenting equivalence
  `[U/R] ⟶ 𝒳` replaces the target. It needs that 1-morphism only *fully faithful*, and points
  from `[U/R]` to `𝒳`.
* `CategoryTheory.TwoFibreProductOver.precomposeSnd` and `...precomposeFst` along the universe
  lift `𝒮_U ⟶ 𝒮_U^+` replace the two factors, and point from the *small* product to the
  enlarged one.

So `𝒮_R^+` reaches `𝒮_U^+ ×_𝒳 𝒮_U^+` from one side and `𝒮_U ×_𝒳 𝒮_U` reaches it from the
other, and the identification is the span. Both legs are explicit on objects — neither involves
a quasi-inverse — which is what a consumer computing the source, the target or the composition
law of the induced groupoid needs; composing them into a single 1-morphism would invert one leg
and destroy exactly that.

**The comparison at `π` is the explicit one.** The library's Stacks 04M9,
`AlgebraicGeometry.Stack.quotientStack_twoFibreProduct`, is terminality in the category of
2-commutative squares and is produced by a choice, so it names no functor. The functor doing the
work is `AlgebraicGeometry.Stack.arrowToRelativeProduct`, with
`AlgebraicGeometry.Stack.isEquivalence_arrowToRelativeProduct`; that is what is used here.

**The universe crossing is paid at the atlas, not here.** Both factors of the small product are
`AlgebraicGeometry.Stack.GroupoidPresentation.objectStack`, the fibred category of the object
space with no universe lift, which is the source of `atlasMap`; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Stacks/PresentationAtlasSmallUniverse.lean`.

## References

* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 044S](https://stacks.math.columbia.edu/tag/044S)
* [Stacks Project, Tag 04M9](https://stacks.math.columbia.edu/tag/04M9)
* [Stacks Project, Tag 04T4](https://stacks.math.columbia.edu/tag/04T4)
* [Stacks Project, Tag 04T5](https://stacks.math.columbia.edu/tag/04T5)
* [Stacks Project, Tag 04TI](https://stacks.math.columbia.edu/tag/04TI)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.GroupoidPresentation

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}

-- The universe lift of an algebraic space's fibred category is reached under two names which
-- agree definitionally but not reducibly; instance search has to see through them, exactly as in
-- `StacksFrontier/AlgebraicGeometry/Stacks/PresentationAtlasSmallUniverse.lean`.
attribute [local implicit_reducible] liftedObjectSpace liftedSpace liftedFibredCategory

variable (P : GroupoidPresentation B S hS 𝒳.val)

/-- **The apex of the comparison span**: the structure functor of `𝒮_U^+ ×_𝒳 𝒮_U^+`, the
self-intersection of the presenting 1-morphism `𝒮_U^+ ⟶ 𝒳` of a presentation, with the
universe-enlarged object space on both factors. -/
noncomputable abbrev atlasRelationBaseProjection :=
  TwoFibreProductOver.structureFunctor (liftedFibredCategory P.groupoid.objects).p
    (liftedFibredCategory P.groupoid.objects).p 𝒳.val.p
    ((liftedQuotientStackProjection P.groupoid).toFunctor ⋙ P.basedFunctor.toFunctor)
    ((liftedQuotientStackProjection P.groupoid).toFunctor ⋙ P.basedFunctor.toFunctor)

/-- The universe-enlarged object space of a presentation is fibred in groupoids over the site. -/
theorem isFiberedInGroupoids_liftedObjects :
    (liftedFibredCategory P.groupoid.objects).p.IsFiberedInGroupoids :=
  isFiberedInGroupoids_uliftHom _ (fibredCategory B S hS P.groupoid.objects.obj).property

/-- The universe-enlarged arrow space of a presentation is fibred in groupoids over the site. -/
theorem isFiberedInGroupoids_liftedArrows :
    (liftedFibredCategory P.groupoid.arrows).p.IsFiberedInGroupoids :=
  isFiberedInGroupoids_uliftHom _ (fibredCategory B S hS P.groupoid.arrows.obj).property

/-- The apex of the comparison span is fibred in groupoids over the site. -/
theorem isFiberedInGroupoids_atlasRelationBaseProjection :
    (atlasRelationBaseProjection P).IsFiberedInGroupoids :=
  TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _
    (isFiberedInGroupoids_liftedObjects P) (isFiberedInGroupoids_liftedObjects P)
    𝒳.isFiberedInGroupoids P.presentingMap.w P.presentingMap.w

/-- The structure functor of the mixed product `𝒮_U^+ ×_𝒳 𝒮_U`, the intermediate step in which
only the second factor has been brought down to the morphism universe of `𝒳`. -/
noncomputable abbrev atlasRelationMixedProjection :=
  TwoFibreProductOver.structureFunctor (liftedFibredCategory P.groupoid.objects).p
    (objectStack P).val.p 𝒳.val.p
    ((liftedQuotientStackProjection P.groupoid).toFunctor ⋙ P.basedFunctor.toFunctor)
    ((liftedFibredCategoryUp P.groupoid.objects).toFunctor ⋙
      ((liftedQuotientStackProjection P.groupoid).toFunctor ⋙ P.basedFunctor.toFunctor))

/-- The mixed product is fibred in groupoids over the site. -/
theorem isFiberedInGroupoids_atlasRelationMixedProjection :
    (atlasRelationMixedProjection P).IsFiberedInGroupoids :=
  TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _
    (isFiberedInGroupoids_liftedObjects P) (objectStack P).isFiberedInGroupoids
    𝒳.isFiberedInGroupoids P.presentingMap.w (atlasMap P).hom.w

/-- **The comparison out of the arrow space.** The comparison 1-morphism of Stacks 04M9 at the
canonical projection `π : 𝒮_U^+ ⟶ [U/R]`, with the presenting equivalence `[U/R] ⟶ 𝒳` applied to
the target: an arrow `r` of the groupoid over a test object goes to the triple consisting of its
source, its target, and the image in `𝒳` of the 2-arrow of Stacks 044S at `r`. -/
noncomputable def arrowToAtlasRelationBase :
    (liftedFibredCategory P.groupoid.arrows).obj ⥤
      TwoFibreProductOver (liftedFibredCategory P.groupoid.objects).p
        (liftedFibredCategory P.groupoid.objects).p 𝒳.val.p
        ((liftedQuotientStackProjection P.groupoid).toFunctor ⋙ P.basedFunctor.toFunctor)
        ((liftedQuotientStackProjection P.groupoid).toFunctor ⋙ P.basedFunctor.toFunctor) :=
  arrowToRelativeProduct P.groupoid ⋙
    TwoFibreProductOver.mapBase _ _ P.basedFunctor.toFunctor P.basedFunctor.w

/-- Composing `F ⋙ G` with `K` is `p` once `G ⋙ K = q` and `F ⋙ q = p`. -/
private theorem comp_comp_eq_of_comp_eq {C D E E' : Type*} [Category C] [Category D] [Category E]
    [Category E'] (F : C ⥤ D) (G : D ⥤ E) (K : E ⥤ E') {q : D ⥤ E'} {p : C ⥤ E'}
    (hG : G ⋙ K = q) (hF : F ⋙ q = p) : (F ⋙ G) ⋙ K = p := by
  subst hG hF
  rfl

/-- The comparison out of the arrow space is strictly over the big fppf site of `S`. -/
theorem arrowToAtlasRelationBase_comp_projection :
    arrowToAtlasRelationBase P ⋙ atlasRelationBaseProjection P =
      (liftedFibredCategory P.groupoid.arrows).p :=
  comp_comp_eq_of_comp_eq _ _ _
    (TwoFibreProductOver.mapBase_comp_structureFunctor _ _ _ _)
    (arrowToRelativeProduct_comp_relativeProjection P.groupoid)

/-- **The comparison out of the arrow space is an equivalence.** Stacks 04M9 at `π` is one
(`AlgebraicGeometry.Stack.isEquivalence_arrowToRelativeProduct`), and changing the target of a
2-fibre product along a fully faithful 1-morphism is one. -/
theorem isEquivalence_arrowToAtlasRelationBase :
    (arrowToAtlasRelationBase P).IsEquivalence := by
  have := isEquivalence_basedFunctor P
  have := isEquivalence_arrowToRelativeProduct P.groupoid
  have := TwoFibreProductOver.isEquivalence_mapBase
    (pT := (liftedFibredCategory P.groupoid.objects).p)
    (p𝒜 := (liftedFibredCategory P.groupoid.objects).p)
    (G := (liftedQuotientStackProjection P.groupoid).toFunctor)
    (F := (liftedQuotientStackProjection P.groupoid).toFunctor) P.basedFunctor.w
  exact inferInstanceAs ((arrowToRelativeProduct P.groupoid ⋙
    TwoFibreProductOver.mapBase _ _ P.basedFunctor.toFunctor
      P.basedFunctor.w).IsEquivalence)

/-- The first component of the comparison out of the arrow space at an arrow `r` is the source of
`r`: changing the target of a 2-fibre product leaves the two factors alone. -/
theorem arrowToAtlasRelationBase_obj_x (T : BigFppfOver B S hS)
    (r : P.groupoid.arrows.obj.obj (Opposite.op T)) :
    ((arrowToAtlasRelationBase P).obj ⟨T, Discrete.mk r⟩).x =
      ⟨T, Discrete.mk (P.groupoid.source.hom.app (Opposite.op T) r)⟩ :=
  arrowToRelativeProduct_obj_x P.groupoid T r

/-- The second component of the comparison out of the arrow space at an arrow `r` is the target
of `r`. -/
theorem arrowToAtlasRelationBase_obj_y (T : BigFppfOver B S hS)
    (r : P.groupoid.arrows.obj.obj (Opposite.op T)) :
    ((arrowToAtlasRelationBase P).obj ⟨T, Discrete.mk r⟩).y =
      ⟨T, Discrete.mk (P.groupoid.target.hom.app (Opposite.op T) r)⟩ :=
  arrowToRelativeProduct_obj_y P.groupoid T r

/-- **The first half of the comparison out of the relation of the atlas**: enlarging the
morphism universe of the *first* factor. -/
noncomputable def atlasRelationLift :
    (SelfIntersection.relation B S hS (objectStack P) 𝒳 (atlasMap P).hom).val.obj ⥤
      TwoFibreProductOver (liftedFibredCategory P.groupoid.objects).p
        (objectStack P).val.p 𝒳.val.p
        ((liftedQuotientStackProjection P.groupoid).toFunctor ⋙ P.basedFunctor.toFunctor)
        ((liftedFibredCategoryUp P.groupoid.objects).toFunctor ⋙
          ((liftedQuotientStackProjection P.groupoid).toFunctor ⋙ P.basedFunctor.toFunctor)) :=
  TwoFibreProductOver.precomposeFst (objectStack P).val.p
    (liftedFibredCategory P.groupoid.objects).p (objectStack P).val.p 𝒳.val.p
    ((liftedQuotientStackProjection P.groupoid).toFunctor ⋙ P.basedFunctor.toFunctor)
    ((liftedFibredCategoryUp P.groupoid.objects).toFunctor ⋙
      ((liftedQuotientStackProjection P.groupoid).toFunctor ⋙ P.basedFunctor.toFunctor))
    (liftedFibredCategoryUp P.groupoid.objects).toFunctor
    (liftedFibredCategoryUp P.groupoid.objects).w

/-- **The second half of the comparison out of the relation of the atlas**: enlarging the
morphism universe of the *second* factor. -/
noncomputable def atlasRelationBaseLift :
    TwoFibreProductOver (liftedFibredCategory P.groupoid.objects).p
        (objectStack P).val.p 𝒳.val.p
        ((liftedQuotientStackProjection P.groupoid).toFunctor ⋙ P.basedFunctor.toFunctor)
        ((liftedFibredCategoryUp P.groupoid.objects).toFunctor ⋙
          ((liftedQuotientStackProjection P.groupoid).toFunctor ⋙ P.basedFunctor.toFunctor)) ⥤
      TwoFibreProductOver (liftedFibredCategory P.groupoid.objects).p
        (liftedFibredCategory P.groupoid.objects).p 𝒳.val.p
        ((liftedQuotientStackProjection P.groupoid).toFunctor ⋙ P.basedFunctor.toFunctor)
        ((liftedQuotientStackProjection P.groupoid).toFunctor ⋙ P.basedFunctor.toFunctor) :=
  TwoFibreProductOver.precomposeSnd
    (pT := (liftedFibredCategory P.groupoid.objects).p)
    (p𝒜' := (objectStack P).val.p)
    (p𝒜 := (liftedFibredCategory P.groupoid.objects).p) (pℬ := 𝒳.val.p)
    ((liftedQuotientStackProjection P.groupoid).toFunctor ⋙ P.basedFunctor.toFunctor)
    ((liftedQuotientStackProjection P.groupoid).toFunctor ⋙ P.basedFunctor.toFunctor)
    (liftedFibredCategoryUp P.groupoid.objects).toFunctor
    (liftedFibredCategoryUp P.groupoid.objects).w

/-- **The comparison out of the relation of the atlas.** The self-intersection of the atlas maps
to that of the presenting 1-morphism by enlarging the morphism universe of the two factors; the
comparison isomorphism of an object is unchanged. -/
noncomputable def atlasRelationToBase :
    (SelfIntersection.relation B S hS (objectStack P) 𝒳 (atlasMap P).hom).val.obj ⥤
      TwoFibreProductOver (liftedFibredCategory P.groupoid.objects).p
        (liftedFibredCategory P.groupoid.objects).p 𝒳.val.p
        ((liftedQuotientStackProjection P.groupoid).toFunctor ⋙ P.basedFunctor.toFunctor)
        ((liftedQuotientStackProjection P.groupoid).toFunctor ⋙ P.basedFunctor.toFunctor) :=
  atlasRelationLift P ⋙ atlasRelationBaseLift P

/-- The comparison out of the relation of the atlas is strictly over the big fppf site of `S`. -/
theorem atlasRelationToBase_comp_projection :
    atlasRelationToBase P ⋙ atlasRelationBaseProjection P =
      (SelfIntersection.relation B S hS (objectStack P) 𝒳 (atlasMap P).hom).val.p :=
  comp_comp_eq_of_comp_eq _ _ _
    (TwoFibreProductOver.precomposeSnd_comp_structureFunctor _ _ _ _)
    (TwoFibreProductOver.precomposeFst_comp_structureFunctor _ _ _ _ _ _ _ _)

/-- **The comparison out of the relation of the atlas is an equivalence.** Changing a factor of a
2-fibre product along an equivalence over the site is one, and the universe lift of the fibred
category of an algebraic space is an equivalence. -/
theorem isEquivalence_atlasRelationToBase :
    (atlasRelationToBase P).IsEquivalence := by
  have := isEquivalence_liftedFibredCategoryUp P.groupoid.objects
  have : (atlasRelationLift P).IsEquivalence :=
    TwoFibreProductOver.isEquivalence_precomposeFst (objectStack P).val.p
      (liftedFibredCategory P.groupoid.objects).p (objectStack P).val.p 𝒳.val.p
      ((liftedQuotientStackProjection P.groupoid).toFunctor ⋙ P.basedFunctor.toFunctor)
      ((liftedFibredCategoryUp P.groupoid.objects).toFunctor ⋙
        ((liftedQuotientStackProjection P.groupoid).toFunctor ⋙ P.basedFunctor.toFunctor))
      (liftedFibredCategoryUp P.groupoid.objects).toFunctor
      (liftedFibredCategoryUp P.groupoid.objects).w
      (objectStack P).isFiberedInGroupoids (objectStack P).isFiberedInGroupoids
      (isFiberedInGroupoids_liftedObjects P) inferInstance P.presentingMap.w
  have : (atlasRelationBaseLift P).IsEquivalence :=
    TwoFibreProductOver.isEquivalence_precomposeSnd
      (pT := (liftedFibredCategory P.groupoid.objects).p) (pℬ := 𝒳.val.p)
      (G := (liftedQuotientStackProjection P.groupoid).toFunctor ⋙ P.basedFunctor.toFunctor)
      (F := (liftedQuotientStackProjection P.groupoid).toFunctor ⋙ P.basedFunctor.toFunctor)
      (a := (liftedFibredCategoryUp P.groupoid.objects).toFunctor)
      (isFiberedInGroupoids_liftedObjects P) (objectStack P).isFiberedInGroupoids
      (isFiberedInGroupoids_liftedObjects P) (liftedFibredCategoryUp P.groupoid.objects).w
      P.presentingMap.w
  exact inferInstanceAs ((atlasRelationLift P ⋙ atlasRelationBaseLift P).IsEquivalence)

/-- The first component of the comparison out of the relation of the atlas is the universe lift of
the first component. -/
theorem atlasRelationToBase_obj_x
    (ρ : (SelfIntersection.relation B S hS (objectStack P) 𝒳 (atlasMap P).hom).val.obj) :
    ((atlasRelationToBase P).obj ρ).x =
      (liftedFibredCategoryUp P.groupoid.objects).toFunctor.obj ρ.x := rfl

/-- The second component of the comparison out of the relation of the atlas is the universe lift
of the second component. -/
theorem atlasRelationToBase_obj_y
    (ρ : (SelfIntersection.relation B S hS (objectStack P) 𝒳 (atlasMap P).hom).val.obj) :
    ((atlasRelationToBase P).obj ρ).y =
      (liftedFibredCategoryUp P.groupoid.objects).toFunctor.obj ρ.y := rfl

/-- **The arrow space of a presentation represents the self-intersection of its atlas.** Let
`P = ((U, R, s, t, c), [U/R] ≃ 𝒳)` be a presentation and let `a : 𝒮_U ⟶ 𝒳` be its atlas. Then
`𝒮_U ×_{a, 𝒳, a} 𝒮_U` is equivalent, over the big fppf site of `S`, to the fibred category of the
arrow space `R`.

This is Stacks 04M9 read at the atlas instead of at the canonical projection
`π : 𝒮_U ⟶ [U/R]`, and it is the datum `eR` that Stacks 04T4 (4) and Stacks 04T5 take as a
hypothesis: for the atlas of a presentation the representing algebraic space of the
self-intersection can be taken to be `R` itself. -/
theorem nonempty_equivalenceOver_relation_atlasMap :
    Nonempty (StacksRepresentableCFG.EquivalenceOver
      (SelfIntersection.relation B S hS (objectStack P) 𝒳 (atlasMap P).hom).val.p
      (presheafOfCategories (P.groupoid.arrows.obj ⋙ typeToCat)).p) := by
  obtain ⟨eDown⟩ := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence
    (isFiberedInGroupoids_liftedArrows P)
    (fibredCategory B S hS P.groupoid.arrows.obj).property
    (liftedFibredCategoryDown P.groupoid.arrows).toFunctor
    (liftedFibredCategoryDown P.groupoid.arrows).w inferInstance
  obtain ⟨eArrow⟩ := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence
    (isFiberedInGroupoids_liftedArrows P)
    (isFiberedInGroupoids_atlasRelationBaseProjection P)
    (arrowToAtlasRelationBase P) (arrowToAtlasRelationBase_comp_projection P)
    (isEquivalence_arrowToAtlasRelationBase P)
  obtain ⟨eRel⟩ := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence
    (SelfIntersection.relation B S hS (objectStack P) 𝒳 (atlasMap P).hom).isFiberedInGroupoids
    (isFiberedInGroupoids_atlasRelationBaseProjection P)
    (atlasRelationToBase P) (atlasRelationToBase_comp_projection P)
    (isEquivalence_atlasRelationToBase P)
  exact ⟨eRel.trans (eArrow.symm.trans eDown)⟩

end AlgebraicGeometry.Stack.GroupoidPresentation

end
