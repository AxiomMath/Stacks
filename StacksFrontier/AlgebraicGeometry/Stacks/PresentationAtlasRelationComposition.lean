module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.ProjectionTwoArrow
public import StacksFrontier.AlgebraicGeometry.Stacks.PresentationAtlasRelationSections
public import StacksFrontier.CategoryTheory.FiberedCategory.Splitting
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverDiagonalFunctoriality

/-!
# The composition law of the self-intersection of an atlas is that of its groupoid

Let `S` be a scheme of a big fppf site, let `𝒳` be a category fibred in groupoids over the big
fppf site of `S` and let `P = ((U, R, s, t, c), [U/R] ≃ 𝒳)` be a presentation of `𝒳` in the sense
of Stacks 04TI, with atlas `a : 𝒮_U ⟶ 𝒳`.

`StacksFrontier/AlgebraicGeometry/Stacks/PresentationAtlasRelationSections.lean` identifies the
object space, the arrow space, the source and the target of the groupoid in algebraic spaces that
Stacks 04T4 (4) builds out of the self-intersection `𝒮_U ×_{a, 𝒳, a} 𝒮_U` of the atlas with
those of `P`'s own groupoid. This module identifies the remaining structure morphism, the
composition law, and so completes the statement that *the self-intersection groupoid of the atlas
of a presentation is the presenting groupoid*.

## The mathematical content

The composition law of Stacks 04T4 (4) is defined by lifting a composable pair of sections of `R`
to a composable pair of arrows of the self-intersection and reading off the section named by the
outer projection of Stacks 04T4 (3). To compute with it one needs an *explicit* arrow of the
self-intersection naming a given section `r` of `R`, and
`AlgebraicGeometry.Stack.GroupoidPresentation.atlasRelationArrow` is not one: it is produced by a
quasi-inverse. The explicit one is
`AlgebraicGeometry.Stack.GroupoidPresentation.atlasRelationTriple`, the triple
`(t r, s r, τ_r⁻¹)` whose comparison isomorphism is built from the canonical 2-morphism `τ` of
Stacks 044S; that it names `r` is
`...sectionOfObj_atlasRelationTriple`, proved by comparing both triples against the image of `r`
under the comparison of Stacks 04M9.

With that, the outer projection of Stacks 04T4 (3) carries the composite of the two comparison
isomorphisms (`AlgebraicGeometry.Stack.SelfIntersection.composition_iso`), so the whole
identification reduces to one fact about `τ`: **it is multiplicative**, which is
`AlgebraicGeometry.Stack.quotientStackTwoArrow_app_compose`.

## Main definitions

* `AlgebraicGeometry.Stack.GroupoidPresentation.atlasRelationTriple`: the explicit triple of the
  self-intersection of the atlas naming an arrow `r` of `R`.
* `AlgebraicGeometry.Stack.GroupoidPresentation.atlasComposableTriple`: the composable pair of
  arrows of the self-intersection attached to a composable pair of arrows of `R`.

## Main results

* `AlgebraicGeometry.Stack.GroupoidPresentation.sectionOfObj_atlasRelationTriple`: the explicit
  triple of `r` names `r`.
* `AlgebraicGeometry.Stack.GroupoidPresentation.composition_obj_atlasComposableTriple`: the
  composite of the two explicit triples of a composable pair is the explicit triple of the
  composite arrow.
* `AlgebraicGeometry.Stack.GroupoidPresentation.compositionLaw_app_atlasRelationEquivalence` and
  `...compose_atlasSelfIntersectionGroupoid`: **the identification** — the composition law of the
  self-intersection groupoid of the atlas is the composition law of `P`'s own groupoid.

## References

* [Stacks Project, Tag 044S](https://stacks.math.columbia.edu/tag/044S)
* [Stacks Project, Tag 04M9](https://stacks.math.columbia.edu/tag/04M9)
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

/-- The chosen equivalence over the site of the universe-enlarged apex `𝒮_U^+ ×_𝒳 𝒮_U^+` with the
arrow space: the second half of
`AlgebraicGeometry.Stack.GroupoidPresentation.atlasRelationEquivalence`. -/
noncomputable abbrev atlasArrowEquivalence :
    StacksRepresentableCFG.EquivalenceOver (atlasRelationBaseProjection P)
      (presheafOfCategories (P.groupoid.arrows.obj ⋙ typeToCat)).p :=
  (atlasArrowBaseEquivalence P).symm.trans (atlasArrowLiftEquivalence P).symm

variable {W : BigFppfOver B S hS}

/-- **The triple of the self-intersection of the atlas attached to an arrow `r` of `R`,
explicitly**: its target is the target of `r`, its source is the source of `r`, and its
comparison isomorphism is the inverse of the image in `𝒳` of the canonical 2-morphism of
Stacks 044S at `r`. Unlike
`AlgebraicGeometry.Stack.GroupoidPresentation.atlasRelationArrow` it involves no quasi-inverse,
which is what makes the composition law computable with it. -/
noncomputable def atlasRelationTriple (r : P.groupoid.arrows.obj.obj (op W)) :
    (SelfIntersection.relation B S hS (objectStack P) 𝒳 (atlasMap P).hom).val.obj where
  base := W
  x := ⟨W, Discrete.mk (P.groupoid.target.hom.app (op W) r)⟩
  y := ⟨W, Discrete.mk (P.groupoid.source.hom.app (op W) r)⟩
  hx := rfl
  hy := rfl
  iso := ((arrowToAtlasRelationBase P).obj ⟨W, Discrete.mk r⟩).iso.symm
  vertical := by
    have hv : 𝒳.val.p.IsHomLift (𝟙 W)
        ((arrowToAtlasRelationBase P).obj ⟨W, Discrete.mk r⟩).iso.hom :=
      ((arrowToAtlasRelationBase P).obj ⟨W, Discrete.mk r⟩).vertical
    exact CategoryTheory.IsHomLift.lift_id_inv 𝒳.val.p W
      ((arrowToAtlasRelationBase P).obj ⟨W, Discrete.mk r⟩).iso

/-- The target of the explicit triple of `r` is the target of `r`. -/
@[simp] theorem atlasRelationTriple_x (r : P.groupoid.arrows.obj.obj (op W)) :
    (atlasRelationTriple P r).x =
      ⟨W, Discrete.mk (P.groupoid.target.hom.app (op W) r)⟩ := rfl

/-- The source of the explicit triple of `r` is the source of `r`. -/
@[simp] theorem atlasRelationTriple_y (r : P.groupoid.arrows.obj.obj (op W)) :
    (atlasRelationTriple P r).y =
      ⟨W, Discrete.mk (P.groupoid.source.hom.app (op W) r)⟩ := rfl

/-- The inverse of the comparison isomorphism of the explicit triple of `r` is the image in `𝒳`
of the 2-morphism of Stacks 044S at `r`. -/
@[simp] theorem atlasRelationTriple_iso_inv (r : P.groupoid.arrows.obj.obj (op W)) :
    (atlasRelationTriple P r).iso.inv =
      ((arrowToAtlasRelationBase P).obj ⟨W, Discrete.mk r⟩).iso.hom := rfl

/-- The exchanged comparison carries the explicit triple of `r` to the image of `r` under the
comparison of Stacks 04M9, on the nose. -/
theorem atlasRelationToBaseSwap_obj_atlasRelationTriple
    (r : P.groupoid.arrows.obj.obj (op W)) :
    (atlasRelationToBaseSwap P).obj (atlasRelationTriple P r) =
      atlasRelationArrowImage P r := rfl

/-- **The explicit triple of `r` names `r`.** Both it and the triple produced by the
quasi-inverse are carried by the exchanged comparison to the image of `r`, the second only up to
the counit, and naming a section is insensitive to a vertical morphism. -/
theorem sectionOfObj_atlasRelationTriple (r : P.groupoid.arrows.obj.obj (op W)) :
    PresheafOfCategories.sectionOfObj (atlasRelationEquivalence P)
        (atlasRelationTriple P r) rfl = r :=
  have hswap : (atlasRelationBaseProjection P).obj
      ((atlasRelationToBaseSwap P).obj (atlasRelationArrow P r)) = W :=
    (Functor.congr_obj (atlasRelationToBaseSwap_comp_projection P)
      (atlasRelationArrow P r)).trans (atlasRelationArrow_over P r)
  have e1 : PresheafOfCategories.sectionOfObj (atlasRelationEquivalence P)
        (atlasRelationTriple P r) rfl =
      PresheafOfCategories.sectionOfObj (atlasArrowEquivalence P)
        (atlasRelationArrowImage P r) (atlasRelationArrowImage_over P r) := rfl
  have e2 : PresheafOfCategories.sectionOfObj (atlasRelationEquivalence P)
        (atlasRelationArrow P r) (atlasRelationArrow_over P r) =
      PresheafOfCategories.sectionOfObj (atlasArrowEquivalence P)
        ((atlasRelationToBaseSwap P).obj (atlasRelationArrow P r)) hswap := rfl
  have e3 : PresheafOfCategories.sectionOfObj (atlasArrowEquivalence P)
        ((atlasRelationToBaseSwap P).obj (atlasRelationArrow P r)) hswap =
      PresheafOfCategories.sectionOfObj (atlasArrowEquivalence P)
        (atlasRelationArrowImage P r) (atlasRelationArrowImage_over P r) :=
    PresheafOfCategories.sectionOfObj_eq_of_hom (atlasArrowEquivalence P) hswap
      (atlasRelationArrowImage_over P r) (atlasRelationArrowCounit P r)
      (isHomLift_atlasRelationArrowCounit P r)
  e1.trans (e3.symm.trans (e2.symm.trans (sectionOfObj_atlasRelationArrow P r)))

section Composition

variable (a b : P.groupoid.arrows.obj.obj (op W))

/-- Equal sections of the object space over `W` give equal objects of the object stack. -/
private theorem objectStack_mk_congr {x y : P.groupoid.objects.obj.obj (op W)} (h : x = y) :
    (⟨W, Discrete.mk x⟩ : (objectStack P).val.obj) = ⟨W, Discrete.mk y⟩ :=
  congrArg (fun z => (⟨W, Discrete.mk z⟩ : (objectStack P).val.obj)) h

/-- The source of a composite of two composable arrows is the source of the second factor. -/
theorem source_compose
    (h : P.groupoid.source.hom.app (op W) a = P.groupoid.target.hom.app (op W) b) :
    P.groupoid.source.hom.app (op W)
        (P.groupoid.toGroupoidInFunctors.compose (op W) a b h) =
      P.groupoid.source.hom.app (op W) b :=
  (P.groupoid.toGroupoidInFunctors.pointwiseData (op W)).source_comp a b h

/-- The target of a composite of two composable arrows is the target of the first factor. -/
theorem target_compose
    (h : P.groupoid.source.hom.app (op W) a = P.groupoid.target.hom.app (op W) b) :
    P.groupoid.target.hom.app (op W)
        (P.groupoid.toGroupoidInFunctors.compose (op W) a b h) =
      P.groupoid.target.hom.app (op W) a :=
  (P.groupoid.toGroupoidInFunctors.pointwiseData (op W)).target_comp a b h

/-- **The comparison isomorphism of Stacks 04M9 is multiplicative**, read in `𝒳`: the image of
the 2-morphism of Stacks 044S at a composite is the composite of the images at the two factors.
The three transports identify the endpoints, and they are hypotheses rather than terms so that a
caller may supply whichever proofs its own goal carries. -/
theorem arrowToAtlasRelationBase_iso_hom_compose
    (h : P.groupoid.source.hom.app (op W) a = P.groupoid.target.hom.app (op W) b)
    (E1 : (atlasMap P).hom.toFunctor.obj
        ⟨W, Discrete.mk (P.groupoid.source.hom.app (op W)
          (P.groupoid.toGroupoidInFunctors.compose (op W) a b h))⟩ =
      (atlasMap P).hom.toFunctor.obj ⟨W, Discrete.mk (P.groupoid.source.hom.app (op W) b)⟩)
    (E2 : (atlasMap P).hom.toFunctor.obj
        ⟨W, Discrete.mk (P.groupoid.target.hom.app (op W) b)⟩ =
      (atlasMap P).hom.toFunctor.obj ⟨W, Discrete.mk (P.groupoid.source.hom.app (op W) a)⟩)
    (E3 : (atlasMap P).hom.toFunctor.obj
        ⟨W, Discrete.mk (P.groupoid.target.hom.app (op W) a)⟩ =
      (atlasMap P).hom.toFunctor.obj
        ⟨W, Discrete.mk (P.groupoid.target.hom.app (op W)
          (P.groupoid.toGroupoidInFunctors.compose (op W) a b h))⟩) :
    ((arrowToAtlasRelationBase P).obj
        ⟨W, Discrete.mk (P.groupoid.toGroupoidInFunctors.compose (op W) a b h)⟩).iso.hom =
      eqToHom E1 ≫ ((arrowToAtlasRelationBase P).obj ⟨W, Discrete.mk b⟩).iso.hom ≫
        eqToHom E2 ≫ ((arrowToAtlasRelationBase P).obj ⟨W, Discrete.mk a⟩).iso.hom ≫
          eqToHom E3 := by
  have hs := congrArg (quotientStackProjection P.groupoid).obj
    (objectStack_mk_congr P (source_compose P a b h))
  have hm := congrArg (quotientStackProjection P.groupoid).obj (objectStack_mk_congr P h.symm)
  have ht := congrArg (quotientStackProjection P.groupoid).obj
    (objectStack_mk_congr P (target_compose P a b h).symm)
  have hτ := quotientStackTwoArrow_app_compose P.groupoid a b h hs hm ht
  have himg := congrArg P.basedFunctor.toFunctor.map hτ
  exact himg.trans (map_eqToHom_comp_two_comp_eqToHom P.basedFunctor.toFunctor hs _ hm _ ht)

/-- The identification of the middle objects of the two explicit triples attached to a composable
pair: the source of the first factor is the target of the second. -/
theorem atlasRelationTriple_middle
    (h : P.groupoid.source.hom.app (op W) a = P.groupoid.target.hom.app (op W) b) :
    ((atlasRelationTriple P a).y : (objectStack P).val.obj) = (atlasRelationTriple P b).x :=
  objectStack_mk_congr P h

/-- **The composable pair of arrows of the self-intersection attached to a composable pair of
arrows of `R`**: the two explicit triples, glued at the transport identifying the middle
objects. -/
noncomputable def atlasComposableTriple
    (h : P.groupoid.source.hom.app (op W) a = P.groupoid.target.hom.app (op W) b) :
    SelfIntersection.composable B S hS (objectStack P) 𝒳 (atlasMap P).hom :=
  SelfIntersection.composableMk (γ := atlasRelationTriple P a) (ϱ := atlasRelationTriple P b)
    rfl rfl
    (Functor.Fiber.isoMk (eqToIso (atlasRelationTriple_middle P a b h))
      (Functor.isHomLift_id_eqToHom (objectStack P).val.p
        (atlasRelationTriple_middle P a b h)))

/-- The first component of the composable pair is the explicit triple of the first factor. -/
@[simp] theorem atlasComposableTriple_x
    (h : P.groupoid.source.hom.app (op W) a = P.groupoid.target.hom.app (op W) b) :
    (atlasComposableTriple P a b h).x = atlasRelationTriple P a := rfl

/-- The second component of the composable pair is the explicit triple of the second factor. -/
@[simp] theorem atlasComposableTriple_y
    (h : P.groupoid.source.hom.app (op W) a = P.groupoid.target.hom.app (op W) b) :
    (atlasComposableTriple P a b h).y = atlasRelationTriple P b := rfl

/-- The composable pair lies over the test object of the two arrows. -/
@[simp] theorem atlasComposableTriple_base
    (h : P.groupoid.source.hom.app (op W) a = P.groupoid.target.hom.app (op W) b) :
    (atlasComposableTriple P a b h).base = W := rfl

/-- The inverse of the comparison isomorphism of the composite of the two explicit triples: by
Stacks 04T4 (3) the outer projection carries the composite of the three isomorphisms. -/
theorem composition_obj_atlasComposableTriple_iso_inv
    (h : P.groupoid.source.hom.app (op W) a = P.groupoid.target.hom.app (op W) b) :
    ((SelfIntersection.composition B S hS (objectStack P) 𝒳 (atlasMap P).hom).toFunctor.obj
        (atlasComposableTriple P a b h)).iso.inv =
      (((arrowToAtlasRelationBase P).obj ⟨W, Discrete.mk b⟩).iso.hom ≫
          (atlasMap P).hom.toFunctor.map
            (eqToHom (atlasRelationTriple_middle P a b h).symm)) ≫
        ((arrowToAtlasRelationBase P).obj ⟨W, Discrete.mk a⟩).iso.hom := rfl

/-- **The composite of the two explicit triples is the explicit triple of the composite.** This
is Stacks 04T4 (3) at the atlas of a presentation: the outer projection carries the composite of
the two comparison isomorphisms, and the 2-morphism of Stacks 044S is multiplicative. -/
theorem composition_obj_atlasComposableTriple
    (h : P.groupoid.source.hom.app (op W) a = P.groupoid.target.hom.app (op W) b) :
    (SelfIntersection.composition B S hS (objectStack P) 𝒳 (atlasMap P).hom).toFunctor.obj
        (atlasComposableTriple P a b h) =
      atlasRelationTriple P (P.groupoid.toGroupoidInFunctors.compose (op W) a b h) := by
  have hx : ((SelfIntersection.composition B S hS (objectStack P) 𝒳
          (atlasMap P).hom).toFunctor.obj (atlasComposableTriple P a b h)).x =
      (atlasRelationTriple P
        (P.groupoid.toGroupoidInFunctors.compose (op W) a b h)).x :=
    objectStack_mk_congr P (target_compose P a b h).symm
  have hy : ((SelfIntersection.composition B S hS (objectStack P) 𝒳
          (atlasMap P).hom).toFunctor.obj (atlasComposableTriple P a b h)).y =
      (atlasRelationTriple P
        (P.groupoid.toGroupoidInFunctors.compose (op W) a b h)).y :=
    objectStack_mk_congr P (source_compose P a b h).symm
  refine TwoFibreProductOver.ext_of_heq_iso rfl hx hy ?_
  have E1 : (atlasMap P).hom.toFunctor.obj
        (atlasRelationTriple P
          (P.groupoid.toGroupoidInFunctors.compose (op W) a b h)).y =
      (atlasMap P).hom.toFunctor.obj (atlasRelationTriple P b).y :=
    congrArg (atlasMap P).hom.toFunctor.obj
      (objectStack_mk_congr P (source_compose P a b h))
  have E2 : (atlasMap P).hom.toFunctor.obj (atlasRelationTriple P b).x =
      (atlasMap P).hom.toFunctor.obj (atlasRelationTriple P a).y :=
    congrArg (atlasMap P).hom.toFunctor.obj (atlasRelationTriple_middle P a b h).symm
  have E3 : (atlasMap P).hom.toFunctor.obj (atlasRelationTriple P a).x =
      (atlasMap P).hom.toFunctor.obj
        (atlasRelationTriple P
          (P.groupoid.toGroupoidInFunctors.compose (op W) a b h)).x :=
    congrArg (atlasMap P).hom.toFunctor.obj hx
  have hAc : (atlasRelationTriple P
        (P.groupoid.toGroupoidInFunctors.compose (op W) a b h)).iso.inv =
      eqToHom E1 ≫ ((arrowToAtlasRelationBase P).obj ⟨W, Discrete.mk b⟩).iso.hom ≫
        eqToHom E2 ≫ ((arrowToAtlasRelationBase P).obj ⟨W, Discrete.mk a⟩).iso.hom ≫
          eqToHom E3 :=
    arrowToAtlasRelationBase_iso_hom_compose P a b h E1 E2 E3
  have hmap : (atlasMap P).hom.toFunctor.map
        (eqToHom (atlasRelationTriple_middle P a b h).symm) = eqToHom E2 :=
    CategoryTheory.eqToHom_map (atlasMap P).hom.toFunctor _
  refine heq_iso_of_inv_eq_conj E3 E1.symm _ _ ?_
  refine (composition_obj_atlasComposableTriple_iso_inv P a b h).trans ?_
  refine Eq.trans (congrArg (fun m =>
      (((arrowToAtlasRelationBase P).obj ⟨W, Discrete.mk b⟩).iso.hom ≫ m) ≫
        ((arrowToAtlasRelationBase P).obj ⟨W, Discrete.mk a⟩).iso.hom) hmap) ?_
  refine Eq.trans ?_ (congrArg (fun m => eqToHom E1.symm ≫ m ≫ eqToHom E3.symm) hAc).symm
  exact eqToHom_conj_cancel E1 E3 _ _ _

/-- **The composition law of the self-intersection groupoid of the atlas is the composition of
the presenting groupoid**, the remaining identification of Stacks 04T4 (4) at the atlas of a
presentation. The two explicit triples of a composable pair of arrows of `R` form a composable
pair of the self-intersection naming that pair, and their composite is the explicit triple of the
composite arrow. -/
theorem compositionLaw_app_atlasRelationEquivalence
    (h : P.groupoid.source.hom.app (op W) a = P.groupoid.target.hom.app (op W) b)
    (h' : (SelfIntersection.relationSourceMap (atlasObjectEquivalence P)
            (atlasRelationEquivalence P)).app (op W) a =
      (SelfIntersection.relationTargetMap (atlasObjectEquivalence P)
            (atlasRelationEquivalence P)).app (op W) b) :
    (SelfIntersection.compositionLaw (atlasObjectEquivalence P) (atlasRelationEquivalence P)
          (isFiberedInSetoids_objectStack P)).app (op W) ⟨(a, b), h'⟩ =
      P.groupoid.toGroupoidInFunctors.compose (op W) a b h := by
  have hq : (SelfIntersection.compositionLaw (atlasObjectEquivalence P)
        (atlasRelationEquivalence P) (isFiberedInSetoids_objectStack P)).app (op W)
          ⟨(a, b), h'⟩ =
      SelfIntersection.compositionValue (atlasObjectEquivalence P)
        (atlasRelationEquivalence P) (isFiberedInSetoids_objectStack P) ⟨(a, b), h'⟩ := rfl
  have key := SelfIntersection.sectionOfObj_composition_eq_compositionValue
    (atlasObjectEquivalence P) (atlasRelationEquivalence P)
    (isFiberedInSetoids_objectStack P) ⟨(a, b), h'⟩ (atlasComposableTriple P a b h) rfl
    (sectionOfObj_atlasRelationTriple P a) (sectionOfObj_atlasRelationTriple P b)
  have transport : ∀ (z : (SelfIntersection.relation B S hS (objectStack P) 𝒳
          (atlasMap P).hom).val.obj)
      (hz : (SelfIntersection.relation B S hS (objectStack P) 𝒳
        (atlasMap P).hom).val.p.obj z = W)
      (_ : z = atlasRelationTriple P (P.groupoid.toGroupoidInFunctors.compose (op W) a b h)),
      PresheafOfCategories.sectionOfObj (atlasRelationEquivalence P) z hz =
        PresheafOfCategories.sectionOfObj (atlasRelationEquivalence P)
          (atlasRelationTriple P
            (P.groupoid.toGroupoidInFunctors.compose (op W) a b h)) rfl := by
    intro z hz hzz
    subst hzz
    rfl
  exact hq.trans (key.symm.trans ((transport _ _
    (composition_obj_atlasComposableTriple P a b h)).trans
      (sectionOfObj_atlasRelationTriple P _)))

/-- **The composition law of the groupoid in algebraic spaces of Stacks 04T4 (4) at the atlas of
a presentation is the composition law of the presenting groupoid itself.** Together with
`...atlasSelfIntersectionGroupoid_objects`, `..._arrows`, `..._source` and `..._target` this says
that the self-intersection groupoid of the atlas *is* the presenting groupoid. -/
theorem compose_atlasSelfIntersectionGroupoid
    (h : P.groupoid.source.hom.app (op W) a = P.groupoid.target.hom.app (op W) b)
    (h' : (atlasSelfIntersectionGroupoid P).source.hom.app (op W) a =
      (atlasSelfIntersectionGroupoid P).target.hom.app (op W) b) :
    (atlasSelfIntersectionGroupoid P).toGroupoidInFunctors.compose (op W) a b h' =
      P.groupoid.toGroupoidInFunctors.compose (op W) a b h :=
  have h1 : (atlasSelfIntersectionGroupoid P).toGroupoidInFunctors.compose (op W) a b h' =
      (SelfIntersection.compositionLaw (atlasObjectEquivalence P) (atlasRelationEquivalence P)
        (isFiberedInSetoids_objectStack P)).app (op W) ⟨(a, b), h'⟩ :=
    compose_ofComposable P.groupoid.objects P.groupoid.arrows
      (ObjectProperty.homMk (SelfIntersection.relationSourceMap (atlasObjectEquivalence P)
        (atlasRelationEquivalence P)))
      (ObjectProperty.homMk (SelfIntersection.relationTargetMap (atlasObjectEquivalence P)
        (atlasRelationEquivalence P)))
      (SelfIntersection.compositionLaw (atlasObjectEquivalence P) (atlasRelationEquivalence P)
        (isFiberedInSetoids_objectStack P))
      (SelfIntersection.nonempty_pointwiseGroupoid (atlasObjectEquivalence P)
        (atlasRelationEquivalence P) (isFiberedInSetoids_objectStack P))
      (op W) a b h'
  h1.trans (compositionLaw_app_atlasRelationEquivalence P a b h h')

end Composition

end AlgebraicGeometry.Stack.GroupoidPresentation

end
