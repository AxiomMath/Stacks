module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStack
public import StacksFrontier.CategoryTheory.Sites.Stackification.UniversalPropertyGroupoid
public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PushforwardStack
public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PushforwardMorSheaf
public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PullbackAdjunction

/-!
# Functoriality of quotient stacks

A morphism `f : (U, R, s, t, c) ⟶ (U', R', s', t', c')` of groupoids in algebraic spaces over a
fixed algebraic space `B` induces a canonical 1-morphism `[f] : [U/R] ⟶ [U'/R']` of quotient
stacks. This file constructs it, and exhibits the 2-isomorphism that makes it compatible with the
two presentations.

## Main definitions

* `AlgebraicGeometry.Stack.quotientPointwiseMap`: the induced map of pointwise groupoid
  fibrations.
* `AlgebraicGeometry.Stack.pointwiseToQuotientStackBased`: the canonical map from the pointwise
  groupoid fibration to the quotient stack, packaged as a functor over the site.
* `AlgebraicGeometry.Stack.quotientStackMap`: the induced 1-morphism `[f]`.

## Main results

* `AlgebraicGeometry.Stack.quotientPointwiseMapData`: the strict natural transformation of the
  groupoid-valued presentations underlying `[f]`, together with the identification of its
  components and of its naturality isomorphisms.
* `AlgebraicGeometry.Stack.quotientStackMap_commutes`: the 2-isomorphism over the site between
  the two routes from the presentation of `[U/R]` to `[U'/R']`.
* `AlgebraicGeometry.Stack.evaluation_comp` and `AlgebraicGeometry.Stack.evaluation_id`:
  evaluation of a morphism of groupoids in presheaves at a test object is functorial, on the nose.

## References

* [Stacks Project, Tag 0436](https://stacks.math.columbia.edu/tag/0436)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 046Q](https://stacks.math.columbia.edu/tag/046Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Pseudofunctor Opposite
open scoped CategoryTheory.Pseudofunctor.StrongTrans

namespace AlgebraicGeometry.Stack

universe u v w u₁ u₂

/- The presenting pseudofunctor of the pointwise groupoid fibration is reached through
`CategoryTheory.Functor.toPseudofunctor'` and the groupoid-to-category inclusion, none of which
the `implicit` transparency level unfolds; naming that chain is what lets the ordinary tactics
see through its objects and morphisms. -/
attribute [local implicit_reducible] Functor.toPseudofunctor'
  pseudofunctorOfIsLocallyDiscrete Quiver.Hom.toLoc BasedCategory.ofFunctor
  Grpd.forgetToCat Grpd.of

/-- Two functors into an evaluated groupoid in presheaves agree once they agree on objects and
on the arrow elements representing their images of morphisms. -/
private theorem functor_ext_of_evaluationArrowEquiv {D : Type u} [Category.{v} D]
    (K : Deformation.GroupoidInFunctors.{u, v, w} D) (T : D) {J : Type*} [Category J]
    (F F' : J ⥤ K.Evaluation T) (hobj : ∀ x, F.obj x = F'.obj x)
    (h : ∀ {x y : J} (m : x ⟶ y), (K.evaluationArrowEquiv T _ _ (F.map m)).1 =
      (K.evaluationArrowEquiv T _ _ (F'.map m)).1) : F = F' :=
  CategoryTheory.Functor.ext hobj fun _ _ m =>
    Deformation.hom_eq_transport K T (hobj _) (hobj _) _ _ (h m)

/-- **Evaluation of a composite of morphisms of groupoids in presheaves is the composite of the
evaluations**, on the nose. -/
theorem evaluation_comp {D : Type u} [Category.{v} D]
    {G H K : Deformation.GroupoidInFunctors.{u, v, w} D}
    (φ : Deformation.GroupoidInFunctors.Hom G H)
    (ψ : Deformation.GroupoidInFunctors.Hom H K) (T : D) :
    (Deformation.GroupoidInFunctors.Hom.comp φ ψ).evaluation T =
      φ.evaluation T ⋙ ψ.evaluation T := by
  refine functor_ext_of_evaluationArrowEquiv K T _ _ (fun _ => rfl) fun m => ?_
  exact (Deformation.GroupoidInFunctors.Hom.evaluation_map_arrow _ T m).trans
    ((congrArg (ψ.mapArrows.app T) (Deformation.GroupoidInFunctors.Hom.evaluation_map_arrow
      φ T m).symm).trans
    (Deformation.GroupoidInFunctors.Hom.evaluation_map_arrow ψ T _).symm)

/-- **Evaluation of the identity morphism of a groupoid in presheaves is the identity functor**,
on the nose. -/
theorem evaluation_id {D : Type u} [Category.{v} D]
    (G : Deformation.GroupoidInFunctors.{u, v, w} D) (T : D) :
    (Deformation.GroupoidInFunctors.Hom.id G).evaluation T =
      CategoryTheory.Functor.id (G.Evaluation T) :=
  functor_ext_of_evaluationArrowEquiv G T _ _ (fun _ => rfl) fun m =>
    Deformation.GroupoidInFunctors.Hom.evaluation_map_arrow
      (Deformation.GroupoidInFunctors.Hom.id G) T m

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- Evaluating a morphism of groupoids in presheaves commutes strictly with pullback of points:
the square of evaluated functors over a morphism of test objects commutes on the nose. -/
theorem evaluation_hom_naturality {G H : GroupoidInAlgebraicSpaces C S hS B}
    (f : GroupoidInAlgebraicSpaces.Hom G H)
    {a b : LocallyDiscrete (BigFppfOver C S hS)ᵒᵖ} (g : a ⟶ b) :
    ((evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙ Grpd.forgetToCat).toPseudofunctor').map
          g ≫ (f.toGroupoidHom.evaluation b.as).toCatHom =
      (f.toGroupoidHom.evaluation a.as).toCatHom ≫
        ((evaluationGroupoidFunctor H.toGroupoidInFunctors ⋙
          Grpd.forgetToCat).toPseudofunctor').map g := by
  dsimp only [Grpd.of, Cat.of] at *
  change ((evaluationGroupoidFunctor G.toGroupoidInFunctors).map g.as).toCatHom ≫
      (f.toGroupoidHom.evaluation b.as).toCatHom =
    (f.toGroupoidHom.evaluation a.as).toCatHom ≫
      ((evaluationGroupoidFunctor H.toGroupoidInFunctors).map g.as).toCatHom
  apply Cat.Hom.ext
  let hObj := fun x => f.toGroupoidHom.mapObjects.naturality_apply g.as x
  refine functor_ext_of_evaluationArrowEquiv H.toGroupoidInFunctors b.as _ _ hObj ?_
  intro x y m
  change (H.toGroupoidInFunctors.evaluationArrowEquiv b.as _ _
      ((f.toGroupoidHom.evaluation b.as).map
        ((Deformation.evaluationMap G.toGroupoidInFunctors g.as).map m))).1 =
    (H.toGroupoidInFunctors.evaluationArrowEquiv b.as _ _
      ((Deformation.evaluationMap H.toGroupoidInFunctors g.as).map
        ((f.toGroupoidHom.evaluation a.as).map m))).1
  simp only [Deformation.GroupoidInFunctors.Hom.evaluation_map_arrow,
    Deformation.evaluationMap_map_arrow]
  exact f.toGroupoidHom.mapArrows.naturality_apply g.as
    (G.toGroupoidInFunctors.evaluationArrowEquiv a.as x y m).1

/-- The strict natural map between the presenting pseudofunctors of the two pointwise groupoid
fibrations: its component at a test object is the evaluated functor of the given groupoid
morphism, and its naturality isomorphisms are transports. -/
@[stacks 046Q "the strict map on the presenting groupoids"]
noncomputable def quotientPointwiseMapData {G H : GroupoidInAlgebraicSpaces C S hS B}
    (f : GroupoidInAlgebraicSpaces.Hom G H) :
    { α : (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
            Grpd.forgetToCat).toPseudofunctor' ⟶
          (evaluationGroupoidFunctor H.toGroupoidInFunctors ⋙
            Grpd.forgetToCat).toPseudofunctor' //
      (∀ T : BigFppfOver C S hS,
        (α.app ⟨op T⟩).toFunctor = f.toGroupoidHom.evaluation (op T)) ∧
      (∀ {a b} (g : a ⟶ b),
        ∃ h : ((evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
              Grpd.forgetToCat).toPseudofunctor').map g ≫ α.app b =
            α.app a ≫ ((evaluationGroupoidFunctor H.toGroupoidInFunctors ⋙
              Grpd.forgetToCat).toPseudofunctor').map g,
          α.naturality g = eqToIso h) } := by
  let α : (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
      Grpd.forgetToCat).toPseudofunctor' ⟶
      (evaluationGroupoidFunctor H.toGroupoidInFunctors ⋙
      Grpd.forgetToCat).toPseudofunctor' := {
    app := fun a => (f.toGroupoidHom.evaluation a.as).toCatHom
    naturality := fun g => eqToIso (evaluation_hom_naturality f g)
    naturality_naturality := by
      intro a b f g η
      obtain rfl := obj_ext_of_isDiscrete η
      have hη : η = 𝟙 f := Subsingleton.elim _ _
      rw [hη]
      let F := (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
        Grpd.forgetToCat).toPseudofunctor'
      let K := (evaluationGroupoidFunctor H.toGroupoidInFunctors ⋙
        Grpd.forgetToCat).toPseudofunctor'
      have hF : F.map₂ (𝟙 f) = 𝟙 (F.map f) := F.toPrelaxFunctor.map₂_id f
      have hK : K.map₂ (𝟙 f) = 𝟙 (K.map f) := K.toPrelaxFunctor.map₂_id f
      rw [hF, hK]
      rw [Bicategory.id_whiskerRight, Bicategory.whiskerLeft_id]
      simp
    naturality_id := by intro a; cat_disch
    naturality_comp := by intro a b c f g; cat_disch
  }
  refine ⟨α, ?_⟩
  · constructor
    · intro T
      rfl
    · intro a b g
      refine ⟨evaluation_hom_naturality f g, ?_⟩
      rfl

/-- The map between the pointwise groupoid fibrations induced by a morphism of groupoids in
algebraic spaces. -/
noncomputable def quotientPointwiseMap {G H : GroupoidInAlgebraicSpaces C S hS B}
    (f : GroupoidInAlgebraicSpaces.Hom G H) :
    BasedFunctor (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors))
      (presheafOfGroupoids (evaluationGroupoidFunctor H.toGroupoidInFunctors)) where
  toFunctor := CoGrothendieck.map (quotientPointwiseMapData f).val
  w := CoGrothendieck.map_comp_forget (quotientPointwiseMapData f).val

/-- The canonical map from the pointwise groupoid fibration to the quotient stack, packaged as a
functor over the big fppf site. -/
noncomputable def pointwiseToQuotientStackBased (G : GroupoidInAlgebraicSpaces C S hS B) :
    BasedFunctor (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors))
      (quotientStack G) where
  toFunctor := pointwiseToQuotientStack G
  w := (isFibredOneMorphism_pointwiseToQuotientStack G).comp_eq

/-- The composite from the presentation of `[U/R]` to `[U'/R']` through the pointwise groupoid
fibrations. -/
noncomputable def quotientMapUnderlying {G H : GroupoidInAlgebraicSpaces C S hS B}
    (f : GroupoidInAlgebraicSpaces.Hom G H) :
    (quotientPrestack G).obj ⥤ (quotientStack H).obj :=
  (quotientPrestackEquivalence G).inverse ⋙
    (quotientPointwiseMap f).toFunctor ⋙ pointwiseToQuotientStack H

/-- `AlgebraicGeometry.Stack.quotientMapUnderlying f` lies strictly over the site. -/
theorem quotientMapUnderlying_comp {G H : GroupoidInAlgebraicSpaces C S hS B}
    (f : GroupoidInAlgebraicSpaces.Hom G H) :
    quotientMapUnderlying f ⋙ (quotientStack H).p = (quotientPrestack G).p := by
  dsimp [quotientMapUnderlying]
  simp only [Functor.assoc, (isFibredOneMorphism_pointwiseToQuotientStack H).comp_eq,
    (quotientPointwiseMap f).w]
  rfl

/-- The extension of `quotientMapUnderlying` along the stackification, by the universal property
of Stacks 0436. -/
noncomputable def quotientMapExtension {G H : GroupoidInAlgebraicSpaces C S hS B}
    (f : GroupoidInAlgebraicSpaces.Hom G H) :
    (quotientStack G).obj ⥤ (quotientStack H).obj := by
  let hF := (isFiberedInGroupoids_quotientStack H).isFibredOneMorphism
    (quotientMapUnderlying_comp f)
  exact CategoryTheory.Functor.Stackification.extendGroupoid
    (isFiberedInGroupoids_quotientPrestack G)
    (isFiberedInGroupoids_quotientStack G) (isStack_quotientStack G)
    (isFiberedInGroupoids_quotientStack H) (isStack_quotientStack H)
    (isFibredOneMorphism_toQuotientStack G).comp_eq (quotientMapUnderlying_comp f)
    (isLocallyBijective_toQuotientStack G) (essImage_toQuotientStack G)

/-- The extension is strictly over the site. -/
theorem quotientMapExtension_comp {G H : GroupoidInAlgebraicSpaces C S hS B}
    (f : GroupoidInAlgebraicSpaces.Hom G H) :
    quotientMapExtension f ⋙ (quotientStack H).p = (quotientStack G).p := by
  dsimp [quotientMapExtension]
  let hF := (isFiberedInGroupoids_quotientStack H).isFibredOneMorphism
    (quotientMapUnderlying_comp f)
  exact CategoryTheory.Functor.Stackification.extendGroupoid_comp_eq
    (isFiberedInGroupoids_quotientPrestack G)
    (isFiberedInGroupoids_quotientStack G) (isStack_quotientStack G)
    (isFiberedInGroupoids_quotientStack H) (isStack_quotientStack H)
    (isFibredOneMorphism_toQuotientStack G).comp_eq (quotientMapUnderlying_comp f)
    (isLocallyBijective_toQuotientStack G) (essImage_toQuotientStack G)

/-- The 2-isomorphism filling the triangle of the universal property. -/
noncomputable def quotientMapExtensionUnit {G H : GroupoidInAlgebraicSpaces C S hS B}
    (f : GroupoidInAlgebraicSpaces.Hom G H) :
    toQuotientStack G ⋙ quotientMapExtension f ≅ quotientMapUnderlying f :=
  CategoryTheory.Functor.Stackification.unitGroupoid
    (isFiberedInGroupoids_quotientPrestack G)
    (isFiberedInGroupoids_quotientStack G) (isStack_quotientStack G)
    (isFiberedInGroupoids_quotientStack H) (isStack_quotientStack H)
    (isFibredOneMorphism_toQuotientStack G).comp_eq (quotientMapUnderlying_comp f)
    (isLocallyBijective_toQuotientStack G) (essImage_toQuotientStack G)

/-- Every component of `AlgebraicGeometry.Stack.quotientMapExtensionUnit f` lies over an identity
of the site. -/
theorem quotientMapExtensionUnit_hom_isHomLift {G H : GroupoidInAlgebraicSpaces C S hS B}
    (f : GroupoidInAlgebraicSpaces.Hom G H) (x : (quotientPrestack G).obj) :
    (quotientStack H).p.IsHomLift (𝟙 ((quotientPrestack G).p.obj x))
      ((quotientMapExtensionUnit f).hom.app x) :=
  CategoryTheory.Functor.Stackification.isHomLift_unitGroupoid_app
    (isFiberedInGroupoids_quotientPrestack G) (isFiberedInGroupoids_quotientStack G)
    (isStack_quotientStack G) (isFiberedInGroupoids_quotientStack H) (isStack_quotientStack H)
    (isFibredOneMorphism_toQuotientStack G).comp_eq (quotientMapUnderlying_comp f)
    (isLocallyBijective_toQuotientStack G) (essImage_toQuotientStack G) x

/-- The canonical 1-morphism `[f] : [U/R] ⟶ [U'/R']` of quotient stacks induced
by a morphism of groupoids in algebraic spaces over the same base. -/
@[stacks 046Q "the induced morphism"]
noncomputable def quotientStackMap {G H : GroupoidInAlgebraicSpaces C S hS B}
    (f : GroupoidInAlgebraicSpaces.Hom G H) :
    BasedFunctor (quotientStack G) (quotientStack H) :=
  ⟨quotientMapExtension f, quotientMapExtension_comp f⟩

/- The 2-isomorphism below is whiskered from the unit of the universal property, whose target is
`quotientMapUnderlying f`; the whiskered composite is well typed only once that composite of
functors unfolds, so the tactics below have to see through it. -/
attribute [local implicit_reducible] quotientMapUnderlying pointwiseToQuotientStackBased
  pointwiseToQuotientStack quotientStackMap BasedFunctor.comp

/-- The induced 1-morphism intertwines the pointwise groupoid map with the two
stackification maps, naturally and over the site. -/
@[stacks 046Q "compatibility with the presentations"]
noncomputable def quotientStackMap_commutes {G H : GroupoidInAlgebraicSpaces C S hS B}
    (f : GroupoidInAlgebraicSpaces.Hom G H) :
    BasedFunctor.comp (quotientPointwiseMap f) (pointwiseToQuotientStackBased H) ≅
      BasedFunctor.comp (pointwiseToQuotientStackBased G) (quotientStackMap f) := by
  let e := quotientPrestackEquivalence G
  let φ :
      (BasedFunctor.comp (quotientPointwiseMap f) (pointwiseToQuotientStackBased H)).toFunctor ≅
        (BasedFunctor.comp (pointwiseToQuotientStackBased G) (quotientStackMap f)).toFunctor := by
    simpa [BasedFunctor.comp, quotientStackMap, pointwiseToQuotientStackBased,
      pointwiseToQuotientStack, quotientMapUnderlying, quotientPointwiseMap,
      Functor.assoc, Functor.id_comp] using
      (((CategoryTheory.Functor.isoWhiskerLeft e.functor (quotientMapExtensionUnit f)).trans
        (CategoryTheory.Functor.isoWhiskerRight e.unitIso.symm
          ((quotientPointwiseMap f).toFunctor ⋙ pointwiseToQuotientStack H))).symm)
  exact BasedNatIso.mkNatIso φ (by
    intro x
    let source := presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)
    have hbase : (quotientPrestack G).p.obj (e.functor.obj x) = source.p.obj x := rfl
    change (quotientStack H).p.IsHomLift (𝟙 (source.p.obj x)) _
    dsimp [φ]
    have hobj : x = e.inverse.obj (e.functor.obj x) := by
      dsimp [e, quotientPrestackEquivalence, ULiftHom.equiv]
      rfl
    have hunitEq : e.unitIso.hom.app x = eqToHom hobj := by
      dsimp [e, quotientPrestackEquivalence, ULiftHom.equiv, hobj]
      rfl
    have hunit : source.p.IsHomLift (𝟙 (source.p.obj x)) (e.unitIso.hom.app x) := by
      rw [hunitEq]
      exact IsHomLift.eqToHom_domain_lift_id hobj rfl
    have hmap₀ : (quotientStack H).p.IsHomLift (𝟙 (source.p.obj x))
        ((pointwiseToQuotientStackBased H).map
          ((quotientPointwiseMap f).map (e.unitIso.hom.app x))) := by
      infer_instance
    have hmap : (quotientStack H).p.IsHomLift
        (𝟙 ((quotientPrestack G).p.obj (e.functor.obj x)))
        ((pointwiseToQuotientStackBased H).map
          ((quotientPointwiseMap f).map (e.unitIso.hom.app x))) :=
      hmap₀
    have hunitInv : (quotientStack H).p.IsHomLift
        (𝟙 ((quotientPrestack G).p.obj (e.functor.obj x)))
        ((quotientMapExtensionUnit f).inv.app (e.functor.obj x)) :=
      @IsHomLift.lift_id_inv _ _ _ _ (quotientStack H).p _ _ _
        ((quotientMapExtensionUnit f).app (e.functor.obj x))
        (by simpa using quotientMapExtensionUnit_hom_isHomLift f (e.functor.obj x))
    exact @IsHomLift.comp_of_lift_id _ _ _ _ (quotientStack H).p _ _ _ _ _ _ hmap hunitInv)

end AlgebraicGeometry.Stack

end
