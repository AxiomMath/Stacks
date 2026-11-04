module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FunctorialityQuotientSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.Functoriality
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.ProjectionTwoArrow
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackProjection
public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PullbackStackCongruence
public import StacksFrontier.CategoryTheory.Sites.Stackification.UniversalPropertyUniqueness

/-!
# The square of quotient stacks of Section 78.21 and the 2-isomorphism filling it

Let `φ : G ⟶ G'` be a morphism of groupoids in algebraic spaces over an algebraic space `B` over
a scheme `S` of a big fppf site, written `f : U ⟶ U'` on objects and `f : R ⟶ R'` on arrows, and
let `(U'', R'', s'', t'', c'')` be the groupoid of Section 78.21 attached to it, with
`U'' = U ×_{f, U', t'} R'` and `R'' = R ×_{f ∘ s, U', t'} R'`. This file assembles the square

```
[U''/R''] ---------> 𝒮_{U'}
    |                   |
   [g]                 π'
    v                   v
  [U/R] ----[f]----> [U'/R']
```

out of the two legs built in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/FunctorialityQuotientSquare.lean`, and builds the
2-isomorphism filling it. The left leg is the quotient stack map of Stacks 046Q applied to the
projection `(U'', R'', s'', t'', c'') ⟶ (U, R, s, t, c)`, the upper leg is the descent to
`[U''/R'']` of the `R''`-invariant morphism `U'' ⟶ U'`, `(u, r') ↦ s'(r')`, and the right leg is
the canonical projection of Stacks 044R.

## Main definitions

* `AlgebraicGeometry.Stack.auxQuotientStackUpper`: the composite `[U''/R''] ⟶ 𝒮_{U'} ⟶ [U'/R']`
  of the upper and right legs.
* `AlgebraicGeometry.Stack.auxQuotientStackLower`: the composite `[U''/R''] ⟶ [U/R] ⟶ [U'/R']`
  of the left and lower legs.
* `AlgebraicGeometry.Stack.auxComparisonArrow`: at a point `(u, r')` of `U''` over a test object,
  the arrow `r'` of the groupoid `G'(T)` from `s'(r')` to `f(u)`.

## Main results

* `AlgebraicGeometry.Stack.quotientStackProjection_comp_auxQuotientToTargetObjects`: the upper leg
  restricts along the projection `𝒮_{U''} ⟶ [U''/R'']` to the morphism `U'' ⟶ U'` itself.
* `AlgebraicGeometry.Stack.auxComparisonIso`: the two composites
  `U'' ⟶ U'` and `U'' ⟶ U ⟶ U'` of the presentations are identified, on the presentation of
  `[U''/R'']`, by the arrow `r'`.
* `AlgebraicGeometry.Stack.auxQuotientStackSquare`: the square 2-commutes, which is the
  2-commutativity the comparison 1-morphism of Stacks 04Y4 is built from.

## Implementation notes

The 2-isomorphism filling the square is built on the *presentation* of `[U''/R'']` and then
extended across the stackification. On the presentation the two legs send a point `(u, r')` of
`U''` over a test object `T` to the points `s'(r')` and `f(u)` of `U'` respectively, and the arrow
`r'` of the groupoid `G'(T)` runs between them, its target being `t'(r') = f(u)` by the very
definition of `U''`. Naturality in an arrow `(r, r')` of `R''` is the formula
`t''(r, r') = (t(r), c'(f(r), r'))` for the target map of Section 78.21: the lower leg sends the
arrow to `f(r)` and the upper one to an identity, the fibres of `𝒮_{U'}` being discrete, so the
naturality square says exactly that `c'(f(r), r')` is the second component of the target.

Extending across the stackification uses Stacks 04W9 in the shape
`CategoryTheory.Functor.Stackification.restrict_full` and `.restrict_faithful`: restriction along
the stackification map of the presentation is fully faithful on 1-morphisms into a stack, so a
2-isomorphism of the restrictions comes from a unique 2-isomorphism of the two legs. The two
restrictions are computed by the units of the two universal properties already in the library —
`AlgebraicGeometry.Stack.quotientMapExtensionUnit` for the quotient stack map of Stacks 046Q and
`AlgebraicGeometry.Stack.quotientStackOfInvariantUnit` for the descent of an invariant
morphism — together with `AlgebraicGeometry.Stack.quotientStackMap_commutes`.

## References

* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 046Q](https://stacks.math.columbia.edu/tag/046Q)
* [Stacks Project, Tag 04W9](https://stacks.math.columbia.edu/tag/04W9)
* [Stacks Project, Tag 04Y4](https://stacks.math.columbia.edu/tag/04Y4)
-/

@[expose] public section

open CategoryTheory Opposite

namespace CategoryTheory.BasedCategory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : BasedCategory.{v₂, u₂} 𝒮}
  {𝒴 : BasedCategory.{v₃, u₃} 𝒮} {𝒵 : BasedCategory.{v₄, u₄} 𝒮}

/-- Left-whiskering an isomorphism of 1-morphisms over the base. -/
def whiskerLeftIso (F : 𝒳 ⥤ᵇ 𝒴) {H K : 𝒴 ⥤ᵇ 𝒵} (α : H ≅ K) :
    BasedFunctor.comp F H ≅ BasedFunctor.comp F K where
  hom := whiskerLeft F α.hom
  inv := whiskerLeft F α.inv
  hom_inv_id :=
    BasedNatTrans.homCategory.ext _ _ (NatTrans.ext (funext fun a =>
      congrArg (fun β : H ⟶ H => β.toNatTrans.app (F.obj a)) α.hom_inv_id))
  inv_hom_id :=
    BasedNatTrans.homCategory.ext _ _ (NatTrans.ext (funext fun a =>
      congrArg (fun β : K ⟶ K => β.toNatTrans.app (F.obj a)) α.inv_hom_id))

/-- Right-whiskering an isomorphism of 1-morphisms over the base. -/
def whiskerRightIso {F H : 𝒳 ⥤ᵇ 𝒴} (α : F ≅ H) (K : 𝒴 ⥤ᵇ 𝒵) :
    BasedFunctor.comp F K ≅ BasedFunctor.comp H K where
  hom := whiskerRight α.hom K
  inv := whiskerRight α.inv K
  hom_inv_id := by
    refine BasedNatTrans.homCategory.ext _ _ (NatTrans.ext (funext fun a => ?_))
    have h : α.hom.toNatTrans.app a ≫ α.inv.toNatTrans.app a = 𝟙 (F.obj a) :=
      congrArg (fun β : F ⟶ F => β.toNatTrans.app a) α.hom_inv_id
    change K.toFunctor.map (α.hom.toNatTrans.app a) ≫
      K.toFunctor.map (α.inv.toNatTrans.app a) = _
    rw [← K.toFunctor.map_comp, h, K.toFunctor.map_id]
    rfl
  inv_hom_id := by
    refine BasedNatTrans.homCategory.ext _ _ (NatTrans.ext (funext fun a => ?_))
    have h : α.inv.toNatTrans.app a ≫ α.hom.toNatTrans.app a = 𝟙 (H.obj a) :=
      congrArg (fun β : H ⟶ H => β.toNatTrans.app a) α.inv_hom_id
    change K.toFunctor.map (α.inv.toNatTrans.app a) ≫
      K.toFunctor.map (α.hom.toNatTrans.app a) = _
    rw [← K.toFunctor.map_comp, h, K.toFunctor.map_id]
    rfl

end CategoryTheory.BasedCategory

namespace AlgebraicGeometry

universe u

namespace AlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}

/-- A composite of morphisms of algebraic spaces acts on the points over a test object as the
composite of the two actions. -/
theorem comp_hom_app_apply {X Y Z : AlgebraicSpaces C S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (T : (BigFppfOver C S hS)ᵒᵖ) (z : X.obj.obj T) :
    (f ≫ g).hom.app T z = g.hom.app T (f.hom.app T z) := rfl

/-- Equal morphisms of algebraic spaces agree at every point. -/
theorem hom_app_apply_congr {X Y : AlgebraicSpaces C S hS} {f g : X ⟶ Y} (h : f = g)
    (T : (BigFppfOver C S hS)ᵒᵖ) (z : X.obj.obj T) : f.hom.app T z = g.hom.app T z := by
  rw [h]

/-- An identity between two composites of morphisms of algebraic spaces, read at a point. -/
theorem comp_hom_app_apply_eq {W X Y Z : AlgebraicSpaces C S hS} {f : W ⟶ X} {g : X ⟶ Z}
    {f' : W ⟶ Y} {g' : Y ⟶ Z} (h : f ≫ g = f' ≫ g') (T : (BigFppfOver C S hS)ᵒᵖ)
    (z : W.obj.obj T) : g.hom.app T (f.hom.app T z) = g'.hom.app T (f'.hom.app T z) := by
  rw [← comp_hom_app_apply, ← comp_hom_app_apply, h]

end AlgebraicSpaces

namespace Stack

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} {G G' : GroupoidInAlgebraicSpaces C S hS B}

open GroupoidInAlgebraicSpaces

/-! ### The two legs of the square -/

/-- The upper leg of the square of Section 78.21 restricts along the canonical projection
`𝒮_{U''} ⟶ [U''/R'']` to the morphism `U'' ⟶ U'` itself, on the nose. -/
theorem quotientStackProjection_comp_auxQuotientToTargetObjects (φ : Hom G G') :
    BasedFunctor.comp (quotientStackProjection (auxGroupoid φ))
        (auxQuotientToTargetObjects φ) =
      (associatedMap C S hS (auxToTargetObjects φ).hom).1.hom :=
  quotientStackProjection_comp_quotientStackOfInvariant (auxGroupoid φ) (auxToTargetObjects φ)
    (auxToTargetObjects_invariant φ)

/-- The composite `[U''/R''] ⟶ 𝒮_{U'} ⟶ [U'/R']`, the upper and right legs of the square of
Section 78.21. -/
noncomputable def auxQuotientStackUpper (φ : Hom G G') :
    quotientStack (auxGroupoid φ) ⥤ᵇ quotientStack G' :=
  BasedFunctor.comp (auxQuotientToTargetObjects φ) (quotientStackProjection G')

/-- The composite `[U''/R''] ⟶ [U/R] ⟶ [U'/R']`, the left and lower legs of the square of
Section 78.21. -/
noncomputable def auxQuotientStackLower (φ : Hom G G') :
    quotientStack (auxGroupoid φ) ⥤ᵇ quotientStack G' :=
  BasedFunctor.comp (auxQuotientToSource φ) (quotientStackMap φ)

/-! ### The comparison on the presentations

The two legs, read on the pointwise groupoid presentation of `[U''/R'']`, send a point `(u, r')`
of `U''` to the points `s'(r')` and `f(u)` of `U'`, and the arrow `r'` of `G'(T)` runs between
them. -/

section Pointwise

/- Objects and morphisms of the pointwise groupoid fibrations are reached through
`CategoryTheory.Functor.toPseudofunctor'` and the groupoid-to-category inclusion, which the
`implicit` transparency level does not unfold; naming that chain is what lets the ordinary tactics
see through them. -/
attribute [local implicit_reducible] CategoryTheory.Functor.toPseudofunctor'
  CategoryTheory.pseudofunctorOfIsLocallyDiscrete Quiver.Hom.toLoc
  CategoryTheory.BasedCategory.ofFunctor Grpd.forgetToCat Grpd.of

/-- The composite `U'' ⟶ U ⟶ U'` of the pointwise groupoid presentations: on a point `(u, r')`
of `U''` over a test object it is `f(u)`. -/
noncomputable def auxPointwiseMap (φ : Hom G G') :
    presheafOfGroupoids (evaluationGroupoidFunctor (auxGroupoid φ).toGroupoidInFunctors) ⥤ᵇ
      presheafOfGroupoids (evaluationGroupoidFunctor G'.toGroupoidInFunctors) :=
  BasedFunctor.comp (quotientPointwiseMap (auxHom φ)) (quotientPointwiseMap φ)

/-- The invariant morphism `U'' ⟶ U'`, `(u, r') ↦ s'(r')`, read from the pointwise groupoid
presentation of `[U''/R'']` into that of `[U'/R']`: it sends every arrow of `R''` to an
identity. -/
noncomputable def auxPointwiseToObjects (φ : Hom G G') :
    presheafOfGroupoids (evaluationGroupoidFunctor (auxGroupoid φ).toGroupoidInFunctors) ⥤ᵇ
      presheafOfGroupoids (evaluationGroupoidFunctor G'.toGroupoidInFunctors) :=
  BasedFunctor.comp
    (pointwiseOfInvariant (auxGroupoid φ) (auxToTargetObjects φ).hom
      (hom_comp_eq_of_invariant (auxGroupoid φ) (auxToTargetObjects_invariant φ)))
    ⟨pointwiseObjectInclusion G', rfl⟩

/-- The map of pointwise groupoid fibrations induced by a morphism of groupoids in algebraic
spaces acts on the underlying element of the arrow space by the map on arrows. -/
theorem quotientPointwiseMap_arrow {H H' : GroupoidInAlgebraicSpaces C S hS B} (f : Hom H H')
    {X Y : (presheafOfGroupoids (evaluationGroupoidFunctor H.toGroupoidInFunctors)).obj}
    (m : X ⟶ Y) :
    (H'.toGroupoidInFunctors.evaluationArrowEquiv (op X.base) _ _
        ((quotientPointwiseMap f).toFunctor.map m).fiber).1 =
      f.toGroupoidHom.mapArrows.app (op X.base)
        ((H.toGroupoidInFunctors.evaluationArrowEquiv (op X.base) _ _ m.fiber).1) := by
  obtain ⟨hh, hnat⟩ := (quotientPointwiseMapData f).2.2 m.base.op.toLoc
  have h : ((quotientPointwiseMap f).toFunctor.map m).fiber =
      (f.toGroupoidHom.evaluation (op X.base)).map m.fiber ≫
        ((quotientPointwiseMapData f).val.naturality
          m.base.op.toLoc).hom.toNatTrans.app Y.fiber := rfl
  rw [h, hnat, eqToIso.hom, Cat.eqToHom_app]
  exact (evaluationArrow_comp_eqToHom _ _ _ _).trans
    (f.toGroupoidHom.evaluation_map_arrow (op X.base) m.fiber)

/-- On an arrow `(r, r')` of `R''` the composite `U'' ⟶ U ⟶ U'` of the presentations is the arrow
`f(r)` of `G'`. -/
theorem auxPointwiseMap_arrow (φ : Hom G G')
    {X Y : (presheafOfGroupoids
      (evaluationGroupoidFunctor (auxGroupoid φ).toGroupoidInFunctors)).obj}
    (m : X ⟶ Y) :
    (G'.toGroupoidInFunctors.evaluationArrowEquiv (op X.base) _ _
        ((auxPointwiseMap φ).toFunctor.map m).fiber).1 =
      φ.arrowsMap.hom.app (op X.base) ((auxArrowsFst φ).hom.app (op X.base)
        (((auxGroupoid φ).toGroupoidInFunctors.evaluationArrowEquiv
          (op X.base) _ _ m.fiber).1)) :=
  (quotientPointwiseMap_arrow φ ((quotientPointwiseMap (auxHom φ)).toFunctor.map m)).trans
    (congrArg (φ.toGroupoidHom.mapArrows.app (op X.base))
      (quotientPointwiseMap_arrow (auxHom φ) m))

/-- The invariant morphism `U'' ⟶ U'` sends every arrow of `R''` to an identity arrow of `G'`. -/
theorem auxPointwiseToObjects_arrow (φ : Hom G G')
    {X Y : (presheafOfGroupoids
      (evaluationGroupoidFunctor (auxGroupoid φ).toGroupoidInFunctors)).obj}
    (m : X ⟶ Y) :
    (G'.toGroupoidInFunctors.evaluationArrowEquiv (op X.base) _ _
        ((auxPointwiseToObjects φ).toFunctor.map m).fiber).1 =
      G'.toGroupoidInFunctors.identity (op X.base)
        ((auxPointwiseToObjects φ).toFunctor.obj X).fiber := by
  obtain ⟨h, he⟩ : ∃ h, ((auxPointwiseToObjects φ).toFunctor.map m).fiber = eqToHom h :=
    ⟨Discrete.eq_of_hom ((pointwiseOfInvariant (auxGroupoid φ) (auxToTargetObjects φ).hom
        (hom_comp_eq_of_invariant (auxGroupoid φ)
          (auxToTargetObjects_invariant φ))).toFunctor.map m).fiber,
      rfl⟩
  rw [he]
  exact evaluationArrow_eqToHom_identity G'.toGroupoidInFunctors (op X.base) h

/-- The second component of the target `t''(r, r')` is the composite `c'(f(r), r')`, read at a
point of `R''` over a test object. -/
theorem auxComp_action_eq (φ : Hom G G') (T : (BigFppfOver C S hS)ᵒᵖ)
    (a : (auxArrows φ).obj.obj T) :
    G'.toGroupoidInFunctors.compose T (φ.arrowsMap.hom.app T ((auxArrowsFst φ).hom.app T a))
        ((auxArrowsSnd φ).hom.app T a) (auxArrows_composable φ T a) =
      (auxObjectsSnd φ).hom.app T ((auxTarget φ).hom.app T a) :=
  (auxTargetSnd_app φ T a).symm.trans (auxTarget_app_snd φ T a).symm

/-- **The arrow comparing the two legs on the presentation of `[U''/R'']`:** at a point `(u, r')`
of `U''` over a test object it is the arrow `r'` of the groupoid `G'(T)`, which runs from `s'(r')`
to `t'(r') = f(u)`. -/
noncomputable def auxComparisonArrow (φ : Hom G G')
    (X : (presheafOfGroupoids
      (evaluationGroupoidFunctor (auxGroupoid φ).toGroupoidInFunctors)).obj) :
    (auxPointwiseToObjects φ).toFunctor.obj X ⟶ (auxPointwiseMap φ).toFunctor.obj X :=
  ⟨𝟙 X.base,
    (G'.toGroupoidInFunctors.evaluationArrowEquiv (op X.base) _ _).symm
      ⟨(auxObjectsSnd φ).hom.app (op X.base) X.fiber, rfl,
        (AlgebraicSpaces.comp_hom_app_apply_eq (isPullback_auxObjects φ).w.symm
            (op X.base) X.fiber).trans
          (G'.toGroupoidInFunctors.objects.map_id_apply (op X.base) _).symm⟩⟩

/-- The comparison arrow lies in a single fibre. -/
theorem auxComparisonArrow_base (φ : Hom G G')
    (X : (presheafOfGroupoids
      (evaluationGroupoidFunctor (auxGroupoid φ).toGroupoidInFunctors)).obj) :
    (auxComparisonArrow φ X).base = 𝟙 X.base := rfl

/-- The underlying element of the arrow space of the comparison arrow at `(u, r')` is `r'`. -/
theorem auxComparisonArrow_arrow (φ : Hom G G')
    (X : (presheafOfGroupoids
      (evaluationGroupoidFunctor (auxGroupoid φ).toGroupoidInFunctors)).obj) :
    (G'.toGroupoidInFunctors.evaluationArrowEquiv (op X.base) _ _
        (auxComparisonArrow φ X).fiber).1 =
      (auxObjectsSnd φ).hom.app (op X.base) X.fiber :=
  congrArg Subtype.val (Equiv.apply_symm_apply _ _)

/-- **The comparison arrows are natural.** On an arrow `(r, r')` of `R''` from `(u₂, r'₂)` to
`(u₁, r'₁)` the naturality square is the identity `c'(f(r), r'₂) = r'₁`, which is the second
component of the formula `t''(r, r') = (t(r), c'(f(r), r'))`. -/
theorem auxComparisonArrow_naturality (φ : Hom G G')
    {X Y : (presheafOfGroupoids
      (evaluationGroupoidFunctor (auxGroupoid φ).toGroupoidInFunctors)).obj}
    (m : X ⟶ Y) :
    (auxPointwiseToObjects φ).toFunctor.map m ≫ auxComparisonArrow φ Y =
      auxComparisonArrow φ X ≫ (auxPointwiseMap φ).toFunctor.map m := by
  have ht : (auxTarget φ).hom.app (op X.base)
      (((auxGroupoid φ).toGroupoidInFunctors.evaluationArrowEquiv
        (op X.base) _ _ m.fiber).1) =
      (auxObjects φ).obj.map m.base.op Y.fiber :=
    ((auxGroupoid φ).toGroupoidInFunctors.evaluationArrowEquiv (op X.base) _ _ m.fiber).2.2
  have hrx : (auxObjectsSnd φ).hom.app (op X.base) X.fiber =
      (auxArrowsSnd φ).hom.app (op X.base)
        (((auxGroupoid φ).toGroupoidInFunctors.evaluationArrowEquiv
          (op X.base) _ _ m.fiber).1) :=
    (congrArg ((auxObjectsSnd φ).hom.app (op X.base))
        ((auxGroupoid φ).toGroupoidInFunctors.evaluationArrowEquiv
          (op X.base) _ _ m.fiber).2.1).symm.trans
      (AlgebraicSpaces.hom_app_apply_congr (auxSource_comp_auxObjectsSnd φ) (op X.base) _)
  have hw : (G'.toGroupoidInFunctors.evaluationArrowEquiv (op X.base) _ _
        ((Deformation.evaluationMap G'.toGroupoidInFunctors (auxComparisonArrow φ X).base.op).map
          ((auxPointwiseMap φ).toFunctor.map m).fiber)).1 =
      φ.arrowsMap.hom.app (op X.base) ((auxArrowsFst φ).hom.app (op X.base)
        (((auxGroupoid φ).toGroupoidInFunctors.evaluationArrowEquiv
          (op X.base) _ _ m.fiber).1)) :=
    (Deformation.evaluationMap_map_arrow G'.toGroupoidInFunctors
        (auxComparisonArrow φ X).base.op ((auxPointwiseMap φ).toFunctor.map m).fiber).trans
      ((congrArg (G'.toGroupoidInFunctors.arrows.map (auxComparisonArrow φ X).base.op)
          (auxPointwiseMap_arrow φ m)).trans
        (G'.toGroupoidInFunctors.arrows.map_id_apply (op X.base) _))
  refine pointwiseHom_ext G'.toGroupoidInFunctors ?_ ?_
  · change m.base ≫ 𝟙 Y.base = 𝟙 X.base ≫ m.base
    simp
  · rw [pointwiseComp_arrow_of_left_identity G'.toGroupoidInFunctors
        ((auxPointwiseToObjects φ).toFunctor.map m) (auxComparisonArrow φ Y)
        (auxPointwiseToObjects_arrow φ m),
      pointwiseComp_arrow G'.toGroupoidInFunctors (auxComparisonArrow φ X)
        ((auxPointwiseMap φ).toFunctor.map m),
      Deformation.GroupoidInFunctors.evaluationArrowEquiv_comp]
    exact (congrArg (G'.toGroupoidInFunctors.arrows.map m.base.op)
          (auxComparisonArrow_arrow φ Y)).trans
      ((NatTrans.naturality_apply (auxObjectsSnd φ).hom m.base.op Y.fiber).symm.trans
        ((congrArg ((auxObjectsSnd φ).hom.app (op X.base)) ht).symm.trans
          ((auxComp_action_eq φ (op X.base) _).symm.trans
            (Deformation.GroupoidInFunctors.compose_congr G'.toGroupoidInFunctors (op X.base)
              _ _ hw.symm ((auxComparisonArrow_arrow φ X).trans hrx).symm))))

/-- The comparison arrows assembled into a morphism of the two legs of the presentations. -/
noncomputable def auxComparisonTrans (φ : Hom G G') :
    (auxPointwiseToObjects φ).toFunctor ⟶ (auxPointwiseMap φ).toFunctor where
  app := auxComparisonArrow φ
  naturality _ _ m := auxComparisonArrow_naturality φ m

/-- Each comparison arrow lies over an identity of the site. -/
theorem isHomLift_auxComparisonArrow (φ : Hom G G')
    (X : (presheafOfGroupoids
      (evaluationGroupoidFunctor (auxGroupoid φ).toGroupoidInFunctors)).obj) :
    (presheafOfGroupoids (evaluationGroupoidFunctor G'.toGroupoidInFunctors)).p.IsHomLift
      (𝟙 X.base) (auxComparisonArrow φ X) := by
  have h : (presheafOfGroupoids (evaluationGroupoidFunctor G'.toGroupoidInFunctors)).p.map
      (auxComparisonArrow φ X) = 𝟙 X.base := auxComparisonArrow_base φ X
  rw [← h]
  exact Functor.IsHomLift.map _

/-- Each comparison arrow is invertible: it lies over an identity of the site, and the pointwise
groupoid fibration is fibred in groupoids. -/
instance isIso_auxComparisonArrow (φ : Hom G G')
    (X : (presheafOfGroupoids
      (evaluationGroupoidFunctor (auxGroupoid φ).toGroupoidInFunctors)).obj) :
    IsIso (auxComparisonArrow φ X) := by
  have hlift := isHomLift_auxComparisonArrow φ X
  have hcart := (isFiberedInGroupoids_presheafOfGroupoids
    (evaluationGroupoidFunctor G'.toGroupoidInFunctors)).isStronglyCartesian_homLift
      (𝟙 X.base) (auxComparisonArrow φ X)
  have := hcart
  exact Functor.IsStronglyCartesian.isIso_of_base_isIso
    (p := (presheafOfGroupoids (evaluationGroupoidFunctor G'.toGroupoidInFunctors)).p)
    (f := 𝟙 X.base) (auxComparisonArrow φ X)

/-- **The two legs agree on the presentation of `[U''/R'']`**, through the arrow `r'` at the point
`(u, r')` of `U''`. -/
noncomputable def auxComparisonIso (φ : Hom G G') :
    (auxPointwiseToObjects φ).toFunctor ≅ (auxPointwiseMap φ).toFunctor :=
  NatIso.ofComponents (fun X => asIso (auxComparisonArrow φ X))
    (fun m => auxComparisonArrow_naturality φ m)

/-- `AlgebraicGeometry.Stack.auxComparisonIso` as a 2-isomorphism over the big fppf site. -/
noncomputable def auxComparisonBasedIso (φ : Hom G G') :
    auxPointwiseToObjects φ ≅ auxPointwiseMap φ :=
  BasedNatIso.mkNatIso (auxComparisonIso φ) (fun X => isHomLift_auxComparisonArrow φ X)

end Pointwise

/-! ### The 2-isomorphism filling the square -/

section Square

/-- The stackification map of the presentation of a quotient stack, as a 1-morphism over the
site. -/
noncomputable def toQuotientStackBased (H : GroupoidInAlgebraicSpaces C S hS B) :
    quotientPrestack H ⥤ᵇ quotientStack H :=
  ⟨toQuotientStack H, (isFibredOneMorphism_toQuotientStack H).comp_eq⟩

/-- The descent of the invariant morphism `U'' ⟶ U'` to the quotient stack, before the comparison
of morphism universes: a 1-morphism into the universe-enlarged fibred category of `U'`. -/
noncomputable def auxLiftedQuotientStackToObjects (φ : Hom G G') :
    quotientStack (auxGroupoid φ) ⥤ᵇ liftedFibredCategory G'.objects :=
  ⟨liftedQuotientStackOfInvariant (auxGroupoid φ) (auxToTargetObjects φ)
      (auxToTargetObjects_invariant φ),
    Functor.Stackification.extendGroupoid_comp_eq
      (isFiberedInGroupoids_quotientPrestack (auxGroupoid φ))
      (isFiberedInGroupoids_quotientStack (auxGroupoid φ))
      (isStack_quotientStack (auxGroupoid φ))
      (isFiberedInGroupoids_uliftHom _ (fibredCategory C S hS G'.objects.obj).property)
      (liftedFibredCategory_isStack G'.objects)
      (isFibredOneMorphism_toQuotientStack (auxGroupoid φ)).comp_eq
      (prestackOfInvariant (auxGroupoid φ) (auxToTargetObjects φ)
        (auxToTargetObjects_invariant φ)).w
      (isLocallyBijective_toQuotientStack (auxGroupoid φ))
      (essImage_toQuotientStack (auxGroupoid φ))⟩

/-- A 1-morphism from the presentation of `[U''/R'']` to `[U'/R']` built from one of the two legs
read on the presentations. -/
noncomputable def auxPresentationComposite (φ : Hom G G')
    (N : presheafOfGroupoids (evaluationGroupoidFunctor (auxGroupoid φ).toGroupoidInFunctors) ⥤ᵇ
      presheafOfGroupoids (evaluationGroupoidFunctor G'.toGroupoidInFunctors)) :
    quotientPrestack (auxGroupoid φ) ⥤ᵇ quotientStack G' :=
  BasedFunctor.comp (quotientPrestackDown (auxGroupoid φ))
    (BasedFunctor.comp N (pointwiseToQuotientStackBased G'))

/-- The upper and right legs, restricted to the presentation of `[U''/R'']`: the universal
property of the stackification identifies the restriction with the invariant morphism itself. -/
noncomputable def auxRestrictedUpperIso (φ : Hom G G') :
    BasedFunctor.comp (toQuotientStackBased (auxGroupoid φ)) (auxQuotientStackUpper φ) ≅
      auxPresentationComposite φ (auxPointwiseToObjects φ) :=
  let unitU : BasedFunctor.comp (toQuotientStackBased (auxGroupoid φ))
        (auxLiftedQuotientStackToObjects φ) ≅
      prestackOfInvariant (auxGroupoid φ) (auxToTargetObjects φ)
        (auxToTargetObjects_invariant φ) :=
    BasedNatIso.mkNatIso
      (quotientStackOfInvariantUnit (auxGroupoid φ) (auxToTargetObjects φ)
        (auxToTargetObjects_invariant φ))
      (isHomLift_quotientStackOfInvariantUnit_app (auxGroupoid φ) (auxToTargetObjects φ)
        (auxToTargetObjects_invariant φ))
  BasedCategory.whiskerRightIso unitU
    (BasedFunctor.comp (liftedFibredCategoryDown G'.objects) (quotientStackProjection G'))

/-- The left and lower legs, restricted to the presentation of `[U''/R'']`: the universal property
of the stackification and the compatibility of the quotient stack map with the presentations
identify the restriction with the composite `U'' ⟶ U ⟶ U'` of the presentations. -/
noncomputable def auxRestrictedLowerIso (φ : Hom G G') :
    BasedFunctor.comp (toQuotientStackBased (auxGroupoid φ)) (auxQuotientStackLower φ) ≅
      auxPresentationComposite φ (auxPointwiseMap φ) :=
  let unitL : BasedFunctor.comp (toQuotientStackBased (auxGroupoid φ))
        (auxQuotientToSource φ) ≅
      (⟨quotientMapUnderlying (auxHom φ), quotientMapUnderlying_comp (auxHom φ)⟩ :
        quotientPrestack (auxGroupoid φ) ⥤ᵇ quotientStack G) :=
    BasedNatIso.mkNatIso (quotientMapExtensionUnit (auxHom φ))
      (quotientMapExtensionUnit_hom_isHomLift (auxHom φ))
  let mid : quotientPrestack (auxGroupoid φ) ⥤ᵇ quotientStack G' :=
    BasedFunctor.comp (quotientPrestackDown (auxGroupoid φ))
      (BasedFunctor.comp (quotientPointwiseMap (auxHom φ))
        (BasedFunctor.comp (pointwiseToQuotientStackBased G) (quotientStackMap φ)))
  let s₁ : BasedFunctor.comp (toQuotientStackBased (auxGroupoid φ))
      (auxQuotientStackLower φ) ≅ mid :=
    BasedCategory.whiskerRightIso unitL (quotientStackMap φ)
  let s₂ : mid ≅ auxPresentationComposite φ (auxPointwiseMap φ) :=
    BasedCategory.whiskerLeftIso (quotientPrestackDown (auxGroupoid φ))
      (BasedCategory.whiskerLeftIso (quotientPointwiseMap (auxHom φ))
        (quotientStackMap_commutes φ).symm)
  s₁.trans s₂

/-- The middle factor of the restricted square: the comparison arrow `r'`, read on the
presentations and carried into the quotient stack of `G'`. -/
noncomputable def auxRestrictedMiddleIso (φ : Hom G G') :
    auxPresentationComposite φ (auxPointwiseToObjects φ) ≅
      auxPresentationComposite φ (auxPointwiseMap φ) :=
  BasedCategory.whiskerLeftIso (quotientPrestackDown (auxGroupoid φ))
    (BasedCategory.whiskerRightIso (auxComparisonBasedIso φ)
      (pointwiseToQuotientStackBased G'))

/-- The component of `AlgebraicGeometry.Stack.auxRestrictedMiddleIso` at a point of the
presentation is the arrow `r'` of the evaluated groupoid of `G'`, carried into the quotient. -/
theorem auxRestrictedMiddleIso_hom_app (φ : Hom G G')
    (X : (quotientPrestack (auxGroupoid φ)).obj) :
    (auxRestrictedMiddleIso φ).hom.toNatTrans.app X =
      (pointwiseToQuotientStack G').map
        (auxComparisonArrow φ ((quotientPrestackDown (auxGroupoid φ)).obj X)) := rfl

/-- **The square of Section 78.21 2-commutes after restriction to the presentation of
`[U''/R'']`**: there the comparison is the arrow `r'` at the point `(u, r')` of `U''`. -/
noncomputable def auxRestrictedSquare (φ : Hom G G') :
    BasedFunctor.comp (toQuotientStackBased (auxGroupoid φ)) (auxQuotientStackUpper φ) ≅
      BasedFunctor.comp (toQuotientStackBased (auxGroupoid φ)) (auxQuotientStackLower φ) :=
  ((auxRestrictedUpperIso φ).trans (auxRestrictedMiddleIso φ)).trans
    (auxRestrictedLowerIso φ).symm

/-- **The component of the restricted square at a point of the presentation**: the unit of the
descent of the invariant morphism, then the arrow `r'` of the evaluated groupoid of `G'`, then the
inverse of the unit of the induced 1-morphism of Stacks 046Q. -/
theorem auxRestrictedSquare_hom_app (φ : Hom G G')
    (X : (quotientPrestack (auxGroupoid φ)).obj) :
    (auxRestrictedSquare φ).hom.toNatTrans.app X =
      (auxRestrictedUpperIso φ).hom.toNatTrans.app X ≫
        (auxRestrictedMiddleIso φ).hom.toNatTrans.app X ≫
          (auxRestrictedLowerIso φ).inv.toNatTrans.app X := by
  rw [auxRestrictedSquare, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc]
  rfl

/-- **The component of the inverse of the restricted square at a point of the presentation.** -/
theorem auxRestrictedSquare_inv_app (φ : Hom G G')
    (X : (quotientPrestack (auxGroupoid φ)).obj) :
    (auxRestrictedSquare φ).inv.toNatTrans.app X =
      (auxRestrictedLowerIso φ).hom.toNatTrans.app X ≫
        (auxRestrictedMiddleIso φ).inv.toNatTrans.app X ≫
          (auxRestrictedUpperIso φ).inv.toNatTrans.app X := by
  rw [auxRestrictedSquare, Iso.trans_inv, Iso.trans_inv, Iso.symm_inv]
  rfl

/-- The upper and right legs of the square, as an object of the morphism category of
Stacks 02ZG. -/
noncomputable def auxUpperFibredMor (φ : Hom G G') :
    Functor.FibredMor (quotientStack (auxGroupoid φ)).p (quotientStack G').p :=
  ⟨(auxQuotientStackUpper φ).toFunctor,
    (isFiberedInGroupoids_quotientStack G').isFibredOneMorphism (auxQuotientStackUpper φ).w⟩

/-- The left and lower legs of the square, as an object of the morphism category of
Stacks 02ZG. -/
noncomputable def auxLowerFibredMor (φ : Hom G G') :
    Functor.FibredMor (quotientStack (auxGroupoid φ)).p (quotientStack G').p :=
  ⟨(auxQuotientStackLower φ).toFunctor,
    (isFiberedInGroupoids_quotientStack G').isFibredOneMorphism (auxQuotientStackLower φ).w⟩

/-- Restriction of 1-morphisms into `[U'/R']` along the stackification map of the presentation of
`[U''/R'']`, the functor of Stacks 04W9 through which the filler of the square is produced. -/
noncomputable abbrev auxRestrictMor (φ : Hom G G') :
    Functor.FibredMor (quotientStack (auxGroupoid φ)).p (quotientStack G').p ⥤
      Functor.FibredMor (quotientPrestack (auxGroupoid φ)).p (quotientStack G').p :=
  Functor.restrictMor (q := (quotientStack G').p)
    (isFibredOneMorphism_toQuotientStack (auxGroupoid φ))

/-- **Stacks 04W9**: restriction along the stackification map of the presentation of `[U''/R'']`
is full on 1-morphisms into the stack `[U'/R']`. -/
theorem full_auxRestrictMor (φ : Hom G G') : (auxRestrictMor φ).Full :=
  Functor.Stackification.restrict_full (isFibredOneMorphism_toQuotientStack (auxGroupoid φ))
    (isLocallyBijective_toQuotientStack (auxGroupoid φ)) (isStack_quotientStack G').isMorSheaf
    (essImage_toQuotientStack (auxGroupoid φ))

/-- **Stacks 04W9**: restriction along the stackification map of the presentation of `[U''/R'']`
is faithful on 1-morphisms into the stack `[U'/R']`. -/
theorem faithful_auxRestrictMor (φ : Hom G G') : (auxRestrictMor φ).Faithful :=
  Functor.Stackification.restrict_faithful
    (isFibredOneMorphism_toQuotientStack (auxGroupoid φ))
    (isStack_quotientStack G').isMorSheaf (essImage_toQuotientStack (auxGroupoid φ))

/-- The square restricted to the presentation of `[U''/R'']`, as an isomorphism in the morphism
category of Stacks 02ZG. -/
noncomputable def auxRestrictedSquareMor (φ : Hom G G') :
    (auxRestrictMor φ).obj (auxUpperFibredMor φ) ≅
      (auxRestrictMor φ).obj (auxLowerFibredMor φ) :=
  Functor.FibredMor.isoMk
    ((BasedNatTrans.forgetful (quotientPrestack (auxGroupoid φ)) (quotientStack G')).mapIso
      (auxRestrictedSquare φ))
    (fun A => (auxRestrictedSquare φ).hom.isHomLift' A)

/-- The filler of the square, as an isomorphism in the morphism category of Stacks 02ZG: the
preimage of `AlgebraicGeometry.Stack.auxRestrictedSquareMor` under the fully faithful restriction
functor. -/
noncomputable def auxSquareFibredMorIso (φ : Hom G G') :
    auxUpperFibredMor φ ≅ auxLowerFibredMor φ :=
  have := full_auxRestrictMor φ
  have := faithful_auxRestrictMor φ
  (auxRestrictMor φ).preimageIso (auxRestrictedSquareMor φ)

/-- **The square of Section 78.21 2-commutes**, which is the 2-commutativity the comparison
1-morphism of Stacks 04Y4 is built from. The projection
`U'' ⟶ U'`, descended to `[U''/R'']` and followed by the canonical arrow `𝒮_{U'} ⟶ [U'/R']`,
agrees with the composite `[U''/R''] ⟶ [U/R] ⟶ [U'/R']` of the two quotient stack maps, through a
2-isomorphism over the big fppf site. On the presentation of `[U''/R'']` the 2-isomorphism is the
arrow `r'` of `G'` at the point `(u, r')` of `U''`. -/
noncomputable def auxQuotientStackSquare (φ : Hom G G') :
    auxQuotientStackUpper φ ≅ auxQuotientStackLower φ :=
  BasedNatIso.mkNatIso (Functor.fibredMorNatIso (auxSquareFibredMorIso φ))
    (fun A => (auxSquareFibredMorIso φ).hom.isHomLift A)

/-- The preimage of a morphism under the restriction functor has the same component at the image of
a point of the presentation as the morphism itself. -/
private theorem auxRestrictMor_preimage_app (φ : Hom G G') [(auxRestrictMor φ).Full]
    {A B : Functor.FibredMor (quotientStack (auxGroupoid φ)).p (quotientStack G').p}
    (f : (auxRestrictMor φ).obj A ⟶ (auxRestrictMor φ).obj B)
    (X : (quotientPrestack (auxGroupoid φ)).obj) :
    ((auxRestrictMor φ).preimage f).trans.app ((toQuotientStack (auxGroupoid φ)).obj X) =
      f.trans.app X :=
  congrArg (fun k : (auxRestrictMor φ).obj A ⟶ (auxRestrictMor φ).obj B => k.trans.app X)
    ((auxRestrictMor φ).map_preimage f)

/-- **The filler of the square, restricted along the stackification map of the presentation of
`[U''/R'']`, is the comparison built on that presentation.** It is the defining property of the
filler: it is the unique 1-morphism of the morphism category of Stacks 02ZG restricting to
`AlgebraicGeometry.Stack.auxRestrictedSquare`, and at a point `(u, r')` of `U''` over a test
object the latter is the arrow `r'` of the evaluated groupoid of `G'`. -/
theorem auxQuotientStackSquare_hom_app_toQuotientStack (φ : Hom G G')
    (X : (quotientPrestack (auxGroupoid φ)).obj) :
    (auxQuotientStackSquare φ).hom.toNatTrans.app ((toQuotientStack (auxGroupoid φ)).obj X) =
      (auxRestrictedSquare φ).hom.toNatTrans.app X :=
  have := full_auxRestrictMor φ
  auxRestrictMor_preimage_app φ (auxRestrictedSquareMor φ).hom X

/-- **The inverse of the filler, restricted along the stackification map of the presentation of
`[U''/R'']`, is the inverse of the comparison built on that presentation.** -/
theorem auxQuotientStackSquare_inv_app_toQuotientStack (φ : Hom G G')
    (X : (quotientPrestack (auxGroupoid φ)).obj) :
    (auxQuotientStackSquare φ).inv.toNatTrans.app ((toQuotientStack (auxGroupoid φ)).obj X) =
      (auxRestrictedSquare φ).inv.toNatTrans.app X :=
  have := full_auxRestrictMor φ
  auxRestrictMor_preimage_app φ (auxRestrictedSquareMor φ).inv X

end Square

end Stack

end AlgebraicGeometry

end
