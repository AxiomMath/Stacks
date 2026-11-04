module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FunctorialityAuxiliaryGroupoid

/-!
# Points and arrows of the auxiliary groupoid of Section 78.21

Let `φ : G ⟶ G'` be a morphism of groupoids in algebraic spaces over an algebraic space `B` over
a scheme `S` of a big fppf site, written `f : U ⟶ U'` on objects, and let
`(U'', R'', s'', t'', c'')` be the groupoid of Section 78.21 attached to it, with
`U'' = U ×_{f, U', t'} R'` and `R'' = R ×_{f ∘ s, U', t'} R'`. This file reads the evaluation of
that groupoid at a test object `T` in elementary terms:

* a `T`-point of `U''` is a pair `(u, r')` of a `T`-point of `U` and a `T`-point of `R'` with
  `t'(r') = f(u)`;
* an arrow `(u₂, r'₂) ⟶ (u₁, r'₁)` of the evaluated groupoid is an arrow `r : u₂ ⟶ u₁` of the
  evaluated groupoid of `G` such that `c'(f(r), r'₂) = r'₁`;
* the evaluated functor of the projection `g : (U'', R'', s'', t'', c'') ⟶ (U, R, s, t, c)` sends
  that arrow to `r`, and is faithful.

## Main definitions

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.auxPoint`: the `T`-point `(u, r')` of `U''`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.auxEvaluationArrow`: the arrow of the evaluated
  auxiliary groupoid attached to an arrow `r` of the evaluated groupoid of `G` satisfying the
  compatibility above.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.auxPoint_fst` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.auxPoint_snd`: the two projections of that point.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.auxHom_evaluation_map_arrow`: the evaluated
  functor of `g` sends an arrow of the evaluated auxiliary groupoid to the arrow of the evaluated
  groupoid of `G` represented by the first projection of the corresponding `T`-point of `R''`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.auxHom_evaluation_faithful`: that functor is
  faithful — an arrow out of a fixed point of `U''` is determined by its first projection,
  the second being the second projection of the source.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.auxEvaluationArrow_map`: the image of
  `auxEvaluationArrow` under the evaluated functor of `g` is the arrow it was built from, so that
  functor is full on the arrows satisfying the compatibility.

## References

* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 044P](https://stacks.math.columbia.edu/tag/044P)
* [Stacks Project, Tag 04Y4](https://stacks.math.columbia.edu/tag/04Y4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

universe u

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} {G G' : GroupoidInAlgebraicSpaces C S hS B}

variable (φ : Hom G G') (T : (BigFppfOver C S hS)ᵒᵖ)

/-! ### Points of `U''` -/

/-- **The `T`-point `(u, r')` of `U''`** attached to a `T`-point `u` of `U` and a `T`-point `r'`
of `R'` whose target is `f(u)`. -/
noncomputable def auxPoint (u : G.objects.obj.obj T) (r' : G'.arrows.obj.obj T)
    (h : G'.target.hom.app T r' = φ.toGroupoidHom.mapObjects.app T u) :
    (auxObjects φ).obj.obj T :=
  fibreProductMk φ.objectsMap G'.target T u r' h.symm

/-- The first projection of the `T`-point `(u, r')` of `U''` is `u`. -/
@[simp]
theorem auxPoint_fst (u : G.objects.obj.obj T) (r' : G'.arrows.obj.obj T)
    (h : G'.target.hom.app T r' = φ.toGroupoidHom.mapObjects.app T u) :
    (auxObjectsFst φ).hom.app T (auxPoint φ T u r' h) = u :=
  fibreProductMk_fst _ _ _ _ _ _

/-- The second projection of the `T`-point `(u, r')` of `U''` is `r'`. -/
@[simp]
theorem auxPoint_snd (u : G.objects.obj.obj T) (r' : G'.arrows.obj.obj T)
    (h : G'.target.hom.app T r' = φ.toGroupoidHom.mapObjects.app T u) :
    (auxObjectsSnd φ).hom.app T (auxPoint φ T u r' h) = r' :=
  fibreProductMk_snd _ _ _ _ _ _

/-! ### Arrows of the evaluated auxiliary groupoid -/

/-- The `T`-point of `R''` underlying an arrow of the evaluated auxiliary groupoid. -/
noncomputable abbrev auxArrowVal {P Q : (auxGroupoid φ).toGroupoidInFunctors.Evaluation T}
    (m : P ⟶ Q) : (auxArrows φ).obj.obj T :=
  ((auxGroupoid φ).toGroupoidInFunctors.evaluationArrowEquiv T P Q m).1

/-- **The evaluated functor of the projection `g` sends an arrow of the evaluated auxiliary
groupoid to the arrow of the evaluated groupoid of `G` represented by the first projection of the
corresponding `T`-point of `R''`.** -/
theorem auxHom_evaluation_map_arrow
    {P Q : (auxGroupoid φ).toGroupoidInFunctors.Evaluation T} (m : P ⟶ Q) :
    (G.toGroupoidInFunctors.evaluationArrowEquiv T _ _
        (((auxHom φ).toGroupoidHom.evaluation T).map m)).1 =
      (auxArrowsFst φ).hom.app T (auxArrowVal φ T m) :=
  (auxHom φ).toGroupoidHom.evaluation_map_arrow T m

/-- The second projection of the `T`-point of `R''` underlying an arrow is the second projection
of its source. -/
theorem auxArrowVal_snd {P Q : (auxGroupoid φ).toGroupoidInFunctors.Evaluation T} (m : P ⟶ Q) :
    (auxArrowsSnd φ).hom.app T (auxArrowVal φ T m) = (auxObjectsSnd φ).hom.app T P :=
  (auxSource_app_snd φ T (auxArrowVal φ T m)).symm.trans
    (congrArg ((auxObjectsSnd φ).hom.app T)
      (((auxGroupoid φ).toGroupoidInFunctors.evaluationArrowEquiv T P Q m).2.1))

/-- **The evaluated functor of the projection `g` is faithful.** An arrow of the evaluated
auxiliary groupoid is a `T`-point of `R''`, that is a pair `(r, r')`; its second component is the
second projection of the source and so is already determined, and its first component is what the
functor records. -/
theorem auxHom_evaluation_faithful :
    ((auxHom φ).toGroupoidHom.evaluation T).Faithful where
  map_injective {P Q} m n h := by
    refine ((auxGroupoid φ).toGroupoidInFunctors.evaluationArrowEquiv T P Q).injective
      (Subtype.ext (auxArrows_ext φ T ?_ ?_))
    · rw [← auxHom_evaluation_map_arrow, ← auxHom_evaluation_map_arrow, h]
    · exact (auxArrowVal_snd φ T m).trans (auxArrowVal_snd φ T n).symm

/-! ### Building arrows of the evaluated auxiliary groupoid -/

/-- **The arrow of the evaluated auxiliary groupoid attached to a compatible arrow of the
evaluated groupoid of `G`.** Given `T`-points `P` and `Q` of `U''` and an arrow `r` of the
evaluated groupoid of `G` from the first projection of `P` to that of `Q` with
`c'(f(r), r'_P) = r'_Q`, the pair `(r, r'_P)` is a `T`-point of `R''` with source `P` and target
`Q`, hence an arrow `P ⟶ Q`. -/
noncomputable def auxEvaluationArrow (P Q : (auxGroupoid φ).toGroupoidInFunctors.Evaluation T)
    (r : (show G.toGroupoidInFunctors.Evaluation T from (auxObjectsFst φ).hom.app T P) ⟶
      (auxObjectsFst φ).hom.app T Q)
    (hr : (auxTargetSnd φ).hom.app T (auxArrowOfHom φ T r) =
      (auxObjectsSnd φ).hom.app T Q) :
    P ⟶ Q :=
  ((auxGroupoid φ).toGroupoidInFunctors.evaluationArrowEquiv T P Q).symm
    ⟨auxArrowOfHom φ T r,
      auxObjects_ext φ T
        ((auxSource_app_fst φ T _).trans ((congrArg (G.source.hom.app T)
            (auxArrowOfHom_fst φ T r)).trans
          (G.toGroupoidInFunctors.evaluationArrowEquiv T _ _ r).2.1))
        ((auxSource_app_snd φ T _).trans (auxArrowOfHom_snd φ T r)),
      auxObjects_ext φ T
        ((auxTarget_app_fst φ T _).trans ((congrArg (G.target.hom.app T)
            (auxArrowOfHom_fst φ T r)).trans
          (G.toGroupoidInFunctors.evaluationArrowEquiv T _ _ r).2.2))
        ((auxTarget_app_snd φ T _).trans hr)⟩

/-- The `T`-point of `R''` underlying
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.auxEvaluationArrow` is the pair built from the given
arrow. -/
theorem auxEvaluationArrow_val (P Q : (auxGroupoid φ).toGroupoidInFunctors.Evaluation T)
    (r : (show G.toGroupoidInFunctors.Evaluation T from (auxObjectsFst φ).hom.app T P) ⟶
      (auxObjectsFst φ).hom.app T Q)
    (hr : (auxTargetSnd φ).hom.app T (auxArrowOfHom φ T r) =
      (auxObjectsSnd φ).hom.app T Q) :
    auxArrowVal φ T (auxEvaluationArrow φ T P Q r hr) = auxArrowOfHom φ T r :=
  congrArg Subtype.val (Equiv.apply_symm_apply _ _)

/-- **The evaluated functor of the projection `g` carries
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.auxEvaluationArrow` to the arrow it was built
from.** -/
theorem auxEvaluationArrow_map (P Q : (auxGroupoid φ).toGroupoidInFunctors.Evaluation T)
    (r : (show G.toGroupoidInFunctors.Evaluation T from (auxObjectsFst φ).hom.app T P) ⟶
      (auxObjectsFst φ).hom.app T Q)
    (hr : (auxTargetSnd φ).hom.app T (auxArrowOfHom φ T r) =
      (auxObjectsSnd φ).hom.app T Q) :
    ((auxHom φ).toGroupoidHom.evaluation T).map (auxEvaluationArrow φ T P Q r hr) = r := by
  refine (G.toGroupoidInFunctors.evaluationArrowEquiv T _ _).injective (Subtype.ext ?_)
  refine (auxHom_evaluation_map_arrow φ T (auxEvaluationArrow φ T P Q r hr)).trans ?_
  exact (congrArg ((auxArrowsFst φ).hom.app T)
    (auxEvaluationArrow_val φ T P Q r hr)).trans (auxArrowOfHom_fst φ T r)

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
