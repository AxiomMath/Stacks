module

public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.StageDatum

/-!
# A descent datum at the limit is the pullback of one at a stage

Let `f : X ⟶ S` be the limit of a cofiltered system of morphisms `f_i : X_i ⟶ S_i`, and let `D`
be a descent datum relative to `X / S`. A descent datum `Dᵢ` relative to `X_i / S_i` whose
underlying scheme models that of `D`, by an identification `e` of `D`'s underlying scheme with
the base change of `Dᵢ`'s, and whose gluing isomorphism acts on generalized points the way `D`'s
does, is carried to `D` by the pullback functor of the square relating the stage to the limit.
This is what turns effectivity of the datum at the stage into effectivity of `D`, through
`AlgebraicGeometry.DescentDatum.isEtaleEffective_pullbackSquare`.

The hypothesis is stated as a single equation between two generalized points of the underlying
scheme of `Dᵢ`: the universal pair of a point of `D`'s underlying scheme and a point of `X` over
one point of `S` is acted on by `D`'s gluing isomorphism and then compared with the stage, or
compared with the stage and then acted on by `Dᵢ`'s. This is exactly the equivariance proved by
`AlgebraicGeometry.LimitDatum.actPullback_stageComparison_universal`, so the datum built from a
stage model satisfies it.

## Main definitions

* `AlgebraicGeometry.LimitDatum.stagePullbackFunctor`: the pullback functor on descent data for
  the square relating a stage to the limit.
* `AlgebraicGeometry.LimitDatum.isoStagePullback`: **a descent datum at the limit is isomorphic
  to the pullback of an equivariantly modelled datum at a stage.**

## Implementation notes

The isomorphism is built by `AlgebraicGeometry.DescentData.isoOfGluingPullback`, so the whole
content is the compatibility of the comparison with the two gluing isomorphisms, read on the
literal fibre products. Of its four components — two from the target `X ×_S V'` and, inside the
second, two from the base change `V' = X ×_{X_i} V` — three are structural, forced by the
structure morphisms and by the pullback condition; the fourth is the hypothesis.

## References

* [Stacks Project, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP)
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

namespace LimitDatum

variable {I : Type u} [Category.{u} I] {𝒳 𝒮 : I ⥤ Scheme.{u}} (φ : 𝒳 ⟶ 𝒮)
  {cX : Cone 𝒳} {cS : Cone 𝒮} (f : cX.pt ⟶ cS.pt)
  (hf : ∀ i, cX.π.app i ≫ φ.app i = f ≫ cS.π.app i)

/-- **The pullback functor on descent data for the square relating a stage to the limit.** -/
abbrev stagePullbackFunctor (i : I) :
    DescentData.PullbackFunctor (φ.app i) f (cS.π.app i) (cX.π.app i) (hf i) :=
  DescentData.pullbackFunctor (φ.app i) f (cS.π.app i) (cX.π.app i) (hf i)

include hf

/-- **A descent datum at the limit is the pullback of an equivariantly modelled datum at a
stage.** -/
def isoStagePullback (D : DescentDatum f) (i : I) (Dᵢ : DescentDatum (φ.app i))
    (e : D.over ≅ (Over.pullback (cX.π.app i)).obj Dᵢ.over)
    (hequiv : DescentDatum.actPullback Dᵢ.over Dᵢ.transitionPullbackIso.hom
        (pullback.fst (D.over.hom ≫ f) f ≫ e.hom.left ≫
          pullback.fst Dᵢ.over.hom (cX.π.app i))
        (pullback.snd (D.over.hom ≫ f) f ≫ cX.π.app i)
        (modelComparison_universal_cond (φ.app i) f (cX.π.app i) (cS.π.app i) (hf i)
          Dᵢ.over D.over e) =
      D.transitionPullbackIso.hom ≫ pullback.snd f (D.over.hom ≫ f) ≫
        e.hom.left ≫ pullback.fst Dᵢ.over.hom (cX.π.app i)) :
    D ≅ DescentDatum.pullbackSquareDatum (stagePullbackFunctor φ f hf i) Dᵢ :=
  DescentData.isoOfGluingPullback
      (e ≪≫ ((stagePullbackFunctor φ f hf i).objIso Dᵢ).symm) (by
    have hcan : (e ≪≫ ((stagePullbackFunctor φ f hf i).objIso Dᵢ).symm).hom.left ≫
        ((stagePullbackFunctor φ f hf i).objIso Dᵢ).hom.left = e.hom.left := by
      rw [Iso.trans_hom, Iso.symm_hom, Over.comp_left, Category.assoc, ← Over.comp_left,
        Iso.inv_hom_id, Over.id_left, Category.comp_id]
    have hiso : IsIso ((stagePullbackFunctor φ f hf i).objIso Dᵢ).hom.left := by
      change IsIso ((Over.forget cX.pt).map ((stagePullbackFunctor φ f hf i).objIso Dᵢ).hom)
      infer_instance
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, DescentData.gluingPullbackIso_hom_fst',
        DescentData.srcPullbackMap_fst_assoc, Category.assoc, DescentData.tgtPullbackMap_fst,
        DescentData.gluingPullbackIso_hom_fst',
        Over.w (e ≪≫ ((stagePullbackFunctor φ f hf i).objIso Dᵢ).symm).hom]
    · rw [← cancel_mono ((stagePullbackFunctor φ f hf i).objIso Dᵢ).hom.left]
      refine pullback.hom_ext ?_ ?_
      · -- the equivariance of the comparison
        have hsrc : DescentData.srcPullbackMap
              (e ≪≫ ((stagePullbackFunctor φ f hf i).objIso Dᵢ).symm).hom ≫
              (stagePullbackFunctor φ f hf i).sourceMap Dᵢ =
            pullback.lift (pullback.fst (D.over.hom ≫ f) f ≫ e.hom.left ≫
                pullback.fst Dᵢ.over.hom (cX.π.app i))
              (pullback.snd (D.over.hom ≫ f) f ≫ cX.π.app i)
              (modelComparison_universal_cond (φ.app i) f (cX.π.app i) (cS.π.app i) (hf i)
                Dᵢ.over D.over e) := by
          refine pullback.hom_ext ?_ ?_
          · rw [Category.assoc, (stagePullbackFunctor φ f hf i).sourceMap_fst Dᵢ,
              DescentData.srcPullbackMap_fst_assoc, pullback.lift_fst, reassoc_of% hcan]
          · rw [Category.assoc, (stagePullbackFunctor φ f hf i).sourceMap_snd Dᵢ,
              DescentData.srcPullbackMap_snd_assoc, pullback.lift_snd]
        have htgt := ((stagePullbackFunctor φ f hf i).targetMap_snd Dᵢ).symm
        simp only [Category.assoc]
        rw [htgt, reassoc_of% ((stagePullbackFunctor φ f hf i).gluing Dᵢ),
          reassoc_of% hsrc, ← htgt, DescentData.tgtPullbackMap_snd_assoc, reassoc_of% hcan]
        exact hequiv
      · -- the structural half: both sides are the second projection
        have hw : ((stagePullbackFunctor φ f hf i).objIso Dᵢ).hom.left ≫
            pullback.snd Dᵢ.over.hom (cX.π.app i) =
            ((DescentDatum.pullbackSquareDatum (stagePullbackFunctor φ f hf i) Dᵢ).obj ()).hom := by
          simpa only [Over.pullback_obj_hom] using
            Over.w ((stagePullbackFunctor φ f hf i).objIso Dᵢ).hom
        simp only [Category.assoc]
        rw [hw, DescentData.gluingPullbackIso_hom_snd, DescentData.srcPullbackMap_snd,
          DescentData.tgtPullbackMap_snd_assoc,
          Over.w (e ≪≫ ((stagePullbackFunctor φ f hf i).objIso Dᵢ).symm).hom,
          DescentData.gluingPullbackIso_hom_snd])

end LimitDatum

end AlgebraicGeometry

end
