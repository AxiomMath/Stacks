module

public import StacksFrontier.AlgebraicGeometry.KerDetected.Basic
public import StacksFrontier.AlgebraicGeometry.FlatGoodDiagram.FlatModel
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.SchemeTheoreticImage

/-!
# Scheme-theoretic images along a flat base change, and a flat model over a stage

Stacks 081I says that the defining ideal of the scheme-theoretic image of a quasi-compact
morphism is pulled back to the defining ideal of the image of its flat base change. Its
downstream form — the square of the two closed embeddings is *cartesian* — is
`AlgebraicGeometry.isPullback_image_of_flat` in
`StacksFrontier.AlgebraicGeometry.Morphisms.Flat.SchemeTheoreticImage`, and this file applies that
together with the flat-model results of `FlatModel.lean` to the inverse system of
scheme-theoretic images attached to a good diagram.

## Main results

* `AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.isPullback_stageTargetMap`: the
  transition between two base changes of the model is itself a base change of a transition of the
  base system.
* `AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.isPullback_induced_baseChange`: the
  square relating the two closed immersions into base changes of a model and of a model's own
  model is cartesian.
* `AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.imageStageGoodDiagram`: a stage of the
  image system of a good diagram is itself the model of a good diagram, over that stage.
* `AlgebraicGeometry.LimitNoetherianSituation.exists_flat_model_imageSystem`: a flat morphism of
  finite presentation to `Y` is the base change, along a cone leg `Y ⟶ Y_j`, of a flat morphism
  of finite presentation over `Y_j`.

## Route

`exists_flat_model_imageSystem` is `AlgebraicGeometry.exists_flat_model_of_noetherian_limit`
applied to the image system, reindexed by `Set.Ici G.index` along the initial functor
`AlgebraicGeometry.tailToOver` so that the index is the opposite of a directed preorder. Its three
hypotheses on the system hold: the stages are Noetherian, being of finite type over a Noetherian
stage of the base; the transitions are affine, which is
`GoodDiagram.isAffineHom_imageSystem_map`; and the cone legs are scheme-theoretically dominant,
which is `GoodDiagram.isSchemeTheoreticallyDominant_π`. That the cone is limiting is Stacks 0CNQ.

`imageStageGoodDiagram` exists because `exists_flat_model_imageSystem` produces a model over a
*stage of the image system*, while the construction of a good diagram for `X` out of that model
needs it to sit over the model of a good diagram for `Y`. The stage `Y_j`, with its closed
embedding into `S_j ×_{S_i} W` followed by the projection to `S_j`, is such a model: the induced
morphism `Y ⟶ S ×_{S_j} Y_j` is a closed immersion because composing it with the affine morphism
`S ×_{S_j} Y_j ⟶ S ×_{S_i} W` gives `GoodDiagram.induced`, which is one.

## Universe situation

The index type is at a universe `v` independent of the scheme universe `u`, with no smallness
instance: `exists_flat_model_of_noetherian_limit` was arranged in `FlatModel.lean` precisely so
that this file inherits that.

## Transparency gotchas

`imageSystem` and `stageMap` are semireducible `def`s, so a statement mixing a stage of the
system with the scheme-theoretic image it is defined to be elaborates but cannot be rewritten
against at instance transparency. Every statement below is phrased with the system's own
vocabulary, and `imageStageGoodDiagram` discharges its closed-immersion field through
`IsClosedImmersion.of_comp` rather than by unfolding.

Mathlib's `AlgebraicGeometry.isAffineHom_isStableUnderBaseChange` is declared under
`backward.isDefEq.respectTransparency.types false`, and in consequence instance search inside
`imageStageGoodDiagram` does *not* find `MorphismProperty.IsStableUnderBaseChangeAlong
@IsAffineHom b` for the morphism `b` built there, so neither `inferInstance` nor
`MorphismProperty.pullback_snd` produces `IsAffineHom (pullback.snd _ b)`. Ascribing the property
as `(@IsAffineHom : MorphismProperty Scheme.{u})` and then applying
`MorphismProperty.IsStableUnderBaseChange.of_isPullback` by hand does resolve it. That is what
the ascription in the proof is for.

## References

* [Stacks Project, Tag 081I](https://stacks.math.columbia.edu/tag/081I).
* [Stacks Project, Tag 0CNQ](https://stacks.math.columbia.edu/tag/0CNQ).
* [Stacks Project, Tag 0CNT](https://stacks.math.columbia.edu/tag/0CNT), whose proof is the
  reason for each of these.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry

namespace LimitNoetherianSituation

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  {D : LimitNoetherianSituation.{v, u} I}

namespace GoodDiagram

variable {X : Scheme.{u}} {p : X ⟶ D.limitScheme}

/-- The transition between the base changes of the model of a good diagram to two stages is a
base change of the corresponding transition of the base system. -/
public lemma isPullback_stageTargetMap (G : GoodDiagram D p) {j k : Over (op G.index)}
    (a : j ⟶ k) :
    IsPullback (G.stageTargetMap a) (pullback.fst (D.system.map j.hom) G.modelMap)
      (pullback.fst (D.system.map k.hom) G.modelMap) (D.system.map a.left) := by
  apply IsPullback.of_right _ _ (IsPullback.of_hasPullback _ _).flip
  · simpa only [stageTargetMap, pullback.lift_snd, ← Functor.map_comp, Over.w] using
      (IsPullback.of_hasPullback (D.system.map j.hom) G.modelMap).flip
  · exact pullback.lift_fst _ _ _

/-- Each stage of the image system of a good diagram is Noetherian: it is a closed subscheme of
a base change of the model, which is of finite type over a Noetherian stage. -/
public instance isNoetherian_imageSystem_obj (G : GoodDiagram D p) (j : Over (op G.index)) :
    IsNoetherian (G.imageSystem.obj j) := by
  change IsNoetherian (G.stageMap j).image
  let q : (G.stageMap j).image ⟶ D.system.obj j.left :=
    (G.stageMap j).imageι ≫ pullback.fst (D.system.map j.hom) G.modelMap
  let : IsNoetherian (D.system.obj j.left) := D.noetherian (unop j.left)
  let : LocallyOfFiniteType q := inferInstance
  let : QuasiCompact q := inferInstance
  exact
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian q
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace q }

/-- The square comparing the closed immersion attached to a good diagram with the one attached
to a model over its model is cartesian. The names are those of the application: `s` is a limit
projection, `m` the model morphism, `p` the structure morphism of `Y`, `y` its morphism to the
model, `q` the morphism of the new model to the old, and `a`, `f` the two legs of a cartesian
square over `q`, `y`. -/
public lemma isPullback_induced_baseChange {S B W Z Y X : Scheme.{u}} (s : S ⟶ B) (m : W ⟶ B)
    (pp : Y ⟶ S) (y : Y ⟶ W) (q : Z ⟶ W) (a : X ⟶ Z) (f : X ⟶ Y)
    (hy : pp ≫ s = y ≫ m) (hx : a ≫ q = f ≫ y) (h : IsPullback a f q y) :
    IsPullback
      (pullback.lift (f ≫ pp) a (by
        calc (f ≫ pp) ≫ s = f ≫ pp ≫ s := Category.assoc _ _ _
          _ = f ≫ y ≫ m := by rw [hy]
          _ = (f ≫ y) ≫ m := (Category.assoc _ _ _).symm
          _ = (a ≫ q) ≫ m := by rw [hx]
          _ = a ≫ q ≫ m := Category.assoc _ _ _))
      f
      (pullback.lift (pullback.fst s (q ≫ m)) (pullback.snd s (q ≫ m) ≫ q) (by
        rw [Category.assoc, ← pullback.condition]))
      (pullback.lift pp y hy) := by
  apply IsPullback.mk' (by
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, pullback.lift_fst]
    · simp only [Category.assoc, pullback.lift_snd]
      rw [← Category.assoc, pullback.lift_snd]
      exact hx)
  · intro T l l' hl hl'
    refine h.hom_ext ?_ hl'
    have := congrArg (· ≫ pullback.snd s (q ≫ m)) hl
    simpa only [Category.assoc, pullback.lift_snd] using this
  · intro T c b hbc
    have hc : (c ≫ pullback.snd s (q ≫ m)) ≫ q = b ≫ y := by
      have := congrArg (· ≫ pullback.snd s m) hbc
      simpa only [Category.assoc, pullback.lift_snd] using this
    refine ⟨h.lift (c ≫ pullback.snd s (q ≫ m)) b hc, ?_, h.lift_snd _ _ _⟩
    refine pullback.hom_ext ?_ ?_
    · have hb : b ≫ pp = c ≫ pullback.fst s (q ≫ m) := by
        have := congrArg (· ≫ pullback.fst s m) hbc
        simpa only [Category.assoc, pullback.lift_fst] using this.symm
      simp only [Category.assoc, pullback.lift_fst, h.lift_snd_assoc, hb]
    · simp only [Category.assoc, pullback.lift_snd, h.lift_fst]

/-- A stage of the image system of a good diagram for `X ⟶ S` is itself the model of a good
diagram for `X ⟶ S`, over that stage of the base system. This is the good diagram the source's
proof of Stacks 0CNT replaces the given one by. -/
public noncomputable def imageStageGoodDiagram (G : GoodDiagram D p) (j : Over (op G.index)) :
    GoodDiagram D p := by
  let q := G.stageMap j
  let b := q.imageι ≫ pullback.fst (D.system.map j.hom) G.modelMap
  have hb : p ≫ D.limitCone.π.app j.left = q.toImage ≫ b := by
    simp only [b, ← Category.assoc, Scheme.Hom.toImage_imageι]
    exact (pullback.lift_fst _ _ _).symm
  let l := pullback.lift p q.toImage hb
  let a : pullback (D.limitCone.π.app j.left) b ⟶
      pullback (D.limitCone.π.app (op G.index)) G.modelMap :=
    pullback.lift (pullback.fst _ _)
      (pullback.snd _ _ ≫ q.imageι ≫ pullback.snd _ _) (by
        rw [Category.assoc, Category.assoc, ← pullback.condition]
        change pullback.fst _ _ ≫ D.limitCone.π.app (op G.index) =
          pullback.snd _ _ ≫ b ≫ D.system.map j.hom
        rw [← pullback.condition_assoc, D.limitCone.w j.hom])
  let : IsAffineHom (D.limitCone.π.app j.left) :=
    EventualLimit.isAffineHom_π_app D.system D.limitCone D.isLimit j.left
  let : IsAffineHom (D.limitCone.π.app (op G.index)) :=
    EventualLimit.isAffineHom_π_app D.system D.limitCone D.isLimit (op G.index)
  let hsbc : MorphismProperty.IsStableUnderBaseChange
      (@IsAffineHom : MorphismProperty Scheme.{u}) := inferInstance
  let : IsAffineHom (pullback.snd (D.limitCone.π.app j.left) b) :=
    hsbc.of_isPullback (IsPullback.of_hasPullback (D.limitCone.π.app j.left) b) inferInstance
  let : IsAffineHom q.imageι := inferInstance
  let : IsAffineHom (D.system.map j.hom) := D.transition_affine j.hom
  let : IsAffineHom (pullback.snd (D.system.map j.hom) G.modelMap) :=
    hsbc.of_isPullback (IsPullback.of_hasPullback (D.system.map j.hom) G.modelMap) inferInstance
  have : IsAffineHom (a ≫ pullback.snd _ _) := by
    rw [pullback.lift_snd]
    infer_instance
  have : IsAffineHom a := IsAffineHom.of_comp a (pullback.snd _ _)
  have hla : l ≫ a = G.induced := by
    refine pullback.hom_ext ?_ ?_
    · simp only [l, a, Category.assoc, pullback.lift_fst]
    · simp only [l, a, Category.assoc, pullback.lift_snd]
      rw [← Category.assoc, pullback.lift_snd, ← Category.assoc, Scheme.Hom.toImage_imageι]
      exact pullback.lift_snd _ _ _
  have : IsClosedImmersion (l ≫ a) := hla ▸ G.isClosedImmersion
  exact
    { index := unop j.left
      W := q.image
      modelMap := b
      toModel := q.toImage
      commutes := hb
      locallyOfFiniteType := inferInstance
      quasiCompact := inferInstance
      isClosedImmersion := IsClosedImmersion.of_comp l a }

end GoodDiagram

/-- **The flat model over a stage of an image system.** A flat morphism `f : X ⟶ Y` of finite
presentation, with `Y` carrying a good diagram over the limit, is the base change along some cone
leg `Y ⟶ Y_j` of a flat morphism of finite presentation over `Y_j`.

This is `AlgebraicGeometry.exists_flat_model_of_noetherian_limit` applied to the image system,
whose cone is limiting by Stacks 0CNQ and whose legs are scheme-theoretically dominant. -/
public lemma exists_flat_model_imageSystem (D : LimitNoetherianSituation.{v, u} I)
    {X Y : Scheme.{u}} {pY : Y ⟶ D.limitScheme} [QuasiSeparated pY] [LocallyOfFiniteType pY]
    [QuasiCompact pY] (f : X ⟶ Y) [Flat f] (hfp : FinitePresentation f)
    (G : GoodDiagram D pY) :
    ∃ (j : Over (op G.index)) (Z : Over (G.imageSystem.obj j)),
      FinitePresentation Z.hom ∧ Flat Z.hom ∧
        Nonempty (Over.mk f ≅ (Over.pullback (G.imageCone.π.app j)).obj Z) := by
  have : Nonempty (Set.Ici G.index) := ⟨⟨G.index, le_rfl⟩⟩
  have := directed_tail (I := I) G.index
  have := initial_tailToOver (I := I) G.index
  let T := tailToOver G.index
  let A := T ⋙ G.imageSystem
  let c := G.imageCone.whisker T
  have hc : IsLimit c := (Functor.Initial.isLimitWhiskerEquiv T _).symm G.isLimit_imageCone
  have (j : (Set.Ici G.index)ᵒᵖ) : IsNoetherian (A.obj j) :=
    G.isNoetherian_imageSystem_obj (T.obj j)
  have {j k : (Set.Ici G.index)ᵒᵖ} (a : j ⟶ k) : IsAffineHom (A.map a) :=
    G.isAffineHom_imageSystem_map (T.map a)
  have (j : (Set.Ici G.index)ᵒᵖ) : IsSchemeTheoreticallyDominant (c.π.app j) :=
    G.isSchemeTheoreticallyDominant_π (T.obj j)
  let f' : X ⟶ c.pt := f
  have : Flat f' := inferInstanceAs (Flat f)
  have hfp' : FinitePresentation f' := hfp
  obtain ⟨j, Z, h⟩ := exists_flat_model_of_noetherian_limit A c hc f' hfp'
  exact ⟨T.obj j, Z, h⟩

end LimitNoetherianSituation

end AlgebraicGeometry
