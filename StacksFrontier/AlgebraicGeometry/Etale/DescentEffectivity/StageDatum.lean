module

public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.LimitDescend

/-!
# A model of a descent datum at a finite stage

Let `f : X ⟶ S` be the limit of a cofiltered system of morphisms `f_i : X_i ⟶ S_i`. A descent
datum relative to `X / S` lives on three schemes: its underlying scheme over `X`, its gluing
isomorphism over `X ×_S X`, and its cocycle condition over `X ×_S X ×_S X`. This file defines a
model of such a datum at a stage `i`, shows that a model at a stage reindexes to every later
stage, and that a datum whose underlying scheme is of finite presentation has a model at some
stage. A morphism into an iterated base change is determined by the composite of the first
projections of the base changes it is iterated from.

## Main definitions

* `AlgebraicGeometry.LimitDatum.stageTransitionIso`: the gluing isomorphism of a descent datum,
  read at a stage model of its underlying scheme.
* `AlgebraicGeometry.LimitDatum.IsStageModel`: the compatibility making a scheme at a stage,
  an isomorphism of its two base changes to the stage's double fibre product, and an
  identification of the datum's underlying scheme with its base change, a model of the datum at
  that stage.

## Main results

* `AlgebraicGeometry.overPullback_comp_hom_ext` and
  `AlgebraicGeometry.overPullback_comp₃_hom_ext`: a morphism into a twice- or thrice-iterated base
  change is determined by the composite of the first projections.
* `AlgebraicGeometry.LimitDatum.stageTransitionIso_hom_left_fst`: that composite, for the gluing
  isomorphism read at a stage model.
* `AlgebraicGeometry.actPullback_modelComparison`: the comparison with a model over a commutative
  square is equivariant for the two actions on generalized points.
* `AlgebraicGeometry.LimitDatum.isStageModel_reindex`: a stage model reindexes to any later stage.
* `AlgebraicGeometry.LimitDatum.exists_stageModel`: a descent datum whose underlying scheme is of
  finite presentation has a model at some stage.
* `AlgebraicGeometry.LimitDatum.actPullback_stageComparison`: the comparison of a datum at the
  limit with a stage model is equivariant.

## References

* [Stacks Project, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP)
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-! ### Morphisms into an iterated base change -/

/-- Cancelling the inverse of an isomorphism of an over category against an equation between
composites of the first components. -/
lemma overIso_inv_left_comp {C : Scheme.{u}} {A B : Over C} (ξ : A ≅ B) {Z : Scheme.{u}}
    {g : B.left ⟶ Z} {h : A.left ⟶ Z} (hgh : ξ.hom.left ≫ g = h) : ξ.inv.left ≫ h = g := by
  rw [← hgh, ← Category.assoc, ← Over.comp_left, ξ.inv_hom_id, Over.id_left, Category.id_comp]

/-- A morphism into a base change lies over the base, read through the second projection. -/
private lemma left_comp_pullback_snd_eq_hom {T S : Scheme.{u}} {r : S ⟶ T} {W : Over T}
    {A : Over S} (m : A ⟶ (Over.pullback r).obj W) : m.left ≫ pullback.snd W.hom r = A.hom := by
  simpa only [Over.pullback_obj_hom] using Over.w m

/-- The first projection of a morphism into a twice-iterated base change lies over the base. -/
lemma overPullback_comp_fst_comp_hom {T S S' : Scheme.{u}} (p : S ⟶ T) (q : S' ⟶ S) (W : Over T)
    {A : Over S'} (m : A ⟶ (Over.pullback q).obj ((Over.pullback p).obj W)) :
    m.left ≫ pullback.fst ((Over.pullback p).obj W).hom q ≫ pullback.snd W.hom p =
      A.hom ≫ q := by
  have h1 : pullback.fst ((Over.pullback p).obj W).hom q ≫ ((Over.pullback p).obj W).hom =
      pullback.snd ((Over.pullback p).obj W).hom q ≫ q := pullback.condition
  rw [show pullback.snd W.hom p = ((Over.pullback p).obj W).hom from rfl, h1, ← Category.assoc,
    left_comp_pullback_snd_eq_hom m]

/-- A morphism into a twice-iterated base change is determined by the composite of the two first
projections. -/
lemma overPullback_comp_hom_ext {T S S' : Scheme.{u}} {p : S ⟶ T} {q : S' ⟶ S} {W : Over T}
    {A : Over S'} {m n : A ⟶ (Over.pullback q).obj ((Over.pullback p).obj W)}
    (h : m.left ≫ pullback.fst ((Over.pullback p).obj W).hom q ≫ pullback.fst W.hom p =
      n.left ≫ pullback.fst ((Over.pullback p).obj W).hom q ≫ pullback.fst W.hom p) :
    m = n := by
  apply overPullback_hom_ext
  refine pullback.hom_ext ?_ ?_
  · rwa [Category.assoc, Category.assoc]
  · rw [Category.assoc, Category.assoc, overPullback_comp_fst_comp_hom p q W m,
      overPullback_comp_fst_comp_hom p q W n]

/-- The second of the three first projections of a morphism into a thrice-iterated base change
lies over the base. -/
lemma overPullback_comp₃_fst_comp_hom {T₀ T S S' : Scheme.{u}} (o : T ⟶ T₀) (p : S ⟶ T)
    (q : S' ⟶ S) (W : Over T₀) {A : Over S'}
    (m : A ⟶ (Over.pullback q).obj ((Over.pullback p).obj ((Over.pullback o).obj W))) :
    m.left ≫ pullback.fst ((Over.pullback p).obj ((Over.pullback o).obj W)).hom q ≫
        pullback.fst ((Over.pullback o).obj W).hom p ≫ pullback.snd W.hom o =
      A.hom ≫ q ≫ p := by
  have h0 := overPullback_comp_fst_comp_hom p q ((Over.pullback o).obj W) m
  have h1 : pullback.fst ((Over.pullback o).obj W).hom p ≫ pullback.snd W.hom o =
      pullback.snd ((Over.pullback o).obj W).hom p ≫ p := pullback.condition
  rw [h1, reassoc_of% h0]

/-- A morphism into a thrice-iterated base change is determined by the composite of the three first
projections. -/
lemma overPullback_comp₃_hom_ext {T₀ T S S' : Scheme.{u}} {o : T ⟶ T₀} {p : S ⟶ T} {q : S' ⟶ S}
    {W : Over T₀} {A : Over S'}
    {m n : A ⟶ (Over.pullback q).obj ((Over.pullback p).obj ((Over.pullback o).obj W))}
    (h : m.left ≫ pullback.fst ((Over.pullback p).obj ((Over.pullback o).obj W)).hom q ≫
          pullback.fst ((Over.pullback o).obj W).hom p ≫ pullback.fst W.hom o =
        n.left ≫ pullback.fst ((Over.pullback p).obj ((Over.pullback o).obj W)).hom q ≫
          pullback.fst ((Over.pullback o).obj W).hom p ≫ pullback.fst W.hom o) :
    m = n := by
  refine overPullback_comp_hom_ext (pullback.hom_ext ?_ ?_)
  · simp only [Category.assoc]; exact h
  · simp only [Category.assoc]
    rw [overPullback_comp₃_fst_comp_hom o p q W m, overPullback_comp₃_fst_comp_hom o p q W n]

/-! ### The comparison with a model over a commutative square

Let `a : T₀ ⟶ B₀` and `b : T ⟶ B` be two morphisms of schemes related by a commutative square,
with vertical arrows `r : T ⟶ T₀` and `s : B ⟶ B₀`. A scheme `V` over `T₀` carrying an
isomorphism `ψ` of its two base changes to `T₀ ×_{B₀} T₀` is a **model** of a scheme `W` over
`T` carrying one, `χ`, when `W` is identified with the base change of `V` along `r` and the base
change of `ψ` along the induced map `T ×_B T ⟶ T₀ ×_{B₀} T₀` is `χ`, read through that
identification. The whole content of being a model, on generalized points, is that the
comparison morphism `W ⟶ V` is equivariant for the two actions that
`AlgebraicGeometry.DescentDatum.actPullback` determines. -/

/-- The comparison morphism `W ⟶ V` of a model lies over the base. -/
@[reassoc]
lemma modelComparison_comp_hom {T₀ T : Scheme.{u}} (r : T ⟶ T₀) (V : Over T₀) (W : Over T)
    (e : W ≅ (Over.pullback r).obj V) :
    e.hom.left ≫ pullback.fst V.hom r ≫ V.hom = W.hom ≫ r := by
  rw [pullback.condition, ← Category.assoc, left_comp_pullback_snd_eq_hom e.hom]

/-- The universal pair of a point of the modelled scheme and a point of its base lying over one
point of `B` lies, after comparison with the model, over one point of `B₀`. -/
lemma modelComparison_universal_cond {T₀ B₀ T B : Scheme.{u}} (a : T₀ ⟶ B₀) (b : T ⟶ B)
    (r : T ⟶ T₀) (s : B ⟶ B₀) (comm : r ≫ a = b ≫ s) (V : Over T₀) (W : Over T)
    (e : W ≅ (Over.pullback r).obj V) :
    (pullback.fst (W.hom ≫ b) b ≫ e.hom.left ≫ pullback.fst V.hom r) ≫ V.hom ≫ a =
      (pullback.snd (W.hom ≫ b) b ≫ r) ≫ a := by
  have hc : pullback.fst (W.hom ≫ b) b ≫ W.hom ≫ b = pullback.snd (W.hom ≫ b) b ≫ b := by
    simpa only [Category.assoc] using pullback.condition (f := W.hom ≫ b) (g := b)
  simp only [Category.assoc]
  rw [modelComparison_comp_hom_assoc, comm, reassoc_of% hc]

/-- The comparison with a model is equivariant at the universal pair of points: acting with the
gluing isomorphism of the modelled scheme and then comparing with the model is comparing with the
model and then acting with the model's gluing isomorphism. -/
lemma actPullback_modelComparison_universal {T₀ B₀ T B : Scheme.{u}} (a : T₀ ⟶ B₀) (b : T ⟶ B)
    (r : T ⟶ T₀) (s : B ⟶ B₀) (comm : r ≫ a = b ≫ s) (V : Over T₀) (W : Over T)
    (e : W ≅ (Over.pullback r).obj V) (q : pullback b b ⟶ pullback a a)
    (hqfst : q ≫ pullback.fst a a = pullback.fst b b ≫ r)
    (hqsnd : q ≫ pullback.snd a a = pullback.snd b b ≫ r)
    (ψ : (Over.pullback (pullback.fst a a)).obj V ≅ (Over.pullback (pullback.snd a a)).obj V)
    (χ : (Over.pullback (pullback.fst b b)).obj W ≅ (Over.pullback (pullback.snd b b)).obj W)
    (Lfst : (Over.pullback q).obj ((Over.pullback (pullback.fst a a)).obj V) ≅
      (Over.pullback (pullback.fst b b)).obj ((Over.pullback r).obj V))
    (Lsnd : (Over.pullback q).obj ((Over.pullback (pullback.snd a a)).obj V) ≅
      (Over.pullback (pullback.snd b b)).obj ((Over.pullback r).obj V))
    (hLfst : Lfst.hom.left ≫
        pullback.fst ((Over.pullback r).obj V).hom (pullback.fst b b) ≫ pullback.fst V.hom r =
      pullback.fst ((Over.pullback (pullback.fst a a)).obj V).hom q ≫
        pullback.fst V.hom (pullback.fst a a))
    (hLsnd : Lsnd.hom.left ≫
        pullback.fst ((Over.pullback r).obj V).hom (pullback.snd b b) ≫ pullback.fst V.hom r =
      pullback.fst ((Over.pullback (pullback.snd a a)).obj V).hom q ≫
        pullback.fst V.hom (pullback.snd a a))
    (hm : (Over.pullback q).map ψ.hom =
      Lfst.hom ≫ (Over.pullback (pullback.fst b b)).map e.inv ≫ χ.hom ≫
        (Over.pullback (pullback.snd b b)).map e.hom ≫ Lsnd.inv) :
    DescentDatum.actPullback V (DescentDatum.pullbackIsoOfBaseChangeIso a V ψ).hom
        (pullback.fst (W.hom ≫ b) b ≫ e.hom.left ≫ pullback.fst V.hom r)
        (pullback.snd (W.hom ≫ b) b ≫ r)
        (modelComparison_universal_cond a b r s comm V W e) =
      (DescentDatum.pullbackIsoOfBaseChangeIso b W χ).hom ≫ pullback.snd b (W.hom ≫ b) ≫
        e.hom.left ≫ pullback.fst V.hom r := by
  have hmfst := congrArg (fun k :
      (Over.pullback q).obj ((Over.pullback (pullback.fst a a)).obj V) ⟶
        (Over.pullback q).obj ((Over.pullback (pullback.snd a a)).obj V) ↦
    k.left ≫ pullback.fst ((Over.pullback (pullback.snd a a)).obj V).hom q ≫
      pullback.fst V.hom (pullback.snd a a)) hm
  simp only [Over.comp_left, Category.assoc, overPullback_map_left_fst_assoc,
    overIso_inv_left_comp Lsnd hLsnd] at hmfst
  have hΓ : ((Over.pullback (pullback.fst b b)).map e.hom).left ≫ Lfst.inv.left ≫
      Lfst.hom.left ≫ ((Over.pullback (pullback.fst b b)).map e.inv).left = 𝟙 _ := by
    have h1 : Lfst.inv.left ≫ Lfst.hom.left = 𝟙 _ := by
      rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
    have h2 : ((Over.pullback (pullback.fst b b)).map e.hom).left ≫
        ((Over.pullback (pullback.fst b b)).map e.inv).left = 𝟙 _ := by
      rw [← Over.comp_left, ← (Over.pullback (pullback.fst b b)).map_comp, Iso.hom_inv_id,
        (Over.pullback (pullback.fst b b)).map_id, Over.id_left]
    rw [← Category.assoc Lfst.inv.left, h1, Category.id_comp, h2]
  have hw : Lfst.inv.left ≫ pullback.snd ((Over.pullback (pullback.fst a a)).obj V).hom q =
      pullback.snd ((Over.pullback r).obj V).hom (pullback.fst b b) :=
    left_comp_pullback_snd_eq_hom Lfst.inv
  have hcond : pullback.fst ((Over.pullback (pullback.fst a a)).obj V).hom q ≫
        pullback.snd V.hom (pullback.fst a a) =
      pullback.snd ((Over.pullback (pullback.fst a a)).obj V).hom q ≫ q := pullback.condition
  have hDc : pullback.snd W.hom (pullback.fst b b) ≫ pullback.fst b b =
      pullback.fst W.hom (pullback.fst b b) ≫ W.hom := pullback.condition.symm
  have hpt : (pullbackRightPullbackFstIso b b W.hom).inv ≫
        ((Over.pullback (pullback.fst b b)).map e.hom).left ≫ Lfst.inv.left ≫
        pullback.fst ((Over.pullback (pullback.fst a a)).obj V).hom q =
      pullback.lift (pullback.fst (W.hom ≫ b) b ≫ e.hom.left ≫ pullback.fst V.hom r)
          (pullback.snd (W.hom ≫ b) b ≫ r)
          (modelComparison_universal_cond a b r s comm V W e) ≫
        (pullbackRightPullbackFstIso a a V.hom).inv := by
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc]
      rw [pullbackRightPullbackFstIso_inv_fst, pullback.lift_fst,
        overIso_inv_left_comp Lfst hLfst, overPullback_map_left_fst_assoc,
        pullbackRightPullbackFstIso_inv_fst_assoc]
    · simp only [Category.assoc]
      rw [hcond, reassoc_of% hw, overPullback_map_left_snd_assoc]
      refine pullback.hom_ext ?_ ?_
      · simp only [Category.assoc]
        rw [hqfst, reassoc_of% hDc, pullbackRightPullbackFstIso_inv_fst_assoc,
          pullbackRightPullbackFstIso_inv_snd_fst, pullback.lift_fst_assoc]
        simp only [Category.assoc]
        rw [modelComparison_comp_hom]
      · simp only [Category.assoc]
        rw [hqsnd, pullbackRightPullbackFstIso_inv_snd_snd_assoc,
          pullbackRightPullbackFstIso_inv_snd_snd, pullback.lift_snd]
  rw [DescentDatum.actPullback]
  simp only [DescentDatum.pullbackIsoOfBaseChangeIso_hom, Category.assoc,
    DescentDatum.sndProjPastingIso_hom_snd, DescentDatum.sndProjPastingIso_hom_snd_assoc]
  rw [← reassoc_of% hpt, hmfst, reassoc_of% hΓ]

/-- The comparison with a model is equivariant, at an arbitrary pair of points. -/
lemma actPullback_modelComparison {T₀ B₀ T B : Scheme.{u}} (a : T₀ ⟶ B₀) (b : T ⟶ B)
    (r : T ⟶ T₀) (s : B ⟶ B₀) (comm : r ≫ a = b ≫ s) (V : Over T₀) (W : Over T)
    (e : W ≅ (Over.pullback r).obj V) (q : pullback b b ⟶ pullback a a)
    (hqfst : q ≫ pullback.fst a a = pullback.fst b b ≫ r)
    (hqsnd : q ≫ pullback.snd a a = pullback.snd b b ≫ r)
    (ψ : (Over.pullback (pullback.fst a a)).obj V ≅ (Over.pullback (pullback.snd a a)).obj V)
    (χ : (Over.pullback (pullback.fst b b)).obj W ≅ (Over.pullback (pullback.snd b b)).obj W)
    (Lfst : (Over.pullback q).obj ((Over.pullback (pullback.fst a a)).obj V) ≅
      (Over.pullback (pullback.fst b b)).obj ((Over.pullback r).obj V))
    (Lsnd : (Over.pullback q).obj ((Over.pullback (pullback.snd a a)).obj V) ≅
      (Over.pullback (pullback.snd b b)).obj ((Over.pullback r).obj V))
    (hLfst : Lfst.hom.left ≫
        pullback.fst ((Over.pullback r).obj V).hom (pullback.fst b b) ≫ pullback.fst V.hom r =
      pullback.fst ((Over.pullback (pullback.fst a a)).obj V).hom q ≫
        pullback.fst V.hom (pullback.fst a a))
    (hLsnd : Lsnd.hom.left ≫
        pullback.fst ((Over.pullback r).obj V).hom (pullback.snd b b) ≫ pullback.fst V.hom r =
      pullback.fst ((Over.pullback (pullback.snd a a)).obj V).hom q ≫
        pullback.fst V.hom (pullback.snd a a))
    (hm : (Over.pullback q).map ψ.hom =
      Lfst.hom ≫ (Over.pullback (pullback.fst b b)).map e.inv ≫ χ.hom ≫
        (Over.pullback (pullback.snd b b)).map e.hom ≫ Lsnd.inv)
    {Z : Scheme.{u}} (v : Z ⟶ W.left) (x : Z ⟶ T) (hvx : v ≫ W.hom ≫ b = x ≫ b)
    (hvx' : (v ≫ e.hom.left ≫ pullback.fst V.hom r) ≫ V.hom ≫ a = (x ≫ r) ≫ a) :
    DescentDatum.actPullback V (DescentDatum.pullbackIsoOfBaseChangeIso a V ψ).hom
        (v ≫ e.hom.left ≫ pullback.fst V.hom r) (x ≫ r) hvx' =
      DescentDatum.actPullback W (DescentDatum.pullbackIsoOfBaseChangeIso b W χ).hom v x hvx ≫
        e.hom.left ≫ pullback.fst V.hom r := by
  have hfst : pullback.lift v x hvx ≫
      (pullback.fst (W.hom ≫ b) b ≫ e.hom.left ≫ pullback.fst V.hom r) =
      v ≫ e.hom.left ≫ pullback.fst V.hom r := by
    rw [← Category.assoc, pullback.lift_fst]
  have hsnd : pullback.lift v x hvx ≫ (pullback.snd (W.hom ≫ b) b ≫ r) = x ≫ r := by
    rw [← Category.assoc, pullback.lift_snd]
  have hcond2 : (pullback.lift v x hvx ≫ (pullback.fst (W.hom ≫ b) b ≫ e.hom.left ≫
          pullback.fst V.hom r)) ≫ V.hom ≫ a =
      (pullback.lift v x hvx ≫ (pullback.snd (W.hom ≫ b) b ≫ r)) ≫ a := by
    rwa [hfst, hsnd]
  rw [← DescentDatum.actPullback_congr V
      (DescentDatum.pullbackIsoOfBaseChangeIso a V ψ).hom hfst hsnd hcond2 hvx',
    ← DescentDatum.comp_actPullback V (DescentDatum.pullbackIsoOfBaseChangeIso a V ψ).hom
      (pullback.lift v x hvx)
      (pullback.fst (W.hom ≫ b) b ≫ e.hom.left ≫ pullback.fst V.hom r)
      (pullback.snd (W.hom ≫ b) b ≫ r)
      (modelComparison_universal_cond a b r s comm V W e) hcond2,
    actPullback_modelComparison_universal a b r s comm V W e q hqfst hqsnd ψ χ Lfst Lsnd
      hLfst hLsnd hm, DescentDatum.actPullback]
  simp only [Category.assoc]

/-- Both sides of the cocycle condition are carried across a comparison morphism `ε` that is
equivariant: a generalized point of the base change of `V` along the first projection of
`T₀ ×_{B₀} T₀ ×_{B₀} T₀`, whose three components come from a point of the corresponding scheme for
`W` through `ε`, is acted on the same way on either side. -/
lemma triAct_comp_comparison {T₀ B₀ T B : Scheme.{u}} (a : T₀ ⟶ B₀) (b : T ⟶ B) (r : T ⟶ T₀)
    (s : B ⟶ B₀) (comm : r ≫ a = b ≫ s) (V : Over T₀) (W : Over T) (ε : W.left ⟶ V.left)
    (hε : ε ≫ V.hom = W.hom ≫ r)
    (τ : pullback (V.hom ≫ a) a ⟶ pullback a (V.hom ≫ a))
    (hτ : τ ≫ pullback.snd a (V.hom ≫ a) ≫ V.hom = pullback.snd (V.hom ≫ a) a)
    (ι : pullback (W.hom ≫ b) b ⟶ pullback b (W.hom ≫ b))
    (hι : ι ≫ pullback.snd b (W.hom ≫ b) ≫ W.hom = pullback.snd (W.hom ≫ b) b)
    (hequiv : ∀ {Y : Scheme.{u}} (v : Y ⟶ W.left) (x : Y ⟶ T)
      (hvx : v ≫ W.hom ≫ b = x ≫ b)
      (hvx' : (v ≫ ε) ≫ V.hom ≫ a = (x ≫ r) ≫ a),
      DescentDatum.actPullback V τ (v ≫ ε) (x ≫ r) hvx' =
        DescentDatum.actPullback W ι v x hvx ≫ ε)
    {Z : Scheme.{u}} (G : Z ⟶ pullback V.hom (DescentDatum.tripleBaseFst a))
    (H : Z ⟶ pullback W.hom (DescentDatum.tripleBaseFst b))
    (v : Z ⟶ W.left) (x y : Z ⟶ T)
    (hHv : H ≫ pullback.fst W.hom (DescentDatum.tripleBaseFst b) = v)
    (hHx : H ≫ pullback.snd W.hom (DescentDatum.tripleBaseFst b) ≫
      DescentDatum.tripleBaseSnd b = x)
    (hHy : H ≫ pullback.snd W.hom (DescentDatum.tripleBaseFst b) ≫
      DescentDatum.tripleBaseThd b = y)
    (hGv : G ≫ pullback.fst V.hom (DescentDatum.tripleBaseFst a) = v ≫ ε)
    (hGx : G ≫ pullback.snd V.hom (DescentDatum.tripleBaseFst a) ≫
      DescentDatum.tripleBaseSnd a = x ≫ r)
    (hGy : G ≫ pullback.snd V.hom (DescentDatum.tripleBaseFst a) ≫
      DescentDatum.tripleBaseThd a = y ≫ r)
    (hv : v ≫ W.hom ≫ b = x ≫ b) (hw : x ≫ b = y ≫ b) :
    G ≫ DescentDatum.triActTwice a V τ hτ =
        (H ≫ DescentDatum.triActTwice b W ι hι) ≫ ε ∧
      G ≫ DescentDatum.triActOnce a V τ = (H ≫ DescentDatum.triActOnce b W ι) ≫ ε := by
  have hc1 : (v ≫ ε) ≫ V.hom ≫ a = (x ≫ r) ≫ a := by
    simp only [Category.assoc]
    rw [reassoc_of% hε, comm, reassoc_of% hv]
  have hc2 : (x ≫ r) ≫ a = (y ≫ r) ≫ a := by
    simp only [Category.assoc]
    rw [comm, reassoc_of% hw]
  have hcAct : (DescentDatum.actPullback W ι v x hv ≫ ε) ≫ V.hom ≫ a = (y ≫ r) ≫ a := by
    simp only [Category.assoc]
    rw [reassoc_of% hε, comm,
      reassoc_of% (DescentDatum.actPullback_comp_hom_comp W ι hι v x y hv hw)]
  refine ⟨?_, ?_⟩
  · rw [DescentDatum.comp_triActTwice a V τ hτ G (v ≫ ε) (x ≫ r) (y ≫ r) hGv hGx hGy hc1 hc2,
      DescentDatum.comp_triActTwice b W ι hι H v x y hHv hHx hHy hv hw,
      DescentDatum.actPullback_congr V τ (hequiv v x hv hc1) rfl _ hcAct]
    exact hequiv (DescentDatum.actPullback W ι v x hv) y
      (DescentDatum.actPullback_comp_hom_comp W ι hι v x y hv hw) hcAct
  · rw [DescentDatum.comp_triActOnce a V τ G (v ≫ ε) (y ≫ r) hGv hGy (hc1.trans hc2),
      DescentDatum.comp_triActOnce b W ι H v y hHv hHy (hv.trans hw)]
    exact hequiv v y (hv.trans hw) (hc1.trans hc2)

namespace LimitDatum

variable {I : Type u} [Category.{u} I] {𝒳 𝒮 : I ⥤ Scheme.{u}} (φ : 𝒳 ⟶ 𝒮)
  {cX : Cone 𝒳} {cS : Cone 𝒮} (f : cX.pt ⟶ cS.pt)
  (hf : ∀ i, cX.π.app i ≫ φ.app i = f ≫ cS.π.app i)

include hf

/-- The gluing isomorphism of a descent datum, read at a stage model of its underlying scheme: an
identification `e` of the underlying scheme of `D` with the base change of a scheme `V` over the
stage turns the gluing isomorphism of `D` into an isomorphism between the two base changes of `V`
to `X ×_S X` through the stage's double fibre product. -/
def stageTransitionIso (D : DescentDatum f) (i : I) (V : Over (𝒳.obj i))
    (e : D.over ≅ (Over.pullback (cX.π.app i)).obj V) :
    (Over.pullback ((sqCone φ f hf).π.app i)).obj
        ((Over.pullback (pullback.fst (φ.app i) (φ.app i))).obj V) ≅
      (Over.pullback ((sqCone φ f hf).π.app i)).obj
        ((Over.pullback (pullback.snd (φ.app i) (φ.app i))).obj V) :=
  sqLegFstIso φ f hf i V ≪≫ (Over.pullback (pullback.fst f f)).mapIso e.symm ≪≫
    DescentDatum.transitionBaseChangeIso f D ≪≫
      (Over.pullback (pullback.snd f f)).mapIso e ≪≫ (sqLegSndIso φ f hf i V).symm

/-- `V` with the isomorphism `ψ` and the identification `e` is a model of the descent datum `D` at
the stage `i`: the base change of `ψ` to `X ×_S X` is the gluing isomorphism of `D`, read through
the identification `e` of the underlying scheme of `D` with the base change of `V`. -/
def IsStageModel (D : DescentDatum f) (i : I) (V : Over (𝒳.obj i))
    (ψ : (Over.pullback (pullback.fst (φ.app i) (φ.app i))).obj V ≅
      (Over.pullback (pullback.snd (φ.app i) (φ.app i))).obj V)
    (e : D.over ≅ (Over.pullback (cX.π.app i)).obj V) : Prop :=
  (Over.pullback ((sqCone φ f hf).π.app i)).map ψ.hom = (stageTransitionIso φ f hf D i V e).hom

/-- The composite of the first projections of the gluing isomorphism read at a stage model. -/
lemma stageTransitionIso_hom_left_fst (D : DescentDatum f) (i : I) (V : Over (𝒳.obj i))
    (e : D.over ≅ (Over.pullback (cX.π.app i)).obj V) :
    (stageTransitionIso φ f hf D i V e).hom.left ≫
        pullback.fst ((Over.pullback (pullback.snd (φ.app i) (φ.app i))).obj V).hom
            ((sqCone φ f hf).π.app i) ≫
          pullback.fst V.hom (pullback.snd (φ.app i) (φ.app i)) =
      (sqLegFstIso φ f hf i V).hom.left ≫
        ((Over.pullback (pullback.fst f f)).map e.inv).left ≫
          (pullbackRightPullbackFstIso f f D.over.hom).hom ≫
            D.transitionPullbackIso.hom ≫ pullback.snd f (D.over.hom ≫ f) ≫
              e.hom.left ≫ pullback.fst V.hom (cX.π.app i) := by
  have hsnd := overIso_inv_left_comp (sqLegSndIso φ f hf i V)
    (sqLegSndIso_hom_left_fst φ f hf i V)
  rw [stageTransitionIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Over.comp_left, Category.assoc]
  rw [hsnd, overPullback_map_left_fst_assoc,
    DescentDatum.transitionBaseChangeIso_hom_left, Category.assoc, Category.assoc,
    DescentDatum.sndProjPastingIso_inv_fst_assoc]
  rfl

/-- The gluing isomorphism read at a stage model, unfolded. -/
lemma stageTransitionIso_hom (D : DescentDatum f) (i : I) (V : Over (𝒳.obj i))
    (e : D.over ≅ (Over.pullback (cX.π.app i)).obj V) :
    (stageTransitionIso φ f hf D i V e).hom =
      (sqLegFstIso φ f hf i V).hom ≫ (Over.pullback (pullback.fst f f)).map e.inv ≫
        (DescentDatum.transitionBaseChangeIso f D).hom ≫
          (Over.pullback (pullback.snd f f)).map e.hom ≫ (sqLegSndIso φ f hf i V).inv :=
  rfl

/-! ### Reindexing a stage model along a transition morphism -/

/-- The reindexing isomorphisms of the first projection commute with a comparison isomorphism
pinned by its first projection. -/
lemma sqLegFstIso_reindex {i j : I} (m : j ⟶ i) (W : Over (𝒳.obj i))
    (α : (Over.pullback ((sqCone φ f hf).π.app j)).obj
          ((Over.pullback ((sqDiagram φ).map m)).obj
            ((Over.pullback (pullback.fst (φ.app i) (φ.app i))).obj W)) ≅
        (Over.pullback ((sqCone φ f hf).π.app i)).obj
          ((Over.pullback (pullback.fst (φ.app i) (φ.app i))).obj W))
    (hα : α.hom.left ≫
        pullback.fst ((Over.pullback (pullback.fst (φ.app i) (φ.app i))).obj W).hom
          ((sqCone φ f hf).π.app i) =
      pullback.fst ((Over.pullback ((sqDiagram φ).map m)).obj
          ((Over.pullback (pullback.fst (φ.app i) (φ.app i))).obj W)).hom
          ((sqCone φ f hf).π.app j) ≫
        pullback.fst ((Over.pullback (pullback.fst (φ.app i) (φ.app i))).obj W).hom
          ((sqDiagram φ).map m)) :
    (Over.pullback ((sqCone φ f hf).π.app j)).map (sqMapFstIso φ m W).inv ≫ α.hom ≫
        (sqLegFstIso φ f hf i W).hom =
      (sqLegFstIso φ f hf j ((Over.pullback (𝒳.map m)).obj W)).hom ≫
        (Over.pullback (pullback.fst f f)).map
          (overPullbackCompIso (𝒳.map m) (cX.π.app j) (cX.π.app i) (cX.w m) W).hom := by
  refine overPullback_comp_hom_ext ?_
  simp only [Over.comp_left, Category.assoc]
  rw [sqLegFstIso_hom_left_fst φ f hf i W, reassoc_of% hα]
  simp only [overPullback_map_left_fst_assoc]
  rw [overIso_inv_left_comp (sqMapFstIso φ m W) (sqMapFstIso_hom_left_fst φ m W),
    overPullbackCompIso_fst (𝒳.map m) (cX.π.app j) (cX.π.app i) (cX.w m) W,
    reassoc_of% (sqLegFstIso_hom_left_fst φ f hf j ((Over.pullback (𝒳.map m)).obj W))]

/-- The reindexing isomorphisms of the second projection commute with a comparison isomorphism
pinned by its first projection. -/
lemma sqLegSndIso_reindex {i j : I} (m : j ⟶ i) (W : Over (𝒳.obj i))
    (β : (Over.pullback ((sqCone φ f hf).π.app j)).obj
          ((Over.pullback ((sqDiagram φ).map m)).obj
            ((Over.pullback (pullback.snd (φ.app i) (φ.app i))).obj W)) ≅
        (Over.pullback ((sqCone φ f hf).π.app i)).obj
          ((Over.pullback (pullback.snd (φ.app i) (φ.app i))).obj W))
    (hβ : β.hom.left ≫
        pullback.fst ((Over.pullback (pullback.snd (φ.app i) (φ.app i))).obj W).hom
          ((sqCone φ f hf).π.app i) =
      pullback.fst ((Over.pullback ((sqDiagram φ).map m)).obj
          ((Over.pullback (pullback.snd (φ.app i) (φ.app i))).obj W)).hom
          ((sqCone φ f hf).π.app j) ≫
        pullback.fst ((Over.pullback (pullback.snd (φ.app i) (φ.app i))).obj W).hom
          ((sqDiagram φ).map m)) :
    (Over.pullback ((sqCone φ f hf).π.app j)).map (sqMapSndIso φ m W).inv ≫ β.hom ≫
        (sqLegSndIso φ f hf i W).hom =
      (sqLegSndIso φ f hf j ((Over.pullback (𝒳.map m)).obj W)).hom ≫
        (Over.pullback (pullback.snd f f)).map
          (overPullbackCompIso (𝒳.map m) (cX.π.app j) (cX.π.app i) (cX.w m) W).hom := by
  refine overPullback_comp_hom_ext ?_
  simp only [Over.comp_left, Category.assoc]
  rw [sqLegSndIso_hom_left_fst φ f hf i W, reassoc_of% hβ]
  simp only [overPullback_map_left_fst_assoc]
  rw [overIso_inv_left_comp (sqMapSndIso φ m W) (sqMapSndIso_hom_left_fst φ m W),
    overPullbackCompIso_fst (𝒳.map m) (cX.π.app j) (cX.π.app i) (cX.w m) W,
    reassoc_of% (sqLegSndIso_hom_left_fst φ f hf j ((Over.pullback (𝒳.map m)).obj W))]

/-! ### Transporting a stage model to a later stage -/

/-- An isomorphism `χ` over a later stage's double fibre product whose base change to `X ×_S X` is
the gluing isomorphism of `D`, up to two comparison isomorphisms pinned by their first projections,
is a model of `D` at that stage. -/
lemma isStageModel_descend (D : DescentDatum f) {i j : I} (m : j ⟶ i) (V : Over (𝒳.obj i))
    (e : D.over ≅ (Over.pullback (cX.π.app i)).obj V)
    (χ : (Over.pullback ((sqDiagram φ).map m)).obj
          ((Over.pullback (pullback.fst (φ.app i) (φ.app i))).obj V) ≅
        (Over.pullback ((sqDiagram φ).map m)).obj
          ((Over.pullback (pullback.snd (φ.app i) (φ.app i))).obj V))
    (α : (Over.pullback ((sqCone φ f hf).π.app j)).obj
          ((Over.pullback ((sqDiagram φ).map m)).obj
            ((Over.pullback (pullback.fst (φ.app i) (φ.app i))).obj V)) ≅
        (Over.pullback ((sqCone φ f hf).π.app i)).obj
          ((Over.pullback (pullback.fst (φ.app i) (φ.app i))).obj V))
    (β : (Over.pullback ((sqCone φ f hf).π.app j)).obj
          ((Over.pullback ((sqDiagram φ).map m)).obj
            ((Over.pullback (pullback.snd (φ.app i) (φ.app i))).obj V)) ≅
        (Over.pullback ((sqCone φ f hf).π.app i)).obj
          ((Over.pullback (pullback.snd (φ.app i) (φ.app i))).obj V))
    (hα : α.hom.left ≫
        pullback.fst ((Over.pullback (pullback.fst (φ.app i) (φ.app i))).obj V).hom
          ((sqCone φ f hf).π.app i) =
      pullback.fst ((Over.pullback ((sqDiagram φ).map m)).obj
          ((Over.pullback (pullback.fst (φ.app i) (φ.app i))).obj V)).hom
          ((sqCone φ f hf).π.app j) ≫
        pullback.fst ((Over.pullback (pullback.fst (φ.app i) (φ.app i))).obj V).hom
          ((sqDiagram φ).map m))
    (hβ : β.hom.left ≫
        pullback.fst ((Over.pullback (pullback.snd (φ.app i) (φ.app i))).obj V).hom
          ((sqCone φ f hf).π.app i) =
      pullback.fst ((Over.pullback ((sqDiagram φ).map m)).obj
          ((Over.pullback (pullback.snd (φ.app i) (φ.app i))).obj V)).hom
          ((sqCone φ f hf).π.app j) ≫
        pullback.fst ((Over.pullback (pullback.snd (φ.app i) (φ.app i))).obj V).hom
          ((sqDiagram φ).map m))
    (hcomm : α.hom ≫ (stageTransitionIso φ f hf D i V e).hom =
      (Over.pullback ((sqCone φ f hf).π.app j)).map χ.hom ≫ β.hom) :
    IsStageModel φ f hf D j ((Over.pullback (𝒳.map m)).obj V)
      ((sqMapFstIso φ m V).symm ≪≫ χ ≪≫ sqMapSndIso φ m V)
      (e ≪≫ (overPullbackCompIso (𝒳.map m) (cX.π.app j) (cX.π.app i) (cX.w m) V).symm) := by
  have hχ : (Over.pullback ((sqCone φ f hf).π.app j)).map χ.hom =
      α.hom ≫ (stageTransitionIso φ f hf D i V e).hom ≫ β.inv := by
    rw [← Category.assoc, hcomm, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hsndInv : (sqLegSndIso φ f hf i V).inv ≫ β.inv ≫
        (Over.pullback ((sqCone φ f hf).π.app j)).map (sqMapSndIso φ m V).hom =
      (Over.pullback (pullback.snd f f)).map
          (overPullbackCompIso (𝒳.map m) (cX.π.app j) (cX.π.app i) (cX.w m) V).inv ≫
        (sqLegSndIso φ f hf j ((Over.pullback (𝒳.map m)).obj V)).inv := by
    have h : ((Over.pullback ((sqCone φ f hf).π.app j)).mapIso (sqMapSndIso φ m V).symm ≪≫
          β ≪≫ sqLegSndIso φ f hf i V) =
        (sqLegSndIso φ f hf j ((Over.pullback (𝒳.map m)).obj V) ≪≫
          (Over.pullback (pullback.snd f f)).mapIso
            (overPullbackCompIso (𝒳.map m) (cX.π.app j) (cX.π.app i) (cX.w m) V)) :=
      Iso.ext (by
        simpa only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc] using
          sqLegSndIso_reindex φ f hf m V β hβ)
    simpa only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Category.assoc] using
      congrArg Iso.inv h
  rw [IsStageModel, stageTransitionIso_hom]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.map_comp, Category.assoc, hχ,
    stageTransitionIso_hom, Iso.trans_inv, Iso.symm_inv]
  rw [reassoc_of% (sqLegFstIso_reindex φ f hf m V α hα), hsndInv]

/-- A stage model reindexes to any later stage. -/
lemma isStageModel_reindex (D : DescentDatum f) {i : I} (V : Over (𝒳.obj i))
    (ψ : (Over.pullback (pullback.fst (φ.app i) (φ.app i))).obj V ≅
      (Over.pullback (pullback.snd (φ.app i) (φ.app i))).obj V)
    (e : D.over ≅ (Over.pullback (cX.π.app i)).obj V)
    (hm : IsStageModel φ f hf D i V ψ e) {j : I} (m : j ⟶ i) :
    IsStageModel φ f hf D j ((Over.pullback (𝒳.map m)).obj V) (sqReindexIso φ m V ψ)
      (e ≪≫ (overPullbackCompIso (𝒳.map m) (cX.π.app j) (cX.π.app i) (cX.w m) V).symm) :=
  isStageModel_descend φ f hf D m V e ((Over.pullback ((sqDiagram φ).map m)).mapIso ψ)
    (overPullbackCompIso ((sqDiagram φ).map m) ((sqCone φ f hf).π.app j)
      ((sqCone φ f hf).π.app i) ((sqCone φ f hf).w m) _)
    (overPullbackCompIso ((sqDiagram φ).map m) ((sqCone φ f hf).π.app j)
      ((sqCone φ f hf).π.app i) ((sqCone φ f hf).w m) _)
    (overPullbackCompIso_fst _ _ _ _ _) (overPullbackCompIso_fst _ _ _ _ _)
    (by
      rw [← hm]
      exact overPullbackCompIso_naturality ((sqDiagram φ).map m) ((sqCone φ f hf).π.app j)
        ((sqCone φ f hf).π.app i) ((sqCone φ f hf).w m) ψ.hom)

/-! ### Existence of a stage model -/

/-- A descent datum whose underlying scheme is of finite presentation has a model at some stage. -/
theorem exists_stageModel [IsCofiltered I] [EssentiallySmall.{u} I]
    [∀ i, IsAffine (𝒳.obj i)] [∀ i, IsAffine (𝒮.obj i)]
    (hX : IsLimit cX) (hS : IsLimit cS) (D : DescentDatum f)
    (hD : FinitePresentation D.over.hom) :
    ∃ (i : I) (V : Over (𝒳.obj i))
      (ψ : (Over.pullback (pullback.fst (φ.app i) (φ.app i))).obj V ≅
        (Over.pullback (pullback.snd (φ.app i) (φ.app i))).obj V)
      (e : D.over ≅ (Over.pullback (cX.π.app i)).obj V),
      FinitePresentation V.hom ∧ IsStageModel φ f hf D i V ψ e := by
  have {i j : I} (m : i ⟶ j) : IsAffineHom (𝒳.map m) := inferInstance
  have (i : I) : CompactSpace (𝒳.obj i) := inferInstance
  have (i : I) : QuasiSeparatedSpace (𝒳.obj i) := inferInstance
  obtain ⟨i₀, V₀, hV₀, ⟨e₀⟩⟩ :=
    LimitFPObjectDescent.exists_model_of_finitePresentation 𝒳 cX hX D.over hD
  have {i j : I} (m : i ⟶ j) : IsAffineHom ((sqDiagram φ).map m) := inferInstance
  have (i : I) : CompactSpace ((sqDiagram φ).obj i) := inferInstance
  have (i : I) : QuasiSeparatedSpace ((sqDiagram φ).obj i) := inferInstance
  obtain ⟨j, m, χ, α, β, hα, hβ, hcomm⟩ :=
    exists_iso_after_baseChange_compat (sqDiagram φ) (sqCone φ f hf)
      (sqIsLimit φ f hf hX hS) i₀
      ((Over.pullback (pullback.fst (φ.app i₀) (φ.app i₀))).obj V₀)
      ((Over.pullback (pullback.snd (φ.app i₀) (φ.app i₀))).obj V₀)
      (LimitFPObjectDescent.finitePresentation_overPullback _ V₀ hV₀)
      (LimitFPObjectDescent.finitePresentation_overPullback _ V₀ hV₀)
      (stageTransitionIso φ f hf D i₀ V₀ e₀)
  exact ⟨j, (Over.pullback (𝒳.map m)).obj V₀,
    (sqMapFstIso φ m V₀).symm ≪≫ χ ≪≫ sqMapSndIso φ m V₀,
    e₀ ≪≫ (overPullbackCompIso (𝒳.map m) (cX.π.app j) (cX.π.app i₀) (cX.w m) V₀).symm,
    LimitFPObjectDescent.finitePresentation_overPullback _ V₀ hV₀,
    isStageModel_descend φ f hf D m V₀ e₀ χ α β hα hβ hcomm⟩

/-! ### The comparison with a stage model is equivariant -/

variable (D : DescentDatum f) (i : I) (V : Over (𝒳.obj i))
  (ψ : (Over.pullback (pullback.fst (φ.app i) (φ.app i))).obj V ≅
    (Over.pullback (pullback.snd (φ.app i) (φ.app i))).obj V)
  (e : D.over ≅ (Over.pullback (cX.π.app i)).obj V)

/-- The comparison with a stage model is equivariant at the universal pair of points: acting with
the gluing isomorphism of `D` and then comparing with the stage is comparing with the stage and
then acting with the model's gluing isomorphism. -/
lemma actPullback_stageComparison_universal (hm : IsStageModel φ f hf D i V ψ e) :
    DescentDatum.actPullback V
        (DescentDatum.pullbackIsoOfBaseChangeIso (φ.app i) V ψ).hom
        (pullback.fst (D.over.hom ≫ f) f ≫ e.hom.left ≫ pullback.fst V.hom (cX.π.app i))
        (pullback.snd (D.over.hom ≫ f) f ≫ cX.π.app i)
        (modelComparison_universal_cond (φ.app i) f (cX.π.app i) (cS.π.app i) (hf i) V
          D.over e) =
      D.transitionPullbackIso.hom ≫ pullback.snd f (D.over.hom ≫ f) ≫
        e.hom.left ≫ pullback.fst V.hom (cX.π.app i) :=
  (actPullback_modelComparison_universal (φ.app i) f (cX.π.app i) (cS.π.app i) (hf i) V D.over e
      ((sqCone φ f hf).π.app i) (FibreProductLimit.cone_π_app_fst φ φ f f hf hf i)
      (FibreProductLimit.cone_π_app_snd φ φ f f hf hf i) ψ
      (DescentDatum.transitionBaseChangeIso f D) (sqLegFstIso φ f hf i V)
      (sqLegSndIso φ f hf i V) (sqLegFstIso_hom_left_fst φ f hf i V)
      (sqLegSndIso_hom_left_fst φ f hf i V)
      (hm.trans (stageTransitionIso_hom φ f hf D i V e))).trans (by
    rw [DescentDatum.pullbackIsoOfBaseChangeIso_transitionBaseChangeIso_hom])

/-- The comparison with a stage model is equivariant, at an arbitrary pair of points. -/
lemma actPullback_stageComparison (hm : IsStageModel φ f hf D i V ψ e)
    {Z : Scheme.{u}} (v : Z ⟶ D.over.left) (x : Z ⟶ cX.pt)
    (hvx : v ≫ D.over.hom ≫ f = x ≫ f)
    (hvx' : (v ≫ e.hom.left ≫ pullback.fst V.hom (cX.π.app i)) ≫ V.hom ≫ φ.app i =
      (x ≫ cX.π.app i) ≫ φ.app i) :
    DescentDatum.actPullback V
        (DescentDatum.pullbackIsoOfBaseChangeIso (φ.app i) V ψ).hom
        (v ≫ e.hom.left ≫ pullback.fst V.hom (cX.π.app i)) (x ≫ cX.π.app i) hvx' =
      DescentDatum.actPullback D.over D.transitionPullbackIso.hom v x hvx ≫
        e.hom.left ≫ pullback.fst V.hom (cX.π.app i) := by
  refine (actPullback_modelComparison (φ.app i) f (cX.π.app i) (cS.π.app i) (hf i) V D.over e
      ((sqCone φ f hf).π.app i) (FibreProductLimit.cone_π_app_fst φ φ f f hf hf i)
      (FibreProductLimit.cone_π_app_snd φ φ f f hf hf i) ψ
      (DescentDatum.transitionBaseChangeIso f D) (sqLegFstIso φ f hf i V)
      (sqLegSndIso φ f hf i V) (sqLegFstIso_hom_left_fst φ f hf i V)
      (sqLegSndIso_hom_left_fst φ f hf i V)
      (hm.trans (stageTransitionIso_hom φ f hf D i V e)) v x hvx hvx').trans ?_
  rw [DescentDatum.pullbackIsoOfBaseChangeIso_transitionBaseChangeIso_hom]

end LimitDatum

end AlgebraicGeometry

end
