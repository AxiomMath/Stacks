module

public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.StageIso

/-!
# The cocycle condition of a stage model holds at a later stage

Let `f : X ⟶ S` be the limit of a cofiltered system of morphisms `f_i : X_i ⟶ S_i` of affine
schemes and let `D` be a descent datum relative to `X / S` with a model at a stage `i`: a scheme
`V` over `X_i`, an isomorphism `ψ` of its two base changes to `X_i ×_{S_i} X_i`, and an
identification of the underlying scheme of `D` with the base change of `V`. The candidate gluing
isomorphism `ψ` determines need not satisfy the cocycle condition at the stage `i` itself; but
the two sides of the condition are two morphisms between base changes over the stage's triple
fibre product, they agree after base change to `X ×_S X ×_S X` because `D`'s own gluing
isomorphism satisfies the cocycle condition there, and therefore they agree at some later stage
by [Stacks, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM) part (3).

## Main results

* `AlgebraicGeometry.LimitDatum.actPullback_sqReindexIso`: the action of the reindexing of a
  stage gluing isomorphism to a later stage is the action of the original one.
* `AlgebraicGeometry.LimitDatum.exists_stage_actPullbackLaw`: **the candidate gluing isomorphism
  of a stage model satisfies the cocycle condition after passing to a later stage.**

## References

* [Stacks Project, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP)
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

namespace DescentDatum

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **Two action-like morphisms over the triple fibre product have equal base changes exactly
when they agree on the universal point of that base change.** -/
lemma overPullback_map_triOverHom_eq_iff {Z : Scheme.{u}}
    (p : Z ⟶ pullback (pullback.fst f f ≫ f) f) (V : Over X)
    (w w' : pullback V.hom (tripleBaseFst f) ⟶ V.left)
    (hw : w ≫ V.hom = pullback.snd V.hom (tripleBaseFst f) ≫ tripleBaseThd f)
    (hw' : w' ≫ V.hom = pullback.snd V.hom (tripleBaseFst f) ≫ tripleBaseThd f) :
    (Over.pullback p).map (triOverHom f V w hw) =
        (Over.pullback p).map (triOverHom f V w' hw') ↔
      pullback.fst ((Over.pullback (tripleBaseFst f)).obj V).hom p ≫ w =
        pullback.fst ((Over.pullback (tripleBaseFst f)).obj V).hom p ≫ w' := by
  constructor
  · intro h
    have h' := congrArg (fun k :
        (Over.pullback p).obj ((Over.pullback (tripleBaseFst f)).obj V) ⟶
          (Over.pullback p).obj ((Over.pullback (tripleBaseThd f)).obj V) ↦
      k.left ≫ pullback.fst ((Over.pullback (tripleBaseThd f)).obj V).hom p ≫
        pullback.fst V.hom (tripleBaseThd f)) h
    simpa only [overPullback_map_left_fst_assoc, triOverHom_left_fst] using h'
  · intro h
    refine overPullback_comp_hom_ext ?_
    simpa only [overPullback_map_left_fst_assoc, triOverHom_left_fst] using h

end DescentDatum

namespace LimitDatum

variable {I : Type u} [Category.{u} I] {𝒳 𝒮 : I ⥤ Scheme.{u}} (φ : 𝒳 ⟶ 𝒮)
  {cX : Cone 𝒳} {cS : Cone 𝒮} (f : cX.pt ⟶ cS.pt)
  (hf : ∀ i, cX.π.app i ≫ φ.app i = f ≫ cS.π.app i)

/-! ### Reindexing the action to a later stage -/

/-- **The action of the reindexing of a stage gluing isomorphism to a later stage**, read
through the first projection, is the action of the original one. -/
lemma actPullback_sqReindexIso {i j : I} (m : j ⟶ i) (V : Over (𝒳.obj i))
    (ψ : (Over.pullback (pullback.fst (φ.app i) (φ.app i))).obj V ≅
      (Over.pullback (pullback.snd (φ.app i) (φ.app i))).obj V)
    {Z : Scheme.{u}} (v : Z ⟶ ((Over.pullback (𝒳.map m)).obj V).left) (x : Z ⟶ 𝒳.obj j)
    (hvx : v ≫ ((Over.pullback (𝒳.map m)).obj V).hom ≫ φ.app j = x ≫ φ.app j)
    (hvx' : (v ≫ pullback.fst V.hom (𝒳.map m)) ≫ V.hom ≫ φ.app i =
      (x ≫ 𝒳.map m) ≫ φ.app i) :
    DescentDatum.actPullback V (DescentDatum.pullbackIsoOfBaseChangeIso (φ.app i) V ψ).hom
        (v ≫ pullback.fst V.hom (𝒳.map m)) (x ≫ 𝒳.map m) hvx' =
      DescentDatum.actPullback ((Over.pullback (𝒳.map m)).obj V)
          (DescentDatum.pullbackIsoOfBaseChangeIso (φ.app j) ((Over.pullback (𝒳.map m)).obj V)
            (sqReindexIso φ m V ψ)).hom v x hvx ≫
        pullback.fst V.hom (𝒳.map m) := by
  have hmk : (Over.pullback ((sqDiagram φ).map m)).map ψ.hom =
      (sqMapFstIso φ m V).hom ≫
        (Over.pullback (pullback.fst (φ.app j) (φ.app j))).map
            (Iso.refl ((Over.pullback (𝒳.map m)).obj V)).inv ≫
          (sqReindexIso φ m V ψ).hom ≫
            (Over.pullback (pullback.snd (φ.app j) (φ.app j))).map
                (Iso.refl ((Over.pullback (𝒳.map m)).obj V)).hom ≫
              (sqMapSndIso φ m V).inv := by
    simp
  have hid : v ≫ (Iso.refl ((Over.pullback (𝒳.map m)).obj V)).hom.left ≫
      pullback.fst V.hom (𝒳.map m) = v ≫ pullback.fst V.hom (𝒳.map m) := by
    rw [Iso.refl_hom, Over.id_left, Category.id_comp]
  have hvx'' : (v ≫ (Iso.refl ((Over.pullback (𝒳.map m)).obj V)).hom.left ≫
        pullback.fst V.hom (𝒳.map m)) ≫ V.hom ≫ φ.app i = (x ≫ 𝒳.map m) ≫ φ.app i := by
    rwa [hid]
  rw [← DescentDatum.actPullback_congr V
      (DescentDatum.pullbackIsoOfBaseChangeIso (φ.app i) V ψ).hom hid rfl hvx'' hvx',
    actPullback_modelComparison (φ.app i) (φ.app j) (𝒳.map m) (𝒮.map m) (φ.naturality m) V
      ((Over.pullback (𝒳.map m)).obj V) (Iso.refl _) ((sqDiagram φ).map m)
      (FibreProductLimit.diagram_map_fst φ φ m) (FibreProductLimit.diagram_map_snd φ φ m)
      ψ (sqReindexIso φ m V ψ) (sqMapFstIso φ m V) (sqMapSndIso φ m V)
      (sqMapFstIso_hom_left_fst φ m V) (sqMapSndIso_hom_left_fst φ m V) hmk v x hvx hvx'',
    Iso.refl_hom, Over.id_left, Category.id_comp]

/-! ### The two sides of the cocycle condition over the limit -/

/-- `triAct_comp_comparison`, with the generalized points `G` and `H` of the two triple fibre
products given by the universal point of the base change along `q` and an isomorphism `θ` of
iterated base changes. -/
private theorem triAct_comp_comparison_of_iso {T₀ B₀ T B : Scheme.{u}} (a : T₀ ⟶ B₀) (b : T ⟶ B)
    (r : T ⟶ T₀) (s : B ⟶ B₀) (comm : r ≫ a = b ≫ s) (V : Over T₀) (W : Over T)
    (ε : W.left ⟶ V.left) (hε : ε ≫ V.hom = W.hom ≫ r)
    (τ : pullback (V.hom ≫ a) a ⟶ pullback a (V.hom ≫ a))
    (hτ : τ ≫ pullback.snd a (V.hom ≫ a) ≫ V.hom = pullback.snd (V.hom ≫ a) a)
    (ι : pullback (W.hom ≫ b) b ⟶ pullback b (W.hom ≫ b))
    (hι : ι ≫ pullback.snd b (W.hom ≫ b) ≫ W.hom = pullback.snd (W.hom ≫ b) b)
    (hequiv : ∀ {Y : Scheme.{u}} (v : Y ⟶ W.left) (x : Y ⟶ T)
      (hvx : v ≫ W.hom ≫ b = x ≫ b)
      (hvx' : (v ≫ ε) ≫ V.hom ≫ a = (x ≫ r) ≫ a),
      DescentDatum.actPullback V τ (v ≫ ε) (x ≫ r) hvx' =
        DescentDatum.actPullback W ι v x hvx ≫ ε)
    (q : pullback (pullback.fst b b ≫ b) b ⟶ pullback (pullback.fst a a ≫ a) a)
    (hq₂ : q ≫ DescentDatum.tripleBaseSnd a = DescentDatum.tripleBaseSnd b ≫ r)
    (hq₃ : q ≫ DescentDatum.tripleBaseThd a = DescentDatum.tripleBaseThd b ≫ r)
    (θ : (Over.pullback q).obj ((Over.pullback (DescentDatum.tripleBaseFst a)).obj V) ≅
      (Over.pullback (DescentDatum.tripleBaseFst b)).obj W)
    (hθ : θ.hom.left ≫ pullback.fst W.hom (DescentDatum.tripleBaseFst b) ≫ ε =
      pullback.fst ((Over.pullback (DescentDatum.tripleBaseFst a)).obj V).hom q ≫
        pullback.fst V.hom (DescentDatum.tripleBaseFst a)) :
    pullback.fst ((Over.pullback (DescentDatum.tripleBaseFst a)).obj V).hom q ≫
        DescentDatum.triActTwice a V τ hτ =
      (θ.hom.left ≫ DescentDatum.triActTwice b W ι hι) ≫ ε ∧
    pullback.fst ((Over.pullback (DescentDatum.tripleBaseFst a)).obj V).hom q ≫
        DescentDatum.triActOnce a V τ =
      (θ.hom.left ≫ DescentDatum.triActOnce b W ι) ≫ ε := by
  have hw : θ.hom.left ≫ pullback.snd W.hom (DescentDatum.tripleBaseFst b) =
      pullback.snd ((Over.pullback (DescentDatum.tripleBaseFst a)).obj V).hom q := by
    simpa only [Over.pullback_obj_hom] using Over.w θ.hom
  have hG : pullback.fst ((Over.pullback (DescentDatum.tripleBaseFst a)).obj V).hom q ≫
      pullback.snd V.hom (DescentDatum.tripleBaseFst a) =
      θ.hom.left ≫ pullback.snd W.hom (DescentDatum.tripleBaseFst b) ≫ q := by
    rw [reassoc_of% hw]
    exact pullback.condition
  exact triAct_comp_comparison a b r s comm V W ε hε τ hτ ι hι hequiv _ θ.hom.left
    (θ.hom.left ≫ pullback.fst W.hom (DescentDatum.tripleBaseFst b))
    (θ.hom.left ≫ pullback.snd W.hom (DescentDatum.tripleBaseFst b) ≫
      DescentDatum.tripleBaseSnd b)
    (θ.hom.left ≫ pullback.snd W.hom (DescentDatum.tripleBaseFst b) ≫
      DescentDatum.tripleBaseThd b)
    rfl rfl rfl (by rw [Category.assoc]; exact hθ.symm)
    (by simp only [Category.assoc]; rw [reassoc_of% hG, hq₂])
    (by simp only [Category.assoc]; rw [reassoc_of% hG, hq₃])
    (by
      simpa only [Category.assoc] using
        congrArg (θ.hom.left ≫ ·) (DescentDatum.tripleObjIso_cond₁ b W))
    (by
      simpa only [Category.assoc] using
        congrArg (θ.hom.left ≫ ·) (DescentDatum.tripleObjIso_cond₂ b W))

include hf

/-- The comparison of the base change to the limit of the base change of a stage object along
the first projection of the stage's triple fibre product with the base change of the datum's own
underlying scheme along the first projection of `X ×_S X ×_S X`. -/
abbrev triLegFstDatumIso (D : DescentDatum f) (i : I) (V : Over (𝒳.obj i))
    (e : D.over ≅ (Over.pullback (cX.π.app i)).obj V) :
    (Over.pullback ((triCone φ f hf).π.app i)).obj
        ((Over.pullback (DescentDatum.tripleBaseFst (φ.app i))).obj V) ≅
      (Over.pullback (DescentDatum.tripleBaseFst f)).obj D.over :=
  triLegFstIso φ f hf i V ≪≫ (Over.pullback (DescentDatum.tripleBaseFst f)).mapIso e.symm

/-- **The two sides of the cocycle condition of a stage model agree on the generalized points
that come from the limit.** -/
lemma triAct_eq_of_isStageModel (D : DescentDatum f) (i : I) (V : Over (𝒳.obj i))
    (ψ : (Over.pullback (pullback.fst (φ.app i) (φ.app i))).obj V ≅
      (Over.pullback (pullback.snd (φ.app i) (φ.app i))).obj V)
    (e : D.over ≅ (Over.pullback (cX.π.app i)).obj V)
    (hm : IsStageModel φ f hf D i V ψ e) :
    pullback.fst ((Over.pullback (DescentDatum.tripleBaseFst (φ.app i))).obj V).hom
          ((triCone φ f hf).π.app i) ≫
        DescentDatum.triActTwice (φ.app i) V
          (DescentDatum.pullbackIsoOfBaseChangeIso (φ.app i) V ψ).hom
          (DescentDatum.pullbackIsoOfBaseChangeIso_hom_snd (φ.app i) V ψ) =
      pullback.fst ((Over.pullback (DescentDatum.tripleBaseFst (φ.app i))).obj V).hom
          ((triCone φ f hf).π.app i) ≫
        DescentDatum.triActOnce (φ.app i) V
          (DescentDatum.pullbackIsoOfBaseChangeIso (φ.app i) V ψ).hom := by
  have hΛ : (triLegFstDatumIso φ f hf D i V e).hom.left ≫
      pullback.fst D.over.hom (DescentDatum.tripleBaseFst f) ≫
        e.hom.left ≫ pullback.fst V.hom (cX.π.app i) =
      pullback.fst ((Over.pullback (DescentDatum.tripleBaseFst (φ.app i))).obj V).hom
          ((triCone φ f hf).π.app i) ≫
        pullback.fst V.hom (DescentDatum.tripleBaseFst (φ.app i)) := by
    rw [Iso.trans_hom, Over.comp_left, Functor.mapIso_hom, Iso.symm_hom, Category.assoc,
      overPullback_map_left_fst_assoc,
      overIso_inv_left_comp e (g := pullback.fst V.hom (cX.π.app i)) rfl]
    exact triLegFstIso_hom_left_fst φ f hf i V
  obtain ⟨h1, h2⟩ := triAct_comp_comparison_of_iso (φ.app i) f (cX.π.app i) (cS.π.app i) (hf i) V
    D.over (e.hom.left ≫ pullback.fst V.hom (cX.π.app i))
    (by rw [Category.assoc]; exact modelComparison_comp_hom (cX.π.app i) V D.over e)
    (DescentDatum.pullbackIsoOfBaseChangeIso (φ.app i) V ψ).hom
    (DescentDatum.pullbackIsoOfBaseChangeIso_hom_snd (φ.app i) V ψ)
    D.transitionPullbackIso.hom (D.gluingPullbackIso_hom_snd () ())
    (fun v x hvx hvx' ↦ actPullback_stageComparison φ f hf D i V ψ e hm v x hvx hvx')
    ((triCone φ f hf).π.app i) (triCone_π_comp_tripleBaseSnd φ f hf i)
    (triCone_π_comp_tripleBaseThd φ f hf i) (triLegFstDatumIso φ f hf D i V e) hΛ
  rw [h1, h2, DescentDatum.triActTwice_eq_triActOnce f D.over D.transitionPullbackIso.hom
    (D.gluingPullbackIso_hom_snd () ())
    (DescentDatum.actPullbackLaw_transitionPullbackIso f D)]

/-! ### The cocycle condition at a later stage -/

/-- **The candidate gluing isomorphism of a stage model satisfies the cocycle condition after
passing to a later stage.** -/
theorem exists_stage_actPullbackLaw [IsCofiltered I] [EssentiallySmall.{u} I]
    [∀ i, IsAffine (𝒳.obj i)] [∀ i, IsAffine (𝒮.obj i)]
    (hX : IsLimit cX) (hS : IsLimit cS) (D : DescentDatum f) (i : I) (V : Over (𝒳.obj i))
    (ψ : (Over.pullback (pullback.fst (φ.app i) (φ.app i))).obj V ≅
      (Over.pullback (pullback.snd (φ.app i) (φ.app i))).obj V)
    (e : D.over ≅ (Over.pullback (cX.π.app i)).obj V) (hV : FinitePresentation V.hom)
    (hm : IsStageModel φ f hf D i V ψ e) :
    ∃ (k : I) (m : k ⟶ i),
      DescentDatum.ActPullbackLaw ((Over.pullback (𝒳.map m)).obj V)
        (DescentDatum.pullbackIsoOfBaseChangeIso (φ.app k) ((Over.pullback (𝒳.map m)).obj V)
          (sqReindexIso φ m V ψ)).hom := by
  have {p q : I} (n : p ⟶ q) : IsAffineHom ((triDiagram φ).map n) := inferInstance
  have (p : I) : CompactSpace ((triDiagram φ).obj p) := inferInstance
  have (p : I) : QuasiSeparatedSpace ((triDiagram φ).obj p) := inferInstance
  obtain ⟨k, m, hLR⟩ := eventually_eq_of_baseChange_eq (triDiagram φ) (triCone φ f hf)
    (triIsLimit φ f hf hX hS) i
    ((Over.pullback (DescentDatum.tripleBaseFst (φ.app i))).obj V)
    ((Over.pullback (DescentDatum.tripleBaseThd (φ.app i))).obj V)
    (LimitFPObjectDescent.finitePresentation_overPullback _ V hV)
    (LimitFPObjectDescent.finitePresentation_overPullback _ V hV)
    (DescentDatum.triOverHom (φ.app i) V
      (DescentDatum.triActTwice (φ.app i) V
        (DescentDatum.pullbackIsoOfBaseChangeIso (φ.app i) V ψ).hom
        (DescentDatum.pullbackIsoOfBaseChangeIso_hom_snd (φ.app i) V ψ))
      (DescentDatum.triActTwice_comp_hom _ _ _ _))
    (DescentDatum.triOverHom (φ.app i) V
      (DescentDatum.triActOnce (φ.app i) V
        (DescentDatum.pullbackIsoOfBaseChangeIso (φ.app i) V ψ).hom)
      (DescentDatum.triActOnce_comp_hom (φ.app i) V _
        (DescentDatum.pullbackIsoOfBaseChangeIso_hom_snd (φ.app i) V ψ)))
    ((DescentDatum.overPullback_map_triOverHom_eq_iff (φ.app i) ((triCone φ f hf).π.app i) V
      _ _ _ _).mpr (triAct_eq_of_isStageModel φ f hf D i V ψ e hm))
  refine ⟨k, m, ?_⟩
  have hG := (DescentDatum.overPullback_map_triOverHom_eq_iff (φ.app i)
    ((triDiagram φ).map m) V _ _ _ _).mp hLR
  have hiso : IsIso (triMapFstIso φ m V).hom.left := by
    show IsIso ((Over.forget _).map (triMapFstIso φ m V).hom)
    infer_instance
  have hlaw : DescentDatum.triActTwice (φ.app k) ((Over.pullback (𝒳.map m)).obj V)
        (DescentDatum.pullbackIsoOfBaseChangeIso (φ.app k) ((Over.pullback (𝒳.map m)).obj V)
          (sqReindexIso φ m V ψ)).hom
        (DescentDatum.pullbackIsoOfBaseChangeIso_hom_snd (φ.app k)
          ((Over.pullback (𝒳.map m)).obj V) (sqReindexIso φ m V ψ)) =
      DescentDatum.triActOnce (φ.app k) ((Over.pullback (𝒳.map m)).obj V)
        (DescentDatum.pullbackIsoOfBaseChangeIso (φ.app k) ((Over.pullback (𝒳.map m)).obj V)
          (sqReindexIso φ m V ψ)).hom := by
    refine pullback.hom_ext ?_ ?_
    · obtain ⟨h1, h2⟩ := triAct_comp_comparison_of_iso (φ.app i) (φ.app k) (𝒳.map m) (𝒮.map m)
        (φ.naturality m) V ((Over.pullback (𝒳.map m)).obj V) (pullback.fst V.hom (𝒳.map m))
        pullback.condition
        (DescentDatum.pullbackIsoOfBaseChangeIso (φ.app i) V ψ).hom
        (DescentDatum.pullbackIsoOfBaseChangeIso_hom_snd (φ.app i) V ψ)
        (DescentDatum.pullbackIsoOfBaseChangeIso (φ.app k) ((Over.pullback (𝒳.map m)).obj V)
          (sqReindexIso φ m V ψ)).hom
        (DescentDatum.pullbackIsoOfBaseChangeIso_hom_snd (φ.app k)
          ((Over.pullback (𝒳.map m)).obj V) (sqReindexIso φ m V ψ))
        (fun v x hvx hvx' ↦ actPullback_sqReindexIso φ m V ψ v x hvx hvx')
        ((triDiagram φ).map m) (triDiagram_map_comp_tripleBaseSnd φ m)
        (triDiagram_map_comp_tripleBaseThd φ m) (triMapFstIso φ m V)
        (triMapFstIso_hom_left_fst φ m V)
      rw [← cancel_epi (triMapFstIso φ m V).hom.left]
      simp only [← Category.assoc]
      rw [← h1, ← h2]
      exact hG
    · simpa only [Over.pullback_obj_hom] using
        (DescentDatum.triActTwice_comp_hom (φ.app k) ((Over.pullback (𝒳.map m)).obj V) _
            (DescentDatum.pullbackIsoOfBaseChangeIso_hom_snd (φ.app k)
              ((Over.pullback (𝒳.map m)).obj V) (sqReindexIso φ m V ψ))).trans
          (DescentDatum.triActOnce_comp_hom (φ.app k) ((Over.pullback (𝒳.map m)).obj V) _
            (DescentDatum.pullbackIsoOfBaseChangeIso_hom_snd (φ.app k)
              ((Over.pullback (𝒳.map m)).obj V) (sqReindexIso φ m V ψ))).symm
  intro Z v x y hv hw hvx
  exact DescentDatum.actPullbackLaw_of_triAct_eq (φ.app k) ((Over.pullback (𝒳.map m)).obj V)
    (DescentDatum.pullbackIsoOfBaseChangeIso (φ.app k) ((Over.pullback (𝒳.map m)).obj V)
      (sqReindexIso φ m V ψ)).hom
    (DescentDatum.pullbackIsoOfBaseChangeIso_hom_snd (φ.app k)
      ((Over.pullback (𝒳.map m)).obj V) (sqReindexIso φ m V ψ)) hlaw v x y hv hw hvx

end LimitDatum

end AlgebraicGeometry

end
