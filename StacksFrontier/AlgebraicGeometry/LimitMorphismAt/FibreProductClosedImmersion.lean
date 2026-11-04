module

public import StacksFrontier.AlgebraicGeometry.LimitMorphismAt.ModelMorphismAt

/-!
# The comparison into the fibre product of the systems is a closed immersion

Let `S = lim S_i` be the limit of a directed inverse system of Noetherian schemes with affine
transition morphisms, and let

```
X¹ ⟶ X³
↓     ↓
X² ⟶ X⁴
```

be a cartesian square of schemes over `S`, presented over one stage `S_i` by a good diagram for
`X⁴` with model `W⁴` and by models `W²` and `W³` for `X²` and `X³` mapping to `W⁴`. Give `X¹` the
model `W² ×_{W⁴} W³`. Then the four morphisms of image systems that the four morphisms of models
induce satisfy `a_j ∘ p_j = b_j ∘ q_j` at every stage, and the induced morphism

```
(q_j, p_j) : X¹_j ⟶ X²_j ×_{X⁴_j} X³_j
```

is a closed immersion at every stage.

## Main definitions

* `AlgebraicGeometry.LimitNoetherianSituation.fibreProductBaseSnd`,
  `AlgebraicGeometry.LimitNoetherianSituation.fibreProductBaseTrd`: the morphisms of image systems
  `b_j` and `a_j`.
* `AlgebraicGeometry.LimitNoetherianSituation.fibreProductProjSnd`,
  `AlgebraicGeometry.LimitNoetherianSituation.fibreProductProjTrd`: the morphisms of image systems
  `q_j` and `p_j`.
* `AlgebraicGeometry.LimitNoetherianSituation.fibreProductStageImmersion`: the closed embedding of
  `X²_j ×_{X⁴_j} X³_j` into the base change of the model `W² ×_{W⁴} W³`.

## Main results

* `AlgebraicGeometry.LimitNoetherianSituation.fibreProduct_comp_eq_comp`: the two composites
  agree, at every stage.
* `AlgebraicGeometry.LimitNoetherianSituation.isClosedImmersion_fibreProductComparison`: the
  comparison `(q_j, p_j)` is a closed immersion, at every stage.
* `AlgebraicGeometry.LimitNoetherianSituation.exists_eventually_isClosedImmersion_fibreComparison`:
  for an arbitrary good diagram of the first corner, the comparison is a closed immersion at
  sufficiently late stages.

## References

* [Stacks Project, Tag 0CNM](https://stacks.math.columbia.edu/tag/0CNM)
* [Stacks Project, Tag 0CNS](https://stacks.math.columbia.edu/tag/0CNS)
* [Stacks Project, Tag 0CNW](https://stacks.math.columbia.edu/tag/0CNW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry.LimitNoetherianSituation

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  {D : LimitNoetherianSituation.{v, u} I}
  {X₁ X₂ X₃ X₄ : Scheme.{u}} {s₁ : X₁ ⟶ D.limitScheme} {s₂ : X₂ ⟶ D.limitScheme}
  {s₃ : X₃ ⟶ D.limitScheme} {s₄ : X₄ ⟶ D.limitScheme}
  {p : X₁ ⟶ X₃} {q : X₁ ⟶ X₂} {a : X₃ ⟶ X₄} {b : X₂ ⟶ X₄}
  (G₄ : GoodDiagram D s₄) (M₂ : G₄.ModelOver b s₂) (M₃ : G₄.ModelOver a s₃)
  (hsq : IsPullback q p b a) (hq : q ≫ s₂ = s₁) (hb : b ≫ s₄ = s₂) (ha : a ≫ s₄ = s₃)
  (i₀ : I) (h : G₄.index ≤ i₀)

/-- The morphism of image systems `b_j : X²_j ⟶ X⁴_j`. -/
@[reducible] noncomputable def fibreProductBaseSnd :
    MorphismAt D b M₂.toGoodDiagram G₄ i₀ h h :=
  M₂.morphismAt hb i₀ h

/-- The morphism of image systems `a_j : X³_j ⟶ X⁴_j`. -/
@[reducible] noncomputable def fibreProductBaseTrd :
    MorphismAt D a M₃.toGoodDiagram G₄ i₀ h h :=
  M₃.morphismAt ha i₀ h

/-- The morphism of image systems `q_j : X¹_j ⟶ X²_j`, for the fibre-product model of `X¹`. -/
@[reducible] noncomputable def fibreProductProjSnd :
    MorphismAt D q (GoodDiagram.fibreProductModel G₄ M₂ M₃ hsq hq hb ha)
      M₂.toGoodDiagram i₀ h h :=
  (GoodDiagram.fibreProductModelSnd G₄ M₂ M₃ hsq hq hb ha).morphismAt hq i₀ h

/-- The morphism of image systems `p_j : X¹_j ⟶ X³_j`, for the fibre-product model of `X¹`. -/
@[reducible] noncomputable def fibreProductProjTrd :
    MorphismAt D p (GoodDiagram.fibreProductModel G₄ M₂ M₃ hsq hq hb ha)
      M₃.toGoodDiagram i₀ h h :=
  (GoodDiagram.fibreProductModelTrd G₄ M₂ M₃ hsq hq hb ha).morphismAt
    (GoodDiagram.comp_eq_of_isPullback hsq hq hb ha) i₀ h

/-- The component of `q_j` at a stage, read inside the base change of the model of the second
corner. -/
lemma fibreProductProjSnd_app_imageι (j : Over (op i₀)) :
    (fibreProductProjSnd G₄ M₂ M₃ hsq hq hb ha i₀ h).maps.app j ≫
        (M₂.toGoodDiagram.stageMap ((Over.map (homOfLE h).op).obj j)).imageι =
      ((GoodDiagram.fibreProductModel G₄ M₂ M₃ hsq hq hb ha).stageMap
          ((Over.map (homOfLE h).op).obj j)).imageι ≫
        (GoodDiagram.fibreProductModelSnd G₄ M₂ M₃ hsq hq hb ha).stageTargetHom
          ((Over.map (homOfLE h).op).obj j) :=
  (GoodDiagram.fibreProductModelSnd G₄ M₂ M₃ hsq hq hb ha).morphismAt_app_imageι hq i₀ h j

/-- The component of `p_j` at a stage, read inside the base change of the model of the third
corner. -/
lemma fibreProductProjTrd_app_imageι (j : Over (op i₀)) :
    (fibreProductProjTrd G₄ M₂ M₃ hsq hq hb ha i₀ h).maps.app j ≫
        (M₃.toGoodDiagram.stageMap ((Over.map (homOfLE h).op).obj j)).imageι =
      ((GoodDiagram.fibreProductModel G₄ M₂ M₃ hsq hq hb ha).stageMap
          ((Over.map (homOfLE h).op).obj j)).imageι ≫
        (GoodDiagram.fibreProductModelTrd G₄ M₂ M₃ hsq hq hb ha).stageTargetHom
          ((Over.map (homOfLE h).op).obj j) :=
  (GoodDiagram.fibreProductModelTrd G₄ M₂ M₃ hsq hq hb ha).morphismAt_app_imageι
    (GoodDiagram.comp_eq_of_isPullback hsq hq hb ha) i₀ h j

/-- The stage fibre product `X²_j ×_{X⁴_j} X³_j` is the fibre product of the base changes of the
models of the second and third corners over that of the fourth. -/
theorem isPullback_fibreProduct_stageTargetHom (j : Over (op i₀)) :
    IsPullback
      ((GoodDiagram.fibreProductModelSnd G₄ M₂ M₃ hsq hq hb ha).stageTargetHom
        ((Over.map (homOfLE h).op).obj j))
      ((GoodDiagram.fibreProductModelTrd G₄ M₂ M₃ hsq hq hb ha).stageTargetHom
        ((Over.map (homOfLE h).op).obj j))
      (M₂.stageTargetHom ((Over.map (homOfLE h).op).obj j))
      (M₃.stageTargetHom ((Over.map (homOfLE h).op).obj j)) :=
  isPullback_fibreProduct_baseChange (IsPullback.of_hasPullback _ _)
    (IsPullback.of_hasPullback _ _) (IsPullback.of_hasPullback _ _)
    (IsPullback.of_hasPullback _ _) (IsPullback.of_hasPullback M₂.toBase M₃.toBase)
    M₂.modelMap_eq M₃.modelMap_eq (GoodDiagram.fibreProductModelMap_eq G₄ M₂ M₃)
    (M₂.stageTargetHom_fst _) (M₂.stageTargetHom_snd _)
    (M₃.stageTargetHom_fst _) (M₃.stageTargetHom_snd _)
    ((GoodDiagram.fibreProductModelSnd G₄ M₂ M₃ hsq hq hb ha).stageTargetHom_fst _)
    ((GoodDiagram.fibreProductModelSnd G₄ M₂ M₃ hsq hq hb ha).stageTargetHom_snd _)
    ((GoodDiagram.fibreProductModelTrd G₄ M₂ M₃ hsq hq hb ha).stageTargetHom_fst _)
    ((GoodDiagram.fibreProductModelTrd G₄ M₂ M₃ hsq hq hb ha).stageTargetHom_snd _)

/-- For the model `W² ×_{W⁴} W³` of the first corner, the two composites of the square of image
systems agree at every stage: `a_j ∘ p_j = b_j ∘ q_j`. -/
theorem fibreProduct_comp_eq_comp (j : Over (op i₀)) :
    (fibreProductProjTrd G₄ M₂ M₃ hsq hq hb ha i₀ h).maps.app j ≫
        (fibreProductBaseTrd G₄ M₃ ha i₀ h).maps.app j =
      (fibreProductProjSnd G₄ M₂ M₃ hsq hq hb ha i₀ h).maps.app j ≫
        (fibreProductBaseSnd G₄ M₂ hb i₀ h).maps.app j := by
  have key := (isPullback_fibreProduct_stageTargetHom G₄ M₂ M₃ hsq hq hb ha i₀ h j).w.symm
  have f₂ := M₂.morphismAt_app_imageι hb i₀ h j
  have f₃ := M₃.morphismAt_app_imageι ha i₀ h j
  have e₂' := reassoc_of% (fibreProductProjSnd_app_imageι G₄ M₂ M₃ hsq hq hb ha i₀ h j)
  have e₃' := reassoc_of% (fibreProductProjTrd_app_imageι G₄ M₂ M₃ hsq hq hb ha i₀ h j)
  refine (cancel_mono (G₄.stageMap ((Over.map (homOfLE h).op).obj j)).imageι).mp ?_
  simp only [Category.assoc]
  rw [f₃, e₃', key, ← e₂', ← f₂]

/-- The closed embedding of the stage fibre product `X²_j ×_{X⁴_j} X³_j` into the base change of
the fibre-product model of the first corner. -/
noncomputable def fibreProductStageImmersion (j : Over (op i₀)) :
    pullback ((fibreProductBaseSnd G₄ M₂ hb i₀ h).maps.app j)
        ((fibreProductBaseTrd G₄ M₃ ha i₀ h).maps.app j) ⟶
      (GoodDiagram.fibreProductModel G₄ M₂ M₃ hsq hq hb ha).stageTarget
        ((Over.map (homOfLE h).op).obj j) :=
  (isPullback_fibreProduct_stageTargetHom G₄ M₂ M₃ hsq hq hb ha i₀ h j).lift
    (pullback.fst _ _ ≫
      (M₂.toGoodDiagram.stageMap ((Over.map (homOfLE h).op).obj j)).imageι)
    (pullback.snd _ _ ≫
      (M₃.toGoodDiagram.stageMap ((Over.map (homOfLE h).op).obj j)).imageι)
    (by
      have e₂ := M₂.morphismAt_app_imageι hb i₀ h j
      have e₃ := M₃.morphismAt_app_imageι ha i₀ h j
      rw [Category.assoc, Category.assoc, ← e₂, ← e₃, ← Category.assoc, ← Category.assoc,
        pullback.condition])

/-- The closed embedding of the stage fibre product followed by the projection to the base change
of the model of the second corner is the first projection followed by the closed embedding of
`X²_j`. -/
@[reassoc (attr := simp)]
lemma fibreProductStageImmersion_fst (j : Over (op i₀)) :
    fibreProductStageImmersion G₄ M₂ M₃ hsq hq hb ha i₀ h j ≫
        (GoodDiagram.fibreProductModelSnd G₄ M₂ M₃ hsq hq hb ha).stageTargetHom
          ((Over.map (homOfLE h).op).obj j) =
      pullback.fst _ _ ≫
        (M₂.toGoodDiagram.stageMap ((Over.map (homOfLE h).op).obj j)).imageι :=
  IsPullback.lift_fst _ _ _ _

/-- The closed embedding of the stage fibre product followed by the projection to the base change
of the model of the third corner is the second projection followed by the closed embedding of
`X³_j`. -/
@[reassoc (attr := simp)]
lemma fibreProductStageImmersion_snd (j : Over (op i₀)) :
    fibreProductStageImmersion G₄ M₂ M₃ hsq hq hb ha i₀ h j ≫
        (GoodDiagram.fibreProductModelTrd G₄ M₂ M₃ hsq hq hb ha).stageTargetHom
          ((Over.map (homOfLE h).op).obj j) =
      pullback.snd _ _ ≫
        (M₃.toGoodDiagram.stageMap ((Over.map (homOfLE h).op).obj j)).imageι :=
  IsPullback.lift_snd _ _ _ _

/-- The embedding of the stage fibre product `X²_j ×_{X⁴_j} X³_j` into the base change of the
fibre-product model of the first corner is a closed immersion. -/
lemma isClosedImmersion_fibreProductStageImmersion (j : Over (op i₀)) :
    IsClosedImmersion (fibreProductStageImmersion G₄ M₂ M₃ hsq hq hb ha i₀ h j) :=
  isClosedImmersion_fibreProduct_baseChange
    (c₂ := (M₂.toGoodDiagram.stageMap ((Over.map (homOfLE h).op).obj j)).imageι)
    (c₃ := (M₃.toGoodDiagram.stageMap ((Over.map (homOfLE h).op).obj j)).imageι)
    (c₄ := (G₄.stageMap ((Over.map (homOfLE h).op).obj j)).imageι)
    (IsPullback.of_hasPullback _ _)
    (isPullback_fibreProduct_stageTargetHom G₄ M₂ M₃ hsq hq hb ha i₀ h j)
    (M₂.morphismAt_app_imageι hb i₀ h j) (M₃.morphismAt_app_imageι ha i₀ h j)
    (fibreProductStageImmersion_fst G₄ M₂ M₃ hsq hq hb ha i₀ h j)
    (fibreProductStageImmersion_snd G₄ M₂ M₃ hsq hq hb ha i₀ h j)

/-- For the model `W² ×_{W⁴} W³` of the first corner of a cartesian square, the comparison
`(q_j, p_j) : X¹_j ⟶ X²_j ×_{X⁴_j} X³_j` is a closed immersion at every stage. -/
@[stacks 0CNW
  "closed immersion of the comparison, for the model `W² ×_{W⁴} W³` of the first corner"]
theorem isClosedImmersion_fibreProductComparison (j : Over (op i₀)) :
    IsClosedImmersion (MorphismAt.fibreComparisonApp
      (fibreProductProjTrd G₄ M₂ M₃ hsq hq hb ha i₀ h)
      (fibreProductProjSnd G₄ M₂ M₃ hsq hq hb ha i₀ h)
      (fibreProductBaseTrd G₄ M₃ ha i₀ h) (fibreProductBaseSnd G₄ M₂ hb i₀ h) j
      (fibreProduct_comp_eq_comp G₄ M₂ M₃ hsq hq hb ha i₀ h j)) := by
  refine MorphismAt.isClosedImmersion_fibreComparisonApp _ _ _ _ j _
    (fibreProductStageImmersion G₄ M₂ M₃ hsq hq hb ha i₀ h j)
    (isClosedImmersion_fibreProductStageImmersion G₄ M₂ M₃ hsq hq hb ha i₀ h j) ?_
  refine (isPullback_fibreProduct_stageTargetHom G₄ M₂ M₃ hsq hq hb ha i₀ h j).hom_ext ?_ ?_
  · simp only [Category.assoc]
    rw [fibreProductStageImmersion_fst, MorphismAt.fibreComparisonApp_fst_assoc,
      fibreProductProjSnd_app_imageι G₄ M₂ M₃ hsq hq hb ha i₀ h j]
  · simp only [Category.assoc]
    rw [fibreProductStageImmersion_snd, MorphismAt.fibreComparisonApp_snd_assoc,
      fibreProductProjTrd_app_imageι G₄ M₂ M₃ hsq hq hb ha i₀ h j]

/-- Restricting along `k₁.trans k₂` and reading at `j` is restricting along `k₁` and reading at `j`
seen as a stage of the tail above the middle index. -/
private theorem restrict_trans_maps_app {X Y : Scheme.{u}} {pX : X ⟶ D.limitScheme}
    {pY : Y ⟶ D.limitScheme} {f : X ⟶ Y} {GX : GoodDiagram D pX} {GY : GoodDiagram D pY}
    {i₀ i₁ i₂ : I} {hX : GX.index ≤ i₀} {hY : GY.index ≤ i₀} (k₁ : i₀ ≤ i₁) (k₂ : i₁ ≤ i₂)
    (F : MorphismAt D f GX GY i₀ hX hY) (j : Over (op i₂)) :
    (F.restrict' (k₁.trans k₂)).maps.app j =
      (F.restrict' k₁).maps.app ((Over.map (homOfLE k₂).op).obj j) := by
  simp only [MorphismAt.restrict_maps_app']
  cases MorphismAt.over_map_obj_trans k₁ k₂ j
  rfl

/-- For any good diagram `G₁` of the first corner and any morphisms `P` and `Q` of image systems
realizing `p` and `q` from it, there is a stage above which the two composites of the square of
systems agree and the induced comparison `(q_j, p_j) : X¹_j ⟶ X²_j ×_{X⁴_j} X³_j` is a closed
immersion. -/
theorem exists_eventually_isClosedImmersion_fibreComparison
    (hsq : IsPullback q p b a) (hq : q ≫ s₂ = s₁)
    (G₁ : GoodDiagram D s₁) (h₁ : G₁.index ≤ i₀)
    (P : MorphismAt D p G₁ M₃.toGoodDiagram i₀ h₁ h)
    (Q : MorphismAt D q G₁ M₂.toGoodDiagram i₀ h₁ h) :
    ∃ (i₉ : I) (k : i₀ ≤ i₉)
      (hcomm : ∀ j : Over (op i₉),
        (P.restrict' k).maps.app j ≫
            ((fibreProductBaseTrd G₄ M₃ ha i₀ h).restrict' k).maps.app j =
          (Q.restrict' k).maps.app j ≫
            ((fibreProductBaseSnd G₄ M₂ hb i₀ h).restrict' k).maps.app j),
      ∀ j : Over (op i₉),
        IsClosedImmersion (MorphismAt.fibreComparisonApp (P.restrict' k) (Q.restrict' k)
          ((fibreProductBaseTrd G₄ M₃ ha i₀ h).restrict' k)
          ((fibreProductBaseSnd G₄ M₂ hb i₀ h).restrict' k) j (hcomm j)) := by
  obtain ⟨i₆, k06, hComm⟩ :=
    eventually_comp_eq_comp_morphismAt D hsq.w.symm P Q
      (fibreProductBaseTrd G₄ M₃ ha i₀ h) (fibreProductBaseSnd G₄ M₂ hb i₀ h)
  obtain ⟨i₁, h₁', hW₁', F, Finv, hFF⟩ :=
    exists_eventual_iso_imageSystem' D s₁ G₁ (GoodDiagram.fibreProductModel G₄ M₂ M₃ hsq hq hb ha)
  obtain ⟨i₂, k02, k12⟩ := exists_ge_ge i₀ i₁
  obtain ⟨i₃, k23, hEqP⟩ :=
    eventually_natural_imageSystem_comparison' D p (F.restrict' k12)
      (MorphismAt.id' M₃.toGoodDiagram i₂ (h.trans k02)) (P.restrict' k02)
      ((fibreProductProjTrd G₄ M₂ M₃ hsq hq hb ha i₀ h).restrict' k02)
  obtain ⟨i₄, k24, hEqQ⟩ :=
    eventually_natural_imageSystem_comparison' D q (F.restrict' k12)
      (MorphismAt.id' M₂.toGoodDiagram i₂ (h.trans k02)) (Q.restrict' k02)
      ((fibreProductProjSnd G₄ M₂ M₃ hsq hq hb ha i₀ h).restrict' k02)
  obtain ⟨i₇, k37, k47⟩ := exists_ge_ge i₃ i₄
  obtain ⟨i₉, k69, k79⟩ := exists_ge_ge i₆ i₇
  have k29 : i₂ ≤ i₉ := (k23.trans k37).trans k79
  have k39 : i₃ ≤ i₉ := k37.trans k79
  have k49 : i₄ ≤ i₉ := k47.trans k79
  set k : i₀ ≤ i₉ := k02.trans k29
  have hcomm : ∀ j : Over (op i₉),
      (P.restrict' k).maps.app j ≫
          ((fibreProductBaseTrd G₄ M₃ ha i₀ h).restrict' k).maps.app j =
        (Q.restrict' k).maps.app j ≫
          ((fibreProductBaseSnd G₄ M₂ hb i₀ h).restrict' k).maps.app j := by
    intro j
    simp only [MorphismAt.restrict_maps_app']
    exact hComm _ (k69.trans (leOfHom j.hom.unop))
  refine ⟨i₉, k, hcomm, fun j => ?_⟩
  set j2 : Over (op i₂) := (Over.map (homOfLE k29).op).obj j
  have hj2left : unop j2.left = unop j.left := by simp [j2]
  have hj3 : i₃ ≤ unop j2.left := by rw [hj2left]; exact k39.trans (leOfHom j.hom.unop)
  have hj4 : i₄ ≤ unop j2.left := by rw [hj2left]; exact k49.trans (leOfHom j.hom.unop)
  have hP := hEqP j2 hj3
  have hQ := hEqQ j2 hj4
  simp only [MorphismAt.id_maps_app', Category.comp_id] at hP hQ
  have hPj : (P.restrict' k).maps.app j = _ := (restrict_trans_maps_app k02 k29 P j).trans hP
  have hQj : (Q.restrict' k).maps.app j = _ := (restrict_trans_maps_app k02 k29 Q j).trans hQ
  have hAj : ((fibreProductBaseTrd G₄ M₃ ha i₀ h).restrict' k).maps.app j =
      ((fibreProductBaseTrd G₄ M₃ ha i₀ h).restrict' k02).maps.app j2 :=
    restrict_trans_maps_app k02 k29 _ j
  have hBj : ((fibreProductBaseSnd G₄ M₂ hb i₀ h).restrict' k).maps.app j =
      ((fibreProductBaseSnd G₄ M₂ hb i₀ h).restrict' k02).maps.app j2 :=
    restrict_trans_maps_app k02 k29 _ j
  have hcomm2 :
      ((fibreProductProjTrd G₄ M₂ M₃ hsq hq hb ha i₀ h).restrict' k02).maps.app j2 ≫
          ((fibreProductBaseTrd G₄ M₃ ha i₀ h).restrict' k02).maps.app j2 =
        ((fibreProductProjSnd G₄ M₂ M₃ hsq hq hb ha i₀ h).restrict' k02).maps.app j2 ≫
          ((fibreProductBaseSnd G₄ M₂ hb i₀ h).restrict' k02).maps.app j2 := by
    simp only [MorphismAt.restrict_maps_app']
    exact fibreProduct_comp_eq_comp G₄ M₂ M₃ hsq hq hb ha i₀ h
      ((Over.map (homOfLE k02).op).obj j2)
  have hIsoF : IsIso ((F.restrict' k12).maps.app j2) := by
    have hw := hFF ((Over.map (homOfLE k12).op).obj j2)
    simp only [MorphismAt.restrict_maps_app']
    exact ⟨Finv.maps.app ((Over.map (homOfLE k12).op).obj j2), hw.1, hw.2⟩
  have hclosed : IsClosedImmersion
      (MorphismAt.fibreComparisonApp
        ((fibreProductProjTrd G₄ M₂ M₃ hsq hq hb ha i₀ h).restrict' k02)
        ((fibreProductProjSnd G₄ M₂ M₃ hsq hq hb ha i₀ h).restrict' k02)
        ((fibreProductBaseTrd G₄ M₃ ha i₀ h).restrict' k02)
        ((fibreProductBaseSnd G₄ M₂ hb i₀ h).restrict' k02) j2 hcomm2) :=
    isClosedImmersion_fibreProductComparison G₄ M₂ M₃ hsq hq hb ha i₀ h
      ((Over.map (homOfLE k02).op).obj j2)
  have hIsoCI : IsClosedImmersion ((F.restrict' k12).maps.app j2) := inferInstance
  set e := pullback.congrHom hBj hAj with he_def
  have hcompEq :
      MorphismAt.fibreComparisonApp (P.restrict' k) (Q.restrict' k)
        ((fibreProductBaseTrd G₄ M₃ ha i₀ h).restrict' k)
        ((fibreProductBaseSnd G₄ M₂ hb i₀ h).restrict' k) j (hcomm j) ≫ e.hom =
      (F.restrict' k12).maps.app j2 ≫
        MorphismAt.fibreComparisonApp
          ((fibreProductProjTrd G₄ M₂ M₃ hsq hq hb ha i₀ h).restrict' k02)
          ((fibreProductProjSnd G₄ M₂ M₃ hsq hq hb ha i₀ h).restrict' k02)
          ((fibreProductBaseTrd G₄ M₃ ha i₀ h).restrict' k02)
          ((fibreProductBaseSnd G₄ M₂ hb i₀ h).restrict' k02) j2 hcomm2 := by
    apply pullback.hom_ext
    · simp only [Category.assoc, he_def, pullback.congrHom_hom, pullback.lift_fst,
        Category.comp_id, MorphismAt.fibreComparisonApp_fst]
      exact hQj
    · simp only [Category.assoc, he_def, pullback.congrHom_hom, pullback.lift_snd,
        Category.comp_id, MorphismAt.fibreComparisonApp_snd]
      exact hPj
  have hCIe : IsClosedImmersion
      (MorphismAt.fibreComparisonApp (P.restrict' k) (Q.restrict' k)
        ((fibreProductBaseTrd G₄ M₃ ha i₀ h).restrict' k)
        ((fibreProductBaseSnd G₄ M₂ hb i₀ h).restrict' k) j (hcomm j) ≫ e.hom) := by
    rw [hcompEq]
    exact IsClosedImmersion.comp _ _
  exact (MorphismProperty.cancel_right_of_respectsIso (P := @IsClosedImmersion) _ e.hom).mp hCIe

/-! ### Flatness and finite presentation of the projections -/

/-- If `b` is flat, so is its base change `p` along the cartesian square `hsq`. -/
theorem flat_p_of_flat_b (hsq : IsPullback q p b a) [Flat b] : Flat p :=
  MorphismProperty.of_isPullback hsq ‹Flat b›

/-- If `a` is flat, so is its base change `q` along the cartesian square `hsq`. -/
theorem flat_q_of_flat_a (hsq : IsPullback q p b a) [Flat a] : Flat q :=
  MorphismProperty.of_isPullback hsq.flip ‹Flat a›

/-- If `b` is of finite presentation, so is its base change `p` along the cartesian square `hsq`.
-/
theorem finitePresentation_p_of_finitePresentation_b (hsq : IsPullback q p b a)
    (hfp_b : FinitePresentation b) : FinitePresentation p :=
  FinitePresentation.mk
    (MorphismProperty.of_isPullback hsq hfp_b.locallyOfFinitePresentation)
    (MorphismProperty.of_isPullback hsq hfp_b.quasiCompact)
    (MorphismProperty.of_isPullback hsq hfp_b.quasiSeparated)

/-- If `a` is of finite presentation, so is its base change `q` along the cartesian square `hsq`.
-/
theorem finitePresentation_q_of_finitePresentation_a (hsq : IsPullback q p b a)
    (hfp_a : FinitePresentation a) : FinitePresentation q :=
  FinitePresentation.mk
    (MorphismProperty.of_isPullback hsq.flip hfp_a.locallyOfFinitePresentation)
    (MorphismProperty.of_isPullback hsq.flip hfp_a.quasiCompact)
    (MorphismProperty.of_isPullback hsq.flip hfp_a.quasiSeparated)

end AlgebraicGeometry.LimitNoetherianSituation
