module

public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.StageCocycle
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Diagonal
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Finite
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Surjective
public import StacksFrontier.AlgebraicGeometry.Limits.ProperImageSystemModels

/-!
# Effectivity of quasi-compact separated étale descent passes to a limit

Let `f : X ⟶ S` be the limit of a cofiltered system of morphisms `f_i : X_i ⟶ S_i` of affine
schemes. If quasi-compact separated étale descent is effective along every `f_i` then it is
effective along `f`. This is the limit step of the proof of
[Stacks, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP).

A quasi-compact separated étale descent datum relative to `X / S` is of finite presentation over
`X`, so it has a model at a finite stage
(`AlgebraicGeometry.LimitDatum.exists_stageModel`). Passing three times to a later stage makes
the model's underlying scheme étale (Tag 07RP) and separated (Tag 01ZQ) over the stage and makes
its candidate gluing isomorphism satisfy the cocycle condition
(`AlgebraicGeometry.LimitDatum.exists_stage_actPullbackLaw`); the model is then a genuine descent
datum at that stage whose pullback along the square relating the stage to the limit is the given
datum, and effectivity transports back by
`AlgebraicGeometry.DescentDatum.isEtaleEffective_pullbackSquare`.

## Main definitions

* `AlgebraicGeometry.LimitDatum.stageDatum`: **the descent datum at a stage determined by a stage
  model whose candidate gluing isomorphism satisfies the cocycle condition.**

## Main results

* `AlgebraicGeometry.exists_etale_overPullback_obj_of_isLimit`,
  `AlgebraicGeometry.exists_isSeparated_overPullback_obj_of_isLimit`,
  `AlgebraicGeometry.exists_isFinite_overPullback_obj_of_isLimit` and
  `AlgebraicGeometry.exists_surjective_overPullback_obj_of_isLimit`: étaleness, separatedness,
  finiteness and surjectivity of the structure morphism of an object of finite presentation over
  a stage descend to a finite stage.
* `AlgebraicGeometry.LimitDatum.exists_good_stageModel`: **a quasi-compact separated étale datum
  has, at some stage, a model which is étale, quasi-compact and separated over the stage and
  whose candidate gluing isomorphism satisfies the cocycle condition.**
* `AlgebraicGeometry.LimitDatum.qcSepEtaleEffective_of_forall_stage`: **effectivity of
  quasi-compact separated étale descent passes to the limit.**

## References

* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 01ZQ](https://stacks.math.columbia.edu/tag/01ZQ)
* [Stacks Project, Tag 07RP](https://stacks.math.columbia.edu/tag/07RP)
* [Stacks Project, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP)
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-! ### Étaleness and separatedness of a stage object descend -/

section Descend

variable {I : Type u} [Category.{u} I] [IsCofiltered I] [EssentiallySmall.{u} I]
  (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
  [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)] [∀ i : I, CompactSpace (D.obj i)]
  [∀ i : I, QuasiSeparatedSpace (D.obj i)] (i₀ : I) (V : Over (D.obj i₀))

/-- A base-change-stable property of the structure morphism of an object `Z` of finite
presentation over `S` descends along a family of base changes, once it descends for the morphism
from `Z` to the terminal object of the over category. -/
private theorem exists_overPullback_obj_of_baseChange {S : Scheme.{u}} [CompactSpace S]
    [QuasiSeparatedSpace S] (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    (Z : Over S) (hZ : FinitePresentation Z.hom) {T₀ : Scheme.{u}} (b₀ : T₀ ⟶ S) {ι : Type*}
    {κ : ι → Type*} {T : ι → Scheme.{u}} (b : ∀ j, κ j → (T j ⟶ S))
    (hP : P ((Over.pullback b₀).obj Z).hom)
    (H : ∀ t : Z ⟶ Over.mk (𝟙 S), [LocallyOfFinitePresentation t.left] → [CompactSpace Z.left] →
      [QuasiSeparatedSpace Z.left] → [CompactSpace (Over.mk (𝟙 S)).left] →
      [QuasiSeparatedSpace (Over.mk (𝟙 S)).left] → P ((Over.pullback b₀).map t).left →
        ∃ (j : ι) (k : κ j), P ((Over.pullback (b j k)).map t).left) :
    ∃ (j : ι) (k : κ j), P ((Over.pullback (b j k)).obj Z).hom := by
  have hRI : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : QuasiCompact Z.hom := hZ.2.1
  have : QuasiSeparated Z.hom := hZ.2.2
  have : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace Z.hom
  have : QuasiSeparatedSpace Z.left := quasiSeparatedSpace_of_quasiSeparated Z.hom
  have : CompactSpace (Over.mk (𝟙 S)).left := inferInstanceAs (CompactSpace S)
  have : QuasiSeparatedSpace (Over.mk (𝟙 S)).left := inferInstanceAs (QuasiSeparatedSpace S)
  have : LocallyOfFinitePresentation (Over.homMk Z.hom (Category.comp_id Z.hom) :
      Z ⟶ Over.mk (𝟙 S)).left := hZ.1
  obtain ⟨j, k, hj⟩ := H (Over.homMk Z.hom (Category.comp_id Z.hom))
    ((overPullback_map_terminal_iff P b₀ Z).mpr hP)
  exact ⟨j, k, (overPullback_map_terminal_iff P (b j k) Z).mp hj⟩

include hc

omit [EssentiallySmall.{u, u, u} I] in
/-- **Étaleness of the structure morphism of an object of finite presentation over a stage
descends to a finite stage.** This is Tag 07RP, read on structure morphisms through
`AlgebraicGeometry.overPullback_map_terminal_iff`. -/
theorem exists_etale_overPullback_obj_of_isLimit (hV : FinitePresentation V.hom)
    (hEt : Etale ((Over.pullback (c.π.app i₀)).obj V).hom) :
    ∃ (j : I) (m : j ⟶ i₀), Etale ((Over.pullback (D.map m)).obj V).hom :=
  exists_overPullback_obj_of_baseChange @Etale V hV (c.π.app i₀)
    (fun _ m ↦ D.map m) hEt fun t _ _ _ _ _ (_ : Etale _) ↦
    (exists_etale_pullback_of_isLimit D c hc i₀ V _ t).elim fun j hj ↦ ⟨j.left, j.hom, hj⟩

/-- **Separatedness of the structure morphism of an object of finite presentation over a stage
descends to a finite stage.** This is Tag 01ZQ, read on structure morphisms. -/
theorem exists_isSeparated_overPullback_obj_of_isLimit (hV : FinitePresentation V.hom)
    (hSep : IsSeparated ((Over.pullback (c.π.app i₀)).obj V).hom) :
    ∃ (j : I) (m : j ⟶ i₀), IsSeparated ((Over.pullback (D.map m)).obj V).hom :=
  exists_overPullback_obj_of_baseChange @IsSeparated V hV (c.π.app i₀)
    (fun _ m ↦ D.map m) hSep fun t _ _ _ _ _ (_ : IsSeparated _) ↦
    exists_isSeparated_baseChange_of_isLimit D c i₀ V _ t hc

/-- **Finiteness of the structure morphism of an object of finite presentation over a stage
descends to a finite stage.** This is Tag 01ZO, read on structure morphisms. -/
theorem exists_isFinite_overPullback_obj_of_isLimit (hV : FinitePresentation V.hom)
    (hFin : IsFinite ((Over.pullback (c.π.app i₀)).obj V).hom) :
    ∃ (j : I) (m : j ⟶ i₀), IsFinite ((Over.pullback (D.map m)).obj V).hom :=
  exists_overPullback_obj_of_baseChange @IsFinite V hV (c.π.app i₀)
    (fun _ m ↦ D.map m) hFin fun t _ _ _ _ _ (_ : IsFinite _) ↦
    exists_isFinite_baseChange_of_isLimit D c hc i₀ V _ t

omit [EssentiallySmall.{u, u, u} I] in
/-- **Surjectivity of the structure morphism of an object of finite presentation over a stage
descends to a finite stage.** This is Tag 07RR, read on structure morphisms. -/
theorem exists_surjective_overPullback_obj_of_isLimit (hV : FinitePresentation V.hom)
    (hSurj : Surjective ((Over.pullback (c.π.app i₀)).obj V).hom) :
    ∃ (j : I) (m : j ⟶ i₀), Surjective ((Over.pullback (D.map m)).obj V).hom :=
  exists_overPullback_obj_of_baseChange @Surjective V hV (c.π.app i₀)
    (fun _ m ↦ D.map m) hSurj fun t _ _ _ _ _ (_ : Surjective _) ↦
    exists_surjective_baseChange_of_surjective_limitBaseChange D c hc i₀ V _ t

end Descend

namespace LimitDatum

variable {I : Type u} [Category.{u} I] {𝒳 𝒮 : I ⥤ Scheme.{u}} (φ : 𝒳 ⟶ 𝒮)
  {cX : Cone 𝒳} {cS : Cone 𝒮} (f : cX.pt ⟶ cS.pt)
  (hf : ∀ i, cX.π.app i ≫ φ.app i = f ≫ cS.π.app i)

/-! ### The descent datum at a stage -/

/-- **The descent datum at a stage determined by a stage model whose candidate gluing
isomorphism satisfies the cocycle condition.** -/
def stageDatum (i : I) (V : Over (𝒳.obj i))
    (ψ : (Over.pullback (pullback.fst (φ.app i) (φ.app i))).obj V ≅
      (Over.pullback (pullback.snd (φ.app i) (φ.app i))).obj V)
    (hcoc : DescentDatum.ActPullbackLaw V
      (DescentDatum.pullbackIsoOfBaseChangeIso (φ.app i) V ψ).hom) :
    DescentDatum (φ.app i) :=
  DescentDatum.ofPullbackIso V (DescentDatum.pullbackIsoOfBaseChangeIso (φ.app i) V ψ)
    (DescentDatum.pullbackIsoOfBaseChangeIso_hom_fst (φ.app i) V ψ)
    (DescentDatum.pullbackIsoOfBaseChangeIso_hom_snd (φ.app i) V ψ) hcoc

/-- The underlying scheme of the descent datum at a stage is the model's. -/
@[simp]
lemma stageDatum_over (i : I) (V : Over (𝒳.obj i))
    (ψ : (Over.pullback (pullback.fst (φ.app i) (φ.app i))).obj V ≅
      (Over.pullback (pullback.snd (φ.app i) (φ.app i))).obj V)
    (hcoc : DescentDatum.ActPullbackLaw V
      (DescentDatum.pullbackIsoOfBaseChangeIso (φ.app i) V ψ).hom) :
    (stageDatum φ i V ψ hcoc).over = V := rfl

/-- The gluing isomorphism of the descent datum at a stage, read on the literal fibre products,
is the model's candidate one. -/
lemma stageDatum_transitionPullbackIso_hom (i : I) (V : Over (𝒳.obj i))
    (ψ : (Over.pullback (pullback.fst (φ.app i) (φ.app i))).obj V ≅
      (Over.pullback (pullback.snd (φ.app i) (φ.app i))).obj V)
    (hcoc : DescentDatum.ActPullbackLaw V
      (DescentDatum.pullbackIsoOfBaseChangeIso (φ.app i) V ψ).hom) :
    (stageDatum φ i V ψ hcoc).transitionPullbackIso.hom =
      (DescentDatum.pullbackIsoOfBaseChangeIso (φ.app i) V ψ).hom :=
  DescentDatum.ofPullbackIso_gluingPullbackIso_hom V _ _ _ hcoc

include hf

/-- **A descent datum at the limit is the pullback of the datum built from one of its stage
models.** -/
def isoStageDatumPullback (D : DescentDatum f) (i : I) (V : Over (𝒳.obj i))
    (ψ : (Over.pullback (pullback.fst (φ.app i) (φ.app i))).obj V ≅
      (Over.pullback (pullback.snd (φ.app i) (φ.app i))).obj V)
    (e : D.over ≅ (Over.pullback (cX.π.app i)).obj V)
    (hcoc : DescentDatum.ActPullbackLaw V
      (DescentDatum.pullbackIsoOfBaseChangeIso (φ.app i) V ψ).hom)
    (hm : IsStageModel φ f hf D i V ψ e) :
    D ≅ DescentDatum.pullbackSquareDatum (stagePullbackFunctor φ f hf i)
      (stageDatum φ i V ψ hcoc) :=
  isoStagePullback φ f hf D i (stageDatum φ i V ψ hcoc) e (by
    rw [stageDatum_transitionPullbackIso_hom]
    exact actPullback_stageComparison_universal φ f hf D i V ψ e hm)

/-! ### A model that is étale, separated and satisfies the cocycle condition -/

/-- **A quasi-compact separated étale descent datum has a model at a stage which is étale,
quasi-compact and separated over the stage and whose candidate gluing isomorphism satisfies the
cocycle condition.** Each of the three requirements is met after passing to a later stage, and
the reindexing of a model to a later stage is again a model. -/
theorem exists_good_stageModel [IsCofiltered I] [EssentiallySmall.{u} I]
    [∀ i, IsAffine (𝒳.obj i)] [∀ i, IsAffine (𝒮.obj i)]
    (hX : IsLimit cX) (hS : IsLimit cS) (D : DescentDatum f) (hD : Etale D.over.hom)
    (hqc : QuasiCompact D.over.hom) (hsep : IsSeparated D.over.hom) :
    ∃ (k : I) (V : Over (𝒳.obj k))
      (ψ : (Over.pullback (pullback.fst (φ.app k) (φ.app k))).obj V ≅
        (Over.pullback (pullback.snd (φ.app k) (φ.app k))).obj V)
      (e : D.over ≅ (Over.pullback (cX.π.app k)).obj V),
      Etale V.hom ∧ QuasiCompact V.hom ∧ IsSeparated V.hom ∧
        DescentDatum.ActPullbackLaw V
          (DescentDatum.pullbackIsoOfBaseChangeIso (φ.app k) V ψ).hom ∧
        IsStageModel φ f hf D k V ψ e := by
  have hRI : MorphismProperty.RespectsIso (@Etale : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hRS : MorphismProperty.RespectsIso (@IsSeparated : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hBE : MorphismProperty.IsStableUnderBaseChange (@Etale : MorphismProperty Scheme.{u}) :=
    inferInstance
  have hBS : MorphismProperty.IsStableUnderBaseChange
      (@IsSeparated : MorphismProperty Scheme.{u}) := inferInstance
  have := hD
  have := hqc
  have := hsep
  have hfp : FinitePresentation D.over.hom := ⟨inferInstance, hqc, inferInstance⟩
  have hA {p q : I} (n : p ⟶ q) : IsAffineHom (𝒳.map n) := inferInstance
  have hC (p : I) : CompactSpace (𝒳.obj p) := inferInstance
  have hQ (p : I) : QuasiSeparatedSpace (𝒳.obj p) := inferInstance
  obtain ⟨i, V, ψ, e, hV, hm⟩ := exists_stageModel φ f hf hX hS D hfp
  -- étale over a later stage
  obtain ⟨j₁, m₁, hEt₁⟩ := exists_etale_overPullback_obj_of_isLimit 𝒳 cX hX i V hV
    (prop_of_overIso @Etale e hD)
  have hV₁ : FinitePresentation ((Over.pullback (𝒳.map m₁)).obj V).hom :=
    LimitFPObjectDescent.finitePresentation_overPullback _ V hV
  have hm₁ := isStageModel_reindex φ f hf D V ψ e hm m₁
  -- separated over a yet later stage
  obtain ⟨j₂, m₂, hSep₂⟩ := exists_isSeparated_overPullback_obj_of_isLimit 𝒳 cX hX j₁
    ((Over.pullback (𝒳.map m₁)).obj V) hV₁
    (prop_of_overIso @IsSeparated
      (e ≪≫ (overPullbackCompIso (𝒳.map m₁) (cX.π.app j₁) (cX.π.app i) (cX.w m₁) V).symm) hsep)
  have hV₂ : FinitePresentation
      ((Over.pullback (𝒳.map m₂)).obj ((Over.pullback (𝒳.map m₁)).obj V)).hom :=
    LimitFPObjectDescent.finitePresentation_overPullback _ _ hV₁
  have hm₂ := isStageModel_reindex φ f hf D ((Over.pullback (𝒳.map m₁)).obj V)
    (sqReindexIso φ m₁ V ψ) _ hm₁ m₂
  -- the cocycle condition at a yet later stage
  obtain ⟨k, m₃, hcoc⟩ := exists_stage_actPullbackLaw φ f hf hX hS D j₂
    ((Over.pullback (𝒳.map m₂)).obj ((Over.pullback (𝒳.map m₁)).obj V))
    (sqReindexIso φ m₂ ((Over.pullback (𝒳.map m₁)).obj V) (sqReindexIso φ m₁ V ψ)) _ hV₂ hm₂
  refine ⟨k, _, _, _, ?_, ?_, ?_, hcoc,
    isStageModel_reindex φ f hf D
      ((Over.pullback (𝒳.map m₂)).obj ((Over.pullback (𝒳.map m₁)).obj V))
      (sqReindexIso φ m₂ ((Over.pullback (𝒳.map m₁)).obj V) (sqReindexIso φ m₁ V ψ)) _ hm₂ m₃⟩
  · have h₁ := hEt₁
    have h₂ : Etale ((Over.pullback (𝒳.map m₂)).obj
        ((Over.pullback (𝒳.map m₁)).obj V)).hom := by
      change Etale (pullback.snd ((Over.pullback (𝒳.map m₁)).obj V).hom (𝒳.map m₂))
      infer_instance
    change Etale (pullback.snd ((Over.pullback (𝒳.map m₂)).obj
      ((Over.pullback (𝒳.map m₁)).obj V)).hom (𝒳.map m₃))
    infer_instance
  · exact (LimitFPObjectDescent.finitePresentation_overPullback _ _ hV₂).2.1
  · have h₁ := hSep₂
    change IsSeparated (pullback.snd ((Over.pullback (𝒳.map m₂)).obj
      ((Over.pullback (𝒳.map m₁)).obj V)).hom (𝒳.map m₃))
    infer_instance

/-! ### The limit step -/

/-- **Effectivity of quasi-compact separated étale descent passes to the limit.** -/
theorem qcSepEtaleEffective_of_forall_stage [IsCofiltered I] [EssentiallySmall.{u} I]
    [∀ i, IsAffine (𝒳.obj i)] [∀ i, IsAffine (𝒮.obj i)]
    (hX : IsLimit cX) (hS : IsLimit cS) (H : ∀ i, QcSepEtaleEffective (φ.app i)) :
    QcSepEtaleEffective f := by
  refine qcSepEtaleEffective_of_isEtaleEffective fun D hD hqc hsep ↦ ?_
  obtain ⟨k, V, ψ, e, hEt, hQc, hSep, hcoc, hm⟩ :=
    exists_good_stageModel φ f hf hX hS D hD hqc hsep
  have hEtk : Etale (stageDatum φ k V ψ hcoc).over.hom := hEt
  have hEff := (H k).isEtaleEffective (stageDatum φ k V ψ hcoc) hQc hSep
  have := hD
  have hEtp : Etale (DescentDatum.pullbackSquareDatum (stagePullbackFunctor φ f hf k)
      (stageDatum φ k V ψ hcoc)).over.hom :=
    DescentDatum.property_pullbackSquare_over_hom _ @Etale _ hEt
  have hEff2 := DescentDatum.isEtaleEffective_pullbackSquare
    (stagePullbackFunctor φ f hf k) hEff
  exact Functor.essImage.ofIso
    (ObjectProperty.isoMk _ (isoStageDatumPullback φ f hf D k V ψ e hcoc hm).symm) hEff2

end LimitDatum

end AlgebraicGeometry

end
