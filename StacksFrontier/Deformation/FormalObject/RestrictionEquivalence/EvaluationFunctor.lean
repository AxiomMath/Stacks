module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import Mathlib.RingTheory.HopkinsLevitzki
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Fibrewise
public import StacksFrontier.Deformation.Basic
public import StacksFrontier.Deformation.Cofibered
public import StacksFrontier.Deformation.Completed.Basic
public import StacksFrontier.Deformation.FormalObject.AdicQuotient
public import StacksFrontier.Deformation.FormalObject.Basic
public import StacksFrontier.Deformation.Groupoid.BaseCategory
public import StacksFrontier.Deformation.FormalObject.RestrictionEquivalence.LevelTransition

/-!
# The evaluation functor

The evaluation of an object of the restriction at its least stabilized level, the resulting
evaluation functor to the original category, its essential surjectivity, its compatibility with
the projections to Artinian local algebras, and the morphisms from an evaluation object to the
levels of the formal object.
-/

@[expose] public section

namespace Deformation

section
open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u v w uF vF

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

namespace FormalEvaluation

/-- An object of `F` over `X.fst` together with an isomorphism to it from the level
`minimalEvaluationIndex p X` of `X.snd`, lying over `levelBaseIso`. -/
structure EvaluationData
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p)
    (X : CategoricalPullback artinianToComplete
      (FormalObject.projection (p := p))) where
  /-- The object of `F`. -/
  object : F
  /-- The object lies over `X.fst`. -/
  object_over : p.obj object = X.fst
  /-- The isomorphism from the level `minimalEvaluationIndex p X` of `X.snd`. -/
  levelIso : X.snd.level (minimalEvaluationIndex p X) ≅ object
  /-- The isomorphism lies over `levelBaseIso`. -/
  levelIso_lift : p.IsHomLift (levelBaseIso p X (minimalEvaluationIndex p X)
    (minimalEvaluationIndex_spec p X)).hom levelIso.hom

/-- A chosen `EvaluationData` for an object of the restriction. -/
noncomputable def evaluationData
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p)
    (X : CategoricalPullback artinianToComplete
      (FormalObject.projection (p := p))) : EvaluationData p hp X := by
  let h := exists_level_lift p hp X (minimalEvaluationIndex p X)
    (minimalEvaluationIndex_spec p X)
  let Y := Classical.choose h
  have hY := Classical.choose_spec h
  let α := Classical.choose hY.2
  have hα := Classical.choose_spec hY.2
  exact ⟨Y, hY.1, α, hα⟩

/-- The object of `F` of the chosen `EvaluationData` of `X`. -/
noncomputable def evaluationObject
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p)
    (X : CategoricalPullback artinianToComplete
      (FormalObject.projection (p := p))) : F :=
  (evaluationData p hp X).object

/-- The isomorphism from `evaluationObject p hp X` to the level `minimalEvaluationIndex p X` of
`X.snd`. -/
noncomputable def evaluationIsoAtMinimalLevel
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p)
    (X : CategoricalPullback artinianToComplete
      (FormalObject.projection (p := p))) :
    evaluationObject p hp X ≅ X.snd.level (minimalEvaluationIndex p X) :=
  (evaluationData p hp X).levelIso.symm


/-- If the `(m + 1)`-st power of the maximal ideal of `X.fst` vanishes, the isomorphism from
`evaluationObject p hp X` to the `m`-th level of `X.snd`. -/
noncomputable def evaluationIsoAtLevel
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p)
    (X : CategoricalPullback artinianToComplete
      (FormalObject.projection (p := p))) (m : ℕ)
    (hm : maximalIdeal X.fst ^ (m + 1) = ⊥) :
    evaluationObject p hp X ≅ X.snd.level m := by
  let n := minimalEvaluationIndex p X
  let hnm : n ≤ m := minimalEvaluationIndex_le p X m hm
  letI : IsIso (formalLevelTransition X.snd m n hnm) :=
    formalLevelTransition_isIso p hp X m n hnm n le_rfl
      (minimalEvaluationIndex_spec p X)
  exact evaluationIsoAtMinimalLevel p hp X ≪≫
    (asIso (formalLevelTransition X.snd m n hnm)).symm

/-- The isomorphisms `evaluationIsoAtLevel` at levels `n ≤ m` are compatible with the composite
transition morphism of `X.snd`. -/
theorem evaluationIsoAtLevel_coherence
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p)
    (X : CategoricalPullback artinianToComplete
      (FormalObject.projection (p := p)))
    {m n : ℕ} (hnm : n ≤ m)
    (hm : maximalIdeal X.fst ^ (m + 1) = ⊥)
    (hn : maximalIdeal X.fst ^ (n + 1) = ⊥) :
    (evaluationIsoAtLevel p hp X m hm).hom ≫
        formalLevelTransition X.snd m n hnm =
      (evaluationIsoAtLevel p hp X n hn).hom := by
  let i := minimalEvaluationIndex p X
  have hin : i ≤ n := minimalEvaluationIndex_le p X n hn
  have him : i ≤ m := minimalEvaluationIndex_le p X m hm
  let : IsIso (formalLevelTransition X.snd m i him) :=
    formalLevelTransition_isIso p hp X m i him i le_rfl
      (minimalEvaluationIndex_spec p X)
  let : IsIso (formalLevelTransition X.snd n i hin) :=
    formalLevelTransition_isIso p hp X n i hin i le_rfl
      (minimalEvaluationIndex_spec p X)
  let : IsIso (formalLevelTransition X.snd m n hnm) :=
    formalLevelTransition_isIso p hp X m n hnm i hin
      (minimalEvaluationIndex_spec p X)
  let dmi := asIso (formalLevelTransition X.snd m i him)
  let dni := asIso (formalLevelTransition X.snd n i hin)
  have hcomp : formalLevelTransition X.snd m n hnm ≫ dni.hom = dmi.hom := by
    simpa [dmi, dni] using formalLevelTransition_comp X.snd hnm hin
  have hInv : dmi.inv ≫ formalLevelTransition X.snd m n hnm = dni.inv := by
    rw [Iso.inv_comp_eq, ← hcomp, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  show ((evaluationData p hp X).levelIso.symm.hom ≫ dmi.inv) ≫
      formalLevelTransition X.snd m n hnm =
    (evaluationData p hp X).levelIso.symm.hom ≫ dni.inv
  rw [Category.assoc, hInv]

/-- The morphism of evaluation objects induced by `f : X ⟶ Y`, computed at a level `m` at which the
`(m + 1)`-st powers of the maximal ideals of `X.fst` and `Y.fst` vanish. -/
noncomputable def evaluationMapAtStage
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p)
    {X Y : CategoricalPullback artinianToComplete
      (FormalObject.projection (p := p))} (f : X ⟶ Y) (m : ℕ)
    (hmX : maximalIdeal X.fst ^ (m + 1) = ⊥)
    (hmY : maximalIdeal Y.fst ^ (m + 1) = ⊥) :
    evaluationObject p hp X ⟶ evaluationObject p hp Y :=
  (evaluationIsoAtLevel p hp X m hmX).hom ≫ f.snd.app m ≫
    (evaluationIsoAtLevel p hp Y m hmY).inv

/-- The morphism `evaluationMapAtStage p hp f m hmX hmY` does not depend on the level `m`. -/
theorem evaluationMapAtStage_independent
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p)
    {X Y : CategoricalPullback artinianToComplete
      (FormalObject.projection (p := p))} (f : X ⟶ Y)
    {m n : ℕ} (hnm : n ≤ m)
    (hmX : maximalIdeal X.fst ^ (m + 1) = ⊥)
    (hmY : maximalIdeal Y.fst ^ (m + 1) = ⊥)
    (hnX : maximalIdeal X.fst ^ (n + 1) = ⊥)
    (hnY : maximalIdeal Y.fst ^ (n + 1) = ⊥) :
    evaluationMapAtStage p hp f m hmX hmY =
      evaluationMapAtStage p hp f n hnX hnY := by
  let eXm := evaluationIsoAtLevel p hp X m hmX
  let eXn := evaluationIsoAtLevel p hp X n hnX
  let eYm := evaluationIsoAtLevel p hp Y m hmY
  let eYn := evaluationIsoAtLevel p hp Y n hnY
  have hX := evaluationIsoAtLevel_coherence p hp X hnm hmX hnX
  have hY := evaluationIsoAtLevel_coherence p hp Y hnm hmY hnY
  have hYinv : formalLevelTransition Y.snd m n hnm ≫ eYn.inv = eYm.inv := by
    rw [Iso.comp_inv_eq, ← hY, Iso.inv_hom_id_assoc]
  dsimp [evaluationMapAtStage, eXm, eXn, eYm, eYn]
  calc
    (evaluationIsoAtLevel p hp X m hmX).hom ≫ f.snd.app m ≫
        (evaluationIsoAtLevel p hp Y m hmY).inv =
      (evaluationIsoAtLevel p hp X m hmX).hom ≫ f.snd.app m ≫
      (formalLevelTransition Y.snd m n hnm ≫
    (evaluationIsoAtLevel p hp Y n hnY).inv) := by
          rw [← hYinv]
    _ = (evaluationIsoAtLevel p hp X m hmX).hom ≫
        (formalLevelTransition X.snd m n hnm ≫ f.snd.app n) ≫
          (evaluationIsoAtLevel p hp Y n hnY).inv := by
          rw [formalHom_naturality_down f.snd hnm]
          simp [Category.assoc]
    _ = (evaluationIsoAtLevel p hp X n hnX).hom ≫ f.snd.app n ≫
        (evaluationIsoAtLevel p hp Y n hnY).inv := by
          calc
            _ = ((evaluationIsoAtLevel p hp X m hmX).hom ≫
                formalLevelTransition X.snd m n hnm) ≫ f.snd.app n ≫
                (evaluationIsoAtLevel p hp Y n hnY).inv := by
                  simp [Category.assoc]
            _ = _ := by rw [hX]

/-- The identity of `X` induces the identity of its evaluation object. -/
theorem evaluationMapAtStage_id
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p)
    (X : CategoricalPullback artinianToComplete
      (FormalObject.projection (p := p))) (m : ℕ)
    (hm : maximalIdeal X.fst ^ (m + 1) = ⊥) :
    evaluationMapAtStage p hp (𝟙 X) m hm hm = 𝟙 (evaluationObject p hp X) := by
  show (evaluationIsoAtLevel p hp X m hm).hom ≫
      𝟙 (X.snd.level m) ≫ (evaluationIsoAtLevel p hp X m hm).inv = _
  simp

/-- The evaluation functor from the restriction of the formal objects of `p` to Artinian local
algebras to `F`. -/
noncomputable def evaluationFunctor
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p) :
    CategoricalPullback artinianToComplete
      (FormalObject.projection (p := p)) ⥤ F where
  obj := evaluationObject p hp
  map {X Y} f := by
    let iX := minimalEvaluationIndex p X
    let iY := minimalEvaluationIndex p Y
    let m := max iX iY
    have hiX : iX ≤ m := le_max_left _ _
    have hiY : iY ≤ m := le_max_right _ _
    have hmX : maximalIdeal X.fst ^ (m + 1) = ⊥ :=
      maximalIdeal_pow_succ_eq_bot_of_le X.fst hiX (minimalEvaluationIndex_spec p X)
    have hmY : maximalIdeal Y.fst ^ (m + 1) = ⊥ :=
      maximalIdeal_pow_succ_eq_bot_of_le Y.fst hiY (minimalEvaluationIndex_spec p Y)
    exact evaluationMapAtStage p hp f m hmX hmY
  map_id X := by
    let i := minimalEvaluationIndex p X
    have h := evaluationMapAtStage_id p hp X i (minimalEvaluationIndex_spec p X)
    simpa only [max_self] using h
  map_comp {X Y Z} f g := by
    let iX := minimalEvaluationIndex p X
    let iY := minimalEvaluationIndex p Y
    let iZ := minimalEvaluationIndex p Z
    let m₁ := max iX iY
    let m₂ := max iY iZ
    let m₃ := max iX iZ
    let M := max m₁ iZ
    have hX₁ : iX ≤ m₁ := le_max_left _ _
    have hY₁ : iY ≤ m₁ := le_max_right _ _
    have hY₂ : iY ≤ m₂ := le_max_left _ _
    have hZ₂ : iZ ≤ m₂ := le_max_right _ _
    have hX₃ : iX ≤ m₃ := le_max_left _ _
    have hZ₃ : iZ ≤ m₃ := le_max_right _ _
    have hX₁M : iX ≤ M := hX₁.trans (le_max_left _ _)
    have hY₁M : iY ≤ M := hY₁.trans (le_max_left _ _)
    have hZ₁M : iZ ≤ M := le_max_right _ _
    have hM₁ : m₁ ≤ M := le_max_left _ _
    have hM₂ : m₂ ≤ M := max_le_iff.mpr ⟨hY₁M, hZ₁M⟩
    have hM₃ : m₃ ≤ M := max_le_iff.mpr ⟨hX₁M, hZ₁M⟩
    have hmX₁ : maximalIdeal X.fst ^ (m₁ + 1) = ⊥ :=
      maximalIdeal_pow_succ_eq_bot_of_le X.fst hX₁ (minimalEvaluationIndex_spec p X)
    have hmY₁ : maximalIdeal Y.fst ^ (m₁ + 1) = ⊥ :=
      maximalIdeal_pow_succ_eq_bot_of_le Y.fst hY₁ (minimalEvaluationIndex_spec p Y)
    have hmY₂ : maximalIdeal Y.fst ^ (m₂ + 1) = ⊥ :=
      maximalIdeal_pow_succ_eq_bot_of_le Y.fst hY₂ (minimalEvaluationIndex_spec p Y)
    have hmZ₂ : maximalIdeal Z.fst ^ (m₂ + 1) = ⊥ :=
      maximalIdeal_pow_succ_eq_bot_of_le Z.fst hZ₂ (minimalEvaluationIndex_spec p Z)
    have hmX₃ : maximalIdeal X.fst ^ (m₃ + 1) = ⊥ :=
      maximalIdeal_pow_succ_eq_bot_of_le X.fst hX₃ (minimalEvaluationIndex_spec p X)
    have hmZ₃ : maximalIdeal Z.fst ^ (m₃ + 1) = ⊥ :=
      maximalIdeal_pow_succ_eq_bot_of_le Z.fst hZ₃ (minimalEvaluationIndex_spec p Z)
    have hmXM : maximalIdeal X.fst ^ (M + 1) = ⊥ :=
      maximalIdeal_pow_succ_eq_bot_of_le X.fst hX₁M (minimalEvaluationIndex_spec p X)
    have hmYM : maximalIdeal Y.fst ^ (M + 1) = ⊥ :=
      maximalIdeal_pow_succ_eq_bot_of_le Y.fst hY₁M (minimalEvaluationIndex_spec p Y)
    have hmZM : maximalIdeal Z.fst ^ (M + 1) = ⊥ :=
      maximalIdeal_pow_succ_eq_bot_of_le Z.fst hZ₁M (minimalEvaluationIndex_spec p Z)
    have hmapf : evaluationMapAtStage p hp f m₁ hmX₁ hmY₁ =
        evaluationMapAtStage p hp f M hmXM hmYM :=
      (evaluationMapAtStage_independent p hp f hM₁ hmXM hmYM hmX₁ hmY₁).symm
    have hmapg : evaluationMapAtStage p hp g m₂ hmY₂ hmZ₂ =
        evaluationMapAtStage p hp g M hmYM hmZM :=
      (evaluationMapAtStage_independent p hp g hM₂ hmYM hmZM hmY₂ hmZ₂).symm
    have hmapfg : evaluationMapAtStage p hp (f ≫ g) m₃ hmX₃ hmZ₃ =
        evaluationMapAtStage p hp (f ≫ g) M hmXM hmZM :=
      (evaluationMapAtStage_independent p hp (f ≫ g) hM₃ hmXM hmZM hmX₃ hmZ₃).symm
    rw [hmapf, hmapg, hmapfg]
    dsimp [evaluationMapAtStage]
    rw [show (f.snd ≫ g.snd).app M = f.snd.app M ≫ g.snd.app M by rfl]
    simp [Category.assoc]

/-- The evaluation functor is essentially surjective. -/
theorem evaluationFunctor_essSurj
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p) : (evaluationFunctor p hp).EssSurj := by
  apply Functor.EssSurj.mk
  intro A
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_succ_eq_bot_of_isArtinian (p.obj A)
  let X := (formalizationFunctor p hp).obj A
  have hq : IsIso (artinianAdicQuotient (p.obj A) n) :=
    artinianAdicQuotient_isIso (p.obj A) n hn
  let := hq
  have hL : IsIso (artinianTruncationLift p hp A n).arrow :=
    isIso_of_isCofiberedInGroupoids_of_base_isIso hp
      (artinianAdicQuotient (p.obj A) n)
      (artinianTruncationLift p hp A n).arrow
      (artinianTruncationLift p hp A n).lift
  let := hL
  refine ⟨X, ?_⟩
  exact ⟨evaluationIsoAtLevel p hp X n hn ≪≫
    (asIso (artinianTruncationLift p hp A n).arrow).symm⟩

/-- At a level `m` at which the `(m + 1)`-st powers of the maximal ideals of `X.fst` and `Y.fst`
vanish, the image of `f` under the evaluation functor corresponds to `f.snd.app m` under
`evaluationIsoAtLevel`. -/
theorem evaluationFunctor_map_naturality_at_level
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p)
    {X Y : CategoricalPullback artinianToComplete
      (FormalObject.projection (p := p))} (f : X ⟶ Y) (m : ℕ)
    (hmX : maximalIdeal X.fst ^ (m + 1) = ⊥)
    (hmY : maximalIdeal Y.fst ^ (m + 1) = ⊥) :
    (evaluationFunctor p hp).map f ≫
        (evaluationIsoAtLevel p hp Y m hmY).hom =
      (evaluationIsoAtLevel p hp X m hmX).hom ≫ f.snd.app m := by
  let iX := minimalEvaluationIndex p X
  let iY := minimalEvaluationIndex p Y
  let M := max iX iY
  have hiX : iX ≤ m := minimalEvaluationIndex_le p X m hmX
  have hiY : iY ≤ m := minimalEvaluationIndex_le p Y m hmY
  have hM : M ≤ m := max_le hiX hiY
  have hMX : maximalIdeal X.fst ^ (M + 1) = ⊥ :=
    maximalIdeal_pow_succ_eq_bot_of_le X.fst (le_max_left _ _) (minimalEvaluationIndex_spec p X)
  have hMY : maximalIdeal Y.fst ^ (M + 1) = ⊥ :=
    maximalIdeal_pow_succ_eq_bot_of_le Y.fst (le_max_right _ _) (minimalEvaluationIndex_spec p Y)
  have hstage := evaluationMapAtStage_independent p hp f
    (m := m) (n := M) hM hmX hmY hMX hMY
  show evaluationMapAtStage p hp f M hMX hMY ≫
      (evaluationIsoAtLevel p hp Y m hmY).hom =
    (evaluationIsoAtLevel p hp X m hmX).hom ≫ f.snd.app m
  rw [← hstage]
  dsimp [evaluationMapAtStage]
  simp [Category.assoc]

/-- The image under `p` of `evaluationIsoAtLevel` followed by `levelBaseIso` does not depend on the
level. -/
theorem evaluationBaseIso_atCommonLevel
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p)
    (X : CategoricalPullback artinianToComplete
      (FormalObject.projection (p := p)))
    {n m : ℕ} (hnm : n ≤ m)
    (hn : maximalIdeal X.fst ^ (n + 1) = ⊥)
    (hm : maximalIdeal X.fst ^ (m + 1) = ⊥) :
    p.map (evaluationIsoAtLevel p hp X n hn).hom ≫
        (levelBaseIso p X n hn).hom =
      p.map (evaluationIsoAtLevel p hp X m hm).hom ≫
        (levelBaseIso p X m hm).hom := by
  rw [← evaluationIsoAtLevel_coherence p hp X hnm hm hn, Functor.map_comp, Category.assoc,
    levelBaseIso_formalTransition p X hnm hn]

/-- The evaluation functor followed by `p` is isomorphic to the projection of the restriction to
Artinian local algebras. -/
noncomputable def evaluationCanOver
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p) :
    (evaluationFunctor p hp) ⋙ p ≅
      CategoricalPullback.π₁ artinianToComplete
        (FormalObject.projection (p := p)) := by
  refine NatIso.ofComponents (fun X => ?_) ?_
  · let i := minimalEvaluationIndex p X
    let hi := minimalEvaluationIndex_spec p X
    exact (p.mapIso (evaluationIsoAtLevel p hp X i hi)).trans
      (levelBaseIso p X i hi)
  · intro X Y f
    let iX := minimalEvaluationIndex p X
    let iY := minimalEvaluationIndex p Y
    let M := max iX iY
    have hX : maximalIdeal X.fst ^ (iX + 1) = ⊥ := minimalEvaluationIndex_spec p X
    have hY : maximalIdeal Y.fst ^ (iY + 1) = ⊥ := minimalEvaluationIndex_spec p Y
    have hMX : maximalIdeal X.fst ^ (M + 1) = ⊥ :=
      maximalIdeal_pow_succ_eq_bot_of_le X.fst (le_max_left _ _) hX
    have hMY : maximalIdeal Y.fst ^ (M + 1) = ⊥ :=
      maximalIdeal_pow_succ_eq_bot_of_le Y.fst (le_max_right _ _) hY
    have hiX : iX ≤ M := le_max_left _ _
    have hiY : iY ≤ M := le_max_right _ _
    have hcX := evaluationBaseIso_atCommonLevel p hp X hiX hX hMX
    have hcY := evaluationBaseIso_atCommonLevel p hp Y hiY hY hMY
    have hEval := evaluationFunctor_map_naturality_at_level p hp f M hMX hMY
    have hBase := levelBaseIso_naturality p f M hMX hMY
    have hEvalMap :
        p.map ((evaluationFunctor p hp).map f) ≫
            p.map (evaluationIsoAtLevel p hp Y M hMY).hom =
          p.map (evaluationIsoAtLevel p hp X M hMX).hom ≫
            p.map (f.snd.app M) := by
      have hEval' := hEval
      change evaluationMapAtStage p hp f M hMX hMY ≫
          (evaluationIsoAtLevel p hp Y M hMY).hom =
        (evaluationIsoAtLevel p hp X M hMX).hom ≫ f.snd.app M at hEval'
      change p.map (evaluationMapAtStage p hp f M hMX hMY) ≫
          p.map (evaluationIsoAtLevel p hp Y M hMY).hom = _
      calc
        _ = p.map (evaluationMapAtStage p hp f M hMX hMY ≫
            (evaluationIsoAtLevel p hp Y M hMY).hom) := (p.map_comp _ _).symm
        _ = p.map ((evaluationIsoAtLevel p hp X M hMX).hom ≫ f.snd.app M) :=
          congrArg (fun g => p.map g) hEval'
        _ = _ := p.map_comp _ _
    have hcX' : p.map (evaluationIsoAtLevel p hp X iX hX).hom ≫
          (levelBaseIso p X iX hX).hom =
        p.map (evaluationIsoAtLevel p hp X M hMX).hom ≫
          (levelBaseIso p X M hMX).hom := by
      simpa only [evaluationFunctor] using hcX
    have hcY' : p.map (evaluationIsoAtLevel p hp Y iY hY).hom ≫
          (levelBaseIso p Y iY hY).hom =
        p.map (evaluationIsoAtLevel p hp Y M hMY).hom ≫
          (levelBaseIso p Y M hMY).hom := by
      simpa only [evaluationFunctor] using hcY
    have hMap : (evaluationFunctor p hp).map f =
        evaluationMapAtStage p hp f M hMX hMY := by
      dsimp only [evaluationFunctor]
    have hEvalMap' :
        p.map (evaluationMapAtStage p hp f M hMX hMY) ≫
            p.map (evaluationIsoAtLevel p hp Y M hMY).hom =
          p.map (evaluationIsoAtLevel p hp X M hMX).hom ≫
            p.map (f.snd.app M) := by
      simpa only [evaluationFunctor, hMap] using hEvalMap
    change p.map (evaluationMapAtStage p hp f M hMX hMY) ≫
        p.map (evaluationIsoAtLevel p hp Y iY hY).hom ≫
          (levelBaseIso p Y iY hY).hom =
      p.map (evaluationIsoAtLevel p hp X iX hX).hom ≫
        (levelBaseIso p X iX hX).hom ≫ f.fst
    calc
      p.map (evaluationMapAtStage p hp f M hMX hMY) ≫
          p.map (evaluationIsoAtLevel p hp Y iY hY).hom ≫
            (levelBaseIso p Y iY hY).hom =
        p.map (evaluationMapAtStage p hp f M hMX hMY) ≫
          p.map (evaluationIsoAtLevel p hp Y M hMY).hom ≫
            (levelBaseIso p Y M hMY).hom := by
              simp only [hcY']
      _ = p.map (evaluationIsoAtLevel p hp X M hMX).hom ≫
            p.map (f.snd.app M) ≫ (levelBaseIso p Y M hMY).hom := by
              rw [← Category.assoc, hEvalMap', Category.assoc]
      _ = p.map (evaluationIsoAtLevel p hp X M hMX).hom ≫
            (levelBaseIso p X M hMX).hom ≫ f.fst := by
              calc
                _ = p.map (evaluationIsoAtLevel p hp X M hMX).hom ≫
                    (p.map (f.snd.app M) ≫ (levelBaseIso p Y M hMY).hom) := by
                      simp
                _ = p.map (evaluationIsoAtLevel p hp X M hMX).hom ≫
                    ((levelBaseIso p X M hMX).hom ≫ f.fst) := by rw [hBase.symm]
                _ = _ := by simp
      _ = p.map (evaluationIsoAtLevel p hp X iX hX).hom ≫
            (levelBaseIso p X iX hX).hom ≫ f.fst := by
              rw [← Category.assoc, ← hcX', Category.assoc]

/-- At the minimal evaluation index, `p` of `evaluationIsoAtLevel` followed by `levelBaseIso` is the
transport along `(evaluationData p hp X).object_over`. -/
private theorem map_evaluationIsoAtLevel_comp_levelBaseIso_minimal
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p)
    (X : CategoricalPullback artinianToComplete
      (FormalObject.projection (p := p))) :
    p.map (evaluationIsoAtLevel p hp X (minimalEvaluationIndex p X)
        (minimalEvaluationIndex_spec p X)).hom ≫
      (levelBaseIso p X (minimalEvaluationIndex p X) (minimalEvaluationIndex_spec p X)).hom =
      eqToHom (evaluationData p hp X).object_over := by
  let i := minimalEvaluationIndex p X
  let hi := minimalEvaluationIndex_spec p X
  let d := evaluationData p hp X
  let c := levelBaseIso p X i hi
  let : p.IsHomLift c.hom d.levelIso.hom := d.levelIso_lift
  let : p.IsHomLift c.inv d.levelIso.inv :=
    IsHomLift.inv_lift_inv p c d.levelIso
  have hfac := IsHomLift.fac' p c.inv d.levelIso.inv
  have hmap' : p.map d.levelIso.inv = eqToHom d.object_over ≫ c.inv := by
    simpa [c, levelBaseIso] using hfac
  have ht : formalLevelTransition X.snd i i
      (minimalEvaluationIndex_le p X i hi) = 𝟙 (X.snd.level i) := by
    have hproof : minimalEvaluationIndex_le p X i hi = Nat.le_refl i :=
      Subsingleton.elim _ _
    rw [hproof, formalLevelTransition_id]
  have hiso : asIso (𝟙 (X.snd.level i)) = Iso.refl (X.snd.level i) := by
    apply Iso.ext
    simp
  have he : evaluationIsoAtLevel p hp X i hi = d.levelIso.symm := by
    simp only [evaluationIsoAtLevel, evaluationIsoAtMinimalLevel,
      evaluationObject, d, evaluationData, ht, hiso, i]
    simp only [Iso.refl_symm, Iso.trans_refl]
  rw [he]
  change p.map d.levelIso.inv ≫ c.hom = _
  rw [hmap', Category.assoc, c.inv_hom_id, Category.comp_id]

/-- The components of `evaluationCanOver p hp` are the transports along
`(evaluationData p hp X).object_over`. -/
theorem evaluationCanOver_hom_eqToHom
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p)
    (X : CategoricalPullback artinianToComplete
      (FormalObject.projection (p := p))) :
    (evaluationCanOver p hp).hom.app X =
      eqToHom (evaluationData p hp X).object_over :=
  map_evaluationIsoAtLevel_comp_levelBaseIso_minimal p hp X

/-- The evaluation functor followed by `p` equals the projection of the restriction to Artinian
local algebras. -/
theorem evaluationFunctor_comp_eq
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p) :
    evaluationFunctor p hp ⋙ p =
      CategoricalPullback.π₁ artinianToComplete
        (FormalObject.projection (p := p)) := by
  let r := CategoricalPullback.π₁ artinianToComplete
    (FormalObject.projection (p := p))
  let hobj : ∀ X, (evaluationFunctor p hp ⋙ p).obj X = r.obj X := fun X => by
    show p.obj (evaluationObject p hp X) = X.fst
    exact (evaluationData p hp X).object_over
  refine CategoryTheory.Functor.ext hobj ?_
  intro X Y f
  have hnat := (evaluationCanOver p hp).hom.naturality f
  rw [evaluationCanOver_hom_eqToHom p hp X,
    evaluationCanOver_hom_eqToHom p hp Y] at hnat
  change p.map ((evaluationFunctor p hp).map f) ≫ eqToHom (hobj Y) =
    eqToHom (hobj X) ≫ f.fst at hnat
  show p.map ((evaluationFunctor p hp).map f) =
    eqToHom (hobj X) ≫ f.fst ≫ eqToHom (hobj Y).symm
  calc
    p.map ((evaluationFunctor p hp).map f) =
        (p.map ((evaluationFunctor p hp).map f) ≫ eqToHom (hobj Y)) ≫
          eqToHom (hobj Y).symm := by simp [Category.assoc]
    _ = (eqToHom (hobj X) ≫ f.fst) ≫ eqToHom (hobj Y).symm :=
      congrArg (fun g => g ≫ eqToHom (hobj Y).symm) hnat
    _ = _ := Category.assoc _ _ _

/-- The morphism from the evaluation object of `X` to the `n`-th level of `X.snd`. -/
noncomputable def evaluationLeg
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p)
    (X : CategoricalPullback artinianToComplete
      (FormalObject.projection (p := p))) (n : ℕ) :
    evaluationObject p hp X ⟶ X.snd.level n := by
  let i := minimalEvaluationIndex p X
  let m := max i n
  let hm : maximalIdeal X.fst ^ (m + 1) = ⊥ :=
    maximalIdeal_pow_succ_eq_bot_of_le X.fst (le_max_left _ _)
      (minimalEvaluationIndex_spec p X)
  exact (evaluationIsoAtLevel p hp X m hm).hom ≫
    formalLevelTransition X.snd m n (le_max_right _ _)

/-- The morphism `evaluationLeg p hp X n` is strongly cocartesian over its image under `p`. -/
theorem evaluationLeg_isStronglyCocartesian
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p)
    (X : CategoricalPullback artinianToComplete
      (FormalObject.projection (p := p))) (n : ℕ) :
    Functor.IsStronglyCocartesian p
      (p.map (evaluationLeg p hp X n)) (evaluationLeg p hp X n) := by
  let i := minimalEvaluationIndex p X
  let m := max i n
  let hm : maximalIdeal X.fst ^ (m + 1) = ⊥ :=
    maximalIdeal_pow_succ_eq_bot_of_le X.fst (le_max_left _ _)
      (minimalEvaluationIndex_spec p X)
  let e := evaluationIsoAtLevel p hp X m hm
  let t := formalLevelTransition X.snd m n (le_max_right _ _)
  let : Functor.IsStronglyCocartesian p (p.map e.hom) e.hom :=
    isStronglyCocartesian_of_isCofiberedInGroupoids hp
      (p.map e.hom) e.hom (IsHomLift.map p e.hom)
  let : Functor.IsStronglyCocartesian p (p.map t) t :=
    isStronglyCocartesian_of_isCofiberedInGroupoids hp
      (p.map t) t (IsHomLift.map p t)
  dsimp only [evaluationLeg, i, m, hm, e, t]
  rw [Functor.map_comp]
  infer_instance

/-- The image under `p` of the composite transition morphism of `X.snd` is the composite transition
map between the adic truncations of its base, up to the identifications `X.snd.level_eq`. -/
theorem formalLevelTransition_fac
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (X : CategoricalPullback artinianToComplete
      (FormalObject.projection (p := p))) (m n : ℕ) (hnm : n ≤ m) :
    p.map (formalLevelTransition X.snd m n hnm) ≫
        eqToHom (X.snd.level_eq n) =
      eqToHom (X.snd.level_eq m) ≫
        adicTransitionComposite X.snd.base m n hnm := by
  let : p.IsHomLift (adicTransitionComposite X.snd.base m n hnm)
      (formalLevelTransition X.snd m n hnm) :=
    formalLevelTransition_lift p X m n hnm
  have hfac := IsHomLift.fac' p
    (adicTransitionComposite X.snd.base m n hnm)
    (formalLevelTransition X.snd m n hnm)
  change p.map (formalLevelTransition X.snd m n hnm) =
    eqToHom (X.snd.level_eq m) ≫
      adicTransitionComposite X.snd.base m n hnm ≫
        eqToHom (X.snd.level_eq n).symm at hfac
  rw [hfac]
  simp [Category.assoc]

/-- For `m` at least `minimalEvaluationIndex p X`, the image under `p` of `evaluationIsoAtLevel`
followed by `levelBaseIso` is the transport along `(evaluationData p hp X).object_over`. -/
theorem evaluationIsoAtLevel_base
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p)
    (X : CategoricalPullback artinianToComplete
      (FormalObject.projection (p := p)))
    (m : ℕ) (hm : maximalIdeal X.fst ^ (m + 1) = ⊥)
    (hmi : minimalEvaluationIndex p X ≤ m) :
    p.map (evaluationIsoAtLevel p hp X m hm).hom ≫
        (levelBaseIso p X m hm).hom =
      eqToHom (evaluationData p hp X).object_over := by
  have hcoh := evaluationBaseIso_atCommonLevel p hp X hmi (minimalEvaluationIndex_spec p X) hm
  simpa using hcoh.symm.trans (map_evaluationIsoAtLevel_comp_levelBaseIso_minimal p hp X)

/-- The image under `p` of `evaluationLeg p hp X n`, through the adic truncations of the base of
`X.snd`. -/
theorem evaluationLeg_map
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p)
    (X : CategoricalPullback artinianToComplete
      (FormalObject.projection (p := p))) (n : ℕ) :
    let i := minimalEvaluationIndex p X
    let m := max i n
    let hm : maximalIdeal X.fst ^ (m + 1) = ⊥ :=
      maximalIdeal_pow_succ_eq_bot_of_le X.fst (le_max_left _ _)
        (minimalEvaluationIndex_spec p X)
    p.map (evaluationLeg p hp X n) =
      eqToHom (evaluationData p hp X).object_over ≫
        (artinianTruncationIso X.fst m hm).inv ≫
        (AdicTruncation.functor m).map X.iso.hom ≫
        adicTransitionComposite X.snd.base m n (le_max_right _ _) ≫
        eqToHom (X.snd.level_eq n).symm := by
  dsimp only
  let i := minimalEvaluationIndex p X
  let m := max i n
  let hm : maximalIdeal X.fst ^ (m + 1) = ⊥ :=
    maximalIdeal_pow_succ_eq_bot_of_le X.fst (le_max_left _ _)
      (minimalEvaluationIndex_spec p X)
  let hmi : i ≤ m := le_max_left _ _
  let hmn : n ≤ m := le_max_right _ _
  let e := evaluationIsoAtLevel p hp X m hm
  let t := formalLevelTransition X.snd m n hmn
  dsimp only [evaluationObject] at ⊢
  have he := evaluationIsoAtLevel_base p hp X m hm hmi
  have ht := formalLevelTransition_fac p X m n hmn
  have ht' : eqToHom (X.snd.level_eq m).symm ≫ p.map t =
      adicTransitionComposite X.snd.base m n hmn ≫
        eqToHom (X.snd.level_eq n).symm := by
    have h := congrArg (fun f => eqToHom (X.snd.level_eq m).symm ≫ f ≫
      eqToHom (X.snd.level_eq n).symm) ht
    simpa [Category.assoc] using h
  have hLeg : evaluationLeg p hp X n = e.hom ≫ t := by
    simp [evaluationLeg, i, m, e, t]
  have hcinv : (levelBaseIso p X m hm).inv = (artinianTruncationIso X.fst m hm).inv ≫
      (AdicTruncation.functor m).map X.iso.hom ≫
        eqToHom (X.snd.level_eq m).symm := by
    simp [levelBaseIso, Iso.trans_inv]
  have hmap : p.map e.hom = eqToHom (evaluationData p hp X).object_over ≫
      (levelBaseIso p X m hm).inv := by
    have h := congrArg (fun f => f ≫ (levelBaseIso p X m hm).inv) he
    rw [Category.assoc, (levelBaseIso p X m hm).hom_inv_id,
      Category.comp_id] at h
    exact h
  have hcomp : p.map (e.hom ≫ t) = p.map e.hom ≫ p.map t := p.map_comp e.hom t
  dsimp only [evaluationObject] at hLeg hmap hcomp
  rw [hLeg]
  rw [hcomp, hmap]
  rw [hcinv]
  simp only [Category.assoc]
  rw [ht']

end FormalEvaluation

end

end Deformation

end
