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
public import StacksFrontier.Deformation.FormalObject.RestrictionEquivalence.EvaluationFunctor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Restricting a completion to Artinian local algebras

For a category cofibered in groupoids over the category of Artinian local
`Λ`-algebras, its category of formal objects restricts back to a category
equivalent to the original category.

## Main definitions

* `RestrictionCompletionEquivalence` packages the canonical inclusion of
  Artinian local algebras into complete local algebras and the comparison functor.

## Main results

* `restrictionCompletionEquivalence` constructs the canonical equivalence
  from the restriction of the completion back to the original cofibered category.

## Implementation notes

Restriction is represented by the categorical pullback of the projection from formal
objects along the inclusion of Artinian local algebras into complete local algebras.
The inclusion is `artinianToComplete`, so the comparison respects the specified
residue-field identifications as well as the underlying algebras.
The comparison is recorded as an equivalence over the Artinian base. Once a power
of the maximal ideal vanishes, its level isomorphisms are natural in morphisms,
compatible with transitions, and lie over the canonical quotient maps. Thus the
comparison transports diagrams as well as objects. Level `m` uses the positive
power `m + 1`; the least vanishing power in the source corresponds to the first
such level.

## References

* [Stacks Project, Tag 06SJ](https://stacks.math.columbia.edu/tag/06SJ)
-/

@[expose] public section

namespace Deformation

section
open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u v w uF vF

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

namespace FormalEvaluation

section

-- `FormalEvaluation.evaluationFunctor` has `evaluationObject` as its object part and
-- `CategoricalPullback.π₁` has the first projection as its object part, so unless both are
-- reducible a goal naming both spellings of either is not type-correct at `implicit`
-- transparency and `rw`/`assumption` fail on it.
attribute [local implicit_reducible] FormalEvaluation.evaluationFunctor
  FormalEvaluation.evaluationObject CategoricalPullback.π₁

/-- The inverse of `artinianTruncationIso A n hn` is the canonical map `artinianAdicQuotient A n`.
-/
theorem artinianTruncationIso_inv
    (A : ArtinianLocalAlgCat.{u, v, w} Λ k) (n : ℕ)
    (hn : maximalIdeal A ^ (n + 1) = ⊥) :
    (artinianTruncationIso A n hn).inv = artinianAdicQuotient A n := by
  apply (cancel_mono (artinianTruncationIso A n hn).hom).mp
  rw [Iso.inv_hom_id]
  symm
  apply ArtinianLocalAlgCat.hom_ext
  apply AlgHom.ext
  exact artinianTruncationIso_mk A n hn

/-- The canonical maps of an Artinian local algebra to its adic truncations are compatible with the
composite transition maps. -/
theorem artinianAdicQuotient_composite
    (A : ArtinianLocalAlgCat.{u, v, w} Λ k) {m n : ℕ} (h : n ≤ m) :
    artinianAdicQuotient A m ≫
        adicTransitionComposite (artinianToComplete.obj A) m n h =
      artinianAdicQuotient A n := by
  induction m, h using Nat.le_induction with
  | base => simp [adicTransitionComposite_id]
  | succ m h ih =>
    rw [adicTransitionComposite_succ _ h, ← Category.assoc]
    show (artinianAdicQuotient A (m + 1) ≫
      AdicTruncation.transition _ m) ≫ _ = _
    rw [artinianAdicQuotient_transition]
    exact ih

/-- The canonical map from `X.fst` to the `n`-th adic truncation of the base of `X.snd`, through
`X.iso`. -/
noncomputable def evaluationBaseLeg
    {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (X : CategoricalPullback artinianToComplete
      (FormalObject.projection (p := p))) (n : ℕ) :
    X.fst ⟶ AdicTruncation.obj X.snd.base n :=
  artinianAdicQuotient X.fst n ≫ (AdicTruncation.functor n).map X.iso.hom

/-- The morphism `evaluationLeg p hp X n` lies over `evaluationBaseLeg X n`. -/
theorem evaluationLeg_lift
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p)
    (X : CategoricalPullback artinianToComplete
      (FormalObject.projection (p := p))) (n : ℕ) :
    p.IsHomLift (evaluationBaseLeg X n) (evaluationLeg p hp X n) := by
  apply IsHomLift.of_fac p _ _ (evaluationData p hp X).object_over (X.snd.level_eq n)
  have h := evaluationLeg_map p hp X n
  dsimp only at h
  rw [artinianTruncationIso_inv] at h
  rw [← Category.assoc ((AdicTruncation.functor _).map X.iso.hom),
    ← adicTransitionComposite_naturality _ X.snd.base X.iso.hom (m := max (minimalEvaluationIndex p
      X) n) (n := n)] at h
  simp only [← Category.assoc] at h
  rw [Category.assoc (eqToHom _), artinianAdicQuotient_composite] at h
  simp only [evaluationBaseLeg]
  rw [h]
  simp [Category.assoc]

/-- The maps `evaluationBaseLeg` are natural in compatible pairs of morphisms of Artinian algebras
and of bases. -/
theorem evaluationBaseLeg_naturality
    {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    {X Y : CategoricalPullback artinianToComplete
      (FormalObject.projection (p := p))}
    (a : X.fst ⟶ Y.fst) (b : X.snd.base ⟶ Y.snd.base)
    (hab : artinianToComplete.map a ≫ Y.iso.hom = X.iso.hom ≫ b)
    (n : ℕ) :
    evaluationBaseLeg X n ≫ (AdicTruncation.functor n).map b =
      a ≫ evaluationBaseLeg Y n := by
  dsimp only [evaluationBaseLeg]
  rw [Category.assoc, ← Functor.map_comp, ← hab, Functor.map_comp,
    ← Category.assoc, artinianAdicQuotient_naturality, Category.assoc]

/-- For `n ≤ m` such that the `(m + 1)`-st power of the maximal ideal of `X.fst` vanishes, the
morphism `evaluationLeg p hp X n` is `evaluationIsoAtLevel` at level `m` followed by the composite
transition morphism to level `n`. -/
theorem evaluationLeg_eq_of_le
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p)
    (X : CategoricalPullback artinianToComplete
      (FormalObject.projection (p := p))) {m n : ℕ} (hn : n ≤ m)
    (hm : maximalIdeal X.fst ^ (m + 1) = ⊥) :
    evaluationLeg p hp X n = (evaluationIsoAtLevel p hp X m hm).hom ≫
      formalLevelTransition X.snd m n hn := by
  let j := max (minimalEvaluationIndex p X) n
  have hj : j ≤ m := max_le (minimalEvaluationIndex_le p X m hm) hn
  have hj0 := maximalIdeal_pow_succ_eq_bot_of_le X.fst
    (le_max_left (minimalEvaluationIndex p X) n) (minimalEvaluationIndex_spec p X)
  show (evaluationIsoAtLevel p hp X j hj0).hom ≫
    formalLevelTransition X.snd j n (le_max_right _ _) = _
  rw [← evaluationIsoAtLevel_coherence p hp X hj hm hj0,
    Category.assoc, formalLevelTransition_comp]

/-- If the `(m + 1)`-st power of the maximal ideal of `X.fst` vanishes, the morphism
`evaluationLeg p hp X m` is `evaluationIsoAtLevel` at level `m`. -/
theorem evaluationLeg_atLevel
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p)
    (X : CategoricalPullback artinianToComplete
      (FormalObject.projection (p := p))) (m : ℕ)
    (hm : maximalIdeal X.fst ^ (m + 1) = ⊥) :
    evaluationLeg p hp X m = (evaluationIsoAtLevel p hp X m hm).hom := by
  rw [evaluationLeg_eq_of_le p hp X le_rfl hm, formalLevelTransition_id, Category.comp_id]

/-- The morphisms `evaluationLeg` are compatible with the transition morphisms of `X.snd`. -/
theorem evaluationLeg_transition
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p)
    (X : CategoricalPullback artinianToComplete
      (FormalObject.projection (p := p))) (n : ℕ) :
    evaluationLeg p hp X (n + 1) ≫ X.snd.transition n = evaluationLeg p hp X n := by
  let m := max (minimalEvaluationIndex p X) (n + 1)
  have hnm : n + 1 ≤ m := le_max_right _ _
  have hm := maximalIdeal_pow_succ_eq_bot_of_le X.fst
    (le_max_left (minimalEvaluationIndex p X) (n + 1)) (minimalEvaluationIndex_spec p X)
  rw [evaluationLeg_eq_of_le p hp X hnm hm,
    evaluationLeg_eq_of_le p hp X (Nat.le_succ n |>.trans hnm) hm, Category.assoc]
  congr 1
  have ht : X.snd.transition n = formalLevelTransition X.snd (n + 1) n (Nat.le_succ n) := by
    rw [formalLevelTransition_succ _ le_rfl, formalLevelTransition_id, Category.comp_id]
  rw [ht, formalLevelTransition_comp]

/-- The morphisms `evaluationLeg` are natural with respect to the evaluation functor. -/
theorem evaluationLeg_naturality
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p)
    {X Y : CategoricalPullback artinianToComplete
      (FormalObject.projection (p := p))} (f : X ⟶ Y) (n : ℕ) :
    (evaluationFunctor p hp).map f ≫ evaluationLeg p hp Y n =
      evaluationLeg p hp X n ≫ f.snd.app n := by
  let m := max (max (minimalEvaluationIndex p X) (minimalEvaluationIndex p Y)) n
  have hn : n ≤ m := le_max_right _ _
  have hmX := maximalIdeal_pow_succ_eq_bot_of_le X.fst
    ((le_max_left _ _).trans (le_max_left _ _) : minimalEvaluationIndex p X ≤ m)
    (minimalEvaluationIndex_spec p X)
  have hmY := maximalIdeal_pow_succ_eq_bot_of_le Y.fst
    ((le_max_right _ _).trans (le_max_left _ _) : minimalEvaluationIndex p Y ≤ m)
    (minimalEvaluationIndex_spec p Y)
  rw [evaluationLeg_eq_of_le p hp X hn hmX, evaluationLeg_eq_of_le p hp Y hn hmY,
    ← Category.assoc, evaluationFunctor_map_naturality_at_level p hp f m hmX hmY,
    Category.assoc, ← formalHom_naturality_down f.snd hn, ← Category.assoc]

/-- A morphism `h` of evaluation objects lying over `a : X.fst ⟶ Y.fst`, for `a` compatible with a
morphism `b` of bases, is induced through the morphisms `evaluationLeg` by a morphism `X ⟶ Y` of
the restriction. -/
theorem exists_restrictionHom_of_evaluationHom
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p)
    {X Y : CategoricalPullback artinianToComplete
      (FormalObject.projection (p := p))}
    (a : X.fst ⟶ Y.fst) (b : X.snd.base ⟶ Y.snd.base)
    (hab : artinianToComplete.map a ≫ Y.iso.hom = X.iso.hom ≫ b)
    (h : evaluationObject p hp X ⟶ evaluationObject p hp Y)
    (hh : p.IsHomLift a h) :
    ∃ f : X ⟶ Y, ∀ n,
      evaluationLeg p hp X n ≫ f.snd.app n = h ≫ evaluationLeg p hp Y n := by
  classical
  have hdesc (n : ℕ) : ∃ t : X.snd.level n ⟶ Y.snd.level n,
      p.IsHomLift ((AdicTruncation.functor n).map b) t ∧
      evaluationLeg p hp X n ≫ t = h ≫ evaluationLeg p hp Y n := by
    let := hh
    let := evaluationLeg_lift p hp Y n
    let := isStronglyCocartesian_of_isCofiberedInGroupoids hp
      (evaluationBaseLeg X n) (evaluationLeg p hp X n) (evaluationLeg_lift p hp X n)
    let H := (evaluationBaseLeg_naturality a b hab n).symm
    exact ⟨Functor.IsStronglyCocartesian.map p _ (evaluationLeg p hp X n) H
      (h ≫ evaluationLeg p hp Y n), inferInstance,
      Functor.IsStronglyCocartesian.fac p _ (evaluationLeg p hp X n) H
        (h ≫ evaluationLeg p hp Y n)⟩
  choose t ht hfac using hdesc
  have hnat (n : ℕ) : X.snd.transition n ≫ t n = t (n + 1) ≫ Y.snd.transition n := by
    let := ht n
    let := ht (n + 1)
    let := X.snd.transition_lift n
    let := Y.snd.transition_lift n
    let := isStronglyCocartesian_of_isCofiberedInGroupoids hp
      (evaluationBaseLeg X (n + 1)) (evaluationLeg p hp X (n + 1))
      (evaluationLeg_lift p hp X (n + 1))
    have hb := (AdicTruncation.transitionNat n).naturality b
    let : p.IsHomLift
        ((AdicTruncation.transitionNat n).app X.snd.base ≫ (AdicTruncation.functor n).map b)
        (t (n + 1) ≫ Y.snd.transition n) := by
      rw [← hb]
      infer_instance
    apply Functor.IsStronglyCocartesian.ext p (evaluationBaseLeg X (n + 1))
      (evaluationLeg p hp X (n + 1))
      ((AdicTruncation.transitionNat n).app X.snd.base ≫ (AdicTruncation.functor n).map b)
    simp only [← Category.assoc]
    rw [evaluationLeg_transition, hfac, hfac]
    rw [Category.assoc, evaluationLeg_transition]
  refine ⟨{ fst := a
            snd := { base := b
                     app := t
                     app_lift := ht
                     naturality := hnat }
            w := hab }, hfac⟩

/-- The evaluation functor is full. -/
theorem evaluationFunctor_full
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p) : (evaluationFunctor p hp).Full := by
  constructor
  intro X Y h
  let a : X.fst ⟶ Y.fst := eqToHom (evaluationData p hp X).object_over.symm ≫
    p.map h ≫ eqToHom (evaluationData p hp Y).object_over
  let b : X.snd.base ⟶ Y.snd.base :=
    X.iso.inv ≫ artinianToComplete.map a ≫ Y.iso.hom
  have hab : artinianToComplete.map a ≫ Y.iso.hom = X.iso.hom ≫ b := by
    simp [b]
  have hh : p.IsHomLift a h := IsHomLift.of_fac p a h
    (evaluationData p hp X).object_over (evaluationData p hp Y).object_over rfl
  obtain ⟨f, hf⟩ := exists_restrictionHom_of_evaluationHom p hp a b hab h hh
  refine ⟨f, ?_⟩
  let m := max (minimalEvaluationIndex p X) (minimalEvaluationIndex p Y)
  have hmX := maximalIdeal_pow_succ_eq_bot_of_le X.fst
    (le_max_left (minimalEvaluationIndex p X) (minimalEvaluationIndex p Y))
    (minimalEvaluationIndex_spec p X)
  have hmY := maximalIdeal_pow_succ_eq_bot_of_le Y.fst
    (le_max_right (minimalEvaluationIndex p X) (minimalEvaluationIndex p Y))
    (minimalEvaluationIndex_spec p Y)
  apply (cancel_mono (evaluationIsoAtLevel p hp Y m hmY).hom).mp
  rw [evaluationFunctor_map_naturality_at_level p hp f m hmX hmY]
  simpa only [evaluationLeg_atLevel p hp X m hmX, evaluationLeg_atLevel p hp Y m hmY]
    using hf m

/-- The evaluation functor is faithful. -/
theorem evaluationFunctor_faithful
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p) : (evaluationFunctor p hp).Faithful := by
  constructor
  intro X Y f g h
  have hf := (evaluationCanOver p hp).hom.naturality f
  have hg := (evaluationCanOver p hp).hom.naturality g
  change p.map ((evaluationFunctor p hp).map f) ≫ _ = _ ≫ f.fst at hf
  change p.map ((evaluationFunctor p hp).map g) ≫ _ = _ ≫ g.fst at hg
  have ha : f.fst = g.fst := by
    apply (cancel_epi ((evaluationCanOver p hp).hom.app X)).mp
    rw [← hf, ← hg, h]
  have hb : f.snd.base = g.snd.base := by
    apply (cancel_epi X.iso.hom).mp
    show X.iso.hom ≫ FormalObject.projection.map f.snd =
      X.iso.hom ≫ FormalObject.projection.map g.snd
    rw [← f.w, ← g.w, ha]
  apply CategoricalPullback.hom_ext ha
  apply FormalObject.Hom.ext hb
  intro n
  let := f.snd.app_lift n
  let : p.IsHomLift ((AdicTruncation.functor n).map f.snd.base) (g.snd.app n) := by
    rw [hb]
    exact g.snd.app_lift n
  let := isStronglyCocartesian_of_isCofiberedInGroupoids hp
    (evaluationBaseLeg X n) (evaluationLeg p hp X n) (evaluationLeg_lift p hp X n)
  apply Functor.IsStronglyCocartesian.ext p (evaluationBaseLeg X n)
    (evaluationLeg p hp X n) ((AdicTruncation.functor n).map f.snd.base)
  rw [← evaluationLeg_naturality p hp f, ← evaluationLeg_naturality p hp g, h]

end

end FormalEvaluation

open FormalEvaluation

/-- The underlying `Λ`-algebra of an Artinian local algebra. -/
public def artinianUnderlying :
    ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ CommAlgCat.{v, u} Λ where
  obj A := CommAlgCat.of Λ A
  map f := CommAlgCat.ofHom f.hom
  map_id A := by ext; rfl
  map_comp f g := by ext; rfl

/-- The underlying `Λ`-algebra of a complete local algebra. -/
public def completeUnderlying :
    CompleteLocalAlgCat.{u, v, w} Λ k ⥤ CommAlgCat.{v, u} Λ where
  obj A := CommAlgCat.of Λ A
  map f := CommAlgCat.ofHom f.hom
  map_id A := by ext; rfl
  map_comp f g := by ext; rfl

/-- The data and properties of the canonical comparison from the restriction of the
category of formal objects to the original category. -/
public structure RestrictionCompletionEquivalence
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k) where
  /-- An Artinian local algebra, regarded as a complete local algebra with the same
  specified residue field. -/
  inclusion : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤
    CompleteLocalAlgCat.{u, v, w} Λ k
  /-- The inclusion agrees with the canonical inclusion as a functor to complete local
  algebras with fixed residue field. -/
  inclusionIso : inclusion ≅ artinianToComplete
  /-- The canonical comparison from the restriction of formal objects to `F`. -/
  can : CategoricalPullback inclusion (FormalObject.projection (p := p)) ⥤ F
  /-- The comparison lies over the Artinian base category. -/
  canOver : can ⋙ p ≅ CategoricalPullback.π₁ inclusion (FormalObject.projection (p := p))
  /-- The comparison is an equivalence. -/
  isEquivalence : can.IsEquivalence
  /-- Over an Artinian base, the comparison evaluates a formal object at any level from
  which onward the maximal-adic filtration is zero. -/
  objIsoLevel (X : CategoricalPullback inclusion (FormalObject.projection (p := p)))
      (m : ℕ) (hm : maximalIdeal X.fst ^ (m + 1) = ⊥) :
      can.obj X ≅ X.snd.level m
  /-- At a common stabilized level, the comparison intertwines every morphism with
  its level component. -/
  objIsoLevel_naturality
      {X Y : CategoricalPullback inclusion (FormalObject.projection (p := p))}
      (f : X ⟶ Y) (m : ℕ)
      (hX : maximalIdeal X.fst ^ (m + 1) = ⊥)
      (hY : maximalIdeal Y.fst ^ (m + 1) = ⊥) :
      can.map f ≫ (objIsoLevel Y m hY).hom =
        (objIsoLevel X m hX).hom ≫ f.snd.app m
  /-- Evaluation at successive stabilized levels agrees through the formal
  object's transition map. -/
  objIsoLevel_transition
      (X : CategoricalPullback inclusion (FormalObject.projection (p := p)))
      (m : ℕ) (hm : maximalIdeal X.fst ^ (m + 1) = ⊥)
      (hm' : maximalIdeal X.fst ^ (m + 1 + 1) = ⊥) :
      (objIsoLevel X (m + 1) hm').hom ≫ X.snd.transition m =
        (objIsoLevel X m hm).hom
  /-- On underlying algebras, evaluation lies over the quotient projection,
  after the specified identifications of the Artinian and complete bases. -/
  objIsoLevel_over
      (X : CategoricalPullback inclusion (FormalObject.projection (p := p)))
      (m : ℕ) (hm : maximalIdeal X.fst ^ (m + 1) = ⊥) :
      artinianUnderlying.map
          (p.map (objIsoLevel X m hm).hom ≫ eqToHom (X.snd.level_eq m)) =
        artinianUnderlying.map (canOver.hom.app X) ≫
          completeUnderlying.map (inclusionIso.inv.app X.fst ≫ X.iso.hom) ≫
          CommAlgCat.ofHom (Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal X.snd.base m))

/-- Forgetting the residue-field identifications in the canonical inclusion comparison
gives the comparison of underlying `Λ`-algebras. -/
public def RestrictionCompletionEquivalence.inclusionUnderlyingIso
    {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (e : RestrictionCompletionEquivalence p) :
    e.inclusion ⋙ completeUnderlying ≅ artinianUnderlying :=
  Functor.isoWhiskerRight e.inclusionIso completeUnderlying

-- `FormalEvaluation.evaluationFunctor` has `evaluationObject` as its object part, so unless it
-- is reducible a goal naming both spellings is not type-correct at `implicit` transparency and
-- `rw` fails on it.
attribute [local implicit_reducible] FormalEvaluation.evaluationFunctor

/-- A trailing `eqToHom` cancels the opposite one nested inside a conjugate. -/
private theorem eqToHom_comp_eqToHom_cancel {C : Type*} [Category C] {W X Y Z : C}
    (h₁ : W = X) (f : X ⟶ Y) (h₂ : Y = Z) (h₃ : Z = Y) :
    (eqToHom h₁ ≫ f ≫ eqToHom h₂) ≫ eqToHom h₃ = eqToHom h₁ ≫ f := by
  cases h₁
  cases h₂
  simp

/-- Restricting the category of formal objects of a category cofibered in groupoids back
to Artinian local algebras gives a canonical equivalence with the original category. -/
@[stacks 06SJ, sga "7 VI 1.15" "special case"]
public noncomputable def restrictionCompletionEquivalence
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p) : RestrictionCompletionEquivalence p where
  inclusion := artinianToComplete
  inclusionIso := Iso.refl _
  can := FormalEvaluation.evaluationFunctor p hp
  canOver := evaluationCanOver p hp
  isEquivalence :=
    ⟨evaluationFunctor_faithful p hp, evaluationFunctor_full p hp,
      evaluationFunctor_essSurj p hp⟩
  objIsoLevel X m hm := evaluationIsoAtLevel p hp X m hm
  objIsoLevel_naturality f m hX hY := evaluationFunctor_map_naturality_at_level p hp f m hX hY
  objIsoLevel_transition := by
    intro X m hm hm'
    have h := evaluationIsoAtLevel_coherence p hp X (Nat.le_succ m) hm' hm
    rw [formalLevelTransition_succ _ le_rfl, formalLevelTransition_id,
      Category.comp_id] at h
    exact h
  objIsoLevel_over := by
    intro X m hm
    let := evaluationLeg_lift p hp X m
    have h := IsHomLift.fac' p (evaluationBaseLeg X m) (evaluationLeg p hp X m)
    change p.map (evaluationLeg p hp X m) =
      eqToHom (evaluationData p hp X).object_over ≫ evaluationBaseLeg X m ≫
        eqToHom (X.snd.level_eq m).symm at h
    rw [evaluationLeg_atLevel p hp X m hm] at h
    have hmap : p.map (evaluationIsoAtLevel p hp X m hm).hom ≫
        eqToHom (X.snd.level_eq m) =
        eqToHom (evaluationData p hp X).object_over ≫ evaluationBaseLeg X m := by
      rw [h]
      exact eqToHom_comp_eqToHom_cancel _ _ _ _
    rw [hmap, Functor.map_comp, evaluationCanOver_hom_eqToHom]
    apply congrArg (fun g => artinianUnderlying.map
      (eqToHom (evaluationData p hp X).object_over) ≫ g)
    simp only [Iso.refl_inv, NatTrans.id_app]
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro r
    rfl

/-! ### Explicit description of the comparison -/

/-- The inclusion used by the canonical comparison of Tag 06SJ is the canonical inclusion
of Artinian local algebras into complete local algebras. -/
@[simp]
public theorem restrictionCompletionEquivalence_inclusion
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p) :
    (restrictionCompletionEquivalence p hp).inclusion = artinianToComplete :=
  rfl

/-- The identification of the inclusion of Tag 06SJ with the canonical inclusion is the
identity. -/
@[simp]
public theorem restrictionCompletionEquivalence_inclusionIso
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p) :
    (restrictionCompletionEquivalence p hp).inclusionIso = Iso.refl _ :=
  rfl

/-- The comparison functor of Tag 06SJ is strictly compatible with the projections to
Artinian local algebras. -/
public theorem restrictionCompletionEquivalence_can_comp_eq
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p) :
    (restrictionCompletionEquivalence p hp).can ⋙ p =
      CategoricalPullback.π₁ (restrictionCompletionEquivalence p hp).inclusion
        (FormalObject.projection (p := p)) :=
  FormalEvaluation.evaluationFunctor_comp_eq p hp

/-- Every component of the canonical base comparison of Tag 06SJ is the transport along
the corresponding equality of Artinian local algebras. -/
public theorem restrictionCompletionEquivalence_canOver_hom_app
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p)
    (X : CategoricalPullback (restrictionCompletionEquivalence p hp).inclusion
      (FormalObject.projection (p := p)))
    (h : p.obj ((restrictionCompletionEquivalence p hp).can.obj X) = X.fst) :
    (restrictionCompletionEquivalence p hp).canOver.hom.app X = eqToHom h :=
  evaluationCanOver_hom_eqToHom p hp X

end

end Deformation

end
