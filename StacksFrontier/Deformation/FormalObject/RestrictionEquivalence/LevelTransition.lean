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
public import StacksFrontier.Deformation.FormalObject.RestrictionEquivalence.Formalization

/-!
# Level transitions of formal objects

Composite adic transition maps and composite transition morphisms of formal objects, the
identification of a level with the Artinian base once a power of the maximal ideal vanishes, and
the least such level, from which onward the transition morphisms are isomorphisms.
-/

@[expose] public section

namespace Deformation

section
open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u v w uF vF

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

namespace FormalEvaluation

/-- The composite of the transition maps from the `m`-th to the `n`-th adic truncation of a
complete local algebra, for `n ≤ m`. -/
noncomputable def adicTransitionComposite
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (m n : ℕ) (hnm : n ≤ m) :
    AdicTruncation.obj R m ⟶ AdicTruncation.obj R n :=
  Nat.leRecOn hnm (fun {j} f => (AdicTruncation.transitionNat j).app R ≫ f) (𝟙 _)

/-- The composite transition map from a level to itself is the identity. -/
theorem adicTransitionComposite_id
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (n : ℕ) :
    adicTransitionComposite R n n (Nat.le_refl n) = 𝟙 (AdicTruncation.obj R n) := by
  simp [adicTransitionComposite, Nat.leRecOn_self]

/-- The composite of the transition morphisms of a formal object from level `m` to level `n`, for
`n ≤ m`. -/
def formalLevelTransition
    {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (X : FormalObject p) (m n : ℕ) (hnm : n ≤ m) : X.level m ⟶ X.level n :=
  Nat.leRecOn hnm (fun {j} f => X.transition j ≫ f) (𝟙 _)

/-- The composite transition morphism of a formal object from a level to itself is the identity. -/
theorem formalLevelTransition_id
    {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (X : FormalObject p) (n : ℕ) :
    formalLevelTransition X n n (Nat.le_refl n) = 𝟙 (X.level n) :=
  by
    simp [formalLevelTransition, Nat.leRecOn_self]

/-- Peeling off the last step of an iterated composite built with `Nat.leRecOn`. -/
private theorem leRecOn_succ_comp {C : Type*} [Category C] {obj : ℕ → C}
    (t : ∀ j, obj (j + 1) ⟶ obj j) {n m : ℕ} (hnm : n ≤ m) (h : n ≤ m + 1) :
    Nat.leRecOn h (fun {j} f => t j ≫ f) (𝟙 (obj n)) =
      t m ≫ Nat.leRecOn hnm (fun {j} f => t j ≫ f) (𝟙 (obj n)) :=
  Nat.leRecOn_succ (C := fun j => obj j ⟶ obj n) (n := n) (m := m) hnm (h2 := h)
    (next := fun {j} f => t j ≫ f) (𝟙 (obj n))

/-- The composite transition map from level `m + 1` is the transition map to level `m` followed by
the composite transition map from level `m`. -/
theorem adicTransitionComposite_succ
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) {n m : ℕ} (hnm : n ≤ m)
    (h : n ≤ m + 1) :
    adicTransitionComposite R (m + 1) n h =
      (AdicTruncation.transitionNat m).app R ≫ adicTransitionComposite R m n hnm := by
  exact leRecOn_succ_comp (obj := fun j => AdicTruncation.obj R j)
    (fun j => (AdicTruncation.transitionNat j).app R) hnm h

/-- The composite transition maps between adic truncations are natural in morphisms of complete
local algebras. -/
theorem adicTransitionComposite_naturality
    (R S : CompleteLocalAlgCat.{u, v, w} Λ k) (f : R ⟶ S)
    {m n : ℕ} (hnm : n ≤ m) :
    adicTransitionComposite R m n hnm ≫ (AdicTruncation.functor n).map f =
      (AdicTruncation.functor m).map f ≫ adicTransitionComposite S m n hnm := by
  induction m, hnm using Nat.le_induction with
  | base =>
      simp only [adicTransitionComposite_id, Category.id_comp]
      exact (Category.comp_id _).symm
  | succ m hnm ih =>
      rw [adicTransitionComposite_succ R hnm (Nat.le_succ_of_le hnm),
        adicTransitionComposite_succ S hnm (Nat.le_succ_of_le hnm)]
      rw [Category.assoc, ih, ← Category.assoc, ← Category.assoc,
        ← (AdicTruncation.transitionNat m).naturality f, Category.assoc]

/-- The composite transition morphism from level `m + 1` is the transition morphism to level `m`
followed by the composite transition morphism from level `m`. -/
theorem formalLevelTransition_succ
    {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (X : FormalObject p) {n m : ℕ} (hnm : n ≤ m) (h : n ≤ m + 1) :
    formalLevelTransition X (m + 1) n h =
      X.transition m ≫ formalLevelTransition X m n hnm := by
  exact leRecOn_succ_comp X.transition hnm h

/-- The composite transition morphism of the formal object `X.snd` lies over the composite
transition map between the adic truncations of its base. -/
theorem formalLevelTransition_lift
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (X : CategoricalPullback artinianToComplete
      (FormalObject.projection (p := p))) (m n : ℕ) (hnm : n ≤ m) :
    p.IsHomLift (adicTransitionComposite X.snd.base m n hnm)
      (formalLevelTransition X.snd m n hnm) := by
  induction m, hnm using Nat.le_induction with
  | base =>
      apply IsHomLift.of_fac p _ _ (X.snd.level_eq n) (X.snd.level_eq n)
      rw [adicTransitionComposite_id, formalLevelTransition_id]
      simp
      rfl
  | succ m hnm ih =>
      rw [adicTransitionComposite_succ X.snd.base hnm (Nat.le_succ_of_le hnm),
        formalLevelTransition_succ X.snd hnm (Nat.le_succ_of_le hnm)]
      let := X.snd.transition_lift m
      let := ih
      exact IsHomLift.comp p _ _ _ _

/-- The composite transition morphism of the formal object `X.snd` is strongly cocartesian over the
composite transition map between the adic truncations of its base. -/
theorem formalLevelTransition_isStronglyCocartesian
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p)
    (X : CategoricalPullback artinianToComplete
      (FormalObject.projection (p := p))) (m n : ℕ) (hnm : n ≤ m) :
    Functor.IsStronglyCocartesian p
      (adicTransitionComposite X.snd.base m n hnm)
      (formalLevelTransition X.snd m n hnm) := by
  induction m, hnm using Nat.le_induction with
  | base =>
      rw [adicTransitionComposite_id, formalLevelTransition_id]
      let : p.IsHomLift (𝟙 (AdicTruncation.obj X.snd.base n)) (𝟙 (X.snd.level n)) :=
        IsHomLift.of_fac p (𝟙 (AdicTruncation.obj X.snd.base n))
          (𝟙 (X.snd.level n)) (X.snd.level_eq n) (X.snd.level_eq n) (by simp)
      infer_instance
  | succ m hnm ih =>
      rw [adicTransitionComposite_succ X.snd.base hnm (Nat.le_succ_of_le hnm),
        formalLevelTransition_succ X.snd hnm (Nat.le_succ_of_le hnm)]
      let : Functor.IsStronglyCocartesian p
          ((AdicTruncation.transitionNat m).app X.snd.base) (X.snd.transition m) :=
        isStronglyCocartesian_of_isCofiberedInGroupoids hp _ _
          (X.snd.transition_lift m)
      let := ih
      infer_instance


/-- Composite transition morphisms of a formal object compose. -/
theorem formalLevelTransition_comp
    {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (X : FormalObject p) {m n l : ℕ} (hmn : n ≤ m) (hnl : l ≤ n) :
    formalLevelTransition X m n hmn ≫ formalLevelTransition X n l hnl =
      formalLevelTransition X m l (hnl.trans hmn) := by
  induction m, hmn using Nat.le_induction with
  | base =>
      rw [formalLevelTransition_id X n]
      simp
  | succ m hnm ih =>
      rw [formalLevelTransition_succ X hnm (Nat.le_succ_of_le hnm), Category.assoc, ih,
        ← formalLevelTransition_succ X (hnl.trans hnm) (Nat.le_succ_of_le (hnl.trans hnm))]

/-- Morphisms of formal objects commute with the composite transition morphisms. -/
theorem formalHom_naturality_down
    {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    {X Y : FormalObject p} (f : X ⟶ Y) {m n : ℕ} (hnm : n ≤ m) :
    formalLevelTransition X m n hnm ≫ f.app n =
      f.app m ≫ formalLevelTransition Y m n hnm := by
  induction m, hnm using Nat.le_induction with
  | base =>
      rw [formalLevelTransition_id X n, formalLevelTransition_id Y n]
      simp
  | succ m hnm ih =>
      rw [formalLevelTransition_succ X hnm (Nat.le_succ_of_le hnm),
        formalLevelTransition_succ Y hnm (Nat.le_succ_of_le hnm), Category.assoc, ih,
        ← Category.assoc, f.naturality m, Category.assoc]


/-- If the `(n + 1)`-st power of the maximal ideal of `X.fst` vanishes, the identification of the
image under `p` of the `n`-th level of `X.snd` with `X.fst`. -/
noncomputable def levelBaseIso
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (X : CategoricalPullback artinianToComplete
      (FormalObject.projection (p := p)))
    (n : ℕ) (hn : maximalIdeal X.fst ^ (n + 1) = ⊥) :
    p.obj (X.snd.level n) ≅ X.fst :=
  eqToIso (X.snd.level_eq n) ≪≫
    ((AdicTruncation.functor n).mapIso X.iso).symm ≪≫
      artinianTruncationIso X.fst n hn

/-- The isomorphisms `levelBaseIso` are natural in morphisms of the restriction. -/
theorem levelBaseIso_naturality
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    {X Y : CategoricalPullback artinianToComplete
      (FormalObject.projection (p := p))} (f : X ⟶ Y) (n : ℕ)
    (hnX : maximalIdeal X.fst ^ (n + 1) = ⊥)
    (hnY : maximalIdeal Y.fst ^ (n + 1) = ⊥) :
    (levelBaseIso p X n hnX).hom ≫ f.fst =
      p.map (f.snd.app n) ≫ (levelBaseIso p Y n hnY).hom := by
  let cX := eqToHom (X.snd.level_eq n)
  let cY := eqToHom (Y.snd.level_eq n)
  let tX := (AdicTruncation.functor n).map X.iso.inv
  let tY := (AdicTruncation.functor n).map Y.iso.inv
  let aX := artinianTruncationIso X.fst n hnX
  let aY := artinianTruncationIso Y.fst n hnY
  let g := artinianToComplete.map f.fst
  let cYinv := eqToHom (Y.snd.level_eq n).symm
  have hw : g ≫ Y.iso.hom = X.iso.hom ≫ f.snd.base := by
    show g ≫ Y.iso.hom = X.iso.hom ≫ FormalObject.projection.map f.snd
    exact f.w
  have hW : X.iso.inv ≫ g = f.snd.base ≫ Y.iso.inv := by
    rw [Iso.inv_comp_eq, ← reassoc_of% hw, Iso.hom_inv_id, Category.comp_id]
  let := f.snd.app_lift n
  have hfac := IsHomLift.fac' p
    ((AdicTruncation.functor n).map f.snd.base) (f.snd.app n)
  have hfac' : p.map (f.snd.app n) = cX ≫
      (AdicTruncation.functor n).map f.snd.base ≫ cYinv := hfac
  show cX ≫ tX ≫ aX.hom ≫ f.fst =
    p.map (f.snd.app n) ≫ cY ≫ tY ≫ aY.hom
  calc
    cX ≫ tX ≫ aX.hom ≫ f.fst =
        cX ≫ tX ≫ ((AdicTruncation.functor n).map g ≫ aY.hom) := by
          rw [artinianTruncationIso_naturality X.fst Y.fst n hnX hnY f.fst]
    _ = cX ≫ (tX ≫ (AdicTruncation.functor n).map g) ≫ aY.hom := by
          simp [Category.assoc]
    _ = cX ≫ (AdicTruncation.functor n).map (X.iso.inv ≫ g) ≫ aY.hom := by
          rw [← Functor.map_comp]
    _ = cX ≫ (AdicTruncation.functor n).map (f.snd.base ≫ Y.iso.inv) ≫ aY.hom := by
          rw [hW]
    _ = cX ≫ (AdicTruncation.functor n).map f.snd.base ≫ tY ≫ aY.hom := by
          rw [Functor.map_comp]
          rfl
    _ = (cX ≫ (AdicTruncation.functor n).map f.snd.base ≫ cYinv) ≫
        (cY ≫ tY ≫ aY.hom) := by
          simp [Category.assoc, cY, cYinv, eqToHom_refl]
    _ = p.map (f.snd.app n) ≫ cY ≫ tY ≫ aY.hom := by
          rw [hfac']

/-- The isomorphisms `levelBaseIso` at levels `n` and `n + 1` are compatible with the `n`-th
transition morphism of `X.snd`. -/
theorem levelBaseIso_transition
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (X : CategoricalPullback artinianToComplete
      (FormalObject.projection (p := p))) (n : ℕ)
    (hn : maximalIdeal X.fst ^ (n + 1) = ⊥)
    (hn' : maximalIdeal X.fst ^ (n + 1 + 1) = ⊥) :
    p.map (X.snd.transition n) ≫ (levelBaseIso p X n hn).hom =
      (levelBaseIso p X (n + 1) hn').hom := by
  let c₀ := eqToHom (X.snd.level_eq (n + 1))
  let c₁ := eqToHom (X.snd.level_eq n)
  let t₀ := (AdicTruncation.transitionNat n).app X.snd.base
  let t₁ := (AdicTruncation.transitionNat n).app
    (artinianToComplete.obj X.fst)
  let u₀ := (AdicTruncation.functor (n + 1)).map X.iso.inv
  let u₁ := (AdicTruncation.functor n).map X.iso.inv
  let a₀ := artinianTruncationIso X.fst (n + 1) hn'
  let a₁ := artinianTruncationIso X.fst n hn
  let := X.snd.transition_lift n
  have hfac := IsHomLift.fac' p t₀ (X.snd.transition n)
  have hnat := (AdicTruncation.transitionNat n).naturality X.iso.inv
  change p.map (X.snd.transition n) = c₀ ≫ t₀ ≫ eqToHom (X.snd.level_eq n).symm at hfac
  change u₀ ≫ t₁ = t₀ ≫ u₁ at hnat
  show p.map (X.snd.transition n) ≫ c₁ ≫ u₁ ≫ a₁.hom =
    c₀ ≫ u₀ ≫ a₀.hom
  calc
    p.map (X.snd.transition n) ≫ c₁ ≫ u₁ ≫ a₁.hom =
        c₀ ≫ t₀ ≫ u₁ ≫ a₁.hom := by
          rw [hfac]
          simp [Category.assoc, c₁]
    _ = c₀ ≫ u₀ ≫ t₁ ≫ a₁.hom := by rw [← reassoc_of% hnat]
    _ = c₀ ≫ u₀ ≫ a₀.hom := by
          rw [artinianTruncationIso_transition X.fst n hn hn']

/-- The isomorphisms `levelBaseIso` at levels `n ≤ m` are compatible with the composite transition
morphism of `X.snd`. -/
theorem levelBaseIso_formalTransition
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (X : CategoricalPullback artinianToComplete
      (FormalObject.projection (p := p)))
    {m n : ℕ} (hnm : n ≤ m)
    (hn : maximalIdeal X.fst ^ (n + 1) = ⊥) :
    p.map (formalLevelTransition X.snd m n hnm) ≫
        (levelBaseIso p X n hn).hom =
      (levelBaseIso p X m
        (maximalIdeal_pow_succ_eq_bot_of_le X.fst hnm hn)).hom := by
  induction m, hnm using Nat.le_induction with
  | base =>
      rw [formalLevelTransition_id]
      simp
  | succ m hnm ih =>
      let hm := maximalIdeal_pow_succ_eq_bot_of_le X.fst hnm hn
      let hm' := maximalIdeal_pow_succ_eq_bot_of_le X.fst
        (Nat.le_succ_of_le hnm) hn
      rw [formalLevelTransition_succ X.snd hnm (Nat.le_succ_of_le hnm),
        Functor.map_comp]
      calc
        (p.map (X.snd.transition m) ≫
            p.map (formalLevelTransition X.snd m n hnm)) ≫
            (levelBaseIso p X n hn).hom =
          p.map (X.snd.transition m) ≫
            (p.map (formalLevelTransition X.snd m n hnm) ≫
              (levelBaseIso p X n hn).hom) := by simp [Category.assoc]
        _ = p.map (X.snd.transition m) ≫ (levelBaseIso p X m hm).hom := by
              rw [ih]
        _ = (levelBaseIso p X (m + 1) hm').hom := levelBaseIso_transition p X m hm hm'

/-- If the `(n + 1)`-st power of the maximal ideal of `X.fst` vanishes, the `n`-th level of `X.snd`
is isomorphic to an object of `F` over `X.fst`, by an isomorphism lying over `levelBaseIso`. -/
theorem exists_level_lift
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p)
    (X : CategoricalPullback artinianToComplete
      (FormalObject.projection (p := p)))
    (n : ℕ) (hn : maximalIdeal X.fst ^ (n + 1) = ⊥) :
    ∃ (Y : F) (_ : p.obj Y = X.fst) (α : X.snd.level n ≅ Y),
      p.IsHomLift (levelBaseIso p X n hn).hom α.hom := by
  let c := levelBaseIso p X n hn
  obtain ⟨y, hy, β, hβ⟩ := hp.exists_iso_lift c.op.symm
  let Y := Opposite.unop y
  have hY : p.obj Y = X.fst := by
    show Opposite.unop (p.op.obj y) = X.fst
    rw [hy]
  let α : X.snd.level n ≅ Y := β.unop.symm
  have hfac := IsHomLift.fac p.op (c.op.symm.hom) β.hom
  have hβ' : p.IsHomLift c.inv β.unop.hom := by
    apply IsHomLift.of_fac p c.inv β.unop.hom hY rfl
    have hfac' : c.inv = eqToHom hY.symm ≫ p.map β.unop.hom := by
      simpa using congrArg (fun f => f.unop) hfac
    simpa using hfac'
  let cY : p.obj Y ≅ p.obj (X.snd.level n) := eqToIso hY ≪≫ c.symm
  have hcast : p.IsHomLift (eqToHom hY) (𝟙 Y) :=
    IsHomLift.id_lift_eqToHom_domain hY rfl
  have hβY : p.IsHomLift cY.hom β.unop.hom := by
    let := hcast
    let := hβ'
    simpa [cY] using
      (IsHomLift.comp p (eqToHom hY) c.inv (𝟙 Y) β.unop.hom)
  have hαY : p.IsHomLift cY.inv α.hom := by
    let := hβY
    exact IsHomLift.inv_lift_inv p cY β.unop
  have hα : p.IsHomLift c.hom α.hom := by
    apply IsHomLift.of_fac p c.hom α.hom rfl hY
    let := hαY
    have hmapα := IsHomLift.eq_of_isHomLift p cY.inv α.hom
    calc
      c.hom = cY.inv ≫ eqToHom hY := by simp [cY]
      _ = p.map α.hom ≫ eqToHom hY := by rw [hmapα]
  exact ⟨Y, hY, α, hα⟩

/-- The least `n` such that the `(n + 1)`-st power of the maximal ideal of `X.fst` vanishes. -/
noncomputable def minimalEvaluationIndex
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (X : CategoricalPullback artinianToComplete
      (FormalObject.projection (p := p))) : ℕ :=
  Nat.find (exists_maximalIdeal_pow_succ_eq_bot_of_isArtinian X.fst)

/-- The `(minimalEvaluationIndex p X + 1)`-st power of the maximal ideal of `X.fst` vanishes. -/
theorem minimalEvaluationIndex_spec
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (X : CategoricalPullback artinianToComplete
      (FormalObject.projection (p := p))) :
    maximalIdeal X.fst ^ (minimalEvaluationIndex p X + 1) = ⊥ :=
  Nat.find_spec (exists_maximalIdeal_pow_succ_eq_bot_of_isArtinian X.fst)

/-- `minimalEvaluationIndex p X` is at most every `n` for which the `(n + 1)`-st power of the
maximal ideal of `X.fst` vanishes. -/
theorem minimalEvaluationIndex_le
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (X : CategoricalPullback artinianToComplete
      (FormalObject.projection (p := p)))
    (n : ℕ) (hn : maximalIdeal X.fst ^ (n + 1) = ⊥) :
    minimalEvaluationIndex p X ≤ n :=
  Nat.find_min' (exists_maximalIdeal_pow_succ_eq_bot_of_isArtinian X.fst) hn

/-- If the `(i + 1)`-st power of the maximal ideal of `X.fst` vanishes for some `i ≤ n`, the
composite transition morphism of `X.snd` from level `m` to level `n` is an isomorphism. -/
theorem formalLevelTransition_isIso
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p)
    (X : CategoricalPullback artinianToComplete
      (FormalObject.projection (p := p))) (m n : ℕ) (hnm : n ≤ m)
    (i : ℕ) (hin : i ≤ n) (hi : maximalIdeal X.fst ^ (i + 1) = ⊥) :
    IsIso (formalLevelTransition X.snd m n hnm) := by
  induction m generalizing n with
  | zero =>
      have hn : n = 0 := by omega
      subst n
      rw [formalLevelTransition_id]
      infer_instance
  | succ m ih =>
      by_cases hn : n = m + 1
      · subst n
        rw [formalLevelTransition_id]
        infer_instance
      · have hnm' : n ≤ m := by omega
        have hm' : maximalIdeal X.fst ^ (m + 1) = ⊥ :=
          maximalIdeal_pow_succ_eq_bot_of_le X.fst (hin.trans hnm') hi
        have hm'' : maximalIdeal X.fst ^ (m + 1 + 1) = ⊥ := by
          convert maximalIdeal_pow_succ_eq_bot_of_le X.fst
            (by omega : i ≤ m + 1) hi using 1
        let : IsIso (X.snd.transition m) := formalTransition_isIso p hp X m hm' hm''
        have htail : IsIso (formalLevelTransition X.snd m n hnm') :=
          ih n hnm' hin
        rw [formalLevelTransition_succ X.snd hnm' (Nat.le_succ_of_le hnm')]
        infer_instance

end FormalEvaluation

end

end Deformation

end
