module

public import Mathlib.CategoryTheory.Localization.Predicate

/-!
# Natural transformations induced along factorizations through localizations

Let `L₁ : C₁ ⥤ D₁` and `L₂ : C₂ ⥤ D₂` be functors, and let `X, Y : D₁ ⥤ D₂` be functors which
factor, up to the isomorphisms `ΦX : L₁ ⋙ X ≅ X₀ ⋙ L₂` and `ΦY : L₁ ⋙ Y ≅ Y₀ ⋙ L₂`, through
functors `X₀, Y₀ : C₁ ⥤ C₂`. A natural transformation `γ : X ⟶ Y` is *induced* by
`γ₀ : X₀ ⟶ Y₀` if the square formed with `ΦX` and `ΦY` commutes after restriction along `L₁`.

When `L₁` is a localization functor, a natural transformation is determined by any
transformation inducing it. Being induced is stable under composition, under whiskering on
either side, and under inversion. This turns an identity between composites of natural
transformations of functors on localized categories — for instance of derived functors on
derived categories — into the corresponding identity between transformations of functors on the
categories being localized, which can be checked there.

## Main definitions

* `CategoryTheory.NatTrans.IsInducedBy`: the transformation `γ` is induced by `γ₀`.
* `CategoryTheory.Functor.compFactorization`: the factorization of a composite.

## Main results

* `CategoryTheory.NatTrans.IsInducedBy.ext`: two transformations induced by the same
  transformation agree, when `L₁` is a localization functor.
* `CategoryTheory.NatTrans.IsInducedBy.comp`, `.whiskerLeft`, `.whiskerRight`, `.inv`: the
  stability properties.
-/

@[expose] public section

namespace CategoryTheory

open Category _root_.CategoryTheory.Functor

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

variable {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] {D₁ : Type u₄} [Category.{v₄} D₁]
  {D₂ : Type u₅} [Category.{v₅} D₂] {D₃ : Type u₆} [Category.{v₆} D₃]
  {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂} {L₃ : C₃ ⥤ D₃}

/-- The factorization of a composite of two functors which factor through functors `X₀`, `Y₀`
along `L₁`, `L₂`, `L₃`. -/
def Functor.compFactorization {X : D₁ ⥤ D₂} {X₀ : C₁ ⥤ C₂} {Y : D₂ ⥤ D₃} {Y₀ : C₂ ⥤ C₃}
    (ΦX : L₁ ⋙ X ≅ X₀ ⋙ L₂) (ΦY : L₂ ⋙ Y ≅ Y₀ ⋙ L₃) : L₁ ⋙ X ⋙ Y ≅ (X₀ ⋙ Y₀) ⋙ L₃ :=
  (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight ΦX Y ≪≫ Functor.associator _ _ _ ≪≫
    isoWhiskerLeft X₀ ΦY ≪≫ (Functor.associator _ _ _).symm

@[simp]
theorem Functor.compFactorization_hom_app {X : D₁ ⥤ D₂} {X₀ : C₁ ⥤ C₂} {Y : D₂ ⥤ D₃}
    {Y₀ : C₂ ⥤ C₃} (ΦX : L₁ ⋙ X ≅ X₀ ⋙ L₂) (ΦY : L₂ ⋙ Y ≅ Y₀ ⋙ L₃) (c : C₁) :
    (Functor.compFactorization ΦX ΦY).hom.app c = Y.map (ΦX.hom.app c) ≫ ΦY.hom.app (X₀.obj c) := by
  simp [Functor.compFactorization]

/-- **A natural transformation induced along factorizations.** The transformation `γ : X ⟶ Y`
is induced by `γ₀ : X₀ ⟶ Y₀` if `L₁ ⋙ X ⟶ L₁ ⋙ Y ≅ Y₀ ⋙ L₂` agrees with
`L₁ ⋙ X ≅ X₀ ⋙ L₂ ⟶ Y₀ ⋙ L₂`. -/
def NatTrans.IsInducedBy {X Y : D₁ ⥤ D₂} {X₀ Y₀ : C₁ ⥤ C₂} (ΦX : L₁ ⋙ X ≅ X₀ ⋙ L₂)
    (ΦY : L₁ ⋙ Y ≅ Y₀ ⋙ L₂) (γ : X ⟶ Y) (γ₀ : X₀ ⟶ Y₀) : Prop :=
  ∀ c : C₁, γ.app (L₁.obj c) ≫ ΦY.hom.app c = ΦX.hom.app c ≫ L₂.map (γ₀.app c)

namespace NatTrans.IsInducedBy

variable {X Y Z : D₁ ⥤ D₂} {X₀ Y₀ Z₀ : C₁ ⥤ C₂} {ΦX : L₁ ⋙ X ≅ X₀ ⋙ L₂}
  {ΦY : L₁ ⋙ Y ≅ Y₀ ⋙ L₂} {ΦZ : L₁ ⋙ Z ≅ Z₀ ⋙ L₂}

/-- **Two transformations induced by the same transformation agree**, along a localization. -/
theorem ext (W : MorphismProperty C₁) [L₁.IsLocalization W] {γ γ' : X ⟶ Y} {γ₀ : X₀ ⟶ Y₀}
    (h : IsInducedBy ΦX ΦY γ γ₀) (h' : IsInducedBy ΦX ΦY γ' γ₀) : γ = γ' :=
  Localization.natTrans_ext L₁ W fun c => by
    rw [← cancel_mono (ΦY.hom.app c), h c, h' c]

theorem id : IsInducedBy ΦX ΦX (𝟙 X) (𝟙 X₀) := fun c => by simp

/-- Transformations induced by equal transformations agree, along a localization. -/
theorem ext_of_eq (W : MorphismProperty C₁) [L₁.IsLocalization W] {γ γ' : X ⟶ Y}
    {γ₀ γ₀' : X₀ ⟶ Y₀} (h : IsInducedBy ΦX ΦY γ γ₀) (h' : IsInducedBy ΦX ΦY γ' γ₀')
    (e : γ₀ = γ₀') : γ = γ' :=
  by subst e; exact h.ext W h'

theorem of_eq {γ : X ⟶ Y} {γ₀ γ₀' : X₀ ⟶ Y₀} (h : IsInducedBy ΦX ΦY γ γ₀) (e : γ₀ = γ₀') :
    IsInducedBy ΦX ΦY γ γ₀' :=
  e ▸ h

theorem comp {γ : X ⟶ Y} {γ₀ : X₀ ⟶ Y₀} {δ : Y ⟶ Z} {δ₀ : Y₀ ⟶ Z₀}
    (hγ : IsInducedBy ΦX ΦY γ γ₀) (hδ : IsInducedBy ΦY ΦZ δ δ₀) :
    IsInducedBy ΦX ΦZ (γ ≫ δ) (γ₀ ≫ δ₀) := fun c => by
  simp only [NatTrans.comp_app, assoc, hδ c, reassoc_of% (hγ c), Functor.map_comp]

/-- The inverse of an induced isomorphism is induced by the inverse. -/
theorem inv {γ : X ≅ Y} {γ₀ : X₀ ≅ Y₀} (h : IsInducedBy ΦX ΦY γ.hom γ₀.hom) :
    IsInducedBy ΦY ΦX γ.inv γ₀.inv := fun c => by
  rw [← cancel_epi (γ.hom.app (L₁.obj c)), Iso.hom_inv_id_app_assoc, reassoc_of% (h c),
    ← L₂.map_comp, Iso.hom_inv_id_app, L₂.map_id, comp_id]

theorem whiskerRight {X X' : D₁ ⥤ D₂} {X₀ X₀' : C₁ ⥤ C₂} {ΦX : L₁ ⋙ X ≅ X₀ ⋙ L₂}
    {ΦX' : L₁ ⋙ X' ≅ X₀' ⋙ L₂} {γ : X ⟶ X'} {γ₀ : X₀ ⟶ X₀'} (h : IsInducedBy ΦX ΦX' γ γ₀)
    {V : D₂ ⥤ D₃} {V₀ : C₂ ⥤ C₃} (ΦV : L₂ ⋙ V ≅ V₀ ⋙ L₃) :
    IsInducedBy (Functor.compFactorization ΦX ΦV) (Functor.compFactorization ΦX' ΦV)
      (Functor.whiskerRight γ V) (Functor.whiskerRight γ₀ V₀) := fun c => by
  simp only [Functor.compFactorization_hom_app, Functor.whiskerRight_app]
  rw [← V.map_comp_assoc, h c, V.map_comp, assoc, assoc]
  exact congrArg (fun t => V.map (ΦX.hom.app c) ≫ t) (ΦV.hom.naturality (γ₀.app c))

theorem whiskerLeft {X : D₁ ⥤ D₂} {X₀ : C₁ ⥤ C₂} (ΦX : L₁ ⋙ X ≅ X₀ ⋙ L₂) {V V' : D₂ ⥤ D₃}
    {V₀ V₀' : C₂ ⥤ C₃} {ΦV : L₂ ⋙ V ≅ V₀ ⋙ L₃} {ΦV' : L₂ ⋙ V' ≅ V₀' ⋙ L₃} {δ : V ⟶ V'}
    {δ₀ : V₀ ⟶ V₀'} (h : IsInducedBy ΦV ΦV' δ δ₀) :
    IsInducedBy (Functor.compFactorization ΦX ΦV) (Functor.compFactorization ΦX ΦV')
      (Functor.whiskerLeft X δ) (Functor.whiskerLeft X₀ δ₀) := fun c => by
  simp only [Functor.compFactorization_hom_app, Functor.whiskerLeft_app]
  have n := δ.naturality (ΦX.hom.app c)
  dsimp at n
  rw [← reassoc_of% n, h (X₀.obj c), assoc]

theorem associator {X : D₁ ⥤ D₂} {X₀ : C₁ ⥤ C₂} {Y : D₂ ⥤ D₃} {Y₀ : C₂ ⥤ C₃}
    {D₄ : Type*} [Category D₄] {C₄ : Type*} [Category C₄] {L₄ : C₄ ⥤ D₄} {V : D₃ ⥤ D₄}
    {V₀ : C₃ ⥤ C₄} (ΦX : L₁ ⋙ X ≅ X₀ ⋙ L₂) (ΦY : L₂ ⋙ Y ≅ Y₀ ⋙ L₃)
    (ΦV : L₃ ⋙ V ≅ V₀ ⋙ L₄) :
    IsInducedBy (Functor.compFactorization (Functor.compFactorization ΦX ΦY) ΦV)
      (Functor.compFactorization ΦX (Functor.compFactorization ΦY ΦV))
      (Functor.associator X Y V).hom (Functor.associator X₀ Y₀ V₀).hom := fun c => by
  simp [Functor.compFactorization_hom_app]

theorem associator_inv {X : D₁ ⥤ D₂} {X₀ : C₁ ⥤ C₂} {Y : D₂ ⥤ D₃} {Y₀ : C₂ ⥤ C₃}
    {D₄ : Type*} [Category D₄] {C₄ : Type*} [Category C₄] {L₄ : C₄ ⥤ D₄} {V : D₃ ⥤ D₄}
    {V₀ : C₃ ⥤ C₄} (ΦX : L₁ ⋙ X ≅ X₀ ⋙ L₂) (ΦY : L₂ ⋙ Y ≅ Y₀ ⋙ L₃)
    (ΦV : L₃ ⋙ V ≅ V₀ ⋙ L₄) :
    IsInducedBy (Functor.compFactorization ΦX (Functor.compFactorization ΦY ΦV))
      (Functor.compFactorization (Functor.compFactorization ΦX ΦY) ΦV)
      (Functor.associator X Y V).inv (Functor.associator X₀ Y₀ V₀).inv :=
  inv (γ := Functor.associator X Y V) (γ₀ := Functor.associator X₀ Y₀ V₀)
    (associator ΦX ΦY ΦV)

end NatTrans.IsInducedBy

section Lift

variable {X Y : D₁ ⥤ D₂} {X₀ Y₀ : C₁ ⥤ C₂} (W : MorphismProperty C₁) [L₁.IsLocalization W]
  (ΦX : L₁ ⋙ X ≅ X₀ ⋙ L₂) (ΦY : L₁ ⋙ Y ≅ Y₀ ⋙ L₂)

/-- The natural transformation induced by `γ₀ : X₀ ⟶ Y₀` along factorizations through a
localization functor. -/
noncomputable def NatTrans.liftAlong (γ₀ : X₀ ⟶ Y₀) : X ⟶ Y :=
  letI : Localization.Lifting L₁ W (X₀ ⋙ L₂) X := ⟨ΦX⟩
  letI : Localization.Lifting L₁ W (Y₀ ⋙ L₂) Y := ⟨ΦY⟩
  Localization.liftNatTrans L₁ W (X₀ ⋙ L₂) (Y₀ ⋙ L₂) X Y (Functor.whiskerRight γ₀ L₂)

theorem NatTrans.isInducedBy_liftAlong (γ₀ : X₀ ⟶ Y₀) :
    NatTrans.IsInducedBy ΦX ΦY (NatTrans.liftAlong W ΦX ΦY γ₀) γ₀ := fun c => by
  let : Localization.Lifting L₁ W (X₀ ⋙ L₂) X := ⟨ΦX⟩
  let : Localization.Lifting L₁ W (Y₀ ⋙ L₂) Y := ⟨ΦY⟩
  rw [NatTrans.liftAlong, Localization.liftNatTrans_app]
  simp [Localization.Lifting.iso]

/-- The natural isomorphism induced by `γ₀ : X₀ ≅ Y₀` along factorizations through a
localization functor. -/
@[simps]
noncomputable def NatIso.liftAlong (γ₀ : X₀ ≅ Y₀) : X ≅ Y where
  hom := NatTrans.liftAlong W ΦX ΦY γ₀.hom
  inv := NatTrans.liftAlong W ΦY ΦX γ₀.inv
  hom_inv_id := by
    have h := (NatTrans.isInducedBy_liftAlong W ΦX ΦY γ₀.hom).comp
      (NatTrans.isInducedBy_liftAlong W ΦY ΦX γ₀.inv)
    rw [Iso.hom_inv_id] at h
    exact h.ext W NatTrans.IsInducedBy.id
  inv_hom_id := by
    have h := (NatTrans.isInducedBy_liftAlong W ΦY ΦX γ₀.inv).comp
      (NatTrans.isInducedBy_liftAlong W ΦX ΦY γ₀.hom)
    rw [Iso.inv_hom_id] at h
    exact h.ext W NatTrans.IsInducedBy.id

end Lift

end CategoryTheory
