module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.NoncommBaseChange

/-!
# Base change of an objectwise extension of scalars along a triangle of presheaves of rings

Let `γ : A ⟶ B` and `ρ : B ⟶ B'` be morphisms of presheaves of not necessarily commutative
rings and let `M` be a presheaf of `A`-modules. This file defines the morphism of presheaves of
`A`-modules

`B ⊗_{γ, A} M ⟶ B' ⊗_{γ ≫ ρ, A} M`

which on sections sends `b ⊗ m` to `ρ(b) ⊗ m`, as the adjoint transpose of the unit of extension
of scalars along `γ ≫ ρ`. It is the unique morphism out of `B ⊗_{γ,A} M` lying in the image of
restriction of scalars along `γ` whose composite with the unit of extension of scalars along `γ`
is the unit of extension of scalars along `γ ≫ ρ`.

## Main definitions

* `Stacks.NoncommChangeOfRings.Presheaf.restrictExtendObj`: the presheaf of `A`-modules
  `B ⊗_{γ, A} M`.
* `Stacks.NoncommChangeOfRings.Presheaf.baseChangeTranspose`: the adjoint transpose of the unit
  of extension of scalars along `γ ≫ ρ`, a morphism of presheaves of `B`-modules.
* `Stacks.NoncommChangeOfRings.Presheaf.baseChange`: the base change morphism itself, and
  `Stacks.NoncommChangeOfRings.Presheaf.baseChangeTo` the same morphism with its target read
  along any `δ` equal to `γ ≫ ρ`.

## Main results

* `Stacks.NoncommChangeOfRings.Presheaf.unit_comp_baseChange` and
  `Stacks.NoncommChangeOfRings.Presheaf.unit_comp_baseChangeTo`: the unit of extension of
  scalars along `γ` followed by the base change is the unit of extension of scalars along
  `γ ≫ ρ`.
* `Stacks.NoncommChangeOfRings.Presheaf.baseChangeTranspose_eq_of_unit_comp` and
  `Stacks.NoncommChangeOfRings.Presheaf.baseChange_eq_of_unit_comp`: this property characterises
  the base change among morphisms in the image of restriction of scalars along `γ`.
* `Stacks.NoncommChangeOfRings.Presheaf.comp_eq_baseChangeTranspose_comp`: a morphism out of
  `B ⊗_{γ,A} M` whose composite with the unit of extension of scalars along `γ` factors through
  the unit of extension of scalars along `γ ≫ ρ` factors through the base change.
* `Stacks.NoncommChangeOfRings.Presheaf.baseChangeTo_eq_of_unit_comp`: the characterisation for
  `baseChangeTo`.
* `Stacks.NoncommChangeOfRings.Presheaf.baseChangeTo_comp_baseChangeTo`: transitivity of base
  change — the base change from `γ` to `δ` followed by the one from `δ` to `δ'` is the one from
  `γ` to `δ'`.
* `Stacks.NoncommChangeOfRings.Presheaf.baseChangeTo_congr`: two equal middle morphisms give the
  same base change.
-/
@[expose] public section

open CategoryTheory

universe v₁ u₁ u

namespace Stacks.NoncommChangeOfRings.Presheaf

variable {C : Type u₁} [Category.{v₁} C] {A B B' : Cᵒᵖ ⥤ RingCat.{u}}

/-- **The presheaf of `A`-modules `B ⊗_{γ, A} M`**: the objectwise extension of scalars along
`γ`, read back as a presheaf of `A`-modules. -/
noncomputable abbrev restrictExtendObj (γ : A ⟶ B) (M : PresheafOfModules.{u} A) :
    PresheafOfModules.{u} A :=
  (PresheafOfModules.restrictScalars γ).obj ((extendScalars.{u} γ).obj M)

variable (γ : A ⟶ B) (ρ : B ⟶ B') (M : PresheafOfModules.{u} A)

/-- **The adjoint transpose of the unit of extension of scalars along `γ ≫ ρ`**, a morphism of
presheaves of `B`-modules `B ⊗_{γ,A} M ⟶ (B' ⊗_{γ ≫ ρ,A} M)_B`. -/
noncomputable def baseChangeTranspose :
    (extendScalars.{u} γ).obj M ⟶
      (PresheafOfModules.restrictScalars ρ).obj ((extendScalars.{u} (γ ≫ ρ)).obj M) :=
  ((extendScalarsAdjunction.{u} γ).homEquiv M _).symm
    ((extendScalarsAdjunction.{u} (γ ≫ ρ)).unit.app M)

/-- **Base change of an objectwise extension of scalars along a triangle**: the morphism of
presheaves of `A`-modules `B ⊗_{γ,A} M ⟶ B' ⊗_{γ ≫ ρ,A} M` which on sections sends `b ⊗ m` to
`ρ(b) ⊗ m`. -/
noncomputable def baseChange :
    restrictExtendObj γ M ⟶ restrictExtendObj (γ ≫ ρ) M :=
  (PresheafOfModules.restrictScalars γ).map (baseChangeTranspose γ ρ M)

/-- **The unit of extension of scalars along `γ` followed by the base change is the unit of
extension of scalars along `γ ≫ ρ`.** -/
lemma unit_comp_baseChange :
    (extendScalarsAdjunction.{u} γ).unit.app M ≫ baseChange γ ρ M =
      (extendScalarsAdjunction.{u} (γ ≫ ρ)).unit.app M :=
  ((extendScalarsAdjunction.{u} γ).homEquiv_unit M _ (baseChangeTranspose γ ρ M)).symm.trans
    (Equiv.apply_symm_apply _ _)

/-- **The base change is the only morphism of `B`-modules whose image under restriction of
scalars along `γ` takes the unit to the unit.** -/
lemma baseChangeTranspose_eq_of_unit_comp
    (t : (extendScalars.{u} γ).obj M ⟶
      (PresheafOfModules.restrictScalars ρ).obj ((extendScalars.{u} (γ ≫ ρ)).obj M))
    (ht : (extendScalarsAdjunction.{u} γ).unit.app M ≫
        (PresheafOfModules.restrictScalars γ).map t =
      (extendScalarsAdjunction.{u} (γ ≫ ρ)).unit.app M) :
    t = baseChangeTranspose γ ρ M :=
  ((extendScalarsAdjunction.{u} γ).homEquiv M _).eq_symm_apply.mpr
    (((extendScalarsAdjunction.{u} γ).homEquiv_unit M _ t).trans ht)

/-- **The base change is the only morphism in the image of restriction of scalars along `γ`
taking the unit to the unit.** -/
lemma baseChange_eq_of_unit_comp
    (t : (extendScalars.{u} γ).obj M ⟶
      (PresheafOfModules.restrictScalars ρ).obj ((extendScalars.{u} (γ ≫ ρ)).obj M))
    (ht : (extendScalarsAdjunction.{u} γ).unit.app M ≫
        (PresheafOfModules.restrictScalars γ).map t =
      (extendScalarsAdjunction.{u} (γ ≫ ρ)).unit.app M) :
    (PresheafOfModules.restrictScalars γ).map t = baseChange γ ρ M :=
  congrArg (PresheafOfModules.restrictScalars γ).map
    (baseChangeTranspose_eq_of_unit_comp γ ρ M t ht)

/-- **A morphism out of `B ⊗_{γ,A} M` factors through the base change as soon as the unit of
extension of scalars along `γ` takes it to something factoring through the unit of extension of
scalars along `γ ≫ ρ`.** -/
lemma comp_eq_baseChangeTranspose_comp {Y : PresheafOfModules.{u} B}
    {Y' : PresheafOfModules.{u} B'} (θ : (extendScalars.{u} γ).obj M ⟶ Y)
    (g : Y ⟶ (PresheafOfModules.restrictScalars ρ).obj Y')
    (θ' : (extendScalars.{u} (γ ≫ ρ)).obj M ⟶ Y')
    (h : (extendScalarsAdjunction.{u} γ).unit.app M ≫
          (PresheafOfModules.restrictScalars γ).map (θ ≫ g) =
        (extendScalarsAdjunction.{u} (γ ≫ ρ)).unit.app M ≫
          (PresheafOfModules.restrictScalars (γ ≫ ρ)).map θ') :
    θ ≫ g = baseChangeTranspose γ ρ M ≫ (PresheafOfModules.restrictScalars ρ).map θ' := by
  refine ((extendScalarsAdjunction.{u} γ).homEquiv M _).injective ?_
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, h, Functor.map_comp, ← Category.assoc]
  exact congrArg (· ≫ (PresheafOfModules.restrictScalars (γ ≫ ρ)).map θ')
    (unit_comp_baseChange γ ρ M).symm

/-- The base change with its target read along a morphism `δ` which is merely *equal* to the
composite `γ ≫ ρ`. -/
noncomputable def baseChangeTo (δ : A ⟶ B') (hδ : γ ≫ ρ = δ) :
    restrictExtendObj γ M ⟶ restrictExtendObj δ M :=
  baseChange γ ρ M ≫ eqToHom (congrArg (fun g => restrictExtendObj g M) hδ)

/-- The base change read along `γ ≫ ρ` itself is the base change. -/
private theorem baseChangeTo_rfl : baseChangeTo γ ρ M (γ ≫ ρ) rfl = baseChange γ ρ M := by
  simp [baseChangeTo]

/-- `Stacks.NoncommChangeOfRings.Presheaf.unit_comp_baseChange` for
`Stacks.NoncommChangeOfRings.Presheaf.baseChangeTo`. -/
lemma unit_comp_baseChangeTo (δ : A ⟶ B') (hδ : γ ≫ ρ = δ) :
    (extendScalarsAdjunction.{u} γ).unit.app M ≫ baseChangeTo γ ρ M δ hδ =
      (extendScalarsAdjunction.{u} δ).unit.app M := by
  subst hδ
  rw [baseChangeTo_rfl, unit_comp_baseChange]

/-- **The base change along a triangle is the only morphism out of `B ⊗_{γ,A} M` in the image of
restriction of scalars along `γ` which takes the unit to the unit**, in the form
`Stacks.NoncommChangeOfRings.Presheaf.baseChangeTo` is stated in. -/
lemma baseChangeTo_eq_of_unit_comp (δ : A ⟶ B') (hδ : γ ≫ ρ = δ)
    (t : restrictExtendObj γ M ⟶ restrictExtendObj δ M)
    (t₀ : (extendScalars.{u} γ).obj M ⟶
      (PresheafOfModules.restrictScalars ρ).obj ((extendScalars.{u} δ).obj M))
    (ht₀ : t ≫ eqToHom (congrArg (fun f ↦ (PresheafOfModules.restrictScalars f).obj
          ((extendScalars.{u} δ).obj M)) hδ).symm =
      (PresheafOfModules.restrictScalars γ).map t₀)
    (hunit : (extendScalarsAdjunction.{u} γ).unit.app M ≫ t =
      (extendScalarsAdjunction.{u} δ).unit.app M) :
    t = baseChangeTo γ ρ M δ hδ := by
  subst hδ
  simp only [eqToHom_refl, Category.comp_id] at ht₀
  rw [baseChangeTo_rfl, ht₀]
  exact baseChange_eq_of_unit_comp γ ρ M t₀ (ht₀ ▸ hunit)

/-- **Base change along a triangle is transitive**: the base change from `γ` to `δ` followed by
the one from `δ` to `δ'` is the base change from `γ` to `δ'` along the composite middle
morphism. -/
lemma baseChangeTo_comp_baseChangeTo {B'' : Cᵒᵖ ⥤ RingCat.{u}} (ρ' : B' ⟶ B'')
    (δ : A ⟶ B') (hδ : γ ≫ ρ = δ) (δ' : A ⟶ B'') (hδ' : δ ≫ ρ' = δ')
    (ρ'' : B ⟶ B'') (hρ'' : ρ ≫ ρ' = ρ'') (hδ'' : γ ≫ ρ'' = δ') :
    baseChangeTo γ ρ M δ hδ ≫ baseChangeTo δ ρ' M δ' hδ' = baseChangeTo γ ρ'' M δ' hδ'' := by
  subst hρ''
  subst hδ
  subst hδ'
  refine baseChangeTo_eq_of_unit_comp γ (ρ ≫ ρ') M ((γ ≫ ρ) ≫ ρ') hδ'' _
    (baseChangeTranspose γ ρ M ≫ (PresheafOfModules.restrictScalars ρ).map
      (baseChangeTranspose (γ ≫ ρ) ρ' M)) ?_ ?_
  · rw [baseChangeTo_rfl, baseChangeTo_rfl]
    rfl
  · rw [← Category.assoc, unit_comp_baseChangeTo, unit_comp_baseChangeTo]

/-- **Two equal middle morphisms `ρ = ρ₁` give the same base change along a triangle.** -/
lemma baseChangeTo_congr (ρ₁ : B ⟶ B') (hρ : ρ = ρ₁) (δ : A ⟶ B') (hδ : γ ≫ ρ = δ)
    (hδ₁ : γ ≫ ρ₁ = δ) :
    baseChangeTo γ ρ M δ hδ = baseChangeTo γ ρ₁ M δ hδ₁ := by
  subst hρ
  rfl

end Stacks.NoncommChangeOfRings.Presheaf

end
