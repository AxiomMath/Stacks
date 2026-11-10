module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedLimits
public import StacksFrontier.Algebra.Homology.DerivedCategory.HigherDerivedFunctors
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.CategoryTheory.Localization.DerivingAdjoints
public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfPresheavesOfModules.TermFunctorExactness
public import StacksFrontier.Homology.KInjective.ChangeOfRings
public import StacksFrontier.RingTheory.Dualizing.TrivialDuality

/-!
# Derived Hom along a ring homomorphism, for an arbitrary chosen derived category

For a homomorphism of rings `f : A →+* B`, coextension of scalars `Hom_A(B, -) : Mod(A) ⥤ Mod(B)`
is right adjoint to restriction of scalars, and its total right derived functor
`RHom_A(B, -) : D(A) ⥤ D(B)` is right adjoint to the functor induced on derived categories by
restriction of scalars. This is Stacks Tag 0A70.

`StacksFrontier/RingTheory/Dualizing/TrivialDuality.lean` already proves exactly this, but that file
installs `HasDerivedCategory.standard` as a file-level local instance, so its
`Dualizing.derivedHom` and `Dualizing.restrictScalarsDerived_adj_derivedHom` are *silently
specialised* to the standard model of the derived category: the declarations carry no
`[HasDerivedCategory]` binder, and a statement that quantifies over an arbitrary chosen model
therefore cannot use them.

This file removes that specialisation. Everything the proof uses is model-generic already:
`Functor.mapDerivedCategory` and `Functor.mapDerivedCategoryFactorsh` take independent
`HasDerivedCategory.{w₁}`/`HasDerivedCategory.{w₂}` instances,
`Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective` mentions no
derived category at all, and
`CategoryTheory.Adjunction.exists_derived_of_isRightDerivedValueAt_of_isLeftDerivedValueAt` is
stated for arbitrary localizations. Only the *statement* of the specialised version needed
standardness, to name `DerivedCategory`. So the whole argument goes through verbatim with
`[HasDerivedCategory.{w} (ModuleCat A)]` and `[HasDerivedCategory.{w'} (ModuleCat B)]` as
hypotheses, and the result below is strictly more general than the specialised one, which it
recovers by supplying `HasDerivedCategory.standard`.

## Main definitions

* `Dualizing.AnyModel.derivedHom` — the derived coextension-of-scalars functor `RHom_A(B, -)`,
  between arbitrary chosen models of `D(A)` and `D(B)`.

## Main results

* `Dualizing.AnyModel.coextendScalars_hasPointwiseRightDerivedFunctor` — coextension of scalars
  admits a pointwise total right derived functor into an arbitrary chosen `D(B)`.
* `Dualizing.AnyModel.restrictScalarsDerived_adj_derivedHom` — **Stacks 0A70** for arbitrary
  chosen models: restriction of scalars on derived categories is left adjoint to derived Hom.

## Implementation notes

The category-theoretic ingredients of the proof — `Dualizing.homotopyAdjunction`,
`Dualizing.coneOfInvertedMorphisms`, `Dualizing.coneOfInvertedMorphisms_isLeftDerivedValueAt`,
`Dualizing.coconeOfTerminalUnder_isRightDerivedValueAt` and
`Dualizing.isTerminalUnderKInjective` — quantify over the chosen derived category wherever they
mention one at all, so they are model-free already and are imported from `TrivialDuality.lean`
rather than restated here.

## References

* [Stacks Project, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor

universe u v u' w w'

namespace Dualizing.AnyModel

/-- Coextension of scalars along a ring homomorphism is an additive functor. -/
local instance {A : Type u} {B : Type u'} [Ring A] [Ring B] (f : A →+* B) :
    (ModuleCat.coextendScalars.{u, u', w} f).Additive where
  map_add := by intros; ext; rfl

/-- Restriction of scalars along a ring homomorphism preserves finite limits. -/
local instance {A : Type u} {B : Type u'} [Ring A] [Ring B] (f : A →+* B) :
    Limits.PreservesFiniteLimits (ModuleCat.restrictScalars.{max v u u'} f) :=
  ⟨fun _ _ _ ↦ ⟨inferInstance⟩⟩

/-- Restriction of scalars along a ring homomorphism preserves finite colimits. -/
local instance {A : Type u} {B : Type u'} [Ring A] [Ring B] (f : A →+* B) :
    Limits.PreservesFiniteColimits (ModuleCat.restrictScalars.{max v u u'} f) :=
  ⟨fun _ _ _ ↦ ⟨inferInstance⟩⟩

/-- Every complex of `A`-modules admits a quasi-isomorphism into a K-injective complex. -/
private theorem exists_isKInjective_quasiIso {A : Type u} [Ring A]
    (K : CochainComplex (ModuleCat.{max v u} A) ℤ) :
    ∃ (I : CochainComplex (ModuleCat.{max v u} A) ℤ) (f : K ⟶ I), I.IsKInjective ∧ QuasiIso f :=
  have : EnoughInjectives (ModuleCat.{max v u} A) := ModuleCat.enoughInjectives.{v, u} A
  let ⟨I, q, hq, hI⟩ := CochainComplex.exists_quasiIso_isKInjective K
  ⟨I, q, hI, hq⟩

/-- Coextension of scalars admits a total right derived functor into an arbitrary chosen model of
`D(B)`, computed on K-injective resolutions. Model-generic form of
`Dualizing.coextendScalars_hasPointwiseRightDerivedFunctor`; only the target `D(B)` is involved,
so no model of `D(A)` needs to be chosen. -/
theorem coextendScalars_hasPointwiseRightDerivedFunctor {A : Type u} {B : Type u'}
    [Ring A] [Ring B] [HasDerivedCategory.{w'} (ModuleCat.{max v u u'} B)] (f : A →+* B) :
    ((ModuleCat.coextendScalars.{u, u', max v u u'} f).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh).HasPointwiseRightDerivedFunctor
        (HomotopyCategory.quasiIso (ModuleCat.{max v u u'} A) (.up ℤ)) := by
  exact (hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
        max v u u', w', max v u u', max (u + 1) (v + 1) (u' + 1),
        max (u + 1) (v + 1) (u' + 1), max (u + 1) (v + 1) (u' + 1)}
      ((ModuleCat.coextendScalars.{u, u', max v u u'} f).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      exists_isKInjective_quasiIso.{u, max v u'}).1

variable {A : Type u} {B : Type u'} [Ring A] [Ring B]
  [HasDerivedCategory.{w} (ModuleCat.{max v u u'} A)]
  [HasDerivedCategory.{w'} (ModuleCat.{max v u u'} B)]

/-- The derived coextension-of-scalars functor `RHom_A(B, -) : D(A) ⥤ D(B)` associated to a ring
homomorphism `f : A →+* B`, between arbitrary chosen models of the two derived categories. -/
noncomputable def derivedHom (f : A →+* B) :
    DerivedCategory (ModuleCat.{max v u u'} A) ⥤
      DerivedCategory (ModuleCat.{max v u u'} B) := by
  have : ((ModuleCat.coextendScalars.{u, u', max v u u'} f).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasPointwiseRightDerivedFunctor
        (HomotopyCategory.quasiIso (ModuleCat.{max v u u'} A) (ComplexShape.up ℤ)) :=
    coextendScalars_hasPointwiseRightDerivedFunctor f
  exact ((ModuleCat.coextendScalars.{u, u', max v u u'} f).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (ModuleCat.{max v u u'} A) (ComplexShape.up ℤ))

/-- **Stacks 0A70.** Derived coextension of scalars `RHom_A(B, -)` is right adjoint to restriction
of scalars from `D(B)` to `D(A)`, for arbitrary chosen models of the two derived categories.

This is the model-generic form of `Dualizing.restrictScalarsDerived_adj_derivedHom`, which is
silently specialised to `HasDerivedCategory.standard`; it is recovered from this by supplying that
instance. -/
@[stacks 0A70]
theorem restrictScalarsDerived_adj_derivedHom (f : A →+* B) :
    Nonempty ((ModuleCat.restrictScalars.{max v u u'} f).mapDerivedCategory ⊣
      derivedHom.{u, v, u', w, w'} f) := by
  let AMod := ModuleCat.{max v u u'} A
  let BMod := ModuleCat.{max v u u'} B
  let F₀ := ModuleCat.coextendScalars.{u, u', max v u u'} f
  let G₀ := ModuleCat.restrictScalars.{max v u u'} f
  let W := HomotopyCategory.quasiIso AMod (ComplexShape.up ℤ)
  let W' := HomotopyCategory.quasiIso BMod (ComplexShape.up ℤ)
  let Q := DerivedCategory.Qh (C := AMod)
  let Q' := DerivedCategory.Qh (C := BMod)
  let F := F₀.mapHomotopyCategory (ComplexShape.up ℤ)
  let G := G₀.mapHomotopyCategory (ComplexShape.up ℤ)
  let LG := G₀.mapDerivedCategory
  let α := G₀.mapDerivedCategoryFactorsh.hom
  have : EnoughInjectives AMod := ModuleCat.enoughInjectives.{max v u', u} A
  let hPoint := hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
      max v u u', w', w, max (u + 1) (v + 1) (u' + 1), max (u + 1) (v + 1) (u' + 1),
      max (u + 1) (v + 1) (u' + 1)}
    (F ⋙ Q') exists_isKInjective_quasiIso.{u, max v u'}
  have : (F ⋙ Q').HasPointwiseRightDerivedFunctor W := hPoint.1
  let RF := (F ⋙ Q').totalRightDerived Q W
  let β := (F ⋙ Q').totalRightDerivedUnit Q W
  have : RF.IsRightDerivedFunctor β W := by
    dsimp [RF, β, F, Q', Q, W]
    infer_instance
  let adj := homotopyAdjunction
    (ModuleCat.restrictCoextendScalarsAdj.{max v u u'} f) (ComplexShape.up ℤ)
  have hInv : W'.IsInvertedBy (G ⋙ Q) := by
    dsimp [G, Q, W']
    exact Stacks.DerivedFunctor.HigherDerivedOfExact.mapHomotopyCategory_inverts_quasiIso G₀
  have hRF : ∀ K : HomotopyCategory AMod (ComplexShape.up ℤ),
      ∃ (c : Limits.Cocone (MorphismProperty.Under.forget W ⊤ K ⋙
        Under.forget K ⋙ F ⋙ Q')),
        ∃ (_ : (F ⋙ Q').IsRightDerivedValueAt W K c),
          ∃ (e : c.pt ≅ RF.obj (Q.obj K)),
            ∀ s : W.Under ⊤ K,
              c.ι.app s ≫ e.hom ≫ RF.map (Q.map s.hom) = β.app s.right := by
    intro K
    obtain ⟨Kc, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    obtain ⟨I, q, hq, hI⟩ := CochainComplex.exists_quasiIso_isKInjective Kc
    let qh := (HomotopyCategory.quotient AMod (ComplexShape.up ℤ)).map q
    have hqh : W qh := (HomotopyCategory.quotient_map_mem_quasiIso_iff q).2 hq
    let t₀ : W.Under ⊤ _ := MorphismProperty.Under.mk ⊤ qh hqh
    let ht := isTerminalUnderKInjective I qh hqh
    let c := Limits.coconeOfDiagramTerminal ht
      (MorphismProperty.Under.forget W ⊤ _ ⋙ Under.forget _ ⋙ F ⋙ Q')
    have : IsIso (β.app t₀.right) := hPoint.2 Q RF β I hI
    have : IsIso (Q.map t₀.hom) := Localization.inverts Q W t₀.hom t₀.prop
    let eRF := asIso (RF.map (Q.map t₀.hom))
    let eβ := asIso (β.app t₀.right)
    let e : c.pt ≅ RF.obj (Q.obj _) := eβ ≪≫ eRF.symm
    have he : e.hom = β.app t₀.right ≫ eRF.inv := rfl
    refine ⟨c, coconeOfTerminalUnder_isRightDerivedValueAt (F ⋙ Q') W _ t₀ ht, e, fun s ↦ ?_⟩
    have hnat : (F ⋙ Q').map (ht.from s).right ≫ β.app t₀.right =
        β.app s.right ≫ RF.map (Q.map (ht.from s).right) := by
      simpa only [Functor.comp_map] using β.naturality (ht.from s).right
    have : IsIso (Q.map s.hom) := Localization.inverts Q W s.hom s.prop
    have hcancel : RF.map (Q.map (ht.from s).right) ≫ eRF.inv ≫ RF.map (Q.map s.hom) = 𝟙 _ := by
      rw [← cancel_epi (RF.map (Q.map s.hom)), ← Functor.map_comp_assoc, ← Functor.map_comp,
        MorphismProperty.Under.w (ht.from s)]
      exact (IsIso.hom_inv_id_assoc (RF.map (Q.map t₀.hom)) _).trans (Category.comp_id _).symm
    dsimp [c, Limits.coconeOfDiagramTerminal]
    rw [he]
    calc
      _ = (((F ⋙ Q').map (ht.from s).right ≫ β.app t₀.right) ≫ eRF.inv) ≫
          RF.map (Q.map s.hom) :=
        (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (Category.assoc _ _ _).symm)
      _ = β.app s.right := by
        rw [hnat]
        simp only [Category.assoc, hcancel]
        exact Category.comp_id _
  have hLG : ∀ M : HomotopyCategory BMod (ComplexShape.up ℤ),
      ∃ (d : Limits.Cone (MorphismProperty.Over.forget W' ⊤ M ⋙
        Over.forget M ⋙ G ⋙ Q)),
        ∃ (_ : (G ⋙ Q).IsLeftDerivedValueAt W' M d),
          ∃ (e : LG.obj (Q'.obj M) ≅ d.pt),
            ∀ t : W'.Over ⊤ M,
              LG.map (Q'.map t.hom) ≫ e.hom ≫ d.π.app t = α.app t.left := by
    intro M
    refine ⟨_, coneOfInvertedMorphisms_isLeftDerivedValueAt (G ⋙ Q) W' hInv M,
      G₀.mapDerivedCategoryFactorsh.app M, fun t ↦ ?_⟩
    have : IsIso ((G ⋙ Q).map t.hom) := hInv t.hom t.prop
    have hn : LG.map (Q'.map t.hom) ≫ α.app M = α.app t.left ≫ (G ⋙ Q).map t.hom := by
      simpa [LG, Q', α, G, Q, Functor.comp_map] using
        G₀.mapDerivedCategoryFactorsh.hom.naturality t.hom
    change LG.map (Q'.map t.hom) ≫ α.app M ≫ inv ((G ⋙ Q).map t.hom) = α.app t.left
    simp [reassoc_of% hn]
  change Nonempty (LG ⊣ RF)
  obtain ⟨adjDerived, _, _⟩ :=
    CategoryTheory.Adjunction.exists_derived_of_isRightDerivedValueAt_of_isLeftDerivedValueAt
      adj W W' Q Q' RF β LG α hRF hLG
  exact ⟨adjDerived⟩

section Standard

attribute [local instance] HasDerivedCategory.standard

/-- At the standard model of the derived category, the model-generic `derivedHom` *is* the
specialised `Dualizing.derivedHom` of `TrivialDuality.lean`, definitionally. So every result proved
about the latter transfers, and conversely this file's adjunction specialises to
`Dualizing.restrictScalarsDerived_adj_derivedHom`. -/
theorem derivedHom_eq_standard {A : Type u} {B : Type u'} [Ring A] [Ring B] (f : A →+* B) :
    derivedHom.{u, v, u', max (u + 1) (v + 1) (u' + 1), max (u + 1) (v + 1) (u' + 1)} f =
      Dualizing.derivedHom.{u, v, u'} f :=
  rfl

end Standard

end Dualizing.AnyModel

end
