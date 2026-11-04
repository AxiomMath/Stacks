module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.ProperCurveCupDualityCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.RelativeCurveDualityReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.TorsionCoefficients
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedPlusRestriction
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution

/-!
# Relative duality on `D⁺` and on the unbounded derived category

Let `f : X ⟶ S` be a morphism of schemes and `Λ = ℤ/ℓ`. The relative duality statement
`Stacks.EtaleCohomology.ProperCurveRelativeDualityInput` is phrased with the derived direct image
`Rf_* : D⁺(X_étale, Λ) ⥤ D⁺(S_étale, Λ)` of bounded below complexes, while the duality map
`Stacks.EtaleCohomology.curveDualityMap` lives on the unbounded derived categories. This file
moves the bijectivity of the trace maps between the two.

The two derived direct images agree on `D⁺`
(`Stacks.EtaleCohomology.etaleModuleDerivedDirectImagePlusIso`, an instance of
`CategoryTheory.Functor.boundedDerivedIso`), but the comparison is not known to commute with the
shifts, so the trace maps cannot be compared directly: for each degree `m` the
comparison changes the trace by an automorphism of `Rf_* E`
(`Stacks.RelativeDuality.exists_traceMap_eq_of_iso`), and a top-degree trace composed with an
automorphism is again a top-degree trace. Hence relative duality for **every** top-degree trace on
the unbounded side gives it for every top-degree trace on `D⁺`
(`Stacks.EtaleCohomology.isBijectiveAt_plus_of_forall_isBijectiveAt`), and conversely
(`Stacks.EtaleCohomology.isBijectiveAt_of_forall_isBijectiveAt_plus`).

The derived categories are those of the standard model `HasDerivedCategory.standard`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

open Stacks.EtaleCohomology.ExtensionTorsor Stacks.RelativeDuality

section Iso

variable (Λ : Type) [Ring Λ] {S X : Scheme.{u}} (f : X ⟶ S)

/-- **The derived direct image on `D⁺` is the restriction of the unbounded one**:
`Rf_*⁺ ⋙ ι ≅ ι ⋙ Rf_*` as functors `D⁺(X_étale, Λ) ⥤ D(S_étale, Λ)`. -/
def etaleModuleDerivedDirectImagePlusIso :
    etaleModuleDerivedDirectImage.{u, 0} Λ f ⋙ DerivedCategory.Plus.ι ≅
      DerivedCategory.Plus.ι ⋙ etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ f :=
  Functor.boundedDerivedIso (etaleModuleDirectImage.{u, 0} Λ f)
    (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ f)
    (etaleModuleDerivedDirectImageUnboundedUnitH.{u, 0} Λ f)
    (fun K => Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian _ K)

end Iso

section Generic

variable {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]

/-- A fully faithful functor commuting with the shifts is bijective on shifted morphisms. -/
lemma bijective_shiftedHom_map_of_fullyFaithful (F : C ⥤ D) [F.Full] [F.Faithful]
    [F.CommShift ℤ] (A B : C) (m : ℤ) :
    Function.Bijective (fun y : ShiftedHom A B m => y.map F) := by
  have e : (fun y : ShiftedHom A B m => y.map F) =
      (fun g => g ≫ (F.commShiftIso m).hom.app B) ∘ (fun y : A ⟶ B⟦m⟧ => F.map y) := rfl
  rw [e]
  exact Function.Bijective.comp
    ⟨fun _ _ h => (cancel_mono _).1 h, fun z => ⟨z ≫ (F.commShiftIso m).inv.app B, by simp⟩⟩
    ((Functor.FullyFaithful.ofFullyFaithful F).map_bijective A (B⟦m⟧))

/-- Along a fully faithful `F` commuting with the shifts, the trace map of `F ⋙ R` at `A` is
bijective iff the trace map of `R` at `F A` is. -/
private lemma bijective_traceMap_comp_iff_of_fullyFaithful
    {E : Type*} [Category* E] [Preadditive C] [Preadditive D] [Preadditive E] [HasShift E ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [∀ n : ℤ, (shiftFunctor E n).Additive] (F : C ⥤ D) [F.Full] [F.Faithful] [F.CommShift ℤ]
    [F.Additive] (R : D ⥤ E) [R.CommShift ℤ] [R.Additive] {B : C} {L : E} {c₀ : ℤ}
    (t : ShiftedHom ((F ⋙ R).obj B) L c₀) (A : C) (m c : ℤ) (h : c₀ + m = c) :
    Function.Bijective (traceMap (F ⋙ R) t A m c h) ↔
      Function.Bijective (traceMap R t (F.obj A) m c h) := by
  have e : ⇑(traceMap (F ⋙ R) t A m c h) =
      traceMap R t (F.obj A) m c h ∘ (fun y : ShiftedHom A B m => y.map F) := by
    funext y
    simp only [Function.comp_apply, traceMap_apply, ShiftedHom.comp_map]
  rw [e]
  exact Function.Bijective.of_comp_iff _ (bijective_shiftedHom_map_of_fullyFaithful F A B m)

end Generic

variable (ℓ : ℕ) {S X : Scheme.{u}} (f : X ⟶ S)

/-- `f⁻¹Λ_S[0]` in `D⁺(X_étale, Λ)`, the object at which
`Stacks.EtaleCohomology.ProperCurveRelativeDualityInput` asks for duality. -/
abbrev curveDualityUnitPlus : DerivedCategory.Plus (EtaleModules.{u, 0} (ZMod ℓ) X) :=
  (DerivedCategory.Plus.singleFunctor _ 0).obj
    ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) f).obj (unitSheaf (X := S) ℓ))

/-- `f⁻¹Λ_S[0]` in `D⁺` is `E = f⁻¹(Λ_S[0])` in `D`. -/
def curveDualityUnitPlusIso :
    DerivedCategory.Plus.ι.obj (curveDualityUnitPlus ℓ f) ≅ curveDualityUnit ℓ f :=
  haveI := etaleModuleInverseImage_preservesFiniteLimits.{u, 0} (ZMod ℓ) f
  haveI := etaleModuleInverseImage_preservesFiniteColimits.{u, 0} (ZMod ℓ) f
  (((etaleModuleInverseImage.{u, 0} (ZMod ℓ) f).mapDerivedCategorySingleFunctor 0).app
    (unitSheaf (X := S) ℓ)).symm

/-- **Relative duality for every top-degree trace on the unbounded side gives it on `D⁺`.** -/
theorem isBijectiveAt_plus_of_forall_isBijectiveAt
    (H : ∀ τ : ShiftedHom (curveDualityComplex ℓ f)
        ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)) (-2),
      IsIso ((DerivedCategory.homologyFunctor _ 2).map τ) →
        letI := etaleModuleDerivedDirectImageUnboundedCommShift.{u, 0} (ZMod ℓ) f
        haveI := etaleModuleDerivedDirectImageUnbounded_isTriangulated.{u, 0} (ZMod ℓ) f
        IsBijectiveAt (etaleModuleDerivedDirectImageUnbounded.{u, 0} (ZMod ℓ) f) τ
          (curveDualityUnit ℓ f))
    (t : ShiftedHom ((etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) f ⋙
        DerivedCategory.Plus.ι).obj (curveDualityUnitPlus ℓ f))
      ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)) (-2))
    (ht : IsIso ((DerivedCategory.homologyFunctor _ 2).map t)) :
    IsBijectiveAt (etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) f ⋙ DerivedCategory.Plus.ι) t
      (curveDualityUnitPlus ℓ f) := by
  let := etaleModuleDerivedDirectImageUnboundedCommShift.{u, 0} (ZMod ℓ) f
  have := etaleModuleDerivedDirectImageUnbounded_isTriangulated.{u, 0} (ZMod ℓ) f
  intro m c h
  let R := etaleModuleDerivedDirectImageUnbounded.{u, 0} (ZMod ℓ) f
  let β := etaleModuleDerivedDirectImagePlusIso.{u} (ZMod ℓ) f
  let A := curveDualityUnitPlus ℓ f
  obtain ⟨s, hs⟩ := exists_traceMap_eq_of_iso (Φ := DerivedCategory.Plus.ι ⋙ R)
    (etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) f ⋙ DerivedCategory.Plus.ι) (A := A) (m := m)
    (β.app A).symm (β.app A).symm (β.app (A⟦m⟧)).symm
    (fun y => β.inv.naturality y) t
  -- the trace on the unbounded side
  let τ₁ : ShiftedHom ((DerivedCategory.Plus.ι ⋙ R).obj A)
      ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)) (-2) :=
    s.hom ≫ (β.app A).inv ≫ t
  let i := curveDualityUnitPlusIso ℓ f
  let τ₂ : ShiftedHom (curveDualityComplex ℓ f)
      ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)) (-2) :=
    (ShiftedHom.mk₀ (0 : ℤ) rfl (R.map i.inv)).comp τ₁ (add_zero _)
  have hτ₂ : IsIso ((DerivedCategory.homologyFunctor _ 2).map τ₂) := by
    simp only [τ₂, τ₁, ShiftedHom.mk₀_comp, CategoryTheory.Functor.map_comp]
    infer_instance
  have hτ : τ₁ = (ShiftedHom.mk₀ (0 : ℤ) rfl (R.map i.hom)).comp τ₂ (add_zero _) := by
    rw [← ShiftedHom.comp_assoc _ _ _ (add_zero _) (add_zero _) (by simp), ShiftedHom.mk₀_comp_mk₀,
      ← R.map_comp, i.hom_inv_id, R.map_id, ShiftedHom.mk₀_id_comp]
  -- bijectivity for `R` at `ι A`, with `B = ι A`
  have h₁ : Function.Bijective (traceMap R τ₁ (DerivedCategory.Plus.ι.obj A) m c h) := by
    rw [hτ, bijective_traceMap_mk₀_map_comp_iff i τ₂ _ h]
    exact bijective_traceMap_of_iso i.symm h (H τ₂ hτ₂ m c h)
  -- bijectivity for `ι ⋙ R` at `A`
  have h₂ : Function.Bijective (traceMap (DerivedCategory.Plus.ι ⋙ R) τ₁ A m c h) :=
    (bijective_traceMap_comp_iff_of_fullyFaithful DerivedCategory.Plus.ι R τ₁ A m c h).2 h₁
  have e : ⇑(traceMap (etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) f ⋙
      DerivedCategory.Plus.ι) t A m c h) =
      (fun z => (ShiftedHom.mk₀ (0 : ℤ) rfl (β.app A).hom).comp z (add_zero c)) ∘
        traceMap (DerivedCategory.Plus.ι ⋙ R) τ₁ A m c h :=
    funext (hs c h)
  rw [e]
  exact (bijective_mk₀_comp_of_iso (Y := (DerivedCategory.singleFunctor _ 0).obj
    (unitSheaf (X := S) ℓ)) (β.app A) c).comp h₂

/-- **Relative duality for every top-degree trace on `D⁺` gives it on the unbounded side.** -/
theorem isBijectiveAt_of_forall_isBijectiveAt_plus
    (H : ∀ τ : ShiftedHom ((etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) f ⋙
        DerivedCategory.Plus.ι).obj (curveDualityUnitPlus ℓ f))
        ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)) (-2),
      IsIso ((DerivedCategory.homologyFunctor _ 2).map τ) →
        IsBijectiveAt (etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) f ⋙ DerivedCategory.Plus.ι)
          τ (curveDualityUnitPlus ℓ f))
    (t : ShiftedHom (curveDualityComplex ℓ f)
      ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)) (-2))
    (ht : IsIso ((DerivedCategory.homologyFunctor _ 2).map t)) :
    letI := etaleModuleDerivedDirectImageUnboundedCommShift.{u, 0} (ZMod ℓ) f
    haveI := etaleModuleDerivedDirectImageUnbounded_isTriangulated.{u, 0} (ZMod ℓ) f
    IsBijectiveAt (etaleModuleDerivedDirectImageUnbounded.{u, 0} (ZMod ℓ) f) t
      (curveDualityUnit ℓ f) := by
  let := etaleModuleDerivedDirectImageUnboundedCommShift.{u, 0} (ZMod ℓ) f
  have := etaleModuleDerivedDirectImageUnbounded_isTriangulated.{u, 0} (ZMod ℓ) f
  intro m c h
  let R := etaleModuleDerivedDirectImageUnbounded.{u, 0} (ZMod ℓ) f
  let β := etaleModuleDerivedDirectImagePlusIso.{u} (ZMod ℓ) f
  let A := curveDualityUnitPlus ℓ f
  let i := curveDualityUnitPlusIso ℓ f
  -- the trace read at `ι A`
  let τ₁ : ShiftedHom ((DerivedCategory.Plus.ι ⋙ R).obj A)
      ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)) (-2) :=
    (ShiftedHom.mk₀ (0 : ℤ) rfl (R.map i.hom)).comp t (add_zero _)
  obtain ⟨s, hs⟩ := exists_traceMap_eq_of_iso
    (Φ := etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) f ⋙ DerivedCategory.Plus.ι)
    (DerivedCategory.Plus.ι ⋙ R) (A := A) (m := m)
    (β.app A) (β.app A) (β.app (A⟦m⟧)) (fun y => β.hom.naturality y) τ₁
  let τ₂ : ShiftedHom ((etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) f ⋙
      DerivedCategory.Plus.ι).obj A)
      ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)) (-2) :=
    s.hom ≫ (β.app A).hom ≫ τ₁
  have hτ₂ : IsIso ((DerivedCategory.homologyFunctor _ 2).map τ₂) := by
    simp only [τ₂, τ₁, ShiftedHom.mk₀_comp, CategoryTheory.Functor.map_comp]
    infer_instance
  -- bijectivity for `ι ⋙ R` at `A`
  have h₂ : Function.Bijective (traceMap (DerivedCategory.Plus.ι ⋙ R) τ₁ A m c h) := by
    have e : ⇑(traceMap (DerivedCategory.Plus.ι ⋙ R) τ₁ A m c h) =
        (fun z => (ShiftedHom.mk₀ (0 : ℤ) rfl (β.app A).inv).comp z (add_zero c)) ∘
          traceMap (etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) f ⋙ DerivedCategory.Plus.ι)
            τ₂ A m c h :=
      funext (hs c h)
    rw [e]
    exact (bijective_mk₀_comp_of_iso (Y := (DerivedCategory.singleFunctor _ 0).obj
      (unitSheaf (X := S) ℓ)) (β.app A).symm c).comp (H τ₂ hτ₂ m c h)
  -- bijectivity for `R` at `ι A`, with `B = ι A`
  have h₁ : Function.Bijective (traceMap R τ₁ (DerivedCategory.Plus.ι.obj A) m c h) :=
    (bijective_traceMap_comp_iff_of_fullyFaithful DerivedCategory.Plus.ι R τ₁ A m c h).1 h₂
  rw [bijective_traceMap_mk₀_map_comp_iff i t _ h] at h₁
  exact bijective_traceMap_of_iso i h h₁

end Stacks.EtaleCohomology

end
