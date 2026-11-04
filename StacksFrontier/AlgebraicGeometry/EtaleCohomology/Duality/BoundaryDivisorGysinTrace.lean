module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.BoundaryDivisorDualityComponents
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Gysin trace of an étale boundary divisor has invertible adjoint

In the setting of `Stacks.EtaleCohomology.BoundaryDivisorGysinTraceInput` (`f̄ : X̄ ⟶ S` smooth
projective of relative dimension one with geometrically irreducible fibres, `S` affine and smooth
over the algebraically closed `k`, `i : Z ⟶ X̄` a closed immersion with `π = f̄ ∘ i` finite étale),
for every purity class `γ ∈ Ext²_X̄(i_* Λ_Z, f̄⁻¹ Λ)` and every top-degree trace `t`, the adjoint
`τ♭ : Λ_Z ⟶ π⁻¹ Λ` of the Gysin trace `t ∘ Rf̄_*(γ)` is an isomorphism
(`Stacks.EtaleCohomology.boundaryDivisorGysinTraceInput`).

Duality along the boundary divisor (`Stacks.EtaleCohomology.boundaryDivisorDualityInput`) says that
the trace map is bijective at `i_* Λ_Z` in degree `2`. Read through the Gysin bijection
`Ext⁰_Z(Λ_Z, Λ_Z) ≅ Ext²_X̄(i_* Λ_Z, f̄⁻¹ Λ)`, the degree-zero identifications of `Ri_*` and
`Rf̄_* ∘ Ri_*`, and the adjunction `π_* ⊣ π⁻¹`, this is the bijectivity of `y ↦ y ≫ τ♭`,
`End(Λ_Z) → Hom(Λ_Z, π⁻¹ Λ)` (the same factorizations as in
`Stacks.EtaleCohomology.isBijectiveAt_directImage_of_isPurityClass`, read backwards). Since
`π⁻¹ Λ ≅ Λ_Z`, a morphism `σ` with `y ↦ y ≫ σ` bijective is an isomorphism
(`Stacks.EtaleCohomology.isIso_of_bijective_comp`).

Hence relative Poincaré duality for an elementary fibration needs only duality on the smooth
projective curve
(`Stacks.EtaleCohomology.relativeCurveDualityInput_of_properCurveRelativeDualityInput`).

This is part of the proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.EtaleCohomology.isIso_of_bijective_comp`.
* `Stacks.EtaleCohomology.isIso_boundaryGysinTraceAdjoint_of_bijective`.
* `Stacks.EtaleCohomology.boundaryDivisorGysinTraceInput`.
* `Stacks.EtaleCohomology.relativeCurveDualityInput_of_properCurveRelativeDualityInput`.

## Implementation notes

The statements consume the derived direct images in the standard model
`HasDerivedCategory.standard` of the derived category, as a local instance, as does
`Stacks.EtaleCohomology.BoundaryDivisorGysinTraceInput`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

open Stacks.EtaleCohomology.ExtensionTorsor Stacks.RelativeDuality

attribute [local instance] HasDerivedCategory.standard

/-- **A morphism `σ : X ⟶ Y` with `Y ≅ X` is an isomorphism as soon as `y ↦ y ≫ σ` is bijective**
on `End(X) → Hom(X, Y)`: a preimage `y` of `ι⁻¹` gives the inverse `ι ≫ y`, two-sided by
injectivity. -/
theorem isIso_of_bijective_comp {C : Type*} [Category* C] {X Y : C} (σ : X ⟶ Y) (ι : Y ≅ X)
    (h : Function.Bijective (fun y : X ⟶ X => y ≫ σ)) : IsIso σ := by
  obtain ⟨y, hy⟩ := h.2 ι.inv
  simp only at hy
  have h₁ : σ ≫ ι.hom ≫ y = 𝟙 X := h.1 (by
    simp only [Category.assoc, hy, Iso.hom_inv_id, Category.comp_id, Category.id_comp])
  exact ⟨⟨ι.hom ≫ y, h₁, by rw [Category.assoc, hy, Iso.hom_inv_id]⟩⟩

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- **The converse of `Stacks.EtaleCohomology.bijective_comp_mapExactFunctor_directImage_of_isIso`
in degree zero**: if `y ↦ τ₀ ∘ π_* y` is bijective on `Ext⁰_Z(Λ_Z, Λ_Z)`, the adjoint
`τ♭ : Λ_Z ⟶ π⁻¹ Λ_S` of `τ₀` is an isomorphism. -/
theorem isIso_homEquiv_of_bijective_comp_mapExactFunctor {Z S : Scheme.{u}} (π : Z ⟶ S)
    [IsFinite π] [Etale π]
    (e : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) π).obj (unitSheaf (X := Z) ℓ))
      (unitSheaf (X := S) ℓ) 0)
    (hb : Function.Bijective (fun y : Ext (unitSheaf (X := Z) ℓ) (unitSheaf (X := Z) ℓ) 0 =>
      (y.mapExactFunctor (etaleModuleDirectImage.{u, 0} (ZMod ℓ) π)).comp e (add_zero 0))) :
    IsIso ((etaleModuleDirectImageInverseImageAdj.{u, 0} (ZMod ℓ) π).homEquiv _ _
      (Ext.homEquiv₀ e)) := by
  let := etaleModules_enoughInjectives.{u, 0} (ZMod ℓ) S
  let adj := etaleModuleDirectImageInverseImageAdj.{u, 0} (ZMod ℓ) π
  let τ₀ := Ext.homEquiv₀ e
  let τb : unitSheaf (X := Z) ℓ ⟶
      (etaleModuleInverseImage.{u, 0} (ZMod ℓ) π).obj (unitSheaf (X := S) ℓ) :=
    adj.homEquiv _ _ τ₀
  have hτ₀ : τ₀ = (etaleModuleDirectImage.{u, 0} (ZMod ℓ) π).map τb ≫
      adj.counit.app (unitSheaf (X := S) ℓ) :=
    ((adj.homEquiv _ _).symm_apply_apply τ₀).symm.trans (Adjunction.homEquiv_counit adj _ _ _)
  have hfac : (fun y : Ext (unitSheaf (X := Z) ℓ) (unitSheaf (X := Z) ℓ) 0 =>
      (y.mapExactFunctor (etaleModuleDirectImage.{u, 0} (ZMod ℓ) π)).comp e (add_zero 0)) =
      ⇑(Stacks.ExtAdjunction.extMap adj (unitSheaf (X := Z) ℓ) (unitSheaf (X := S) ℓ) 0) ∘
        ⇑((Ext.mk₀ τb).postcomp (a := 0) (b := 0) (unitSheaf (X := Z) ℓ) (add_zero 0)) := by
    funext y
    simp only [Function.comp_apply, Stacks.ExtAdjunction.extMap_apply,
      Stacks.ExtAdjunction.postcomp_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
    rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, ← hτ₀, Ext.mk₀_homEquiv₀_apply]
  rw [hfac] at hb
  have hp := (Function.Bijective.of_comp_iff'
    (Stacks.ExtAdjunction.extMap_bijective adj _ _ 0) _).1 hb
  refine isIso_of_bijective_comp τb (unitSheafInverseImageIso (ℓ := ℓ) π) ?_
  have e₀ : (fun y : unitSheaf (X := Z) ℓ ⟶ unitSheaf (X := Z) ℓ => y ≫ τb) =
      Ext.homEquiv₀ ∘ ⇑((Ext.mk₀ τb).postcomp (a := 0) (b := 0) (unitSheaf (X := Z) ℓ)
        (add_zero 0)) ∘ Ext.mk₀ := by
    funext y
    simp only [Function.comp_apply, Stacks.ExtAdjunction.postcomp_apply, Ext.mk₀_comp_mk₀]
    rw [← Ext.homEquiv₀_symm_apply, Equiv.apply_symm_apply]
  rw [e₀]
  exact Ext.homEquiv₀.bijective.comp (hp.comp Ext.homEquiv₀.symm.bijective)

section Boundary

variable {S Xbar Z : Scheme.{u}} (fbar : Xbar ⟶ S) (i : Z ⟶ Xbar)
  [IsClosedImmersion i] [IsFinite (i ≫ fbar)] [Etale (i ≫ fbar)]

omit [IsClosedImmersion i] in
/-- **The converse of `Stacks.EtaleCohomology.bijective_traceMap_derivedDirectImageComp_extPlus`
in degree zero**: if the trace map of `Rf̄_* ∘ Ri_*` at `Λ_Z` is bijective in degree `0`, the
adjoint of the trace is an isomorphism. -/
theorem isIso_derivedDirectImageCompTraceAdjoint_of_bijective
    (t₁ : ShiftedHom (((etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) i ⋙
        etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar) ⋙ DerivedCategory.Plus.ι).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := Z) ℓ)))
        ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)) (0 : ℤ))
    (hb : Function.Bijective (fun y : Ext (unitSheaf (X := Z) ℓ) (unitSheaf (X := Z) ℓ) 0 =>
      traceMap ((etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) i ⋙
        etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar) ⋙ DerivedCategory.Plus.ι) t₁
          ((DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := Z) ℓ)) ((0 : ℕ) : ℤ) 0
          (by norm_num) (Stacks.TopTruncationExt.extPlus y))) :
    IsIso (derivedDirectImageCompTraceAdjoint ℓ fbar i t₁) := by
  let := etaleModules_enoughInjectives.{u, 0} (ZMod ℓ) Z
  let κ := HomologicalDuality.degreeZeroIso
    (etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) i ⋙
      etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar)
    (isLE_derivedDirectImageComp_single ℓ i fbar) (isGE_derivedDirectImageComp_single ℓ i fbar)
    (etaleModuleDirectImage.{u, 0} (ZMod ℓ) (i ≫ fbar))
    (derivedDirectImageCompTopHomologyIso ℓ i fbar) (unitSheaf (X := Z) ℓ)
  let t₂ : ShiftedHom ((DerivedCategory.singleFunctor _ 0).obj
      ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) (i ≫ fbar)).obj (unitSheaf (X := Z) ℓ)))
      ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)) ((0 : ℕ) : ℤ) :=
    (ShiftedHom.mk₀ (0 : ℤ) rfl (DerivedCategory.Plus.ι.map κ.inv)).comp t₁ (add_zero 0)
  let e₀ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) (i ≫ fbar)).obj (unitSheaf (X := Z) ℓ))
      (unitSheaf (X := S) ℓ) 0 := Ext.homEquiv.symm t₂
  have he₀ : e₀.hom = t₂ := Ext.homEquiv.apply_symm_apply t₂
  have hF := traceMap_comp_extPlus_degreeZero
    (etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) i ⋙
      etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar)
    (isLE_derivedDirectImageComp_single ℓ i fbar) (isGE_derivedDirectImageComp_single ℓ i fbar)
    (etaleModuleDirectImage.{u, 0} (ZMod ℓ) (i ≫ fbar))
    (derivedDirectImageCompTopHomologyIso ℓ i fbar) DerivedCategory.Plus.ι
    (M := unitSheaf (X := Z) ℓ) t₁ 0 (by norm_num : (0 : ℤ) + ((0 : ℕ) : ℤ) = 0)
  have hfac : (fun y : Ext (unitSheaf (X := Z) ℓ) (unitSheaf (X := Z) ℓ) 0 =>
      traceMap ((etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) i ⋙
        etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar) ⋙ DerivedCategory.Plus.ι) t₁
          ((DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := Z) ℓ)) ((0 : ℕ) : ℤ) 0
          (by norm_num) (Stacks.TopTruncationExt.extPlus y)) =
      (fun x : ShiftedHom ((DerivedCategory.singleFunctor _ 0).obj
          ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) (i ≫ fbar)).obj (unitSheaf (X := Z) ℓ)))
          ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)) ((0 : ℕ) : ℤ) =>
        (ShiftedHom.mk₀ (0 : ℤ) rfl (DerivedCategory.Plus.ι.map κ.hom)).comp x (add_zero _)) ∘
        (fun w : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) (i ≫ fbar)).obj
          (unitSheaf (X := Z) ℓ)) (unitSheaf (X := S) ℓ) 0 => Ext.homEquiv w) ∘
        (fun y : Ext (unitSheaf (X := Z) ℓ) (unitSheaf (X := Z) ℓ) 0 =>
          (y.mapExactFunctor (etaleModuleDirectImage.{u, 0} (ZMod ℓ) (i ≫ fbar))).comp e₀
            (add_zero 0)) := by
    funext y
    rw [hF y]
    simp only [Function.comp_apply]
    congr 1
    rw [traceMap_apply, Stacks.TopTruncationExt.extPlus_map_ι]
    show _ = (Ext.comp _ e₀ (add_zero 0)).hom
    rw [Ext.comp_hom, he₀]
    rfl
  rw [hfac] at hb
  have h₁ := (Function.Bijective.of_comp_iff' (bijective_mk₀_comp_of_iso
    (DerivedCategory.Plus.ι.mapIso κ) _) _).1 hb
  exact isIso_homEquiv_of_bijective_comp_mapExactFunctor ℓ (i ≫ fbar) e₀
    ((Function.Bijective.of_comp_iff' Ext.homEquiv.bijective _).1 h₁)

/-- **The converse of
`Stacks.EtaleCohomology.bijective_traceMap_directImage_extPlus_mapExactFunctor` in degree zero**:
if the trace map of a degree-zero trace `τ : Rf̄_*(i_* Λ_Z) ⟶ Λ` is bijective on the classes
`i_* y`, `y ∈ Ext⁰_Z(Λ_Z, Λ_Z)`, its adjoint is an isomorphism. -/
theorem isIso_boundaryTraceAdjoint_of_bijective
    (τ : ShiftedHom ((etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar ⋙
        DerivedCategory.Plus.ι).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := Z) ℓ))))
        ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)) (0 : ℤ))
    (hb : Function.Bijective (fun y : Ext (unitSheaf (X := Z) ℓ) (unitSheaf (X := Z) ℓ) 0 =>
      traceMap (etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar ⋙ DerivedCategory.Plus.ι) τ
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := Z) ℓ))) ((0 : ℕ) : ℤ) 0
        (by norm_num) (Stacks.TopTruncationExt.extPlus
          (y.mapExactFunctor (etaleModuleDirectImage.{u, 0} (ZMod ℓ) i) : Ext _ _ 0)))) :
    IsIso (boundaryTraceAdjoint ℓ fbar i τ) := by
  let := etaleModules_enoughInjectives.{u, 0} (ZMod ℓ) Z
  let κ := HomologicalDuality.degreeZeroIso (etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) i)
    (isLE_derivedDirectImage_single_of_isIntegralHom ℓ i)
    (isGE_derivedDirectImage_single_of_isIntegralHom ℓ i)
    (etaleModuleDirectImage.{u, 0} (ZMod ℓ) i) (derivedDirectImageTopHomologyIsoOfIsIntegralHom ℓ i)
    (unitSheaf (X := Z) ℓ)
  let t := (ShiftedHom.mk₀ (0 : ℤ) rfl ((etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar ⋙
    DerivedCategory.Plus.ι).map κ.hom)).comp τ (add_zero 0)
  have htτ : (ShiftedHom.mk₀ (0 : ℤ) rfl ((etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar ⋙
      DerivedCategory.Plus.ι).map κ.inv)).comp t (add_zero 0) = τ := by
    simp only [t, ShiftedHom.mk₀_comp]
    rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  have hF := traceMap_comp_extPlus_degreeZero (etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) i)
    (isLE_derivedDirectImage_single_of_isIntegralHom ℓ i)
    (isGE_derivedDirectImage_single_of_isIntegralHom ℓ i)
    (etaleModuleDirectImage.{u, 0} (ZMod ℓ) i) (derivedDirectImageTopHomologyIsoOfIsIntegralHom ℓ i)
    (etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar ⋙ DerivedCategory.Plus.ι)
    (M := unitSheaf (X := Z) ℓ) t 0 (by norm_num : (0 : ℤ) + ((0 : ℕ) : ℤ) = 0)
  have hfac : (fun y : Ext (unitSheaf (X := Z) ℓ) (unitSheaf (X := Z) ℓ) 0 =>
      traceMap ((etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) i ⋙
        etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar) ⋙ DerivedCategory.Plus.ι) t
          ((DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := Z) ℓ)) ((0 : ℕ) : ℤ) 0
          (by norm_num) (Stacks.TopTruncationExt.extPlus y)) =
      (fun x => (ShiftedHom.mk₀ (0 : ℤ) rfl ((etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar ⋙
        DerivedCategory.Plus.ι).map κ.hom)).comp x (add_zero 0)) ∘
      (fun y : Ext (unitSheaf (X := Z) ℓ) (unitSheaf (X := Z) ℓ) 0 =>
        traceMap (etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar ⋙ DerivedCategory.Plus.ι) τ
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := Z) ℓ))) ((0 : ℕ) : ℤ)
          0 (by norm_num) (Stacks.TopTruncationExt.extPlus
            (y.mapExactFunctor (etaleModuleDirectImage.{u, 0} (ZMod ℓ) i) : Ext _ _ 0))) := by
    funext y
    simp only [Function.comp_apply]
    rw [← htτ, ← hF y]
    simp only [traceMap_apply, ShiftedHom.comp_map]
  refine isIso_derivedDirectImageCompTraceAdjoint_of_bijective ℓ fbar i t ?_
  rw [hfac]
  exact (bijective_mk₀_comp_of_iso
    ((etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar ⋙ DerivedCategory.Plus.ι).mapIso κ)
      0).comp hb

/-- **The converse of `Stacks.EtaleCohomology.bijective_traceMap_directImage_of_isPurityClass` in
degree `2`**: for a purity class `γ`, if the trace map of `t` at `i_* Λ_Z` is bijective in
degree `2`, the adjoint of the Gysin trace is an isomorphism. -/
theorem isIso_boundaryGysinTraceAdjoint_of_bijective
    (γ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := Z) ℓ))
      ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) fbar).obj (unitSheaf (X := S) ℓ)) 2)
    (hγ : IsPurityClass i _ γ)
    (t : ShiftedHom ((etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar ⋙
        DerivedCategory.Plus.ι).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) fbar).obj (unitSheaf (X := S) ℓ))))
        ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)) (-2))
    (hb : Function.Bijective (traceMap (etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar ⋙
      DerivedCategory.Plus.ι) t ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := Z) ℓ)))
      ((0 + 2 : ℕ) : ℤ) 0 (by norm_num))) :
    IsIso (boundaryGysinTraceAdjoint ℓ fbar i γ t) := by
  have hβ : Function.Bijective (fun y : Ext (unitSheaf (X := Z) ℓ) (unitSheaf (X := Z) ℓ) 0 =>
      Stacks.TopTruncationExt.extPlus ((y.mapExactFunctor
        (etaleModuleDirectImage.{u, 0} (ZMod ℓ) i)).comp γ (rfl : 0 + 2 = 0 + 2))) :=
    (HomologicalDuality.extPlus_bijective _ _ (0 + 2)).comp (hγ.1 (unitSheaf (X := Z) ℓ) 0)
  have hc0 : (-2 : ℤ) + ((2 : ℕ) : ℤ) = 0 := by norm_num
  have e : ⇑(traceMap (etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar ⋙
      DerivedCategory.Plus.ι) t ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := Z) ℓ)))
      ((0 + 2 : ℕ) : ℤ) 0 (by norm_num)) ∘
      (fun y : Ext (unitSheaf (X := Z) ℓ) (unitSheaf (X := Z) ℓ) 0 =>
        Stacks.TopTruncationExt.extPlus ((y.mapExactFunctor
          (etaleModuleDirectImage.{u, 0} (ZMod ℓ) i)).comp γ (rfl : 0 + 2 = 0 + 2))) =
      (fun y : Ext (unitSheaf (X := Z) ℓ) (unitSheaf (X := Z) ℓ) 0 =>
        traceMap (etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar ⋙ DerivedCategory.Plus.ι)
          (((Stacks.TopTruncationExt.extPlus γ).map (etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ)
            fbar ⋙ DerivedCategory.Plus.ι)).comp t hc0)
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := Z) ℓ))) ((0 : ℕ) : ℤ)
          0 (by norm_num) (Stacks.TopTruncationExt.extPlus
            (y.mapExactFunctor (etaleModuleDirectImage.{u, 0} (ZMod ℓ) i) : Ext _ _ 0))) := by
    funext y
    simp only [Function.comp_apply]
    rw [Stacks.TopTruncationExt.extPlus_comp]
    exact traceMap_comp_shiftedHom t _ hc0 _ _ _ _ _
  have h := hb.comp hβ
  rw [e] at h
  exact isIso_boundaryTraceAdjoint_of_bijective ℓ fbar i _ h

end Boundary

section Input

variable (k : Type u) [Field k] [IsAlgClosed k]

/-- **The Gysin trace of the boundary divisor has invertible adjoint**
(`Stacks.EtaleCohomology.BoundaryDivisorGysinTraceInput`): duality along the boundary divisor
(`Stacks.EtaleCohomology.boundaryDivisorDualityInput`) in degree `2`, read backwards through the
Gysin bijection and the adjunction `π_* ⊣ π⁻¹`
(`Stacks.EtaleCohomology.isIso_boundaryGysinTraceAdjoint_of_bijective`). -/
theorem boundaryDivisorGysinTraceInput : BoundaryDivisorGysinTraceInput ℓ k := by
  intro hℓ S Xbar Z q e _ _ fbar i _ _ _ _ _ hproj γ hγ t ht
  have hd := boundaryDivisorDualityInput ℓ k hℓ S Xbar Z q e fbar i hproj t ht
  let eZ : (etaleModuleInverseImage.{u, 0} (ZMod ℓ) i).obj
      ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) fbar).obj (unitSheaf (X := S) ℓ)) ≅
      unitSheaf (X := Z) ℓ :=
    (etaleModuleInverseImage.{u, 0} (ZMod ℓ) i).mapIso
        ((etaleModuleInverseImageConstantIso.{u, 0} (ZMod ℓ) fbar).app
          (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ)))) ≪≫
      (etaleModuleInverseImageConstantIso.{u, 0} (ZMod ℓ) i).app
        (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ)))
  have hd' := isBijectiveAt_of_iso ((DerivedCategory.Plus.singleFunctor _ 0).mapIso
    ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).mapIso eZ)) hd
  exact isIso_boundaryGysinTraceAdjoint_of_bijective ℓ fbar i γ hγ t (hd' _ _ _)

/-- **Relative Poincaré duality for an elementary fibration, from duality on the smooth projective
curve alone**: with the boundary-divisor input proved
(`Stacks.EtaleCohomology.boundaryDivisorDualityInput`, equivalently from
`Stacks.EtaleCohomology.boundaryDivisorPurityInput` and
`Stacks.EtaleCohomology.boundaryDivisorGysinTraceInput`), relative duality
(`Stacks.EtaleCohomology.RelativeCurveDualityInput`) follows from
`Stacks.EtaleCohomology.ProperCurveRelativeDualityInput`. -/
@[sga "4½ Dualite 2.2" "special case"]
theorem relativeCurveDualityInput_of_properCurveRelativeDualityInput
    (he : ProperCurveRelativeDualityInput ℓ k) : RelativeCurveDualityInput ℓ k :=
  relativeCurveDualityInput_of_inputs ℓ k
    (boundaryDivisorDualityInput_of_inputs ℓ k (boundaryDivisorPurityInput ℓ k)
      (boundaryDivisorGysinTraceInput ℓ k)) he

end Input

end Stacks.EtaleCohomology

end
