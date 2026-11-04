module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.RelativeCurveDualityReduction
public import StacksFrontier.Algebra.Homology.DerivedCategory.TraceMapDegreeZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.FiniteEtaleAdjunction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LocallyConstantDevissage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.LocalPurityGluing

/-!
# Duality along an étale boundary divisor, reduced to the nonvanishing of the Gysin trace

Let `f̄ : X̄ → S`, `i : Z → X̄` a closed immersion with `π = f̄ ∘ i` finite étale, `Λ = ℤ/ℓ`, and
`γ ∈ Ext²_X̄(i_* Λ_Z, f̄⁻¹ Λ)` a purity class (`Stacks.EtaleCohomology.IsPurityClass`). For a trace
`t : Rf̄_*(f̄⁻¹ Λ) ⟶ Λ[-2]`, write `τ = t ∘ Rf̄_*(γ) : Rf̄_*(i_* Λ_Z) ⟶ Λ` (the Gysin trace). The
trace map `y ↦ t[m] ∘ Rf̄_*(y)`, `Hom_X̄(i_* Λ_Z, f̄⁻¹ Λ[m]) → Hom_S(Rf̄_* i_* Λ_Z, Λ[m - 2])`, is
bijective for every `m` as soon as the adjoint `Λ_Z ⟶ π⁻¹ Λ` of `τ` is invertible; for `Z`
irreducible, as soon as `τ ≠ 0`.

## Main definitions

* `Stacks.EtaleCohomology.boundaryGysinTraceAdjoint`: the adjoint `Λ_Z ⟶ π⁻¹ Λ` of the Gysin
  trace.
* `Stacks.EtaleCohomology.BoundaryDivisorPurityInput`: the existence of a purity class along an
  étale boundary divisor.
* `Stacks.EtaleCohomology.BoundaryDivisorGysinTraceInput`: the invertibility of the adjoint of the
  Gysin trace along an étale boundary divisor.

## Main results

* `Stacks.EtaleCohomology.bijective_comp_mapExactFunctor_directImage_of_isIso`: for `π` finite
  étale, a morphism `π_* Λ_Z ⟶ Λ` with invertible adjoint induces bijections on `Ext`.
* `Stacks.EtaleCohomology.isIso_boundaryGysinTraceAdjoint_of_ne_zero`: on an irreducible `Z`, a
  nonzero Gysin trace has invertible adjoint.
* `Stacks.EtaleCohomology.isBijectiveAt_directImage_of_isPurityClass`: the trace map at
  `i_* Λ_Z` is bijective in every degree when the adjoint of the Gysin trace is invertible.
* `Stacks.EtaleCohomology.boundaryDivisorDualityInput_of_inputs`: the boundary-divisor input of
  relative duality follows from `BoundaryDivisorPurityInput` and
  `BoundaryDivisorGysinTraceInput`.

## References

* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open Stacks.EtaleCohomology.ExtensionTorsor Stacks.RelativeDuality

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-! ### Derived direct images along integral morphisms, in degree zero -/

section Integral

variable (N : ℕ) {T Y : Scheme.{u}} (g : T ⟶ Y) [IsIntegralHom g]

/-- `H⁰(Rg_*((-)[0])) ≅ g_*` for an integral morphism `g`, direct image being exact. -/
def derivedDirectImageTopHomologyIsoOfIsIntegralHom :
    Stacks.TopTruncationExt.topHomology
        (etaleModuleDerivedDirectImage.{u, 0} (ZMod N) g ⋙ DerivedCategory.Plus.ι) 0 ≅
      etaleModuleDirectImage.{u, 0} (ZMod N) g :=
  (Iso.refl _ : _ ≅ (DerivedCategory.Plus.singleFunctor _ 0 ⋙
      etaleModuleDerivedDirectImage.{u, 0} (ZMod N) g) ⋙
        (DerivedCategory.Plus.ι ⋙ DerivedCategory.homologyFunctor _ 0)) ≪≫
    Functor.isoWhiskerRight (Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
      (etaleModuleDirectImage.{u, 0} (ZMod N) g) 0).symm _ ≪≫
    (Iso.refl _ : _ ≅ etaleModuleDirectImage.{u, 0} (ZMod N) g ⋙
      (DerivedCategory.singleFunctor _ 0 ⋙ DerivedCategory.homologyFunctor _ 0)) ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0) ≪≫
    Functor.rightUnitor _

/-- `Rg_*(M[0]) ≅ (g_* M)[0]` for an integral morphism `g`, read in `D`. -/
def derivedDirectImageSingleIsoOfIsIntegralHom (M : EtaleModules.{u, 0} (ZMod N) T) :
    DerivedCategory.Plus.ι.obj ((etaleModuleDerivedDirectImage.{u, 0} (ZMod N) g).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj M)) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((etaleModuleDirectImage.{u, 0} (ZMod N) g).obj M) :=
  DerivedCategory.Plus.ι.mapIso ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
    (etaleModuleDirectImage.{u, 0} (ZMod N) g) 0).app M).symm

/-- For an integral morphism `g`, `Rg_*(M[0])` is concentrated in degrees `≤ 0`. -/
theorem isLE_derivedDirectImage_single_of_isIntegralHom (M : EtaleModules.{u, 0} (ZMod N) T) :
    ((etaleModuleDerivedDirectImage.{u, 0} (ZMod N) g ⋙ DerivedCategory.Plus.ι).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj M)).IsLE 0 :=
  DerivedCategory.TStructure.t.isLE_of_iso (derivedDirectImageSingleIsoOfIsIntegralHom N g M).symm 0

/-- For an integral morphism `g`, `Rg_*(M[0])` is concentrated in degrees `≥ 0`. -/
theorem isGE_derivedDirectImage_single_of_isIntegralHom (M : EtaleModules.{u, 0} (ZMod N) T) :
    ((etaleModuleDerivedDirectImage.{u, 0} (ZMod N) g ⋙ DerivedCategory.Plus.ι).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj M)).IsGE 0 :=
  DerivedCategory.TStructure.t.isGE_of_iso (derivedDirectImageSingleIsoOfIsIntegralHom N g M).symm 0

end Integral

/-! ### `Rf̄_* ∘ Ri_*` in degree zero -/

section Composite

variable (N : ℕ) {Z X S : Scheme.{u}} (i : Z ⟶ X) (f : X ⟶ S) [IsIntegralHom (i ≫ f)]

/-- `Rf_*(Ri_*(M[0])) ≅ R(i ≫ f)_*(M[0])`, read in `D`. -/
def derivedDirectImageCompSingleIso (M : EtaleModules.{u, 0} (ZMod N) Z) :
    ((etaleModuleDerivedDirectImage.{u, 0} (ZMod N) i ⋙ etaleModuleDerivedDirectImage.{u, 0}
        (ZMod N) f) ⋙ DerivedCategory.Plus.ι).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj M) ≅
      (etaleModuleDerivedDirectImage.{u, 0} (ZMod N) (i ≫ f) ⋙ DerivedCategory.Plus.ι).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj M) :=
  DerivedCategory.Plus.ι.mapIso
    ((etaleModuleDerivedDirectImageComp.{u, 0} (ZMod N) i f (i ≫ f) rfl).app _).symm

/-- `H⁰(Rf_*(Ri_*((-)[0]))) ≅ (i ≫ f)_*` when `i ≫ f` is integral. -/
def derivedDirectImageCompTopHomologyIso :
    Stacks.TopTruncationExt.topHomology
        ((etaleModuleDerivedDirectImage.{u, 0} (ZMod N) i ⋙
          etaleModuleDerivedDirectImage.{u, 0} (ZMod N) f) ⋙ DerivedCategory.Plus.ι) 0 ≅
      etaleModuleDirectImage.{u, 0} (ZMod N) (i ≫ f) :=
  Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor _ 0)
      (Functor.isoWhiskerRight (Functor.isoWhiskerRight
        (etaleModuleDerivedDirectImageComp.{u, 0} (ZMod N) i f (i ≫ f) rfl).symm
          DerivedCategory.Plus.ι) (DerivedCategory.homologyFunctor _ 0)) ≪≫
    derivedDirectImageTopHomologyIsoOfIsIntegralHom N (i ≫ f)

/-- When `i ≫ f` is integral, `Rf_*(Ri_*(M[0]))` is concentrated in degrees `≤ 0`. -/
theorem isLE_derivedDirectImageComp_single (M : EtaleModules.{u, 0} (ZMod N) Z) :
    (((etaleModuleDerivedDirectImage.{u, 0} (ZMod N) i ⋙
      etaleModuleDerivedDirectImage.{u, 0} (ZMod N) f) ⋙ DerivedCategory.Plus.ι).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj M)).IsLE 0 :=
  have := isLE_derivedDirectImage_single_of_isIntegralHom N (i ≫ f) M
  DerivedCategory.TStructure.t.isLE_of_iso (derivedDirectImageCompSingleIso N i f M).symm 0

/-- When `i ≫ f` is integral, `Rf_*(Ri_*(M[0]))` is concentrated in degrees `≥ 0`. -/
theorem isGE_derivedDirectImageComp_single (M : EtaleModules.{u, 0} (ZMod N) Z) :
    (((etaleModuleDerivedDirectImage.{u, 0} (ZMod N) i ⋙
      etaleModuleDerivedDirectImage.{u, 0} (ZMod N) f) ⋙ DerivedCategory.Plus.ι).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj M)).IsGE 0 :=
  have := isGE_derivedDirectImage_single_of_isIntegralHom N (i ≫ f) M
  DerivedCategory.TStructure.t.isGE_of_iso (derivedDirectImageCompSingleIso N i f M).symm 0

end Composite

/-! ### Duality along a finite étale morphism from an irreducible source -/

section FiniteEtale

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- Let `π : Z → S` be finite étale and `τ₀ : π_* Λ_Z ⟶ Λ_S`. If the adjoint `τ♭ : Λ_Z ⟶ π⁻¹ Λ_S`
of `τ₀` under `π_* ⊣ π⁻¹` is an isomorphism, then `y ↦ τ₀ ∘ π_* y` is a bijection
`Ext^q_Z(Λ_Z, Λ_Z) → Ext^q_S(π_* Λ_Z, Λ_S)`. -/
theorem bijective_comp_mapExactFunctor_directImage_of_isIso {Z S : Scheme.{u}} (π : Z ⟶ S)
    [IsFinite π] [Etale π]
    (e : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) π).obj (unitSheaf (X := Z) ℓ))
      (unitSheaf (X := S) ℓ) 0)
    (he : IsIso ((etaleModuleDirectImageInverseImageAdj.{u, 0} (ZMod ℓ) π).homEquiv _ _
      (Ext.homEquiv₀ e))) (q : ℕ) :
    Function.Bijective (fun y : Ext (unitSheaf (X := Z) ℓ) (unitSheaf (X := Z) ℓ) q =>
      (y.mapExactFunctor (etaleModuleDirectImage.{u, 0} (ZMod ℓ) π)).comp e (add_zero q)) := by
  let := etaleModules_enoughInjectives.{u, 0} (ZMod ℓ) S
  let adj := etaleModuleDirectImageInverseImageAdj.{u, 0} (ZMod ℓ) π
  let τ₀ := Ext.homEquiv₀ e
  let τb : unitSheaf (X := Z) ℓ ⟶
      (etaleModuleInverseImage.{u, 0} (ZMod ℓ) π).obj (unitSheaf (X := S) ℓ) :=
    adj.homEquiv _ _ τ₀
  have hτ₀ : τ₀ = (etaleModuleDirectImage.{u, 0} (ZMod ℓ) π).map τb ≫
      adj.counit.app (unitSheaf (X := S) ℓ) :=
    ((adj.homEquiv _ _).symm_apply_apply τ₀).symm.trans (Adjunction.homEquiv_counit adj _ _ _)
  have : IsIso τb := he
  have hfac : (fun y : Ext (unitSheaf (X := Z) ℓ) (unitSheaf (X := Z) ℓ) q ↦
      (y.mapExactFunctor (etaleModuleDirectImage.{u, 0} (ZMod ℓ) π)).comp e (add_zero q)) =
      ⇑(Stacks.ExtAdjunction.extMap adj (unitSheaf (X := Z) ℓ) (unitSheaf (X := S) ℓ) q) ∘
        ⇑((Ext.mk₀ τb).postcomp (a := q) (b := q) (unitSheaf (X := Z) ℓ) (add_zero q)) := by
    funext y
    simp only [Function.comp_apply, Stacks.ExtAdjunction.extMap_apply,
      Stacks.ExtAdjunction.postcomp_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
    rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, ← hτ₀, Ext.mk₀_homEquiv₀_apply]
  rw [hfac]
  exact (Stacks.ExtAdjunction.extMap_bijective adj _ _ q).comp
    (Stacks.ExtAdjunction.postcomp_mk₀_bijective_of_isIso τb q)

/-- Let `π : Z → S` be finite étale with `Z` irreducible. A nonzero `τ₀ : π_* Λ_Z ⟶ Λ` has
invertible adjoint `τ♭ : Λ_Z ⟶ π⁻¹ Λ_S`. -/
theorem isIso_homEquiv_directImageInverseImageAdj_of_ne_zero {Z S : Scheme.{u}} (π : Z ⟶ S)
    [IsFinite π] [Etale π] [IrreducibleSpace Z]
    (e : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) π).obj (unitSheaf (X := Z) ℓ))
      (unitSheaf (X := S) ℓ) 0) (he : e ≠ 0) :
    IsIso ((etaleModuleDirectImageInverseImageAdj.{u, 0} (ZMod ℓ) π).homEquiv _ _
      (Ext.homEquiv₀ e)) := by
  let adj := etaleModuleDirectImageInverseImageAdj.{u, 0} (ZMod ℓ) π
  let τ₀ := Ext.homEquiv₀ e
  let τb : unitSheaf (X := Z) ℓ ⟶
      (etaleModuleInverseImage.{u, 0} (ZMod ℓ) π).obj (unitSheaf (X := S) ℓ) :=
    adj.homEquiv _ _ τ₀
  let ι := unitSheafInverseImageIso (ℓ := ℓ) π
  have hτ₀ : τ₀ = (etaleModuleDirectImage.{u, 0} (ZMod ℓ) π).map τb ≫
      adj.counit.app (unitSheaf (X := S) ℓ) :=
    ((adj.homEquiv _ _).symm_apply_apply τ₀).symm.trans (Adjunction.homEquiv_counit adj _ _ _)
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  obtain ⟨r, hr⟩ := Purity.exists_eq_smul_id_unitSheaf (N := ℓ) Z (τb ≫ ι.hom)
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply he
    have hb : τb = 0 := by
      rw [zero_smul] at hr
      simpa using congrArg (· ≫ ι.inv) hr
    have h0 : τ₀ = 0 := by rw [hτ₀, hb, Functor.map_zero, zero_comp]
    rw [← Ext.mk₀_homEquiv₀_apply e]
    change Ext.mk₀ τ₀ = 0
    rw [h0, Ext.mk₀_zero]
  change IsIso τb
  have hτb : τb = (r • 𝟙 (unitSheaf (X := Z) ℓ)) ≫ ι.inv := by
    rw [← hr, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have : IsIso (r • 𝟙 (unitSheaf (X := Z) ℓ)) :=
    ⟨r⁻¹ • 𝟙 _, by simp [smul_smul, inv_mul_cancel₀ hr0, mul_inv_cancel₀ hr0]⟩
  rw [hτb]
  infer_instance

end FiniteEtale


/-! ### The trace map at `i_* Λ_Z` -/

section Boundary

variable (ℓ : ℕ) [Fact ℓ.Prime] {S Xbar Z : Scheme.{u}} (fbar : Xbar ⟶ S) (i : Z ⟶ Xbar)
  [IsClosedImmersion i] [IsFinite (i ≫ fbar)] [Etale (i ≫ fbar)]

/-- Precomposing a nonzero shifted morphism with an isomorphism keeps it nonzero. -/
private theorem mk₀_comp_ne_zero_of_iso {D : Type*} [Category D] [Preadditive D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] {X X' Y : D} (g : X ≅ X') {c : ℤ}
    {x : ShiftedHom X' Y c} (hx : x ≠ 0) :
    (ShiftedHom.mk₀ (0 : ℤ) rfl g.hom).comp x (add_zero c) ≠ 0 :=
  fun h ↦ hx ((bijective_mk₀_comp_of_iso g c).1 (h.trans (ShiftedHom.comp_zero _ _ _).symm))

/-- The adjoint of a degree-zero trace on `Rπ_*(Λ_Z)`, `π = f̄ ∘ i`: for
`t₁ : Rf̄_*(Ri_*(Λ_Z)) ⟶ Λ`, the adjoint `τ♭ : Λ_Z ⟶ π⁻¹ Λ` under `π_* ⊣ π⁻¹` of the morphism
`τ₀ : π_* Λ_Z ⟶ Λ` that `t₁` induces through `Rf̄_*(Ri_*(-[0])) ≅ (π_* -)[0]`. -/
def derivedDirectImageCompTraceAdjoint
    (t₁ : ShiftedHom (((etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) i ⋙
        etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar) ⋙ DerivedCategory.Plus.ι).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := Z) ℓ)))
        ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)) (0 : ℤ)) :
    unitSheaf (X := Z) ℓ ⟶
      (etaleModuleInverseImage.{u, 0} (ZMod ℓ) (i ≫ fbar)).obj (unitSheaf (X := S) ℓ) :=
  letI := etaleModules_enoughInjectives.{u, 0} (ZMod ℓ) Z
  let t₂ : ShiftedHom ((DerivedCategory.singleFunctor _ 0).obj
      ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) (i ≫ fbar)).obj (unitSheaf (X := Z) ℓ)))
      ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)) ((0 : ℕ) : ℤ) :=
    (ShiftedHom.mk₀ (0 : ℤ) rfl (DerivedCategory.Plus.ι.map (HomologicalDuality.degreeZeroIso
      (etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) i ⋙
        etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar)
      (isLE_derivedDirectImageComp_single ℓ i fbar) (isGE_derivedDirectImageComp_single ℓ i fbar)
      (etaleModuleDirectImage.{u, 0} (ZMod ℓ) (i ≫ fbar))
      (derivedDirectImageCompTopHomologyIso ℓ i fbar) (unitSheaf (X := Z) ℓ)).inv)).comp
      t₁ (add_zero 0)
  (etaleModuleDirectImageInverseImageAdj.{u, 0} (ZMod ℓ) (i ≫ fbar)).homEquiv _ _
    (Ext.homEquiv₀ (Ext.homEquiv.symm t₂))

omit [IsClosedImmersion i] in
/-- The trace map of `Rπ_* = Rf̄_* ∘ Ri_*` at `Λ_Z` is bijective on `Ext` for a degree-zero trace
`t₁ : Rπ_*(Λ_Z) ⟶ Λ` whose adjoint `derivedDirectImageCompTraceAdjoint` is invertible. -/
theorem bijective_traceMap_derivedDirectImageComp_extPlus
    (t₁ : ShiftedHom (((etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) i ⋙
        etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar) ⋙ DerivedCategory.Plus.ι).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := Z) ℓ)))
        ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)) (0 : ℤ))
    (ht₁ : IsIso (derivedDirectImageCompTraceAdjoint ℓ fbar i t₁)) (q : ℕ) {c : ℤ}
    (h : 0 + (q : ℤ) = c) :
    Function.Bijective (fun y : Ext (unitSheaf (X := Z) ℓ) (unitSheaf (X := Z) ℓ) q =>
      traceMap ((etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) i ⋙
        etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar) ⋙ DerivedCategory.Plus.ι) t₁
          ((DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := Z) ℓ)) q c h
          (Stacks.TopTruncationExt.extPlus y)) := by
  let := etaleModules_enoughInjectives.{u, 0} (ZMod ℓ) Z
  obtain rfl : c = (q : ℤ) := by omega
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
    (M := unitSheaf (X := Z) ℓ) t₁ q h
  have hfac : (fun y : Ext (unitSheaf (X := Z) ℓ) (unitSheaf (X := Z) ℓ) q ↦
      traceMap ((etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) i ⋙
        etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar) ⋙ DerivedCategory.Plus.ι) t₁
          ((DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := Z) ℓ)) q q h
          (Stacks.TopTruncationExt.extPlus y)) =
      (fun x : ShiftedHom ((DerivedCategory.singleFunctor _ 0).obj
          ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) (i ≫ fbar)).obj (unitSheaf (X := Z) ℓ)))
          ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)) (q : ℤ) ↦
        (ShiftedHom.mk₀ (0 : ℤ) rfl (DerivedCategory.Plus.ι.map κ.hom)).comp x (add_zero _)) ∘
        (fun w : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) (i ≫ fbar)).obj
          (unitSheaf (X := Z) ℓ)) (unitSheaf (X := S) ℓ) q ↦ Ext.homEquiv w) ∘
        (fun y : Ext (unitSheaf (X := Z) ℓ) (unitSheaf (X := Z) ℓ) q ↦
          (y.mapExactFunctor (etaleModuleDirectImage.{u, 0} (ZMod ℓ) (i ≫ fbar))).comp e₀
            (add_zero q)) := by
    funext y
    rw [hF y]
    simp only [Function.comp_apply]
    congr 1
    rw [traceMap_apply, Stacks.TopTruncationExt.extPlus_map_ι]
    change _ = (Ext.comp _ e₀ (add_zero q)).hom
    rw [Ext.comp_hom, he₀]
    rfl
  rw [hfac]
  exact (bijective_mk₀_comp_of_iso (DerivedCategory.Plus.ι.mapIso κ) _).comp
    (Ext.homEquiv.bijective.comp
      (bijective_comp_mapExactFunctor_directImage_of_isIso ℓ (i ≫ fbar) e₀ ht₁ q))

omit [IsClosedImmersion i] in
/-- On an irreducible `Z`, a nonzero degree-zero trace `t₁ : Rπ_*(Λ_Z) ⟶ Λ` has invertible adjoint.
-/
theorem isIso_derivedDirectImageCompTraceAdjoint_of_ne_zero [IrreducibleSpace Z]
    (t₁ : ShiftedHom (((etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) i ⋙
        etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar) ⋙ DerivedCategory.Plus.ι).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := Z) ℓ)))
        ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)) (0 : ℤ))
    (ht₁ : t₁ ≠ 0) : IsIso (derivedDirectImageCompTraceAdjoint ℓ fbar i t₁) := by
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
  have hne : e₀ ≠ 0 := fun h0 ↦ mk₀_comp_ne_zero_of_iso (DerivedCategory.Plus.ι.mapIso κ.symm) ht₁
    (by rw [← he₀, h0, Ext.zero_hom] : t₂ = 0)
  exact isIso_homEquiv_directImageInverseImageAdj_of_ne_zero ℓ (i ≫ fbar) e₀ hne

/-- The adjoint of a degree-zero trace on `Rf̄_*(i_* Λ_Z)`: for `τ : Rf̄_*(i_* Λ_Z) ⟶ Λ`, the
adjoint `τ♭ : Λ_Z ⟶ π⁻¹ Λ` of the trace `τ ∘ Rf̄_*(Ri_*(Λ_Z) ≅ i_* Λ_Z)` on `Rf̄_*(Ri_*(Λ_Z))`. -/
def boundaryTraceAdjoint
    (τ : ShiftedHom ((etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar ⋙
        DerivedCategory.Plus.ι).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := Z) ℓ))))
        ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)) (0 : ℤ)) :
    unitSheaf (X := Z) ℓ ⟶
      (etaleModuleInverseImage.{u, 0} (ZMod ℓ) (i ≫ fbar)).obj (unitSheaf (X := S) ℓ) :=
  letI := etaleModules_enoughInjectives.{u, 0} (ZMod ℓ) Z
  derivedDirectImageCompTraceAdjoint ℓ fbar i ((ShiftedHom.mk₀ (0 : ℤ) rfl
    ((etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar ⋙ DerivedCategory.Plus.ι).map
      (HomologicalDuality.degreeZeroIso (etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) i)
        (isLE_derivedDirectImage_single_of_isIntegralHom ℓ i)
        (isGE_derivedDirectImage_single_of_isIntegralHom ℓ i)
        (etaleModuleDirectImage.{u, 0} (ZMod ℓ) i)
        (derivedDirectImageTopHomologyIsoOfIsIntegralHom ℓ i) (unitSheaf (X := Z) ℓ)).hom)).comp
    τ (add_zero 0))

/-- On an irreducible `Z`, a nonzero degree-zero trace `τ : Rf̄_*(i_* Λ_Z) ⟶ Λ` has invertible
adjoint. -/
theorem isIso_boundaryTraceAdjoint_of_ne_zero [IrreducibleSpace Z]
    (τ : ShiftedHom ((etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar ⋙
        DerivedCategory.Plus.ι).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := Z) ℓ))))
        ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)) (0 : ℤ)) (hτ : τ ≠ 0) :
    IsIso (boundaryTraceAdjoint ℓ fbar i τ) := by
  let := etaleModules_enoughInjectives.{u, 0} (ZMod ℓ) Z
  let κ := HomologicalDuality.degreeZeroIso (etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) i)
    (isLE_derivedDirectImage_single_of_isIntegralHom ℓ i)
    (isGE_derivedDirectImage_single_of_isIntegralHom ℓ i)
    (etaleModuleDirectImage.{u, 0} (ZMod ℓ) i) (derivedDirectImageTopHomologyIsoOfIsIntegralHom ℓ i)
    (unitSheaf (X := Z) ℓ)
  let t := (ShiftedHom.mk₀ (0 : ℤ) rfl ((etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar ⋙
    DerivedCategory.Plus.ι).map κ.hom)).comp τ (add_zero 0)
  exact isIso_derivedDirectImageCompTraceAdjoint_of_ne_zero ℓ fbar i t
    (mk₀_comp_ne_zero_of_iso ((etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar ⋙
      DerivedCategory.Plus.ι).mapIso κ) hτ)

/-- The trace map of `Rf̄_*` at `i_* Λ_Z` is bijective on the classes `i_* y` for a degree-zero
trace `τ : Rf̄_*(i_* Λ_Z) ⟶ Λ` whose adjoint `boundaryTraceAdjoint` is invertible. -/
theorem bijective_traceMap_directImage_extPlus_mapExactFunctor
    (τ : ShiftedHom ((etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar ⋙
        DerivedCategory.Plus.ι).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := Z) ℓ))))
        ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)) (0 : ℤ))
    (hτ : IsIso (boundaryTraceAdjoint ℓ fbar i τ)) (q : ℕ) {c : ℤ} (h : 0 + (q : ℤ) = c) :
    Function.Bijective (fun y : Ext (unitSheaf (X := Z) ℓ) (unitSheaf (X := Z) ℓ) q =>
      traceMap (etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar ⋙ DerivedCategory.Plus.ι) τ
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := Z) ℓ))) q c h
        (Stacks.TopTruncationExt.extPlus
          (y.mapExactFunctor (etaleModuleDirectImage.{u, 0} (ZMod ℓ) i) : Ext _ _ q))) := by
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
    (M := unitSheaf (X := Z) ℓ) t q h
  have hS2 := bijective_traceMap_derivedDirectImageComp_extPlus ℓ fbar i t hτ q h
  have hfac : (fun y : Ext (unitSheaf (X := Z) ℓ) (unitSheaf (X := Z) ℓ) q ↦
      traceMap ((etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) i ⋙
        etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar) ⋙ DerivedCategory.Plus.ι) t
          ((DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := Z) ℓ)) q c h
          (Stacks.TopTruncationExt.extPlus y)) =
      (fun x ↦ (ShiftedHom.mk₀ (0 : ℤ) rfl ((etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar ⋙
        DerivedCategory.Plus.ι).map κ.hom)).comp x (add_zero c)) ∘
      (fun y : Ext (unitSheaf (X := Z) ℓ) (unitSheaf (X := Z) ℓ) q ↦
        traceMap (etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar ⋙ DerivedCategory.Plus.ι) τ
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := Z) ℓ))) q c h
          (Stacks.TopTruncationExt.extPlus
            (y.mapExactFunctor (etaleModuleDirectImage.{u, 0} (ZMod ℓ) i) : Ext _ _ q))) := by
    funext y
    simp only [Function.comp_apply]
    rw [← htτ, ← hF y]
    simp only [traceMap_apply, ShiftedHom.comp_map]
  rw [hfac] at hS2
  exact (Function.Bijective.of_comp_iff' (bijective_mk₀_comp_of_iso
    ((etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar ⋙ DerivedCategory.Plus.ι).mapIso κ) c)
    _).1 hS2

/-- The adjoint of the Gysin trace of a class `γ ∈ Ext²_X̄(i_* Λ_Z, f̄⁻¹ Λ)` and a trace
`t : Rf̄_*(f̄⁻¹ Λ) ⟶ Λ[-2]`: the adjoint `τ♭ : Λ_Z ⟶ π⁻¹ Λ` of the morphism `π_* Λ_Z ⟶ Λ`
underlying the Gysin trace `t ∘ Rf̄_*(γ) : Rf̄_*(i_* Λ_Z) ⟶ Λ`. -/
def boundaryGysinTraceAdjoint
    (γ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := Z) ℓ))
      ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) fbar).obj (unitSheaf (X := S) ℓ)) 2)
    (t : ShiftedHom ((etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar ⋙
        DerivedCategory.Plus.ι).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) fbar).obj (unitSheaf (X := S) ℓ))))
        ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)) (-2)) :
    unitSheaf (X := Z) ℓ ⟶
      (etaleModuleInverseImage.{u, 0} (ZMod ℓ) (i ≫ fbar)).obj (unitSheaf (X := S) ℓ) :=
  boundaryTraceAdjoint ℓ fbar i (((Stacks.TopTruncationExt.extPlus γ).map
    (etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar ⋙ DerivedCategory.Plus.ι)).comp t
      (by norm_num : (-2 : ℤ) + ((2 : ℕ) : ℤ) = 0))

/-- On an irreducible `Z`, a nonzero Gysin trace has invertible adjoint. -/
theorem isIso_boundaryGysinTraceAdjoint_of_ne_zero [IrreducibleSpace Z]
    (γ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := Z) ℓ))
      ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) fbar).obj (unitSheaf (X := S) ℓ)) 2)
    (t : ShiftedHom ((etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar ⋙
        DerivedCategory.Plus.ι).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) fbar).obj (unitSheaf (X := S) ℓ))))
        ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)) (-2))
    (hτ : ((Stacks.TopTruncationExt.extPlus γ).map (etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ)
      fbar ⋙ DerivedCategory.Plus.ι)).comp t (by norm_num : (-2 : ℤ) + ((2 : ℕ) : ℤ) = 0) ≠ 0) :
    IsIso (boundaryGysinTraceAdjoint ℓ fbar i γ t) :=
  isIso_boundaryTraceAdjoint_of_ne_zero ℓ fbar i _ hτ

/-- For a purity class `γ ∈ Ext²_X̄(i_* Λ_Z, f̄⁻¹ Λ)` and a trace `t : Rf̄_*(f̄⁻¹ Λ) ⟶ Λ[-2]` whose
Gysin trace `t ∘ Rf̄_*(γ)` has invertible adjoint `boundaryGysinTraceAdjoint`, the trace map of `t`
at `i_* Λ_Z` is bijective in degree `q + 2`. -/
theorem bijective_traceMap_directImage_of_isPurityClass
    (γ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := Z) ℓ))
      ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) fbar).obj (unitSheaf (X := S) ℓ)) 2)
    (hγ : IsPurityClass i _ γ)
    (t : ShiftedHom ((etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar ⋙
        DerivedCategory.Plus.ι).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) fbar).obj (unitSheaf (X := S) ℓ))))
        ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)) (-2))
    (hτ : IsIso (boundaryGysinTraceAdjoint ℓ fbar i γ t))
    (q : ℕ) {c : ℤ} (h : -2 + ((q + 2 : ℕ) : ℤ) = c) :
    Function.Bijective (traceMap (etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar ⋙
      DerivedCategory.Plus.ι) t ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := Z) ℓ)))
      ((q + 2 : ℕ) : ℤ) c h) := by
  have hβ : Function.Bijective (fun y : Ext (unitSheaf (X := Z) ℓ) (unitSheaf (X := Z) ℓ) q ↦
      Stacks.TopTruncationExt.extPlus ((y.mapExactFunctor
        (etaleModuleDirectImage.{u, 0} (ZMod ℓ) i)).comp γ (rfl : q + 2 = q + 2))) :=
    (HomologicalDuality.extPlus_bijective _ _ (q + 2)).comp (hγ.1 (unitSheaf (X := Z) ℓ) q)
  rw [← Function.Bijective.of_comp_iff _ hβ]
  have hc0 : (-2 : ℤ) + ((2 : ℕ) : ℤ) = 0 := by norm_num
  have e : ⇑(traceMap (etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar ⋙
      DerivedCategory.Plus.ι) t ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := Z) ℓ)))
      ((q + 2 : ℕ) : ℤ) c h) ∘ (fun y : Ext (unitSheaf (X := Z) ℓ) (unitSheaf (X := Z) ℓ) q ↦
        Stacks.TopTruncationExt.extPlus ((y.mapExactFunctor
          (etaleModuleDirectImage.{u, 0} (ZMod ℓ) i)).comp γ (rfl : q + 2 = q + 2))) =
      (fun y : Ext (unitSheaf (X := Z) ℓ) (unitSheaf (X := Z) ℓ) q ↦
        traceMap (etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar ⋙ DerivedCategory.Plus.ι)
          (((Stacks.TopTruncationExt.extPlus γ).map (etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ)
            fbar ⋙ DerivedCategory.Plus.ι)).comp t hc0)
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := Z) ℓ))) q c
          (by omega) (Stacks.TopTruncationExt.extPlus
            (y.mapExactFunctor (etaleModuleDirectImage.{u, 0} (ZMod ℓ) i) : Ext _ _ q))) := by
    funext y
    simp only [Function.comp_apply]
    rw [Stacks.TopTruncationExt.extPlus_comp]
    exact traceMap_comp_shiftedHom t _ hc0 _ _ h _ _
  rw [e]
  exact bijective_traceMap_directImage_extPlus_mapExactFunctor ℓ fbar i _ hτ q _

/-- For a purity class `γ ∈ Ext²_X̄(i_* Λ_Z, f̄⁻¹ Λ)` and a trace `t : Rf̄_*(f̄⁻¹ Λ) ⟶ Λ[-2]` such
that the adjoint `boundaryGysinTraceAdjoint` of the Gysin trace `t ∘ Rf̄_*(γ)` is invertible, the
trace map `Hom_X̄(i_* Λ_Z, f̄⁻¹ Λ[m]) → Hom_S(Rf̄_* i_* Λ_Z, Λ[m - 2])` is bijective for every `m`.
-/
theorem isBijectiveAt_directImage_of_isPurityClass
    (γ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := Z) ℓ))
      ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) fbar).obj (unitSheaf (X := S) ℓ)) 2)
    (hγ : IsPurityClass i _ γ)
    (t : ShiftedHom ((etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar ⋙
        DerivedCategory.Plus.ι).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) fbar).obj (unitSheaf (X := S) ℓ))))
        ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)) (-2))
    (hτ : IsIso (boundaryGysinTraceAdjoint ℓ fbar i γ t)) :
    IsBijectiveAt (etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar ⋙ DerivedCategory.Plus.ι) t
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := Z) ℓ))) := by
  intro m c h
  rcases lt_or_ge m 2 with hm | hm
  · have : Subsingleton (ShiftedHom ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := Z) ℓ)))
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) fbar).obj (unitSheaf (X := S) ℓ))) m) := by
      rcases lt_or_ge m 0 with hm0 | hm0
      · exact HomologicalDuality.subsingleton_hom_single_shift_of_neg _ _ hm0
      · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hm0
        have := hγ.2 (unitSheaf (X := Z) ℓ) n (by omega)
        exact (Equiv.ofBijective _ (HomologicalDuality.extPlus_bijective _ _ n)).symm.subsingleton
    have : Subsingleton (ShiftedHom ((etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar ⋙
        DerivedCategory.Plus.ι).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := Z) ℓ))))
        ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)) c) := by
      have hK : DerivedCategory.TStructure.t.IsLE ((etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ)
          fbar ⋙ DerivedCategory.Plus.ι).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := Z) ℓ)))) 0 := by
        refine (DerivedCategory.isLE_iff _ 0).2 fun p hp ↦ ?_
        exact (isZero_singleHomology_directImage_of_isFinite (ZMod ℓ) i fbar _ p (by omega)).of_iso
          ((singleHomologyPlusSingleIso (etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar)
            p).app _).symm
      have hL : DerivedCategory.TStructure.t.IsGE
          (((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ))⟦c⟧) (-c) :=
        DerivedCategory.TStructure.t.isGE_shift _ 0 c (-c) (by omega)
      exact ⟨fun u v ↦ by
        rw [DerivedCategory.TStructure.t.zero_of_isLE_of_isGE u 0 (-c) (by omega) hK hL,
          DerivedCategory.TStructure.t.zero_of_isLE_of_isGE v 0 (-c) (by omega) hK hL]⟩
    exact HomologicalDuality.bijective_of_subsingleton _ 0
  · obtain ⟨q, rfl⟩ : ∃ q : ℕ, m = ((q + 2 : ℕ) : ℤ) := ⟨(m - 2).toNat, by omega⟩
    exact bijective_traceMap_directImage_of_isPurityClass ℓ fbar i γ hγ t hτ q h

end Boundary


/-! ### The boundary-divisor input of relative duality -/

section Inputs

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [IsAlgClosed k]

/-- Global purity along the étale boundary divisor: in the setting of
`Stacks.EtaleCohomology.BoundaryDivisorDualityInput` (`X̄` smooth of dimension `e + 1` over `k`,
`Z ⊆ X̄` closed and étale over the `e`-dimensional `S`), there is a purity class
`γ ∈ Ext²_X̄(i_* Λ_Z, f̄⁻¹ Λ)`. -/
def BoundaryDivisorPurityInput : Prop :=
  IsUnit (ℓ : k) → ∀ (S Xbar Z : Scheme.{u}) (q : S ⟶ Spec (.of k)) (e : ℕ)
    [SmoothOfRelativeDimension e q] [IsAffine S] (fbar : Xbar ⟶ S) (i : Z ⟶ Xbar)
    [SmoothOfRelativeDimension 1 fbar] [GeometricallyIrreducible fbar] [IsClosedImmersion i]
    [IsFinite (i ≫ fbar)] [Etale (i ≫ fbar)], IsProjectiveMorphism fbar →
    ∃ γ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := Z) ℓ))
        ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) fbar).obj (unitSheaf (X := S) ℓ)) 2,
      IsPurityClass i _ γ

/-- In the setting of `Stacks.EtaleCohomology.BoundaryDivisorDualityInput`, for every purity class
`γ ∈ Ext²_X̄(i_* Λ_Z, f̄⁻¹ Λ)` and every trace `t : Rf̄_* Λ ⟶ Λ[-2]` inducing an isomorphism on
`H²`, the adjoint `boundaryGysinTraceAdjoint` of the Gysin trace `t ∘ Rf̄_*(γ) : π_* Λ_Z ⟶ Λ` is an
isomorphism. -/
def BoundaryDivisorGysinTraceInput : Prop :=
  IsUnit (ℓ : k) → ∀ (S Xbar Z : Scheme.{u}) (q : S ⟶ Spec (.of k)) (e : ℕ)
    [SmoothOfRelativeDimension e q] [IsAffine S] (fbar : Xbar ⟶ S) (i : Z ⟶ Xbar)
    [SmoothOfRelativeDimension 1 fbar] [GeometricallyIrreducible fbar] [IsClosedImmersion i]
    [IsFinite (i ≫ fbar)] [Etale (i ≫ fbar)], IsProjectiveMorphism fbar →
    ∀ γ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := Z) ℓ))
        ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) fbar).obj (unitSheaf (X := S) ℓ)) 2,
      IsPurityClass i _ γ →
    ∀ t : ShiftedHom ((etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar ⋙
        DerivedCategory.Plus.ι).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) fbar).obj (unitSheaf (X := S) ℓ))))
        ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)) (-2),
      IsIso ((DerivedCategory.homologyFunctor _ 2).map t) →
      IsIso (boundaryGysinTraceAdjoint ℓ fbar i γ t)

omit [IsAlgClosed k] in
/-- The boundary-divisor input of relative duality follows from global purity along the boundary
divisor and the invertibility of the adjoint of the Gysin trace. -/
theorem boundaryDivisorDualityInput_of_inputs (hP : BoundaryDivisorPurityInput ℓ k)
    (hG : BoundaryDivisorGysinTraceInput ℓ k) : BoundaryDivisorDualityInput ℓ k := by
  intro hℓ S Xbar Z q e _ _ fbar i _ _ _ _ _ hproj t ht
  obtain ⟨γ, hγ⟩ := hP hℓ S Xbar Z q e fbar i hproj
  have H := isBijectiveAt_directImage_of_isPurityClass ℓ fbar i γ hγ t
    (hG hℓ S Xbar Z q e fbar i hproj γ hγ t ht)
  let eZ : (etaleModuleInverseImage.{u, 0} (ZMod ℓ) i).obj
      ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) fbar).obj (unitSheaf (X := S) ℓ)) ≅
      unitSheaf (X := Z) ℓ :=
    (etaleModuleInverseImage.{u, 0} (ZMod ℓ) i).mapIso
        ((etaleModuleInverseImageConstantIso.{u, 0} (ZMod ℓ) fbar).app
          (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ)))) ≪≫
      (etaleModuleInverseImageConstantIso.{u, 0} (ZMod ℓ) i).app
        (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ)))
  exact isBijectiveAt_of_iso ((DerivedCategory.Plus.singleFunctor _ 0).mapIso
    ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).mapIso eZ.symm)) H

end Inputs

end Stacks.EtaleCohomology

end
