module

public import StacksFrontier.RingTheory.TateMap.DetNLBaseChangeComp
public import StacksFrontier.RingTheory.TateMap.DualizingBaseChange

/-!
# Pulling back an isomorphism `det(NL_{B/A}) ≅ ω_{B/A}` along a chart base change

For a chart base change `D` from `A → B` to `A' → B'` and a `B`-linear isomorphism
`e : det(NL_{B/A}) ≅ ω_{B/A}`, the pulled-back isomorphism `det(NL_{B'/A'}) ≅ ω_{B'/A'}` is
`B' ⊗_B e` read through the base-change isomorphisms of the determinant of the naive cotangent
complex and of the relative dualizing module. This is the affine form of `b^* c` in the proof of
Stacks 0FKD.

## Main definitions

* `Stacks.TateMap.pullbackTate D e G`: the pulled-back isomorphism.

## Main results

* `Stacks.TateMap.pullbackTate_deltaNL`: if `e` carries `δ` to `τ`, so does its pullback.
* `Stacks.TateMap.pullbackTate_congr`: the pullback does not depend on the localization datum.
* `Stacks.TateMap.pullbackTate_refl`, `Stacks.TateMap.pullbackTate_comp`: functoriality.
* `Stacks.TateMap.eq_pullbackTate`: the pullback is characterized by its values on `1 ⊗ x`.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open Stacks.Discriminant

universe u

namespace Stacks.TateMap

section Pullback

variable {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
  [Algebra A B] [Algebra A A'] [Algebra A' B'] [Algebra B B']
  [Algebra.Syntomic A B] [Algebra.Syntomic A' B'] [IsNoetherianRing A] [IsNoetherianRing A']

/-- The pullback of an isomorphism `det(NL_{B/A}) ≅ ω_{B/A}` along a chart base change. -/
def pullbackTate (D : ChartBaseChange A B A' B') {F : FiniteOpenFactorization.{u, u, u} A B}
    (e : detNL A B ≃ₗ[B] dualizingModule F) (G : FiniteOpenFactorization.{u, u, u} A' B') :
    detNL A' B' ≃ₗ[B'] dualizingModule G :=
  (detNLBaseChange D).symm ≪≫ₗ e.baseChange B B' _ _ ≪≫ₗ omegaBaseChange D F G

variable (D : ChartBaseChange A B A' B') {F : FiniteOpenFactorization.{u, u, u} A B}
  (e : detNL A B ≃ₗ[B] dualizingModule F) (G : FiniteOpenFactorization.{u, u, u} A' B')

theorem pullbackTate_detNLBaseChange (x : B' ⊗[B] detNL A B) :
    pullbackTate D e G (detNLBaseChange D x) =
      omegaBaseChange D F G (e.baseChange B B' _ _ x) := by
  simp [pullbackTate]

theorem pullbackTate_detNLBaseChange_one_tmul (x : detNL A B) :
    pullbackTate D e G (detNLBaseChange D (1 ⊗ₜ x)) = omegaBaseChange D F G (1 ⊗ₜ e x) := by
  rw [pullbackTate_detNLBaseChange, LinearEquiv.baseChange_tmul]

/-- **The pullback is characterized by its values on `1 ⊗ x`.** -/
theorem eq_pullbackTate (φ : detNL A' B' ≃ₗ[B'] dualizingModule G)
    (hφ : ∀ x : detNL A B, φ (detNLBaseChange D (1 ⊗ₜ x)) = omegaBaseChange D F G (1 ⊗ₜ e x)) :
    φ = pullbackTate D e G := by
  have key : ∀ z : B' ⊗[B] detNL A B,
      φ (detNLBaseChange D z) = pullbackTate D e G (detNLBaseChange D z) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | add z w hz hw => rw [map_add, map_add, map_add, hz, hw]
    | tmul b' x =>
      have h : (b' ⊗ₜ x : B' ⊗[B] detNL A B) = b' • (1 ⊗ₜ x) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [h, map_smul, map_smul, map_smul, hφ, pullbackTate_detNLBaseChange_one_tmul]
  refine LinearEquiv.ext fun y ↦ ?_
  obtain ⟨z, rfl⟩ := (detNLBaseChange D).surjective y
  exact key z

/-- If `e` carries `δ(NL_{B/A})` to `τ_{B/A}`, its pullback carries `δ(NL_{B'/A'})` to
`τ_{B'/A'}`. -/
theorem pullbackTate_deltaNL [Algebra.QuasiFinite A B] [Algebra.QuasiFinite A' B']
    [IsNoetherianRing B] [IsNoetherianRing B']
    (he : e (deltaNL A B) = dualizingModule.traceElement F) :
    pullbackTate D e G (deltaNL A' B') = dualizingModule.traceElement G := by
  rw [← detNLBaseChange_delta D, pullbackTate_detNLBaseChange_one_tmul, he,
    omegaBaseChange_traceElement]

/-- The pullback does not depend on the localization datum of the chart base change. -/
theorem pullbackTate_congr (D' : ChartBaseChange A B A' B') :
    pullbackTate D e G = pullbackTate D' e G := by
  simp only [pullbackTate, detNLBaseChange_congr D D', omegaBaseChange_congr D D' F G]

/-- The pullback does not depend on the factorizations computing the dualizing modules. -/
theorem pullbackTate_natural_right (G' : FiniteOpenFactorization.{u, u, u} A' B') :
    pullbackTate D e G ≪≫ₗ dualizingModuleEquiv G G' = pullbackTate D e G' := by
  refine LinearEquiv.ext fun y ↦ ?_
  simp only [pullbackTate, LinearEquiv.trans_apply, omegaBaseChange_natural_right]

/-- The pullback does not depend on the factorization computing the source dualizing module. -/
theorem pullbackTate_natural_left {F' : FiniteOpenFactorization.{u, u, u} A B} :
    pullbackTate D (e ≪≫ₗ dualizingModuleEquiv F F') G = pullbackTate D e G := by
  refine eq_pullbackTate D e G _ fun x ↦ ?_
  rw [pullbackTate_detNLBaseChange_one_tmul, LinearEquiv.trans_apply,
    omegaBaseChange_one_tmul_natural_left]

end Pullback

/-- **The pullback along the identity.** -/
theorem pullbackTate_refl {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.Syntomic A B] [IsNoetherianRing A] (D : ChartBaseChange A B A B)
    {F : FiniteOpenFactorization.{u, u, u} A B} (e : detNL A B ≃ₗ[B] dualizingModule F)
    (G : FiniteOpenFactorization.{u, u, u} A B) :
    pullbackTate D e G = e ≪≫ₗ dualizingModuleEquiv F G := by
  refine (eq_pullbackTate D e G _ fun x ↦ ?_).symm
  rw [detNLBaseChange_refl, omegaBaseChange_refl]
  simp

/-- **The pullback along a composite.** -/
theorem pullbackTate_comp {A B A' B' A'' B'' : Type u} [CommRing A] [CommRing B]
    [CommRing A'] [CommRing B'] [CommRing A''] [CommRing B''] [Algebra A B] [Algebra A A']
    [Algebra A' B'] [Algebra B B'] [Algebra A' A''] [Algebra B' B''] [Algebra A A'']
    [Algebra B B''] [Algebra A'' B''] [IsScalarTower A A' A''] [IsScalarTower B B' B'']
    [IsNoetherianRing A] [IsNoetherianRing A'] [IsNoetherianRing A'']
    [Algebra.Syntomic A B] [Algebra.Syntomic A' B'] [Algebra.Syntomic A'' B'']
    (D₁ : ChartBaseChange A B A' B') (D₂ : ChartBaseChange A' B' A'' B'')
    (D₃ : ChartBaseChange A B A'' B'') {F : FiniteOpenFactorization.{u, u, u} A B}
    (e : detNL A B ≃ₗ[B] dualizingModule F) (G : FiniteOpenFactorization.{u, u, u} A' B')
    (H : FiniteOpenFactorization.{u, u, u} A'' B'') :
    pullbackTate D₃ e H = pullbackTate D₂ (pullbackTate D₁ e G) H := by
  refine (eq_pullbackTate D₃ e H _ fun x ↦ ?_).symm
  rw [detNLBaseChange_comp D₁ D₂ D₃, omegaBaseChange_comp D₁ D₂ D₃ F G H]
  simp only [LinearEquiv.trans_apply,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearEquiv.baseChange_tmul,
    pullbackTate_detNLBaseChange_one_tmul]

/-- **Pullbacks around a square of chart base changes agree.** If `A → B` goes to `A' → B'` by
`D` and to `A → B₀` by `D₁`, and both `A' → B'` (by `D₂`) and `A → B₀` (by `D₃`) go on to
`A' → B''`, compatibly with the maps `B → B''`, then pulling back along `D` then `D₂` is the same
as pulling back along `D₁` then `D₃`. -/
theorem pullbackTate_square {A B A' B' B₀ B'' : Type u} [CommRing A] [CommRing B] [CommRing A']
    [CommRing B'] [CommRing B₀] [CommRing B''] [Algebra A B] [Algebra A A'] [Algebra A' B']
    [Algebra B B'] [Algebra B B₀] [Algebra A B₀] [Algebra B' B''] [Algebra A' B'']
    [Algebra B₀ B''] [Algebra B B''] [IsScalarTower B B' B''] [IsScalarTower B B₀ B'']
    [IsNoetherianRing A] [IsNoetherianRing A']
    [Algebra.Syntomic A B] [Algebra.Syntomic A' B'] [Algebra.Syntomic A B₀]
    [Algebra.Syntomic A' B'']
    (D : ChartBaseChange A B A' B') (D₁ : ChartBaseChange A B A B₀)
    (D₂ : ChartBaseChange A' B' A' B'') (D₃ : ChartBaseChange A B₀ A' B'')
    {F : FiniteOpenFactorization.{u, u, u} A B} (e : detNL A B ≃ₗ[B] dualizingModule F)
    (G : FiniteOpenFactorization.{u, u, u} A' B') (G₀ : FiniteOpenFactorization.{u, u, u} A B₀)
    (G'' : FiniteOpenFactorization.{u, u, u} A' B'') :
    pullbackTate D₂ (pullbackTate D e G) G'' = pullbackTate D₃ (pullbackTate D₁ e G₀) G'' := by
  rw [← pullbackTate_comp D D₂ (D₂.comp D), ← pullbackTate_comp D₁ D₃ (D₂.comp D)]

end Stacks.TateMap
