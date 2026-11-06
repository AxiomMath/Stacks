/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotHilbertPolynomialSurjection

/-!
# `Quot^P` depends on the module only up to isomorphism

Let `F/X/B` be a Quot situation and `φ : F ⟶ G` an isomorphism of quasi-coherent `𝒪_X`-modules.
The inclusion `Quot_{G/X/B} ⟶ Quot_{F/X/B}` of Stacks 0DP5, sending `G_T ⟶ 𝒬` to
`F_T ⟶ G_T ⟶ 𝒬`, is then bijective: every quotient of `F_T` kills the (zero) kernel of `φ`, so
comes from `G_T`. It preserves the Hilbert polynomial, so it restricts to an isomorphism
`Quot^{P, L}_{G/X/B} ≅ Quot^{P, L}_{F/X/B}` over `B`.

This is the transport, along an isomorphism of modules, used in the proof of Stacks 0DPD.

## Main results

* `AlgebraicGeometry.Space.QuotSituation.hilbertPolynomialQuotWithModuleIso`.
* `AlgebraicGeometry.Space.QuotSituation.hilbertPolynomialQuotWithModuleIso_hom_comp_toBase`.

## References

* [Stacks Project, Tag 0DP5](https://stacks.math.columbia.edu/tag/0DP5)
* [Stacks Project, Tag 0DPD](https://stacks.math.columbia.edu/tag/0DPD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space.QuotSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (D : QuotSituation B S hS)
  {G : Modules.{u, u} B S hS D.X.1 D.X.2} {hG : G.IsQuasicoherentOnSite} (φ : D.F ⟶ G) [IsIso φ]
  (L : Modules.{u, u} B S hS D.X.1 D.X.2)
  [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.X.1)
    ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).property L]
  (P : ℤ → ℤ)

/-- Along an isomorphism `φ : F ⟶ G`, every member of `Quot_{F/X/B}(T)` comes from a member of
`Quot_{G/X/B}(T)`: it kills the kernel of `φ`, which is zero. -/
theorem exists_quotientSubobject_eq_of_isIso {T : SchemesOver D.Y}
    {K : Subobject (D.baseChangeModule T)} (hK : K ∈ D.properlySupportedQuotients T) :
    ∃ L : Subobject ((D.withModule G hG).baseChangeModule T),
      L ∈ (D.withModule G hG).properlySupportedQuotients T ∧ D.quotientSubobject φ T L = K := by
  refine (D.exists_quotientSubobject_eq_iff (hG := hG) φ hK).2 ?_
  have hI : IsIso ((modulePullback B S hS (D.sourceProjection T)).map φ) :=
    Functor.map_isIso _ φ
  have hM : Mono ((modulePullback B S hS (D.sourceProjection T)).map φ) :=
    @IsIso.mono_of_iso _ _ _ _ _ hI
  have h1 : (modulePullback B S hS (D.sourceProjection T)).map (kernel.ι φ) = 0 :=
    (@cancel_mono _ _ _ _ _ ((modulePullback B S hS (D.sourceProjection T)).map φ) hM _ _).1
      ((D.map_kernel_ι_comp_baseChangeModuleMap φ T).trans (zero_comp).symm)
  rw [h1, zero_comp]

/-- Along an isomorphism `φ : F ⟶ G`, every quotient of `F_T` comes from `G_T`. -/
theorem exists_inclusionFamily_eq_of_isIso {T : BigFppfOver B S hS} (y : QuotFamilyOver D T) :
    ∃ x : QuotFamilyOver (D.withModule G hG) T, D.inclusionFamily φ x = y := by
  obtain ⟨b, K, hK⟩ := y
  obtain ⟨L, hL, hLK⟩ := D.exists_quotientSubobject_eq_of_isIso (hG := hG) φ hK
  refine ⟨⟨b, L, hL⟩, QuotFamilyOver.ext rfl (heq_of_eq ?_)⟩
  dsimp only [inclusionFamily]
  exact hLK

/-- **`Quot^{P, L}_{G/X/B} ≅ Quot^{P, L}_{F/X/B}`** for an isomorphism `φ : F ⟶ G`, through the
inclusion of Stacks 0DP5. -/
def hilbertPolynomialQuotWithModuleIso :
    ((D.withModule G hG).hilbertPolynomialQuot L P).toFunctor ≅
      (D.hilbertPolynomialQuot L P).toFunctor :=
  @asIso _ _ _ _ (Subfunctor.lift (((D.withModule G hG).hilbertPolynomialQuot L P).ι ≫
      D.quotSiteInclusion φ) (by
        rintro T _ ⟨x, rfl⟩
        exact (D.mem_hilbertPolynomialQuot_withModule_iff φ L P x.1).1 x.2)) (by
    rw [NatTrans.isIso_iff_isIso_app]
    intro T
    rw [isIso_iff_bijective]
    refine ⟨fun x x' h => Subtype.ext (D.quotSiteInclusion_injective φ T
      (congrArg Subtype.val h)), fun y => ?_⟩
    obtain ⟨x, hx⟩ := D.exists_inclusionFamily_eq_of_isIso φ y.1
    have hy : (D.quotSiteInclusion φ).app T x ∈ (D.hilbertPolynomialQuot L P).obj T := by
      change D.inclusionFamily φ x ∈ _
      rw [hx]
      exact y.2
    exact ⟨⟨x, (D.mem_hilbertPolynomialQuot_withModule_iff φ L P x).2 hy⟩, Subtype.ext hx⟩)

/-- The isomorphism `Quot^{P, L}_{G/X/B} ≅ Quot^{P, L}_{F/X/B}` is an isomorphism over `B`. -/
theorem hilbertPolynomialQuotWithModuleIso_hom_comp_toBase :
    (D.hilbertPolynomialQuotWithModuleIso φ L P).hom ≫ (D.hilbertPolynomialQuot L P).ι ≫
        D.quotSitePresheafToBase =
      ((D.withModule G hG).hilbertPolynomialQuot L P).ι ≫
        (D.withModule G hG).quotSitePresheafToBase := by
  ext T x
  rfl

end AlgebraicGeometry.Space.QuotSituation

end
