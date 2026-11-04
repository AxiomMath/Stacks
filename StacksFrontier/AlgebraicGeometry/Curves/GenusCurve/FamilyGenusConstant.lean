module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFibreEulerCharacteristicUnconditional
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.EulerCharacteristicComparison
public import StacksFrontier.AlgebraicGeometry.Curves.LargeDegreeVanishing
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.Invertible
public import StacksFrontier.AlgebraicGeometry.Flatness.ExtendingFromOpen.OpenImmersion
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackAlgebraIso

/-!
# The genus is constant in a smooth proper family over a connected base

Let `p : Y ⟶ S` be proper and smooth over a connected scheme `S`, and let `Z₁`, `Z₂` be the base
changes of `Y` to two points `Spec K₁ ⟶ S`, `Spec K₂ ⟶ S` with values in algebraically closed
fields. If both are integral of dimension at most one, they have the same genus.

## Main results

* `AlgebraicGeometry.genus_eq_of_isPullback_of_smooth_of_isProper`: the geometric fibres of a
  smooth proper family over a connected base that are integral curves have the same genus.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

open ProperFlatFibreEulerCharacteristic in
/-- **The genus of the geometric fibres of a smooth proper family over a connected base is
constant.** -/
theorem genus_eq_of_isPullback_of_smooth_of_isProper {S Y : Scheme.{u}} [PreconnectedSpace S]
    (p : Y ⟶ S) [IsProper p] [Smooth p]
    {K₁ K₂ : Type u} [Field K₁] [IsAlgClosed K₁] [Field K₂] [IsAlgClosed K₂]
    (x₁ : Spec (.of K₁) ⟶ S) (x₂ : Spec (.of K₂) ⟶ S)
    {Z₁ Z₂ : Scheme.{u}} (q₁ : Z₁ ⟶ Y) (g₁ : Z₁ ⟶ Spec (.of K₁)) (sq₁ : IsPullback q₁ g₁ p x₁)
    (q₂ : Z₂ ⟶ Y) (g₂ : Z₂ ⟶ Spec (.of K₂)) (sq₂ : IsPullback q₂ g₂ p x₂)
    [IsProper g₁] [IsProper g₂] [IsIntegral Z₁] [IsIntegral Z₂]
    (hdim₁ : topologicalKrullDim Z₁ ≤ 1) (hdim₂ : topologicalKrullDim Z₂ ≤ 1) :
    genus g₁ = genus g₂ := by
  have hfp : FinitePresentation p := FinitePresentation.mk inferInstance inferInstance inferInstance
  let F := SheafOfModules.unit Y.ringCatSheaf
  have hF : F.IsFinitePresentation :=
    Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_unit Y
  have hflat : IsFlatOver p.toLRSHom.toShHom F := isFlatOver_unit_of_flat p
  have h₁ := chiDerivedFibre_eq_eulerSum p hfp F hF hflat K₁ x₁ q₁ g₁ sq₁
    (IsLocalRing.closedPoint K₁)
  have h₂ := chiDerivedFibre_eq_eulerSum p hfp F hF hflat K₂ x₂ q₂ g₂ sq₂
    (IsLocalRing.closedPoint K₂)
  have hc := DerivedFibreBetti.isLocallyConstant_chiDerivedFibre S _
    (perfectDerivedPushforward_of_baseChange baseChangeDerivedPushforward p hfp inferInstance F hF
      hflat)
  have heq : eulerSum K₁ g₁ ((Scheme.Modules.pullback q₁).obj F) =
      eulerSum K₂ g₂ ((Scheme.Modules.pullback q₂).obj F) := by
    rw [← h₁, ← h₂]
    exact hc.apply_eq_of_preconnectedSpace _ _
  have i₁ : (Scheme.Modules.pullback q₁).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit Z₁.ringCatSheaf :=
    Stacks.PullbackAlgebra.pullbackUnitIso q₁.toLRSHom.toShHom
  have i₂ : (Scheme.Modules.pullback q₂).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit Z₂.ringCatSheaf :=
    Stacks.PullbackAlgebra.pullbackUnitIso q₂.toLRSHom.toShHom
  rw [eulerSum_congr K₁ g₁ i₁, eulerSum_congr K₂ g₂ i₂] at heq
  have e₁ := one_sub_genus_eq_eulerCharacteristic_unit K₁ g₁ hdim₁
    (finrank_globalSections_eq_one K₁ g₁)
  have e₂ := one_sub_genus_eq_eulerCharacteristic_unit K₂ g₂ hdim₂
    (finrank_globalSections_eq_one K₂ g₂)
  have : (1 : ℤ) - genus g₁ = 1 - genus g₂ := by rwa [e₁, e₂]
  exact_mod_cast (sub_right_injective this)

end AlgebraicGeometry

end
