module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.RestrictScalarsRepCurveRoots
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LocalTermsBasePoint
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.AffineLineProjectiveCompactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactificationChangeLinear
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonUniformInertia
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantLimitDescent

/-!
# Frobenius characteristic polynomials do not depend on the compactification

For a separated morphism `f : X ⟶ Spec k` of finite type to a finite field and a coefficient
sheaf `F`, the `E`-linear Frobenius characteristic polynomial on `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` is the
same for any two compactifications of `f`. In the duality step of Laumon's purity of the Fourier
family ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH); Kedlaya, *Fourier transforms and
p-adic Weil II*, proof of Theorem 6.4) the compactification of `𝔸¹_{k'}` is arbitrary, so this
lets one use `ℙ¹_{k'}`, whose base change to `k̄'` is a smooth curve.

The compactly supported cohomology lives in the standard model of the derived category
(`HasDerivedCategory.standard`), whence the local instance.

## Main results

* `CoefficientSheaf.charpoly_rationalGeometricCompactlySupportedFrobenius_eq_of_compactification'`,
  in the namespace `Stacks.EtaleCohomology.LAdicSheaf`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale Matrix
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

section Compactification

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

variable (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  {X : B.Scheme} [IsNoetherian X.1] {k : Type u} [Field k] [Fintype k]
  (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (kbar : Type u) [Field kbar] [Algebra k kbar]
  {O : Type} [CommRing O] [Algebra ℤ_[ℓ] O] (F : LAdicSheaf.CoefficientSheaf B X ℓ O) (i : ℤ)
  (E : Type) [CommRing E] [Algebra ℚ_[ℓ] E] [Algebra O E]
  [IsLocalization (Submonoid.powers (ℓ : O)) E]
  (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

namespace LAdicSheaf.CoefficientSheaf

/-- **The `E`-linear Frobenius characteristic polynomial on `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` does not
depend on the compactification.** -/
theorem charpoly_rationalGeometricCompactlySupportedFrobenius_eq_of_compactification'
    (j₁ j₂ : CompactificationOf (Over.mk f)) :
    letI := F.rationalCohomologyModule f j₁ kbar i E
    letI := F.rationalCohomologyModule f j₂ kbar i E
    ∀ [Module.Finite E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j₁ kbar
        F.toLAdicSheaf i)]
      [Module.Finite E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j₂ kbar
        F.toLAdicSheaf i)] [Module.Free E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology
          B X ℓ f j₁ kbar F.toLAdicSheaf i)]
      [Module.Free E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j₂ kbar
        F.toLAdicSheaf i)],
    (F.rationalGeometricCompactlySupportedFrobenius f j₁ kbar i E p q hcard).charpoly =
      (F.rationalGeometricCompactlySupportedFrobenius f j₂ kbar i E p q hcard).charpoly := by
  let := F.rationalCohomologyModule f j₁ kbar i E
  let := F.rationalCohomologyModule f j₂ kbar i E
  intro _ _ _ _
  rw [← (F.rationalCompactificationLinearEquiv B ℓ f kbar i E j₁ j₂).charpoly_conj]
  congr 1
  refine LinearMap.ext fun v => ?_
  rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.coe_coe, F.rationalCompactificationLinearEquiv_frobenius B ℓ f kbar i E p q hcard,
    LinearEquiv.apply_symm_apply]

end LAdicSheaf.CoefficientSheaf

end Compactification

end Stacks.EtaleCohomology

end
