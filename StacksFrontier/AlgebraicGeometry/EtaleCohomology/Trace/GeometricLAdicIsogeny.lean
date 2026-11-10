module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicCompactSupportFunctoriality

/-!
# `Hⁱ_c(X_k̄, F ⊗ Q_ℓ)` is invariant under isogenies of ℓ-adic sheaves

Two ℓ-adic sheaves `F` and `G` with morphisms `φ : F ⟶ G`, `ψ : G ⟶ F` whose composites are
multiplication by `ℓᴺ` define the same `ℚ_ℓ`-sheaf.  Their compactly supported cohomologies
`Hⁱ_c(X_k̄, - ⊗ Q_ℓ)` are then isomorphic through `φ`, compatibly with every endomorphism of
`RΓ_c(X_k̄, -)`, in particular with the geometric Frobenius: `Hⁱ_c(φ)` and `Hⁱ_c(ψ)` compose to
multiplication by `ℓᴺ`, which is invertible on a `ℚ_ℓ`-vector space.

This is how [Tag 03V2](https://stacks.math.columbia.edu/tag/03V2) passes from a `ℚ_ℓ`-sheaf
`F ⊗ Q_ℓ` to a torsion-free model `F'` of it (the first step of the proof): `F` and its image
under a large power of `ℓ` are isogenous.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.isIso_rationalGeometricCompactlySupportedCohomologyMap`.

## References

* [Stacks Project, Tag 03V2](https://stacks.math.columbia.edu/tag/03V2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

variable {B : BigEtaleSite.{u}} {X : B.Scheme} {ℓ : ℕ}

variable [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
  ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
  HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [∀ n : ℕ, HasWeakSheafify
  (SmallEtale.topology B X.1 X.property)
  (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [IsNoetherian X.1] [Fact ℓ.Prime]

variable {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- `Hⁱ_c(X_k̄, -)` carries multiplication by `N` to multiplication by `N`. -/
theorem LAdicSheaf.geometricCompactlySupportedCohomologyMap_nsmul_id (F : LAdicSheaf B X ℓ) (i : ℤ)
    (N : ℕ) :
    LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar (N • 𝟙 F) i =
      N • 𝟙 (LAdicSheaf.geometricCompactlySupportedCohomology B X ℓ f j kbar F i) := by
  induction N with
  | zero => rw [zero_nsmul, zero_nsmul, LAdicSheaf.geometricCompactlySupportedCohomologyMap_zero]
  | succ N ih =>
    rw [succ_nsmul, succ_nsmul, LAdicSheaf.geometricCompactlySupportedCohomologyMap_add, ih,
      LAdicSheaf.geometricCompactlySupportedCohomologyMap_id]

/-- Multiplication by a nonzero integer on a `ℚ_ℓ`-module is an isomorphism. -/
theorem isIso_nsmul_id_of_rational (M : ModuleCat.{u + 1} ℚ_[ℓ]) (N : ℕ) (hN : N ≠ 0) :
    IsIso (N • 𝟙 M) := by
  have hN' : (N : ℚ_[ℓ]) ≠ 0 := Nat.cast_ne_zero.2 hN
  refine ⟨((N : ℚ_[ℓ])⁻¹) • 𝟙 M, ?_, ?_⟩
  · ext x
    change (N : ℚ_[ℓ])⁻¹ • (N • x) = x
    rw [← Nat.cast_smul_eq_nsmul ℚ_[ℓ], smul_smul, inv_mul_cancel₀ hN', one_smul]
  · ext x
    change N • ((N : ℚ_[ℓ])⁻¹ • x) = x
    rw [← Nat.cast_smul_eq_nsmul ℚ_[ℓ], smul_smul, mul_inv_cancel₀ hN', one_smul]

/-- **An isogeny of ℓ-adic sheaves induces an isomorphism on `Hⁱ_c(X_k̄, - ⊗ Q_ℓ)`.** If
`φ ≫ ψ` and `ψ ≫ φ` are multiplication by `ℓᴺ`, then `Hⁱ_c(φ) ⊗ Q_ℓ` is an isomorphism. -/
theorem LAdicSheaf.isIso_rationalGeometricCompactlySupportedCohomologyMap {F G : LAdicSheaf B X ℓ}
    (φ : F ⟶ G) (ψ : G ⟶ F) (N : ℕ) (h₁ : φ ≫ ψ = (ℓ ^ N) • 𝟙 F) (h₂ : ψ ≫ φ = (ℓ ^ N) • 𝟙 G)
    (i : ℤ) :
    IsIso ((ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
      (LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar φ i)) := by
  let E := ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])
  have : E.Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).left_adjoint_additive
  have hℓ : ℓ ^ N ≠ 0 := pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero
  have hc : ∀ {F' G' : LAdicSheaf B X ℓ} (a : F' ⟶ G') (b : G' ⟶ F'), a ≫ b = (ℓ ^ N) • 𝟙 F' →
      IsIso (E.map (LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar a i) ≫
        E.map (LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar b i)) := by
    intro F' G' a b h
    rw [← E.map_comp, ← LAdicSheaf.geometricCompactlySupportedCohomologyMap_comp, h,
      LAdicSheaf.geometricCompactlySupportedCohomologyMap_nsmul_id, E.map_nsmul, E.map_id]
    exact isIso_nsmul_id_of_rational _ _ hℓ
  have i₁ := hc φ ψ h₁
  have i₂ := hc ψ φ h₂
  have : Mono (E.map (LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar φ i)) :=
    mono_of_mono _ (E.map (LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar ψ i))
  have : Epi (E.map (LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar φ i)) :=
    epi_of_epi (E.map (LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar ψ i)) _
  exact isIso_of_mono_of_epi _

end Stacks.EtaleCohomology
