module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFourierLineAwayFibreTop

/-!
# Laumon's local theory away from `a = 0`, from the inertia half and the first direct image

`Stacks.EtaleCohomology.LaumonFourierLineAwayFibreQuotientInput` is
`Stacks.EtaleCohomology.LaumonFourierLineAwayFibreInput` with the vanishing of `H^q_c`, `q ≠ 1`,
on the geometric fibres replaced by the absence of constant simple quotients of the level zero
on the geometric fibres (`Stacks.EtaleCohomology.LaumonFourierLineAwayFibreNoConstantQuotient`).
With the curve half `Stacks.EtaleCohomology.AffineLineOpenTopCohomologyVanishingInput` it gives
`Stacks.EtaleCohomology.LaumonFourierLineAwayFibreInput`
(`Stacks.EtaleCohomology.laumonFourierLineAwayFibreInput_of_quotient`), hence the lisse transform
away from `a = 0`, `Stacks.EtaleCohomology.LaumonFourierLineLisseAwayInput`
(`Stacks.EtaleCohomology.laumonFourierLineLisseAwayInput_of_quotient`), in the proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main definitions

* `Stacks.EtaleCohomology.LaumonFourierLineAwayFibreQuotientInput`.

## Main results

* `Stacks.EtaleCohomology.laumonFourierLineAwayFibreInput_of_quotient`.
* `Stacks.EtaleCohomology.laumonFourierLineLisseAwayInput_of_quotient`.

## Implementation notes

`Stacks.EtaleCohomology.derivedLowerShriek` lives in the standard model
`HasDerivedCategory.standard` of the derived category, hence so do the statements here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale Matrix
open CategoryTheory.LAdicTower

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-- **Laumon's local theory away from `a = 0`, by the inertia half and in degree one**: under the
hypotheses of `Stacks.EtaleCohomology.LaumonFourierLineLisseInput` there is `N` such that for
`n > N` prime to `p` both `Stacks.EtaleCohomology.LaumonFourierLineAwayFibreNoConstantQuotient`
and `Stacks.EtaleCohomology.LaumonFourierLineAwayFirstLocallyConstant` hold. -/
public def LaumonFourierLineAwayFibreQuotientInput : Prop :=
  ∀ (B : BigEtaleSite.{u}) (U : B.Scheme) (ℓ : ℕ)
    [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B U.1 U.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [IsNoetherian U.1] [Fact ℓ.Prime] [ConnectedSpace U.1]
    (k : Type u) [Field k] [Fintype k] (f : U.1 ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    [IsAffine U.1] (e : U.1 ⟶ Spec (.of (Polynomial k))) [IsOpenImmersion e] [IsIso e]
    (_ : e ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) = f)
    (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar]
    [ConnectedSpace ↥(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))]
    (p n : ℕ) [Fact p.Prime] [CharP k p] (_ : Fintype.card k = p ^ n) (_ : ℓ ≠ p)
    (x : GeometricPoint U.1)
    (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {d : ℕ}
    (b : Module.Basis (Fin d) ℚ_[ℓ] E) {m : ℕ} (σ : EtaleFundamentalGroup U.1 x →* GL (Fin m) E)
    (hσ : Continuous (restrictScalarsRep b σ)) (K : Type) [Field K] [IsAlgClosed K] [Algebra E K],
    (∀ W : Submodule K (Fin m → K),
      (∀ g, ∀ v ∈ W, (σ g).val.map (algebraMap E K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤) →
    LaumonStablyAbsIrr k e x σ → (∃ ζ : E, IsPrimitiveRoot ζ p) →
    ∀ (ι' : E →+* ℂ) (β : ℤ)
    [FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j kbar
          (LAdicSheaf.representationSheaf B U x (restrictScalarsRep b σ) hσ) 1)],
    (∀ (y : closedPoints U.1) (z : ℂ),
        ((σ (geometricFrobeniusFamily f x y)).val.charpoly.map ι').IsRoot z →
        ‖z‖ = ((p ^ n : ℕ) : ℝ) ^ (((residueDegree f y.1 : ℤ) * β : ℝ) / 2)) →
    ∀ ψ : AddChar k E, ψ ≠ 1 → ∃ N : ℕ, ∀ n : ℕ, N < n → ¬ p ∣ n →
      LaumonFourierLineAwayFibreNoConstantQuotient B U ℓ k e x E b σ ψ n ∧
        LaumonFourierLineAwayFirstLocallyConstant B U ℓ k e x E b σ ψ n

/-- **The fibres and the first direct image away from `a = 0`, from the curve half, the inertia
half and the first direct image**:
`Stacks.EtaleCohomology.laumonFourierLineAwayFibreVanishing_of_halves` for each `n > N`. -/
public theorem laumonFourierLineAwayFibreInput_of_quotient
    (hC : AffineLineOpenTopCohomologyVanishingInput.{u})
    (H : LaumonFourierLineAwayFibreQuotientInput.{u}) : LaumonFourierLineAwayFibreInput.{u} := by
  intro B U ℓ _ _ _ _ _ _ k _ _ f _ _ _ _ _ e _ _ hef j kbar _ _ _ _ p q _ _ hcard hℓp x E _ _ _
    d b m σ hσ K _ _ _ hirr hstab hζ ι' β hV hpure ψ hψ
  obtain ⟨N, hN⟩ :=
    H B U ℓ k f e hef j kbar p q hcard hℓp x E b σ hσ K hirr hstab hζ ι' β hpure ψ hψ
  exact ⟨N, fun n hn hpn => ⟨laumonFourierLineAwayFibreVanishing_of_halves B U ℓ k e x E b σ ψ n
    hC (hN n hn hpn).1, (hN n hn hpn).2⟩⟩

/-- **The lisse transform away from `a = 0`, from the curve half, the inertia half and the first
direct image.** -/
public theorem laumonFourierLineLisseAwayInput_of_quotient
    (hC : AffineLineOpenTopCohomologyVanishingInput.{u})
    (H : LaumonFourierLineAwayFibreQuotientInput.{u}) : LaumonFourierLineLisseAwayInput.{u} :=
  laumonFourierLineLisseAwayInput_of_fibre (laumonFourierLineAwayFibreInput_of_quotient hC H)

end Stacks.EtaleCohomology

end
