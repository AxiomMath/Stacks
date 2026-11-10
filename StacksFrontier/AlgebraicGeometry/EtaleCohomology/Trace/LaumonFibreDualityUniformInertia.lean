module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFibreDuality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LocalTermsSmoothGaloisProof
public import StacksFrontier.AlgebraicGeometry.Curves.AffineLineShiftFiniteEtale

/-!
# Poincaré duality on the fibres of the Fourier family from the uniform inertia at `∞`

This file proves `Stacks.EtaleCohomology.LaumonFibreDualityInput`, the duality step of Laumon's
purity of the Fourier family ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH); Kedlaya,
*Fourier transforms and p-adic Weil II*, proof of Theorem 6.4), from the uniform vanishing of the
inertia invariants at `∞` of the fibres (`Stacks.EtaleCohomology.LaumonUniformInertiaInput`).

For a fibre `G = ℱ_{Res_b(σ' ⊗ χ)}` over `k'`, the compactification `j` of `𝔸¹_{k'}` in the
statement is arbitrary. The `ℚ_ℓ`-dimension of `H¹_c` and the `E`-linear Frobenius characteristic
polynomials do not depend on it, so Poincaré duality on Frobenius roots
(`LAdicSheaf.isRoot_div_charpoly_restrictScalarsRep_contragredient`), proved at a
compactification `j₀` whose base change to `k̄` is a smooth curve, holds at `j`
(`LAdicSheaf.isRoot_div_charpoly_restrictScalarsRep_contragredient_of_compactification`).
For `𝔸¹_{k'}` one takes `j₀ = ℙ¹_{k'}`; there the inertia at `∞` has no invariants for `n > N`,
so the local terms are bounded
(`Stacks.EtaleCohomology.LAdicSheaf.exists_localTermsKilledBy_of_basePoint`, with the boundary
stalks of `Stacks.EtaleCohomology.LAdicSheaf.localTermsSmoothBoundaryStalkInput`).

The compactly supported cohomology lives in the standard model of the derived category
(`HasDerivedCategory.standard`), whence the local instance.

## Main results

All names are in the namespace `Stacks.EtaleCohomology`.

* `LAdicSheaf.finiteDimensional_rationalGeometricCompactlySupportedCohomology_of_compactification`:
  finite dimensionality of `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` does not depend on the compactification.
* `LAdicSheaf.isRoot_div_charpoly_restrictScalarsRep_contragredient_of_compactification`:
  Poincaré duality on Frobenius roots for `ℱ_{Res_b σ}` through any compactification.
* `laumonFibreDualityInput_of_uniformInertia`: `LaumonFibreDualityInput` follows from
  `LaumonUniformInertiaInput`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale Matrix
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

section Dimension

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
  {X : B.Scheme} [IsNoetherian X.1] {k : Type u} [Field k] [Finite k]
  (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- **The `ℚ_ℓ`-dimension of `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` does not depend on the compactification**:
it is finite through `j₂` when it is through `j₁`, through a third compactification mapping to
both ([Stacks, Tag 0ATU]). -/
theorem
    LAdicSheaf.finiteDimensional_rationalGeometricCompactlySupportedCohomology_of_compactification
    (j₁ j₂ : CompactificationOf (Over.mk f)) (F : LAdicSheaf B X ℓ) (i : ℤ)
    [FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j₁ kbar F i)] :
    FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j₂ kbar F i) :=
  have : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ
      f (IsCofiltered.min j₁ j₂) kbar F i) :=
    LAdicSheaf.finiteDimensional_rationalGeometricCompactlySupportedCohomology_of_hom' B ℓ f
      (IsCofiltered.minToLeft j₁ j₂) kbar F i
  LAdicSheaf.finiteDimensional_rationalGeometricCompactlySupportedCohomology_of_hom B ℓ f
    (IsCofiltered.minToRight j₁ j₂) kbar F i

end Dimension

section Roots

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1] [Fact ℓ.Prime] [ConnectedSpace X.1] (x : GeometricPoint X.1)
  (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {d : ℕ}
  (b : Module.Basis (Fin d) ℚ_[ℓ] E) {m : ℕ}
  (σ : EtaleFundamentalGroup X.1 x →* GL (Fin m) E) (hσ : Continuous (restrictScalarsRep b σ))
  {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [IsAlgClosed kbar]
  [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p] [CharP kbar p]
  (hcard : Fintype.card k = p ^ q)

/-- **Poincaré duality for `ℱ_{Res_b σ}` and `ℱ_{Res_b(σ^∨)}` on an open curve, on Frobenius
roots, through any compactification.** If some compactification `j₀` of `X` has `X̄_k̄` a smooth
curve and the local terms of `ℱ_{Res_b σ}` at its boundary killed by `ℓ ^ K`, `X` is nonempty,
`ℓ ≠ p`, and `H¹_c(X_k̄, ℱ_{Res_b σ} ⊗ ℚ_ℓ)` computed through a compactification `j` is finite
dimensional, then so is `H¹_c(X_k̄, ℱ_{Res_b(σ^∨)} ⊗ ℚ_ℓ)` through `j`, and for every
`ι : E →+* ℂ` every root `z` along `ι` of the `E`-linear Frobenius characteristic polynomial of
the first is nonzero, with `q / z` a root of that of the second. Neither the dimensions nor the
characteristic polynomials depend on the compactification. -/
theorem LAdicSheaf.isRoot_div_charpoly_restrictScalarsRep_contragredient_of_compactification
    [Algebra.IsAlgebraic k kbar] (j₀ : CompactificationOf (Over.mk f))
    [IsCurve kbar (pullback.snd (Over.mk j₀.toBase).hom (specAlgebraMap k kbar))]
    [Smooth (pullback.snd (Over.mk j₀.toBase).hom (specAlgebraMap k kbar))]
    [Nonempty X.1] (hℓp : ℓ ≠ p) {K : ℕ}
    (hF : LAdicSheaf.LocalTermsKilledBy B X ℓ f j₀ kbar
      (LAdicSheaf.representationSheaf B X x (restrictScalarsRep b σ) hσ) K)
    [hV : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
      j kbar (LAdicSheaf.representationSheaf B X x (restrictScalarsRep b σ) hσ) 1)] :
    letI := (restrictScalarsRepCoefficientSheaf B X x b σ hσ).rationalCohomologyModule f j kbar 1 E
    haveI := (restrictScalarsRepCoefficientSheaf B X x b σ
      hσ).rationalCohomologyModule_isScalarTower f j kbar 1 E
        (algebraMap_conjIntegralSubring_algebraMap _ _)
    haveI : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ
        f j kbar (restrictScalarsRepCoefficientSheaf B X x b σ hσ).toLAdicSheaf 1) := hV
    haveI : FiniteDimensional E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j
        kbar (restrictScalarsRepCoefficientSheaf B X x b σ hσ).toLAdicSheaf 1) :=
      Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E _
    ∃ hV' : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ
        f j kbar (LAdicSheaf.representationSheaf B X x (restrictScalarsRep b (contragredient σ))
          (continuous_restrictScalarsRep_contragredient b hσ)) 1),
      letI := (restrictScalarsRepCoefficientSheaf B X x b _
        (continuous_restrictScalarsRep_contragredient b hσ)).rationalCohomologyModule f j kbar 1 E
      haveI := (restrictScalarsRepCoefficientSheaf B X x b _
        (continuous_restrictScalarsRep_contragredient b hσ)).rationalCohomologyModule_isScalarTower
          f j kbar 1 E (algebraMap_conjIntegralSubring_algebraMap _ _)
      haveI : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X
          ℓ f j kbar (restrictScalarsRepCoefficientSheaf B X x b _
            (continuous_restrictScalarsRep_contragredient b hσ)).toLAdicSheaf 1) := hV'
      haveI : FiniteDimensional E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
          j kbar (restrictScalarsRepCoefficientSheaf B X x b _
            (continuous_restrictScalarsRep_contragredient b hσ)).toLAdicSheaf 1) :=
        Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E _
      ∀ (ι : E →+* ℂ) (z : ℂ),
        ((LinearMap.charpoly ((restrictScalarsRepCoefficientSheaf B X x b σ
          hσ).rationalGeometricCompactlySupportedFrobenius f j kbar 1 E p q
            hcard)).map ι).IsRoot z →
        z ≠ 0 ∧ ((LinearMap.charpoly ((restrictScalarsRepCoefficientSheaf B X x b _
          (continuous_restrictScalarsRep_contragredient b
            hσ)).rationalGeometricCompactlySupportedFrobenius f j kbar 1 E p q
              hcard)).map ι).IsRoot (((p ^ q : ℕ) : ℂ) / z) := by
  have hV₀ : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X
      ℓ f j₀ kbar (LAdicSheaf.representationSheaf B X x (restrictScalarsRep b σ) hσ) 1) :=
    LAdicSheaf.finiteDimensional_rationalGeometricCompactlySupportedCohomology_of_compactification
      B ℓ f kbar j j₀ _ 1
  obtain ⟨hV₀', hroots⟩ := LAdicSheaf.isRoot_div_charpoly_restrictScalarsRep_contragredient B X ℓ x
    E b σ hσ f j₀ kbar p q hcard hℓp hF (hV := hV₀)
  have hV' : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X
      ℓ f j kbar (LAdicSheaf.representationSheaf B X x (restrictScalarsRep b (contragredient σ))
        (continuous_restrictScalarsRep_contragredient b hσ)) 1) :=
    have := hV₀'
    LAdicSheaf.finiteDimensional_rationalGeometricCompactlySupportedCohomology_of_compactification
      B ℓ f kbar j₀ j _ 1
  refine ⟨hV', ?_⟩
  intro ι z hz
  have key : ∀ (τ : EtaleFundamentalGroup X.1 x →* GL (Fin m) E)
      (hτ : Continuous (restrictScalarsRep b τ)) (j : CompactificationOf (Over.mk f))
      [FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j
        kbar (LAdicSheaf.representationSheaf B X x (restrictScalarsRep b τ) hτ) 1)],
      letI := (restrictScalarsRepCoefficientSheaf B X x b τ hτ).rationalCohomologyModule f j kbar
        1 E
      Module.Finite E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar
        (restrictScalarsRepCoefficientSheaf B X x b τ hτ).toLAdicSheaf 1) := by
    intro τ hτ j _
    let := (restrictScalarsRepCoefficientSheaf B X x b τ hτ).rationalCohomologyModule f j kbar 1 E
    have := (restrictScalarsRepCoefficientSheaf B X x b τ
      hτ).rationalCohomologyModule_isScalarTower f j kbar 1 E
        (algebraMap_conjIntegralSubring_algebraMap _ _)
    have : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ
        f j kbar (restrictScalarsRepCoefficientSheaf B X x b τ hτ).toLAdicSheaf 1) := ‹_›
    exact Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E _
  have := key σ hσ j
  have := key σ hσ j₀
  have := key _ (continuous_restrictScalarsRep_contragredient b hσ) j
  have := key _ (continuous_restrictScalarsRep_contragredient b hσ) j₀
  rw [(restrictScalarsRepCoefficientSheaf B X x b σ
    hσ).charpoly_rationalGeometricCompactlySupportedFrobenius_eq_of_compactification' B ℓ f kbar 1
      E p q hcard j j₀] at hz
  rw [(restrictScalarsRepCoefficientSheaf B X x b _
    (continuous_restrictScalarsRep_contragredient b
      hσ)).charpoly_rationalGeometricCompactlySupportedFrobenius_eq_of_compactification' B ℓ f
        kbar 1 E p q hcard j j₀]
  exact hroots ι z hz

end Roots

section Final

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

/-- **Poincaré duality on the fibres of the Fourier family** (Kedlaya, *Fourier transforms and
p-adic Weil II*, proof of Theorem 6.4), from the uniform vanishing of the inertia invariants at
`∞` (`Stacks.EtaleCohomology.LaumonUniformInertiaInput`). For each fibre over `k'`, with `N` the
uniform bound, the inertia at every place at `∞` of `𝔸¹_{k'}` has no invariants on the fibre for
`n > N`, so the local terms at the boundary of `ℙ¹_{k'}` are killed by a power of `ℓ`; Poincaré
duality on Frobenius roots at `ℙ¹_{k'}` then holds through the given compactification. -/
theorem laumonFibreDualityInput_of_uniformInertia (h : LaumonUniformInertiaInput.{u}) :
    LaumonFibreDualityInput.{u} := by
  intro B U ℓ _ _ _ _ _ _ k _ _ f _ _ _ _ _ e _ _ he j kbar _ _ _ _ p n _ _ hcard hℓp x E _ _ _ d b
    m σ hσ K _ _ _ hirr hζ ι' β _ hpure ψ hψ
  obtain ⟨N, hN⟩ := h ℓ k U.1 e p x E b σ hσ ψ hψ
  refine ⟨N, fun n hn hpn => ?_⟩
  intro k' _ _ _ hX' _ _ x' hx' a c hac p₀ hτ _ _ _ j' kbar' _ _ _ p' n' _ _ hcard' hV
  have ha : a ≠ 0 := by simpa using hac
  have : IrreducibleSpace (Spec (.of (Polynomial k'))) :=
    inferInstanceAs (IrreducibleSpace (PrimeSpectrum (Polynomial k')))
  have : Nonempty (Spec (.of (Polynomial k'))) :=
    inferInstanceAs (Nonempty (PrimeSpectrum (Polynomial k')))
  have := Stacks.GenericFiniteEtale.smoothOfRelativeDimension_specMap_polynomial k'
  have : IsAlgClosed kbar' := IsAlgClosure.isAlgClosed k'
  have : Algebra.IsAlgebraic k' kbar' := IsAlgClosure.isAlgebraic
  have : CharP kbar' p' := charP_of_injective_algebraMap (algebraMap k' kbar').injective p'
  have hpp : p' = p := CharP.eq k' inferInstance ((Algebra.charP_iff k k' p).1 inferInstance)
  have hℓp' : ℓ ≠ p' := hpp ▸ hℓp
  obtain ⟨K₀, hF⟩ := LAdicSheaf.exists_localTermsKilledBy_of_basePoint B
    (Stacks.ArtinSchreier.specObject (Polynomial k') B hX') ℓ k'
    (Spec.map (CommRingCat.ofHom (algebraMap k' (Polynomial k'))))
    (affineLineProjectiveCompactification k') kbar' p' LAdicSheaf.localTermsSmoothBoundaryStalkInput
    hℓp' x' _ hτ (fun L Ω _ _ _ _ _ _ _ _ _ t A _ _ _ _ _ _ _ P _ hA =>
      (hN n hn hpn k' x' hx' a c ha p₀ L Ω t A P hA).1)
  obtain ⟨hV', hroots⟩ :=
    LAdicSheaf.isRoot_div_charpoly_restrictScalarsRep_contragredient_of_compactification B
      (Stacks.ArtinSchreier.specObject (Polynomial k') B hX') ℓ x' E b _ hτ
      (Spec.map (CommRingCat.ofHom (algebraMap k' (Polynomial k')))) j' kbar' p' n' hcard'
      (affineLineProjectiveCompactification k') hℓp' hF (hV := hV)
  exact ⟨hV', hroots ι'⟩

end Final

end Stacks.EtaleCohomology

end
