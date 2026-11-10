module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicTraceFormulaPow
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TwistedFieldExtensionPointTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TwistedFieldExtensionCohomology

/-!
# The twisted trace formula for `ψ ∘ (π_X^*)^N` from the twisted trace formula over extensions

Let `F` be an ℓ-adic sheaf on a separated scheme `X` of finite type over a finite field `k` and
`ψ` an endomorphism of `F`. If for every finite extension `k ⊆ k' ⊆ k̄` the trace formula twisted
by `ψ` holds for `X' = X ×_k k'` and `g⁻¹F`, `g⁻¹ψ`, then for every `N ≥ 1`

`∑_{deg x ∣ N} deg x · Tr(ψ ∘ (π_x^*)^{N / deg x} | F_x̄)`
`  = ∑ᵢ (-1)ⁱ Tr(ψ ∘ (π_X^*)^N | Hⁱ_c(X_k̄, F))`,

the twisted form of `Stacks.EtaleCohomology.LAdicSheaf.finsum_trace_pow_eq_of_traceFormula`.

The statements consume objects defined in the standard model `HasDerivedCategory.standard` of the
derived category, which is therefore a local instance here.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.finsum_trace_comp_pow_eq_of_traceFormula`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.SmallEtale Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ) [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.obj T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f]
  [QuasiCompact f] [IsSeparated f] (j : CompactificationOf (Over.mk f))
  (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)
  [IsNoetherian X.1]

omit [IsSeparated f] in
/-- **The twisted trace formula for `ψ ∘ (π_X^*)^N` from the twisted trace formula over the finite
extensions of `k`.** -/
public theorem LAdicSheaf.finsum_trace_comp_pow_eq_of_traceFormula (F : LAdicSheaf.{u, u + 1} B X ℓ)
    (ψ : F ⟶ F)
    (htr : ∀ (k' : Type u) [Field k'] [Fintype k'] [Algebra k k'] [Module.Finite k k']
      [Algebra k' kbar] [IsScalarTower k k' kbar] [CharP k' p]
      [IsNoetherian (fieldExtensionScheme B X f k').1] (q' : ℕ)
      (hcard' : Fintype.card k' = p ^ q'),
      ∑ᶠ (y : closedPoints (fieldExtensionScheme B X f k').1)
          (_ : residueDegree (pullback.snd f (specAlgebraMap k k')) y.1 = 1),
          LinearMap.trace ℚ_[ℓ] _
            (LAdicSheaf.rationalStalkMap
                (LAdicSheaf.inverseImageMap (fieldExtensionProj B X f k') ψ)
                (geometricPointAt _ y.1) ∘ₗ
              LAdicSheaf.rationalStalkFrobenius B (fieldExtensionScheme B X f k') ℓ
              (LAdicSheaf.inverseImage (fieldExtensionProj B X f k') F) y.1
              (finite_residueField (pullback.snd f (specAlgebraMap k k')) y.1 y.2) ^ 1) =
        ∑ᶠ i : ℤ, (if Even i then (1 : ℚ_[ℓ]) else -1) * LinearMap.trace ℚ_[ℓ] _
          (((ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
              (LAdicSheaf.geometricCompactlySupportedCohomologyMap
                (X := fieldExtensionScheme B X f k') (pullback.snd f (specAlgebraMap k k'))
                (compactificationFieldBaseChange f j k') kbar
                (LAdicSheaf.inverseImageMap (fieldExtensionProj B X f k') ψ) i)).hom ∘ₗ
            (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B
              (fieldExtensionScheme B X f k') ℓ (pullback.snd f (specAlgebraMap k k'))
              (compactificationFieldBaseChange f j k') kbar p q' hcard'
              (LAdicSheaf.inverseImage (fieldExtensionProj B X f k') F) i).hom))
    (N : ℕ) (hN : N ≠ 0) :
    ∑ᶠ (x : closedPoints X.1) (_ : residueDegree f x.1 ∣ N),
        (residueDegree f x.1 : ℚ_[ℓ]) * LinearMap.trace ℚ_[ℓ] _
          (LAdicSheaf.rationalStalkMap ψ (geometricPointAt X.1 x.1) ∘ₗ
            LAdicSheaf.rationalStalkFrobenius B X ℓ F x.1 (finite_residueField f x.1 x.2) ^
            (N / residueDegree f x.1)) =
      ∑ᶠ i : ℤ, (if Even i then (1 : ℚ_[ℓ]) else -1) * LinearMap.trace ℚ_[ℓ] _
        (((ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
            (LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar ψ i)).hom ∘ₗ
          (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F
            i).hom ^ N) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := Nat.exists_eq_succ_of_ne_zero hN
  obtain ⟨K, hKfin, hK⟩ := exists_intermediateField_finrank_eq k kbar p (m + 1)
  let : Fintype K := @Fintype.ofFinite _ (Module.finite_of_finite k)
  have : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
  have := isNoetherian_fieldExtensionScheme B X f K
  have hcard' : Fintype.card K = p ^ (q * (m + 1)) := by
    rw [Module.card_eq_pow_finrank (K := k) (V := K), hK, hcard, pow_mul]
  rw [← LAdicSheaf.finsum_rationalStalkMap_comp_rationalStalkFrobenius_fieldExtension B X ℓ f K F ψ
    (m + 1) hK hN, htr K (q * (m + 1)) hcard']
  refine finsum_congr fun i => ?_
  congr 1
  exact
    LAdicSheaf.trace_rationalMap_comp_rationalGeometricCompactlySupportedFrobenius_fieldExtension
      B X ℓ f j K kbar i p q hcard m hcard' F ψ

end Stacks.EtaleCohomology

end
