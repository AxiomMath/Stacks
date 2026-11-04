module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoefficientTwistedTraceFormula
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafTwistedStalkTrace

/-!
# The twisted trace formula for the sheaf of `σ : π₁ → GL_m(O)`, with stalk local terms

The twisted trace formula `Stacks.EtaleCohomology.alternating_trace_coefficientScalar_comp`,
rewritten with the local terms as twisted traces of Frobenius on the rational stalks
(`Stacks.EtaleCohomology.trace_rationalStalkMap_coefficientScalar_comp_rationalStalkFrobenius_pow`)
and the cohomological side as the trace of `c ∘ π_X^*` on `Hⁱ_c(X_k̄, ℱ) ⊗ ℚ_ℓ`:

`∑_{deg y = 1} Tr(c ∘ π_y | ℱ_ȳ ⊗ ℚ_ℓ) = ∑ᵢ (-1)ⁱ Tr(c ∘ π_X^* | Hⁱ_c(X_k̄, ℱ) ⊗ ℚ_ℓ)`.

This is the form the twisted trace formula over the extensions of the base field takes in
`Stacks.EtaleCohomology.LAdicSheaf.finsum_trace_comp_pow_eq_of_traceFormula`.

The statements consume objects defined in the standard model `HasDerivedCategory.standard` of the
derived category, which is therefore a local instance here.

## Main results

* `Stacks.EtaleCohomology.baseChange_limMap_pullback_comp_systemMap`
* `Stacks.EtaleCohomology.finsum_trace_coefficientScalar_comp_rationalStalkFrobenius`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale
open Stacks.Frobenius Stacks.InverseSystem

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

section Limit

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ) [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [IsNoetherian X.1]
  {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f]
  [QuasiCompact f] [IsSeparated f] (J : CompactificationOf (Over.mk f)) (kbar : Type u)
  [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

/-- **`ψ_* ∘ π_X^*` on `Hⁱ_c(X_k̄, F) ⊗ ℚ_ℓ`, as the base change of the limit of the levels.** -/
public theorem baseChange_limMap_pullback_comp_systemMap (F : LAdicSheaf B X ℓ) (ψ : F ⟶ F)
    (i : ℤ) :
    LinearMap.baseChange ℚ_[ℓ] (limMap
        (LAdicSheaf.geometricCompactlySupportedCohomologySystemPullback B X ℓ f J kbar F i
            (canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ] f J kbar p q hcard) ≫
          LAdicSheaf.geometricCompactlySupportedCohomologySystemMap f J kbar ψ i)).hom =
      ((ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
          (LAdicSheaf.geometricCompactlySupportedCohomologyMap f J kbar ψ i)).hom ∘ₗ
        (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f J kbar p q hcard F
          i).hom := by
  have hl : limMap
      (LAdicSheaf.geometricCompactlySupportedCohomologySystemPullback B X ℓ f J kbar F i
          (canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ] f J kbar p q hcard) ≫
        LAdicSheaf.geometricCompactlySupportedCohomologySystemMap f J kbar ψ i) =
      limMap (LAdicSheaf.geometricCompactlySupportedCohomologySystemPullback B X ℓ f J kbar F i
          (canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ] f J kbar p q hcard)) ≫
        limMap (LAdicSheaf.geometricCompactlySupportedCohomologySystemMap f J kbar ψ i) :=
    limit.hom_ext fun n => by simp
  rw [hl, ModuleCat.hom_comp, LinearMap.baseChange_comp]
  rfl

end Limit

variable {ℓ : ℕ} [Fact ℓ.Prime] {O : Type} [CommRing O] [Algebra ℤ_[ℓ] O] {d : ℕ}
  (b : Module.Basis (Fin d) ℤ_[ℓ] O) {m : ℕ}
  (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  (σ : EtaleFundamentalGroup X.1 x →* GL (Fin m) O)
  (hρ : Continuous ((Units.map (coefficientMatrixRingHom b m).toMonoidHom).comp σ))
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1]
  {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f]
  [QuasiCompact f] [IsSeparated f] (J : CompactificationOf (Over.mk f)) (kbar : Type u)
  [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] [Algebra.IsAlgebraic k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP k p] [CharP kbar p] (hcard : Fintype.card k = p ^ q)

local notation "e₀" => canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x

/-- **The twisted trace formula for the sheaf of `σ : π₁ → GL_m(O)`, with stalk local terms**:
`∑_{deg y = 1} Tr(c ∘ π_y | ℱ_ȳ ⊗ ℚ_ℓ) = ∑ᵢ (-1)ⁱ Tr(c ∘ π_X^* | Hⁱ_c(X_k̄, ℱ) ⊗ ℚ_ℓ)`, for `X` of
dimension at most one over `k` and `ℓ ≠ p`. -/
public theorem finsum_trace_coefficientScalar_comp_rationalStalkFrobenius [Module.Free ℤ_[ℓ] O]
    [Module.Finite ℤ_[ℓ] O] (hℓp : ℓ ≠ p) (hdim : topologicalKrullDim X.1 ≤ 1) (c : O) :
    ∑ᶠ (y : closedPoints X.1) (_ : residueDegree f y.1 = 1),
        LinearMap.trace ℚ_[ℓ] _
          (LAdicSheaf.rationalStalkMap (representationLAdicSheafMap B X x e₀ hρ hρ
              (coefficientScalarRingHom b m c)
              (fun g => coefficientScalarRingHom_commute b m c (σ g).val))
              (geometricPointAt X.1 y.1) ∘ₗ
            LAdicSheaf.rationalStalkFrobenius B X ℓ (representationLAdicSheaf B X x e₀
              ((Units.map (coefficientMatrixRingHom b m).toMonoidHom).comp σ) hρ) y.1
              (finite_residueField f y.1 y.2) ^ 1) =
      ∑ᶠ i : ℤ, (if Even i then (1 : ℚ_[ℓ]) else -1) * LinearMap.trace ℚ_[ℓ] _
        (((ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
            (LAdicSheaf.geometricCompactlySupportedCohomologyMap f J kbar
              (representationLAdicSheafMap B X x e₀ hρ hρ (coefficientScalarRingHom b m c)
                (fun g => coefficientScalarRingHom_commute b m c (σ g).val)) i)).hom ∘ₗ
          (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f J kbar p q hcard
            (representationLAdicSheaf B X x e₀
              ((Units.map (coefficientMatrixRingHom b m).toMonoidHom).comp σ) hρ) i).hom) := by
  have : Fintype (rationalPoints f) := @Fintype.ofFinite _ (finite_rationalPoints f)
  have h := alternating_trace_coefficientScalar_comp b B X x σ hρ f J kbar p q hcard hℓp hdim c
  refine Eq.trans ?_ ((finsum_congr fun i => congrArg (fun z =>
    (if Even i then (1 : ℚ_[ℓ]) else -1) * LinearMap.trace ℚ_[ℓ] _ z)
    (baseChange_limMap_pullback_comp_systemMap B X ℓ f J kbar p q hcard _ _ i)).symm.trans h).symm
  rw [finsum_residueDegree_eq_one_eq_sum f, PadicInt.coe_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [trace_rationalStalkMap_coefficientScalar_comp_rationalStalkFrobenius_pow B X x b σ hρ f c,
    pow_one, PadicInt.algebraMap_apply]

end Stacks.EtaleCohomology

end
