module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicTwistedTower
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoefficientLevelStalkFrobenius
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationLevelPowExact

/-!
# The trace formula for the `O`-sheaf of a representation, twisted by `O`

Let `σ : π₁(X, x̄) → GL_m(O)` be a continuous representation with coefficients in a finite free
`ℤ_ℓ`-algebra `O`, `ℱ` its sheaf and `c ∈ O`, acting on `ℱ` by the scalar matrices. For `X`
separated of finite type and of dimension at most one over a finite field `k` and `ℓ ≠ p`,

`∑ᵢ (-1)ⁱ Tr(π_X^* ∘ c | Hⁱ_c(X_k̄, ℱ) ⊗ ℚ_ℓ) = ∑_{x ∈ X(k)} Tr_{O/ℤ_ℓ}(c · tr σ(F_x))`.

At the finite levels this is `Stacks.EtaleCohomology.coeffLevel_twistedTraceFormula_explicit`;
the levels form the tower twisted by `c`
(`Stacks.EtaleCohomology.LAdicSheaf.geometricPerfectTowerTwist`), whose ℓ-adic trace is the
alternating sum on the limit (`Stacks.EtaleCohomology.LAdicSheaf.alternating_trace_comp_of_flat`).

The statements consume objects defined in the standard model `HasDerivedCategory.standard` of the
derived category, which is therefore a local instance here.

## Main results

* `Stacks.EtaleCohomology.alternating_trace_coefficientScalar_comp`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale
open Stacks.Frobenius Stacks.InverseSystem

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

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

/-- **The trace formula for the sheaf of `σ : π₁ → GL_m(O)`, twisted by `c ∈ O`**:
`∑ᵢ (-1)ⁱ Tr(π_X^* ∘ c | Hⁱ_c(X_k̄, ℱ) ⊗ ℚ_ℓ) = ∑_{x ∈ X(k)} Tr_{O/ℤ_ℓ}(c · tr σ(F_x))`, for `X`
of dimension at most one over `k` and `ℓ ≠ p`. -/
public theorem alternating_trace_coefficientScalar_comp [Module.Free ℤ_[ℓ] O]
    [Module.Finite ℤ_[ℓ] O] (hℓp : ℓ ≠ p) (hdim : topologicalKrullDim X.1 ≤ 1)
    [Fintype (rationalPoints f)] (c : O) :
    ∑ᶠ i : ℤ, (if Even i then (1 : ℚ_[ℓ]) else -1) *
        LinearMap.trace ℚ_[ℓ]
          (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f J kbar
            (representationLAdicSheaf B X x e₀
              ((Units.map (coefficientMatrixRingHom b m).toMonoidHom).comp σ) hρ) i)
          (LinearMap.baseChange ℚ_[ℓ] (limMap
            (LAdicSheaf.geometricCompactlySupportedCohomologySystemPullback B X ℓ f J kbar
                (representationLAdicSheaf B X x e₀
                  ((Units.map (coefficientMatrixRingHom b m).toMonoidHom).comp σ) hρ) i
                (canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ] f J kbar p q hcard) ≫
              LAdicSheaf.geometricCompactlySupportedCohomologySystemMap f J kbar
                (representationLAdicSheafMap B X x e₀ hρ hρ (coefficientScalarRingHom b m c)
                  (fun g => coefficientScalarRingHom_commute b m c (σ g).val)) i)).hom) =
      ((∑ y : rationalPoints f, Algebra.trace ℤ_[ℓ] O
          (c * (σ (geometricFrobeniusFamily f x (rationalPointsEquivDegreeOne f y).1)).val.trace) :
        ℤ_[ℓ]) : ℚ_[ℓ]) := by
  have hF := powExact_etaleLevel_representationLAdicSheaf B X x
    ((Units.map (coefficientMatrixRingHom b m).toMonoidHom).comp σ) hρ
  have hE := fun n => coeffLevel_twistedTraceFormula_explicit b B X x σ hρ f kbar p q hcard J hℓp
    hdim n c
  refine (LAdicSheaf.alternating_trace_comp_of_flat f J kbar p q hcard _ hF (fun n => (hE n).fst)
    _).trans ?_
  refine congrArg _ (eq_of_toZModPow_succ_eq fun n => ?_)
  rw [toZModPow_padicTrace, map_sum]
  exact (hE n).snd

end Stacks.EtaleCohomology

end
