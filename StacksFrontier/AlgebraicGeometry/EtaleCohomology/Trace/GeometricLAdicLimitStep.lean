module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicCompactSupport
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.PerfectTowerSystem

/-!
# The ℓ-adic limit step of Theorem 03V2

The source proves Theorem 03V2 by producing a tower of perfect complexes
`Kₙ = RΓ_c(X_k̄, Fₙ) ∈ D_perf(ℤ/ℓⁿ⁺¹ℤ)`, with endomorphisms `πₙ` induced by the geometric
Frobenius and comparisons `Kₙ₊₁ ⊗ᴸ ℤ/ℓⁿ⁺¹ℤ ≅ Kₙ`, and then applying the algebra lemma
[Tag 03V4](https://stacks.math.columbia.edu/tag/03V4) to it.  This file is that last step,
for the compactly supported ℓ-adic cohomology of the geometric fibre
`Stacks.EtaleCohomology.LAdicSheaf.rationalGeometricCompactlySupportedCohomology`: whenever the
inverse systems `n ↦ Hⁱ_c(X_k̄, Fₙ)` are identified with the cohomology systems of a perfect
tower, compatibly with an endomorphism `φ` of `RΓ_c(X_k̄, -)`, then
`Hⁱ_c(X_k̄, F ⊗ Q_ℓ)` is finite-dimensional, vanishes in all but finitely many degrees, and the
alternating sum of the traces of `φ` on it is the ℓ-adic trace of the tower.

None of these is registered under Tag 03V2: their hypotheses — the perfect tower and its
identification with the cohomology of the levels — are what Tag 03V3 (perfectness of
`RΓ_c(X_k̄, Fₙ)`), the compatibility of `RΓ_c` with reduction of coefficients, and the
comparison of `RΓ_c` with `ℤ_[ℓ]`- and `ℤ/ℓⁿ⁺¹ℤ`-coefficients provide, and none of those is
available yet.

## Main results

* `LAdicSheaf.finite_rationalGeometricCompactlySupportedCohomology_of_iso`: finiteness.
* `LAdicSheaf.finite_nontrivial_rationalGeometricCompactlySupportedCohomology_of_iso`: finitely
  many nonzero degrees.
* `LAdicSheaf.alternating_trace_rationalGeometricCompactlySupportedCohomology_of_iso`: the
  alternating trace is `t_∞`.

(All in the namespace `Stacks.EtaleCohomology`.)

## References

* [Stacks Project, Tag 03V2](https://stacks.math.columbia.edu/tag/03V2)
* [Stacks Project, Tag 03V4](https://stacks.math.columbia.edu/tag/03V4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale
open Stacks.InverseSystem
open scoped TensorProduct

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)

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
  (F : LAdicSheaf B X ℓ) (T : PerfectTower.{u + 1} ℓ)

/-- If `n ↦ Hⁱ_c(X_k̄, Fₙ)` is the cohomology system of a perfect tower, then
`Hⁱ_c(X_k̄, F ⊗ Q_ℓ)` is finite-dimensional. -/
public theorem LAdicSheaf.finite_rationalGeometricCompactlySupportedCohomology_of_iso (i : ℤ)
    (e : LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f j kbar F i ≅
      levelCohomologySystem T i) :
    Module.Finite ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i) :=
  finite_rational_limit_of_iso T i e

/-- If, in every degree, `n ↦ Hⁱ_c(X_k̄, Fₙ)` is the cohomology system of a perfect tower, then
`Hⁱ_c(X_k̄, F ⊗ Q_ℓ)` vanishes in all but finitely many degrees. -/
public theorem LAdicSheaf.finite_nontrivial_rationalGeometricCompactlySupportedCohomology_of_iso
    (e : ∀ i, LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f j kbar F i ≅
      levelCohomologySystem T i) :
    {i : ℤ | Nontrivial
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i)}.Finite :=
  finite_nontrivial_rational_limit_of_iso T e

/-- If, in every degree, `n ↦ Hⁱ_c(X_k̄, Fₙ)` with the action of an endomorphism `φ` of
`RΓ_c(X_k̄, -)` is the cohomology system of a perfect tower with `n ↦ Hⁱ(πₙ)`, then the
alternating sum of the traces of `φ` on `Hⁱ_c(X_k̄, F ⊗ Q_ℓ)` is the ℓ-adic trace `t_∞` of the
tower. -/
public theorem LAdicSheaf.alternating_trace_rationalGeometricCompactlySupportedCohomology_of_iso
    (φ : compactSupportFrobeniusFunctor.{u, 0} ℤ_[ℓ] f j kbar ⟶
      compactSupportFrobeniusFunctor.{u, 0} ℤ_[ℓ] f j kbar)
    (e : ∀ i, LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f j kbar F i ≅
      levelCohomologySystem T i)
    (he : ∀ i,
      LAdicSheaf.geometricCompactlySupportedCohomologySystemPullback B X ℓ f j kbar F i φ ≫
        (e i).hom = (e i).hom ≫ levelCohomologyEndoSystem T i) :
    ∑ᶠ i : ℤ, (if Even i then (1 : ℚ_[ℓ]) else -1) *
        LinearMap.trace ℚ_[ℓ]
          (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i)
          (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyPullback B X ℓ f j kbar F i
            φ).hom =
      (padicTrace T : ℚ_[ℓ]) :=
  alternating_trace_rational_limit_of_iso T _ e he

end Stacks.EtaleCohomology
