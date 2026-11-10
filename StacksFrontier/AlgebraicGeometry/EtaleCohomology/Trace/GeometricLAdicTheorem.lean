module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicVanishingDimension

/-!
# Tag 03V2 from its finite-level inputs

[Stacks, Tag 03V2]: for a separated scheme `X` of finite type over a finite field `k` and a
`ℚ_ℓ`-sheaf `F` on `X`, the groups `Hⁱ_c(X_k̄, F)` are finite dimensional, nonzero only for
`0 ≤ i ≤ 2 dim X`, and

`∑_{x ∈ X(k)} Tr(π_x | F_x̄) = ∑ᵢ (-1)ⁱ Tr(π_X^* | Hⁱ_c(X_k̄, F))`.

This file assembles the three parts from the inputs of the source's proof, which are hypotheses
here:

* `hP`, the perfectness of the complexes `Kₙ = RΓ_c(X_k̄, F'ₙ)` of the torsion-free model `F'` of
  `F` (item (1) of the proof);
* `hT`, the trace formula of [Stacks, Tag 03V3] at every finite level (item (3));
* `h095U`, the absolute case over `k̄` of [Stacks, Tag 095U], which bounds the cohomological
  degrees.

The assembly is `LAdicSheaf.traceFormula_of_levelTraceFormula`. It carries no `@[stacks]`
attribute, since its hypotheses are results the source proves.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale
open Stacks.Frobenius Stacks.InverseSystem CategoryTheory.FilteredDerived Stacks.Trace

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

variable {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [IsAlgClosed kbar]
  [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p] [CharP kbar p]
  (hcard : Fintype.card k = p ^ q)

local notation "model" F => LAdicSheaf.torsionFreeModel F (LAdicSheaf.torsionBound F)

/-- **[Stacks, Tag 03V2] from its finite-level inputs.** Let `F` be an ℓ-adic sheaf on a
separated scheme `X` of finite type over a finite field `k`, with torsion-free model `F'`. Suppose
that the complexes `Kₙ = RΓ_c(X_k̄, F'ₙ)` are perfect (`hP`), that they satisfy the trace formula
of [Stacks, Tag 03V3] (`hT`), and the absolute case of [Stacks, Tag 095U] over `k̄` (`h095U`).
Then the groups `Hⁱ_c(X_k̄, F)` are finite dimensional over `ℚ_ℓ`, nonzero only for
`0 ≤ i ≤ 2 dim X`, and the alternating sum of the traces of `π_X^*` on them is the sum over the
rational points of the traces of the geometric Frobenius on the stalks. -/
theorem LAdicSheaf.traceFormula_of_levelTraceFormula
    (h095U : ProperSeparablyClosedSheafHVanishingStatement.{u})
    (F : LAdicSheaf.{u, u + 1} B X ℓ)
    (hP : ∀ n, StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar
        (LAdicSheaf.levelComplex B X ℓ (model F) n))))
    [Fintype (rationalPoints f)]
    (hT : ∀ n, traceAtLevel (LAdicSheaf.geometricPerfectTower B X ℓ f j kbar p q hcard (model F)
        (LAdicSheaf.powExact_etaleLevel_torsionFreeModel B X ℓ F le_rfl) hP) n =
      ∑ y : rationalPoints f, commutativeAdditiveCommutatorQuotientEval (ZMod (ℓ ^ (n + 1)))
        (perfectDerivedTrace (ZMod (ℓ ^ (n + 1))) ⟨_,
          LAdicSheaf.isPerfect_rationalPointStalkComplex_torsionFreeModel B X ℓ f kbar F n y⟩
          (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, 0} (ZMod (ℓ ^ (n + 1))) kbar p q
            hcard y.1 (LAdicSheaf.levelComplex B X ℓ (model F) n))))) :
    (∀ i : ℤ, Module.Finite ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i)) ∧
    (∀ i : ℤ, Nontrivial
        (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i) →
      0 ≤ i ∧ ∃ d : ℕ, topologicalKrullDim X.1 = d ∧ i ≤ 2 * (d : ℤ)) ∧
    ∑ᶠ (x : closedPoints X.1) (_ : residueDegree f x.1 = 1),
        LinearMap.trace ℚ_[ℓ] _
          (LAdicSheaf.rationalStalkFrobenius B X ℓ F x.1 (finite_residueField f x.1 x.2)) =
      ∑ᶠ i : ℤ, (if Even i then (1 : ℚ_[ℓ]) else -1) *
        LinearMap.trace ℚ_[ℓ]
          (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i)
          (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyPullback B X ℓ f j kbar F i
            (canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ] f j kbar p q hcard)).hom :=
  ⟨LAdicSheaf.finite_rationalGeometricCompactlySupportedCohomology_of_perfect B X ℓ f j kbar p q
      hcard F hP,
    LAdicSheaf.nontrivial_rationalGeometricCompactlySupportedCohomology_bounds B X ℓ f j kbar p q
      hcard h095U F hP,
    (LAdicSheaf.alternating_trace_eq_sum_rationalStalkFrobenius_of_levelTraceFormula B X ℓ f j
      kbar p q hcard F hP hT).symm⟩

end Stacks.EtaleCohomology

end
