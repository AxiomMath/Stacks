module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.AdicCohomologicalInterpretation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FiniteCoefficientCohomologicalInterpretation

/-!
# The ℓ-adic cohomological interpretation of the L-function

Let `X` be a separated scheme of finite type over a finite field `k`, `ℓ` a prime invertible in
`k`, and `F = (Fₙ)` an ℓ-adic sheaf on `X_étale` whose levels are flat over `ℤ/ℓⁿ⁺¹ℤ`. By Tag 03UZ
at every level, the complexes `RΓ_c(X_k̄, Fₙ)` are perfect and the ℓ-adic L-function
`L_{ℤ_ℓ}(X, F) ∈ ℤ_ℓ⟦T⟧` reduces modulo every `ℓⁿ⁺¹` to `det(1 - π_X^* T | RΓ_c(X_k̄, Fₙ))⁻¹`.
This is not more general than Tag 03V0: `ℤ_ℓ` has no `ℓ`-torsion, so `ℤ_ℓ⟦T⟧ → ℚ_ℓ⟦T⟧` is
injective, and for every power series `c` with these reductions, `L_{ℤ_ℓ}(X, F) = c` holds exactly
when `L(X, F ⊗ ℚ_ℓ) = ∏ᵢ det(1 - π_X^* T | Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)) ^ ((-1) ^ (i + 1))`.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.adicLFunction_eq_inv_charSeries_compactSupport`: the
  reductions of `L_{ℤ_ℓ}(X, F)` modulo `ℓⁿ⁺¹`, and the equivalence of the ℓ-adic identity with the
  `ℚ_ℓ` one.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale
open Stacks.Frobenius Stacks.InverseSystem PowerSeries

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring
attribute [local instance high] Stacks.ConstantSheaf.hasSheafify_moduleCat_of_univLE

/-- A scheme locally of finite type and quasi-compact over a field is Noetherian. -/
public theorem isNoetherian_of_locallyOfFiniteType {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] :
    AlgebraicGeometry.IsNoetherian X := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X :=
    ⟨by simpa using QuasiCompact.isCompact_preimage (f := f) Set.univ isOpen_univ isCompact_univ⟩
  exact {}

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] [Algebra.IsAlgebraic k kbar]

/-- **The ℓ-adic cohomological interpretation of the L-function.** Let `X` be a separated scheme
of finite type over a finite field `k`, `k̄` an algebraic closure of `k`, `ℓ` a prime invertible
in `k`, and `F = (Fₙ)` an ℓ-adic sheaf on `X_étale` whose levels are flat over `ℤ/ℓⁿ⁺¹ℤ`. Then `X`
has a compactification, and for every compactification `j` and every presentation `#k = p ^ q`:
* the complexes `RΓ_c(X_k̄, Fₙ)` are perfect and the ℓ-adic L-function `L_{ℤ_ℓ}(X, F)` reduces
  modulo every `ℓⁿ⁺¹` to `det(1 - π_X^* T | RΓ_c(X_k̄, Fₙ))⁻¹`;
* for every `c ∈ ℤ_ℓ⟦T⟧` with these reductions, `L_{ℤ_ℓ}(X, F) = c` if and only if
  `L(X, F ⊗ ℚ_ℓ) = ∏ᵢ det(1 - π_X^* T | Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)) ^ ((-1) ^ (i + 1))`. -/
@[stacks 03V1 "the identity for Z_l coefficients is the l-adic limit of 03UZ at the levels, and \
it is equivalent to 03V0 for F ⊗ Q_l since Z_l has no l-torsion"]
public theorem LAdicSheaf.adicLFunction_eq_inv_charSeries_compactSupport (hℓ : (ℓ : k) ≠ 0) :
    haveI := isNoetherian_of_locallyOfFiniteType f
    ∀ (F : LAdicSheaf B X ℓ) (hF : ∀ n, PowExact ℓ (n + 1) (F.level n)),
    Nonempty (CompactificationOf (Over.mk f)) ∧
      ∀ (j : CompactificationOf (Over.mk f)) (p q : ℕ) [Fact p.Prime] [CharP k p]
        (hcard : Fintype.card k = p ^ q),
        ∃ hP : ∀ n, StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
            (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar
              (LAdicSheaf.levelComplex B X ℓ F n))),
          (∀ n : ℕ, PowerSeries.map (PadicInt.toZModPow (n + 1))
              (LAdicSheaf.adicLFunction B X ℓ F hF f) =
            (((CategoryTheory.FilteredDerived.perfectDerivedCharSeries.{u + 2, 0, u + 1}
              (ZMod (ℓ ^ (n + 1)))
              ((LAdicSheaf.geometricPerfectTower B X ℓ f j kbar p q hcard F
                (LAdicSheaf.powExact_etaleLevel B X ℓ F hF) hP).obj n) (hP n)
              ((LAdicSheaf.geometricPerfectTower B X ℓ f j kbar p q hcard F
                (LAdicSheaf.powExact_etaleLevel B X ℓ F hF) hP).endo n))⁻¹ :
                (ZMod (ℓ ^ (n + 1)))⟦X⟧ˣ) : (ZMod (ℓ ^ (n + 1)))⟦X⟧)) ∧
          ∀ c : ℤ_[ℓ]⟦X⟧, (∀ n : ℕ, PowerSeries.map (PadicInt.toZModPow (n + 1)) c =
              (((CategoryTheory.FilteredDerived.perfectDerivedCharSeries.{u + 2, 0, u + 1}
                (ZMod (ℓ ^ (n + 1)))
                ((LAdicSheaf.geometricPerfectTower B X ℓ f j kbar p q hcard F
                  (LAdicSheaf.powExact_etaleLevel B X ℓ F hF) hP).obj n) (hP n)
                ((LAdicSheaf.geometricPerfectTower B X ℓ f j kbar p q hcard F
                  (LAdicSheaf.powExact_etaleLevel B X ℓ F hF) hP).endo n))⁻¹ :
                  (ZMod (ℓ ^ (n + 1)))⟦X⟧ˣ) : (ZMod (ℓ ^ (n + 1)))⟦X⟧)) →
            (LAdicSheaf.adicLFunction B X ℓ F hF f = c ↔
              LAdicSheaf.rationalLFunction B X ℓ F f =
                gradedCharSeries
                  (fun i =>
                    LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i)
                  (fun i => (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar
                    p q hcard F i).hom)) := by
  have := isNoetherian_of_locallyOfFiniteType f
  intro F hF
  refine ⟨nonempty_compactificationOf B X f, fun j p q _ _ hcard => ?_⟩
  exact LAdicSheaf.adicDeterminantIdentity_of_lFunctionCharSeriesIdentity B X ℓ f j kbar p q hcard
    F hF fun n => by
      have := finite_zmod_pow_succ ℓ n
      exact (lFunction_eq_inv_charSeries_compactSupport B X f kbar (ZMod (ℓ ^ (n + 1)))
        (natCard_zmod_pow_ne_zero hℓ n) (F.level n)
        (LAdicSheaf.isConstructibleFlatModuleSheaf_level B X ℓ F hF n)).2 j p q hcard

end Stacks.EtaleCohomology

end
