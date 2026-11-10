module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.AdicDeterminantIdentity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.IdempotentCoefficientReduction

/-!
# The ℓ-adic cohomological interpretation from the finite-coefficient one

Let `F` be an ℓ-adic sheaf with flat levels on a separated scheme of finite type `X` over a finite
field `k`. If the cohomological interpretation `L(X, Fₙ) = det(1 - π_X^* T | RΓ_c(X_k̄, Fₙ))⁻¹`
of Tag 03UZ holds at every level `Fₙ` (`Stacks.EtaleCohomology.LFunctionCharSeriesIdentity`),
then the complexes `RΓ_c(X_k̄, Fₙ)` are perfect, `L_{ℤ_ℓ}(X, F)` reduces modulo every `ℓⁿ⁺¹` to
`det(1 - π_X^* T | RΓ_c(X_k̄, Fₙ))⁻¹`, and for every power series `c` with these reductions
`L_{ℤ_ℓ}(X, F) = c` exactly when
`L(X, F ⊗ ℚ_ℓ) = ∏ᵢ det(1 - π_X^* T | Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)) ^ ((-1) ^ (i + 1))`. This is Remark
64.20.3 (Tag 03V1) once Tag 03UZ is available; the levels are finite rings of order a power of
`ℓ`, invertible in `k` when `ℓ` is.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.adicDeterminantIdentity_of_lFunctionCharSeriesIdentity`.
* `Stacks.EtaleCohomology.natCard_zmod_pow_ne_zero`: the levels have order invertible in `k`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale
open Stacks.Frobenius Stacks.InverseSystem PowerSeries

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
attribute [local instance high] Stacks.ConstantSheaf.hasSheafify_moduleCat_of_univLE

/-- The order of `ℤ/ℓⁿ⁺¹ℤ` is invertible in a field in which `ℓ` is. -/
public theorem natCard_zmod_pow_ne_zero {k : Type*} [Field k] {ℓ : ℕ} (hℓ : (ℓ : k) ≠ 0)
    (n : ℕ) : ((Nat.card (ZMod (ℓ ^ (n + 1))) : ℕ) : k) ≠ 0 := by
  have hℓ0 : ℓ ≠ 0 := by
    rintro rfl
    exact hℓ Nat.cast_zero
  have : NeZero (ℓ ^ (n + 1)) := ⟨pow_ne_zero _ hℓ0⟩
  rw [Nat.card_zmod, Nat.cast_pow]
  exact pow_ne_zero _ hℓ

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [AlgebraicGeometry.IsNoetherian X.1] [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- The levels of `ℤ_ℓ`-coefficients are finite rings. -/
public theorem finite_zmod_pow_succ (n : ℕ) : Finite (ZMod (ℓ ^ (n + 1))) :=
  have : NeZero (ℓ ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  inferInstance

omit [IsSeparated f] in
/-- **The ℓ-adic identity from the finite-coefficient identity at every level.** -/
public theorem LAdicSheaf.adicDeterminantIdentity_of_lFunctionCharSeriesIdentity
    (F : LAdicSheaf B X ℓ) (hF : ∀ n, PowExact ℓ (n + 1) (F.level n))
    (hlev : ∀ n : ℕ,
      haveI := finite_zmod_pow_succ ℓ n
      LFunctionCharSeriesIdentity B X (ZMod (ℓ ^ (n + 1))) f kbar (F.level n)
        (LAdicSheaf.isConstructibleFlatModuleSheaf_level B X ℓ F hF n) j p q hcard) :
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
              (fun i => LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i)
              (fun i => (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q
                hcard F i).hom)) :=
  LAdicSheaf.adicDeterminantIdentity_of_levels B X ℓ f j kbar p q hcard F hF hlev

end Stacks.EtaleCohomology

end
