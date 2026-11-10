module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.AdicCompactSupportCharSeries
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.AdicLFunction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.LevelConstructibleFlat
public import StacksFrontier.CategoryTheory.FilteredDerived.Perfectness.CharSeriesLogDerivative
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FiniteCoefficientLFunction

/-!
# The determinant identity with `ℤ_ℓ` coefficients

Let `F = (Fₙ)` be an ℓ-adic sheaf with flat levels on a separated scheme `X` of finite type over a
finite field `k`.  Its `ℤ_ℓ`-valued L-function `L_{ℤ_ℓ}(X, F)` reduces modulo `ℓⁿ⁺¹` to the
L-functions `L(X, Fₙ)` of the levels (Tag 03UV) and maps in `ℚ_ℓ⟦T⟧` to `L(X, F ⊗ ℚ_ℓ)`
(Tag 03UX).  The complexes `Kₙ = RΓ_c(X_k̄, Fₙ)`, when perfect, have characteristic series
`det(1 - π_X^* T | Kₙ)`, and a `ℤ_ℓ`-valued series `c` reducing to `det(1 - π_X^* T | Kₙ)⁻¹` at
every level maps in `ℚ_ℓ⟦T⟧` to `∏ᵢ det(1 - π_X^* T | Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)) ^ ((-1) ^ (i + 1))`.

Since `ℤ_ℓ` has no `ℓ`-torsion, `ℤ_ℓ⟦T⟧ → ℚ_ℓ⟦T⟧` is injective, so the `ℤ_ℓ`-coefficient
determinant identity `L_{ℤ_ℓ}(X, F) = c` holds exactly when the identity of Tag 03V0 holds for
`F ⊗ ℚ_ℓ`: there is no version of the theorem with `ℤ_ℓ` coefficients more general than the one
with `ℚ_ℓ` coefficients (Remark 64.20.3, Tag 03V1).

## Main results

* `Stacks.EtaleCohomology.padicPowerSeries_map_injective`: `ℤ_ℓ⟦T⟧ → ℚ_ℓ⟦T⟧` is injective.
* `Stacks.EtaleCohomology.LAdicSheaf.map_padic_eq_gradedCharSeries_of_reductions`: the rational
  image of an ℓ-adic limit of the `det(1 - π_X^* T | Kₙ)⁻¹`.
* `Stacks.EtaleCohomology.LAdicSheaf.adicLFunction_eq_iff_of_isPerfect`: the `ℤ_ℓ`-coefficient
  identity is equivalent to the identity of Tag 03V0 for `F ⊗ ℚ_ℓ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale
open Stacks.Frobenius Stacks.InverseSystem PowerSeries

universe u

namespace Stacks.EtaleCohomology

/-- **`ℤ_ℓ` has no `ℓ`-torsion**: the map `ℤ_ℓ⟦T⟧ → ℚ_ℓ⟦T⟧` is injective. -/
public theorem padicPowerSeries_map_injective (ℓ : ℕ) [Fact ℓ.Prime] :
    Function.Injective (PowerSeries.map (algebraMap ℤ_[ℓ] ℚ_[ℓ])) :=
  PowerSeries.map_injective _ (FaithfulSMul.algebraMap_injective ℤ_[ℓ] ℚ_[ℓ])

/-- A series over `ℤ_ℓ` whose reductions modulo every `ℓⁿ⁺¹` have constant coefficient `1` has
constant coefficient `1`. -/
public theorem constantCoeff_eq_one_of_toZModPow {ℓ : ℕ} [Fact ℓ.Prime] {c : ℤ_[ℓ]⟦X⟧}
    (hc : ∀ n : ℕ, constantCoeff (PowerSeries.map (PadicInt.toZModPow (n + 1)) c) = 1) :
    constantCoeff c = 1 :=
  eq_of_toZModPow_succ_eq fun n => by
    have h := hc n
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map] at h
    rw [map_one, ← h, coeff_zero_eq_constantCoeff_apply]

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
variable [AlgebraicGeometry.IsNoetherian X.1] [Fact ℓ.Prime]

/-- Flatness of the levels, read on Mathlib's small étale site. -/
public theorem LAdicSheaf.powExact_etaleLevel (F : LAdicSheaf B X ℓ)
    (hF : ∀ n, PowExact ℓ (n + 1) (F.level n)) (n : ℕ) :
    PowExact ℓ (n + 1) (LAdicSheaf.etaleLevel B X ℓ F n) :=
  have : (SmallEtale.sheafEquiv B X.1 X.property
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).functor.Additive :=
    Functor.additive_of_preserves_binary_products _
  (hF n).map
    (SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).functor
    (zmodSheaf_nsmul_id (SmallEtale.topology B X.1 X.property) (ℓ ^ (n + 1)) (F.level n))

variable {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

omit [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- **The rational image of an ℓ-adic limit of `det(1 - π_X^* T | Kₙ)⁻¹`.** If the complexes
`Kₙ = RΓ_c(X_k̄, Fₙ)` are perfect and `c ∈ ℤ_ℓ⟦T⟧` reduces modulo every `ℓⁿ⁺¹` to
`det(1 - π_X^* T | Kₙ)⁻¹`, then
`c ⊗ ℚ_ℓ = ∏ᵢ det(1 - π_X^* T | Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)) ^ ((-1) ^ (i + 1))`. -/
public theorem LAdicSheaf.map_padic_eq_gradedCharSeries_of_reductions (F : LAdicSheaf B X ℓ)
    (hF : ∀ n, PowExact ℓ (n + 1) (LAdicSheaf.etaleLevel B X ℓ F n))
    (hP : ∀ n, StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar
        (LAdicSheaf.levelComplex B X ℓ F n))))
    {c : ℤ_[ℓ]⟦X⟧}
    (hc : ∀ n : ℕ, PowerSeries.map (PadicInt.toZModPow (n + 1)) c =
      (((FilteredDerived.perfectDerivedCharSeries (ZMod (ℓ ^ (n + 1)))
        ((LAdicSheaf.geometricPerfectTower B X ℓ f j kbar p q hcard F hF hP).obj n) (hP n)
        ((LAdicSheaf.geometricPerfectTower B X ℓ f j kbar p q hcard F hF hP).endo n))⁻¹ :
          (ZMod (ℓ ^ (n + 1)))⟦X⟧ˣ) : (ZMod (ℓ ^ (n + 1)))⟦X⟧)) :
    PowerSeries.map (algebraMap ℤ_[ℓ] ℚ_[ℓ]) c =
      gradedCharSeries
        (fun i => LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i)
        (fun i => (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q
          hcard F i).hom) := by
  set T := LAdicSheaf.geometricPerfectTower B X ℓ f j kbar p q hcard F hF hP
  have hunit : ∀ n, constantCoeff (PowerSeries.map (PadicInt.toZModPow (n + 1)) c) = 1 := by
    intro n
    rw [hc n]
    exact PowerSeries.constantCoeff_units_inv
      (FilteredDerived.constantCoeff_perfectDerivedCharSeries _ _ _ _)
  have hc1 : constantCoeff c = 1 := constantCoeff_eq_one_of_toZModPow hunit
  refine LAdicSheaf.map_padic_eq_gradedCharSeries_of_logDerivative B X ℓ f j kbar p q hcard F hF hP
    hc1 fun m hm n => ?_
  rw [← coeff_map, map_logDerivative _ hc1, hc n]
  exact FilteredDerived.coeff_logDerivative_inv_perfectDerivedCharSeries (ZMod (ℓ ^ (n + 1)))
    (T.obj n) (hP n) (T.endo n) hm

omit [IsSeparated f] in
/-- **The `ℤ_ℓ`-coefficient determinant identity is equivalent to that of Tag 03V0.** Let `F` be an
ℓ-adic sheaf with flat levels whose complexes `Kₙ = RΓ_c(X_k̄, Fₙ)` are perfect, and `c ∈ ℤ_ℓ⟦T⟧`
the ℓ-adic limit of the `det(1 - π_X^* T | Kₙ)⁻¹`.  Then `L_{ℤ_ℓ}(X, F) = c` in `ℤ_ℓ⟦T⟧` if and
only if
`L(X, F ⊗ ℚ_ℓ) = ∏ᵢ det(1 - π_X^* T | Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)) ^ ((-1) ^ (i + 1))` in `ℚ_ℓ⟦T⟧`. -/
public theorem LAdicSheaf.adicLFunction_eq_iff_of_isPerfect (F : LAdicSheaf B X ℓ)
    (hF : ∀ n, PowExact ℓ (n + 1) (F.level n))
    (hP : ∀ n, StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar
        (LAdicSheaf.levelComplex B X ℓ F n))))
    {c : ℤ_[ℓ]⟦X⟧}
    (hc : ∀ n : ℕ, PowerSeries.map (PadicInt.toZModPow (n + 1)) c =
      (((FilteredDerived.perfectDerivedCharSeries (ZMod (ℓ ^ (n + 1)))
        ((LAdicSheaf.geometricPerfectTower B X ℓ f j kbar p q hcard F
          (LAdicSheaf.powExact_etaleLevel B X ℓ F hF) hP).obj n) (hP n)
        ((LAdicSheaf.geometricPerfectTower B X ℓ f j kbar p q hcard F
          (LAdicSheaf.powExact_etaleLevel B X ℓ F hF) hP).endo n))⁻¹ :
          (ZMod (ℓ ^ (n + 1)))⟦X⟧ˣ) : (ZMod (ℓ ^ (n + 1)))⟦X⟧)) :
    LAdicSheaf.adicLFunction B X ℓ F hF f = c ↔
      LAdicSheaf.rationalLFunction B X ℓ F f =
        gradedCharSeries
          (fun i => LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i)
          (fun i => (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q
            hcard F i).hom) := by
  rw [← LAdicSheaf.map_adicLFunction_padic B X ℓ F hF f,
    ← LAdicSheaf.map_padic_eq_gradedCharSeries_of_reductions B X ℓ f j kbar p q hcard F
      (LAdicSheaf.powExact_etaleLevel B X ℓ F hF) hP hc]
  exact (padicPowerSeries_map_injective ℓ).eq_iff.symm

omit [IsSeparated f] in
/-- **The determinant identity with `ℤ_ℓ` coefficients, from the finite-coefficient one at every
level.** If at every level `n` the complex `Kₙ = RΓ_c(X_k̄, Fₙ)` is perfect with
`L(X, Fₙ) = det(1 - π_X^* T | Kₙ)⁻¹` (Tag 03UZ for `Λ = ℤ/ℓⁿ⁺¹ℤ`), then the `Kₙ` are perfect, the
`ℤ_ℓ`-valued L-function is the ℓ-adic limit of the `det(1 - π_X^* T | Kₙ)⁻¹`, and for any such
ℓ-adic limit `c` the identity `L_{ℤ_ℓ}(X, F) = c` is equivalent to the identity of Tag 03V0 for
`F ⊗ ℚ_ℓ`. -/
public theorem LAdicSheaf.adicDeterminantIdentity_of_levels (F : LAdicSheaf B X ℓ)
    (hF : ∀ n, PowExact ℓ (n + 1) (F.level n))
    (hlev : ∀ n : ℕ, ∃ hperf : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
        (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar
          (LAdicSheaf.levelComplex B X ℓ F n))),
      constructibleFlatLFunction B X (ZMod (ℓ ^ (n + 1))) (F.level n) f
          (LAdicSheaf.isConstructibleFlatModuleSheaf_level B X ℓ F hF n) =
        (((FilteredDerived.perfectDerivedCharSeries (ZMod (ℓ ^ (n + 1))) _ hperf
          (DerivedCategory.Plus.ι.map (canonicalCompactSupportFrobenius.{u, 0}
            (ZMod (ℓ ^ (n + 1))) f j kbar p q hcard (LAdicSheaf.levelComplex B X ℓ F n))))⁻¹ :
              (ZMod (ℓ ^ (n + 1)))⟦X⟧ˣ) : (ZMod (ℓ ^ (n + 1)))⟦X⟧)) :
    ∃ hP : ∀ n, StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
        (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar
          (LAdicSheaf.levelComplex B X ℓ F n))),
      (∀ n : ℕ, PowerSeries.map (PadicInt.toZModPow (n + 1))
          (LAdicSheaf.adicLFunction B X ℓ F hF f) =
        (((FilteredDerived.perfectDerivedCharSeries (ZMod (ℓ ^ (n + 1)))
          ((LAdicSheaf.geometricPerfectTower B X ℓ f j kbar p q hcard F
            (LAdicSheaf.powExact_etaleLevel B X ℓ F hF) hP).obj n) (hP n)
          ((LAdicSheaf.geometricPerfectTower B X ℓ f j kbar p q hcard F
            (LAdicSheaf.powExact_etaleLevel B X ℓ F hF) hP).endo n))⁻¹ :
            (ZMod (ℓ ^ (n + 1)))⟦X⟧ˣ) : (ZMod (ℓ ^ (n + 1)))⟦X⟧)) ∧
      ∀ c : ℤ_[ℓ]⟦X⟧, (∀ n : ℕ, PowerSeries.map (PadicInt.toZModPow (n + 1)) c =
          (((FilteredDerived.perfectDerivedCharSeries (ZMod (ℓ ^ (n + 1)))
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
                hcard F i).hom)) := by
  choose hP hL using hlev
  refine ⟨hP, fun n => ?_, fun c hc =>
    LAdicSheaf.adicLFunction_eq_iff_of_isPerfect B X ℓ f j kbar p q hcard F hF hP hc⟩
  have := zmod_pow_succ_isLocalRing (ℓ := ℓ) n
  have hcf := LAdicSheaf.isConstructibleFlatModuleSheaf_level B X ℓ F hF n
  rw [LAdicSheaf.map_adicLFunction_toZModPow B X ℓ F hF f n
      (finite_etaleModuleStalk_of_isConstructibleFlatModuleSheaf.{u, u + 1, 0} B X
        (ZMod (ℓ ^ (n + 1))) (F.level n) hcf)
      (projective_etaleModuleStalk_of_isConstructibleFlatModuleSheaf.{u, u + 1, 0} B X
        (ZMod (ℓ ^ (n + 1))) (F.level n) hcf)]
  change lFunctionOfConstructibleFlat B X _ (F.level n) f hcf = _
  rw [← constructibleFlatLFunction_eq_lFunctionOfConstructibleFlat, hL n]
  rfl

end Stacks.EtaleCohomology

end
