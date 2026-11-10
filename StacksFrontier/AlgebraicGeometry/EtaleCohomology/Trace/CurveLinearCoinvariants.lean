module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTopCohomologyCoinvariantsNatural
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTopCohomologyLevelsNatural
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RestrictScalarsCoinvariants
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonAffineLineAssembly

/-!
# `H²_c` of `ℱ_{Res_b σ}` on a smooth geometrically connected curve, `E`-linearly

Let `U` be a smooth geometrically connected curve over a finite field `k` with `q` elements, `E` a
finite extension of `ℚ_ℓ` with basis `b`, and `σ : π₁(U, x̄) → GL_m(E)` with `Res_b σ` continuous.
The integral part `O` of `E` acts on `ℱ_{Res_b σ}`, hence `E` acts on
`H²_c(U_k̄, ℱ_{Res_b σ} ⊗ ℚ_ℓ)`. This file proves that the identification of this cohomology with
the geometric coinvariants ([Stacks, Tag 03VN] in the proof of Tag 03VH) is `E`-linear:
`H²_c(U_k̄, ℱ_{Res_b σ} ⊗ ℚ_ℓ) ≅ (E^m)_{π₁(U_k̄)}` as `E`-vector spaces, carrying `π_U^*` to
`q · σ(φ)`.

The level isomorphisms are natural in the endomorphisms of the coefficients
(`LAdicSheaf.exists_linearEquiv_compactSupportSheafCohomology_two_levelModule_natural`, names
being relative to `Stacks.EtaleCohomology`), so the identification over `ℚ_ℓ` carries the action
of every `o ∈ O` to its action on the coinvariants of `Res_b σ`
(`LAdicSheaf.exists_linearEquiv_coinvariants_of_levels_natural`); these are the coinvariants of
`σ` with `o` acting by multiplication (`restrictScalarsCoinvariantsAddEquiv_scalar`), and a map
compatible with the action of `O` is `E`-linear since `E = O[1/ℓ]`.

The statements consume objects defined in the standard model `HasDerivedCategory.standard` of the
derived category, which is therefore a local instance here.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.CoefficientSheaf.map_rationalRingHom_of_integral`.
* `Stacks.EtaleCohomology.curveLinearCoinvariantsInput`: the proposition
  `Stacks.EtaleCohomology.CurveLinearCoinvariantsInput` holds.

## References

* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Representation
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius Stacks.GroupCohomology

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-! ### Maps compatible with the integral part are `E`-linear -/

namespace LAdicSheaf.CoefficientSheaf

variable {ℓ : ℕ} [Fact ℓ.Prime] {B : BigEtaleSite.{u}} {X : B.Scheme}
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
  {O : Type} [CommRing O] [Algebra ℤ_[ℓ] O] (F : LAdicSheaf.CoefficientSheaf B X ℓ O)
  {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar] (i : ℤ)
  (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [Algebra O E]
  [IsLocalization (Submonoid.powers (ℓ : O)) E]

/-- **A map out of `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` compatible with the action of `O` is compatible with the
action of `E = O[1/ℓ]`.** -/
theorem map_rationalRingHom_of_integral {W : Type*} [AddCommGroup W] [Module E W]
    (T : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F.toLAdicSheaf i →+
      W)
    (hT : ∀ o v, T (F.rationalIntegralRingHom f j kbar i o v) = algebraMap O E o • T v) (c : E)
    (v : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F.toLAdicSheaf i) :
    T (F.rationalRingHom f j kbar i E c v) = c • T v := by
  obtain ⟨⟨s, t⟩, hst⟩ := IsLocalization.surj (Submonoid.powers (ℓ : O)) c
  obtain ⟨N, hN⟩ := t.2
  have hℓ : ((ℓ ^ N : ℕ) : E) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ_[ℓ] E)]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 (pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero))
  have ht : algebraMap O E (t : O) = ((ℓ ^ N : ℕ) : E) := by
    rw [← hN, map_pow, map_natCast, Nat.cast_pow]
  have key : F.rationalRingHom f j kbar i E c * F.rationalRingHom f j kbar i E (algebraMap O E t) =
      F.rationalIntegralRingHom f j kbar i s := by
    rw [← map_mul, hst, rationalRingHom_algebraMap_apply]
  have htN : F.rationalRingHom f j kbar i E (algebraMap O E t) =
      ((ℓ ^ N : ℕ) : Module.End ℚ_[ℓ] _) := by
    rw [ht, map_natCast]
  have h1 : T (F.rationalIntegralRingHom f j kbar i s v) =
      (ℓ ^ N) • T (F.rationalRingHom f j kbar i E c v) := by
    rw [← key, Module.End.mul_apply, htN, Module.End.natCast_apply, map_nsmul, map_nsmul]
  have h2 : T (F.rationalIntegralRingHom f j kbar i s v) = (ℓ ^ N) • (c • T v) := by
    rw [hT, ← hst, mul_comm, mul_smul, ht, Nat.cast_smul_eq_nsmul]
  have h3 : ((ℓ ^ N : ℕ) : E) • T (F.rationalRingHom f j kbar i E c v) =
      ((ℓ ^ N : ℕ) : E) • (c • T v) := by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, ← h1, ← h2]
  exact smul_right_injective W hℓ h3

end LAdicSheaf.CoefficientSheaf

/-! ### The `E`-linear coinvariants input -/

/-- **`H²_c(U_k̄, ℱ_{Res_b σ} ⊗ ℚ_ℓ)` is the geometric coinvariants of `σ`, `E`-linearly**
([Stacks, Tag 03VN] with coefficients in `E`, in the proof of Tag 03VH): on a smooth geometrically
connected curve over a finite field with `q` elements and for every `φ` over the inverse of the
Frobenius, an `E`-linear isomorphism with the coinvariants of `σ` under `π₁(U_k̄)` carrying `π_U^*`
to `q · σ(φ)`. -/
theorem curveLinearCoinvariantsInput : CurveLinearCoinvariantsInput.{u} := by
  intro B U ℓ _ _ _ _ _ _ k _ _ f _ _ _ _ j kbar _ _ _ _ p n _ _ hcard hℓ x E _ _ _ d b m σ hσ φ hφ
  have := compactSpace_etaleFundamentalGroup U.1 x
  have : IsCurve k f := isCurve_of_smoothOfRelativeDimension_one_of_connectedSpace f
  have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed k
  let τ := restrictScalarsRep b σ
  let Hg := (etaleFundamentalGroupMap f x).toMonoidHom.ker
  let P := representationSheafConj B U x τ hσ
  let α := restrictScalarsScalarAlgHom (F := ℚ_[ℓ]) b m
  let O := conjIntegralSubring P α
  let A : O → Matrix (Fin (m * d)) (Fin (m * d)) ℤ_[ℓ] := fun o => conjIntegralLift P α o
  have hA : ∀ o g, A o * (integralModel τ hσ g).val = (integralModel τ hσ g).val * A o :=
    conjIntegralLift_mul_integralModel B U x τ hσ α (restrictScalarsScalarAlgHom_commute b σ)
  have hAB : ∀ o, ((exists_conj_integral τ hσ).choose).val *
      (A o).map (PadicInt.Coe.ringHom (p := ℓ)) =
        α (o : E) * ((exists_conj_integral τ hσ).choose).val := fun o => by
    have h : (PadicInt.Coe.ringHom (p := ℓ)).mapMatrix (A o) = _ := mapMatrix_conjIntegralLift P α o
    change P.val * (PadicInt.Coe.ringHom (p := ℓ)).mapMatrix (A o) = α (o : E) * P.val
    rw [h, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mul]
  obtain ⟨e, he, hen⟩ := LAdicSheaf.exists_linearEquiv_coinvariants_of_levels_natural B U ℓ f j kbar
    p n hcard x τ hσ Hg φ A hA (fun N => by
      have : NeZero (ℓ ^ (N + 1)) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
      obtain ⟨e, he, hn⟩ :=
        LAdicSheaf.exists_linearEquiv_compactSupportSheafCohomology_two_levelModule_natural
          B U ℓ f j kbar p n hcard x τ hσ hℓ φ hφ N
      exact ⟨e, he, fun a t =>
        hn (levelModuleMap (continuous_integralModel τ hσ) (A a) (hA a) (N + 1))
        (levelCoinvariantsMap Hg (continuous_integralModel τ hσ) (A a) (hA a) (N + 1))
        (levelModuleMap_comp_levelCoinvariantsQuotient Hg (continuous_integralModel τ hσ) (A a)
          (hA a) (N + 1)) t⟩)
    (fun o => α (o : E)) (fun o g => restrictScalarsScalarAlgHom_commute b σ (o : E) g) hAB
    (LAdicSheaf.surjective_geometricCompactlySupportedCohomologySystem_map_two B U ℓ f j kbar
      (LAdicSheaf.representationSheaf B U x τ hσ)
      (IsCurve.topologicalKrullDim_eq_one (f := f)).le)
  let FS := restrictScalarsRepCoefficientSheaf B U x b σ hσ
  let Ξ := restrictScalarsCoinvariantsAddEquiv b Hg σ
  let Φ :
      LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j kbar FS.toLAdicSheaf 2 ≃+
      Coinvariants ((matrixRepresentation σ).comp Hg.subtype) := e.toAddEquiv.trans Ξ
  have hT : ∀ o v, Φ.toAddMonoidHom (FS.rationalIntegralRingHom f j kbar 2 o v) =
      algebraMap O E o • Φ.toAddMonoidHom v := fun o v =>
    (congrArg Ξ (hen o v)).trans (restrictScalarsCoinvariantsAddEquiv_scalar b Hg σ (o : E) (e v))
  let := FS.rationalCohomologyModule f j kbar 2 E
  refine ⟨Φ.toLinearEquiv (FS.map_rationalRingHom_of_integral f j kbar 2 E Φ.toAddMonoidHom hT),
    fun v => ?_⟩
  have h1 := congrArg Ξ (he v)
  rw [Nat.cast_smul_eq_nsmul, map_nsmul,
    restrictScalarsCoinvariantsAddEquiv_coinvariantsFrobenius] at h1
  exact h1.trans (Nat.cast_smul_eq_nsmul E _ _).symm

end Stacks.EtaleCohomology

end
