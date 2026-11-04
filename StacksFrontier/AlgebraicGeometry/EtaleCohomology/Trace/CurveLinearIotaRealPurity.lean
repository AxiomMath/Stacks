module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.IotaRealizableAbsIrrPurity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveDegreeOneWeights
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveLinearTraceFormula
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveLinearCoinvariants
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusTraceFormulaOfCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseCompactSupportZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIICurveBoundAffineLineInputs

/-!
# Weil II 1.5.1 with coefficients in `E` on a smooth affine curve over a finite field

Let `U` be a smooth geometrically connected affine curve over a finite field `k` (`#k = q`), `E` a
finite extension of `ℚ_ℓ` with basis `b`, `ℓ ≠ p`, and `ρ, ρ' : π₁(U, x̄) → GL(E)` with continuous
restrictions of scalars, such that `ρ ⊕ ρ'` has Frobenius characteristic polynomials with real
coefficients along `ι' : E → ℂ`. If `ρ` is absolutely irreducible, it is `ι'`-pure: there is
`β > 0` with every root along `ι'` of the characteristic polynomial of `ρ(F_y)` at a closed point
`y` of absolute value `β ^ deg y`
(`Stacks.EtaleCohomology.exists_norm_eq_pow_of_isIotaRealizable_curve`; Weil II 1.5.1, Kedlaya,
*Fourier transforms and p-adic Weil II*, Theorem 6.5.2).

The group-level inputs are discharged on the curve: the `E`-linear Frobenius trace formula
`Stacks.EtaleCohomology.SatisfiesFrobeniusTraceFormula` for every `E`-linear representation with
continuous restriction of scalars
(`Stacks.EtaleCohomology.satisfiesFrobeniusTraceFormula_restrictScalarsRep_curve`) comes from the
`E`-linear trace formula (`Stacks.EtaleCohomology.curveLinearTraceFormulaInput`), the vanishing of
`H⁰_c` on an affine curve and `H²_c ≅` geometric coinvariants
(`Stacks.EtaleCohomology.curveLinearCoinvariantsInput`); Weil II 1.3.4 is
`Stacks.EtaleCohomology.forall_eq_zero_of_isCurve`.

## Main results

* `Stacks.EtaleCohomology.satisfiesFrobeniusTraceFormula_restrictScalarsRep_curve`.
* `Stacks.EtaleCohomology.exists_norm_eq_pow_of_isIotaRealizable_curve`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale Matrix

universe u

namespace Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) (U : B.Scheme) (ℓ : ℕ)
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B U.1 U.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian U.1] [Fact ℓ.Prime] [ConnectedSpace U.1]
  {k : Type u} [Field k] [Fintype k] (f : U.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [SmoothOfRelativeDimension 1 f]
  [IsAffine U.1]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  [IsAlgClosure k kbar]
  [ConnectedSpace ↥(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))]
  (p n : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ n)

include j kbar in
/-- **The `E`-linear Frobenius trace formula on a smooth affine curve, in cohomology-free form**:
every `E`-linear representation `τ` of `π₁(U, x̄)` with continuous restriction of scalars satisfies
`Stacks.EtaleCohomology.SatisfiesFrobeniusTraceFormula` along every `ι₁ : E → ℂ`, for a lift `φ`
of the geometric Frobenius of `k`. -/
public theorem satisfiesFrobeniusTraceFormula_restrictScalarsRep_curve (hℓp : ℓ ≠ p)
    (x : GeometricPoint U.1) (φ : EtaleFundamentalGroup U.1 x)
    (hφ : etaleFundamentalGroupMap f x φ = (finiteFieldFrobenius p n hcard (x.map f))⁻¹)
    (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {d : ℕ}
    (b : Module.Basis (Fin d) ℚ_[ℓ] E) (ι₁ : E →+* ℂ) {m : ℕ}
    (τ : EtaleFundamentalGroup U.1 x →* GL (Fin m) E) (hτ : Continuous (restrictScalarsRep b τ)) :
    SatisfiesFrobeniusTraceFormula ((p ^ n : ℕ) : ℝ) ι₁
      (etaleFundamentalGroupMap f x).toMonoidHom.ker φ
      (fun y : closedPoints U.1 => geometricFrobeniusFamily f x y)
      (fun y => residueDegree f y.1) τ := by
  have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed k
  have : CharP kbar p := charP_of_injective_algebraMap (algebraMap k kbar).injective p
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap ℚ_[ℓ] E).injective
  have : Nonempty U.1 := ConnectedSpace.toNonempty
  have hdim : topologicalKrullDim U.1 ≤ 1 :=
    (topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 1 f).le
  set F := restrictScalarsRepCoefficientSheaf B U x b τ hτ with hF
  let hmod : ∀ i : ℕ, Module E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f
      j kbar F.toLAdicSheaf (i : ℤ)) := fun i => F.rationalCohomologyModule f j kbar (i : ℤ) E
  have : ∀ i : ℕ, IsScalarTower ℚ_[ℓ] E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology
      B U ℓ f j kbar F.toLAdicSheaf (i : ℤ)) := fun i =>
    F.rationalCohomologyModule_isScalarTower f j kbar (i : ℤ) E
      (algebraMap_conjIntegralSubring_algebraMap _ _)
  have : ∀ i : ℕ, FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology
      B U ℓ f j kbar F.toLAdicSheaf (i : ℤ)) := fun i =>
    LAdicSheaf.finite_rationalGeometricCompactlySupportedCohomology_of_topologicalKrullDim_le_one
      B U ℓ f j kbar p n hcard hdim _ (i : ℤ)
  have : ∀ i : ℕ, FiniteDimensional E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology
      B U ℓ f j kbar F.toLAdicSheaf (i : ℤ)) := fun i =>
    Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E _
  obtain ⟨e₂, he₂⟩ := curveLinearCoinvariantsInput B U ℓ k f j kbar p n hcard hℓp x E b τ hτ φ hφ
  exact satisfiesFrobeniusTraceFormula_of_trace_eq (etaleFundamentalGroupMap f x).toMonoidHom.ker
    (p ^ n) (Nat.cast_ne_zero.2 (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)) ι₁ φ
    (fun y : closedPoints U.1 => geometricFrobeniusFamily f x y) (fun y => residueDegree f y.1) τ
    (fun i : ℕ => ↥(LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j kbar
      F.toLAdicSheaf (i : ℤ)))
    (fun i => F.rationalGeometricCompactlySupportedFrobenius f j kbar (i : ℤ) E p n hcard)
    (LAdicSheaf.subsingleton_rationalGeometricCompactlySupportedCohomology_zero_representationSheaf
      B U ℓ f j kbar x _ _) e₂ he₂
    (fun N hN => curveLinearTraceFormulaInput B U ℓ k f j kbar p n hcard hℓp x E b τ hτ N hN)

include j kbar p n hcard in
/-- **Weil II 1.5.1 with coefficients in `E` on a smooth affine curve over a finite field**
(Kedlaya, *Fourier transforms and p-adic Weil II*, Theorem 6.5.2): for `ρ, ρ'` with continuous
restrictions of scalars, `ρ ⊕ ρ'` with `ι'`-real Frobenius characteristic polynomials and `ρ`
absolutely irreducible, there is `β > 0` with every root along `ι'` of the characteristic
polynomial of `ρ(F_y)` of absolute value `β ^ deg y`. -/
public theorem exists_norm_eq_pow_of_isIotaRealizable_curve (hℓp : ℓ ≠ p) (x : GeometricPoint U.1)
    (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {d : ℕ}
    (b : Module.Basis (Fin d) ℚ_[ℓ] E) {r r' : ℕ}
    (ρ : EtaleFundamentalGroup U.1 x →* GL (Fin r) E) (hρ : Continuous (restrictScalarsRep b ρ))
    (ρ' : EtaleFundamentalGroup U.1 x →* GL (Fin r') E)
    (hρ' : Continuous (restrictScalarsRep b ρ')) (ι' : E →+* ℂ)
    (hreal : ∀ (y : closedPoints U.1) (m : ℕ),
      ι' (((ρ (geometricFrobeniusFamily f x y)).val.charpoly *
        (ρ' (geometricFrobeniusFamily f x y)).val.charpoly).coeff m) ∈ Set.range ((↑) : ℝ → ℂ))
    (hirr : ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra E K] (W : Submodule K (Fin r → K)),
      (∀ g, ∀ v ∈ W, (ρ g).val.map (algebraMap E K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤) :
    ∃ β : ℝ, 0 < β ∧ ∀ (y : closedPoints U.1) (z : ℂ),
      ((ρ (geometricFrobeniusFamily f x y)).val.charpoly.map ι').IsRoot z →
        ‖z‖ = β ^ residueDegree f y.1 := by
  classical
  have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed k
  obtain ⟨φ, hφ⟩ := exists_etaleFundamentalGroupMap_eq_finiteFieldFrobenius_inv p n hcard f x kbar
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : IsIntegral U.1 := Stacks.Chow.isIntegral_of_connectedSpace_of_smooth f
  have : IsCurve k f := (isCurve_iff k f).2
    ⟨{ toIsIntegral := ‹_›
       toIsSeparated := inferInstance
       toLocallyOfFiniteType := inferInstance
       toQuasiCompact := inferInstance },
      topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 1 f⟩
  have hD1 := forall_eq_zero_of_isCurve (K := ℂ_[ℓ]) p n hcard f x ℓ hℓp φ hφ
  have hcomm := commutator_mem_ker_etaleFundamentalGroupMap_of_finite k f x
  have hFr : ∀ y : closedPoints U.1, (φ ^ residueDegree f y.1)⁻¹ * geometricFrobeniusFamily f x y ∈
      (etaleFundamentalGroupMap f x).toMonoidHom.ker := fun y => by
    have := finite_residueField f y.1 y.2
    exact inv_pow_mul_geometricFrobeniusFamily_mem_ker p n hcard f x y φ hφ
  have hdeg : ∀ y : closedPoints U.1, 0 < residueDegree f y.1 := fun y =>
    residueDegree_pos f y.1 y.2
  have hfinpts : ∀ m : ℕ, 0 < m → {y : closedPoints U.1 | residueDegree f y.1 ∣ m}.Finite :=
    fun m hm => (finite_setOf_closedPoints_residueDegree_le f m).subset fun y hy =>
      Nat.le_of_dvd hm hy
  have : Countable (closedPoints U.1) := by
    have h : (Set.univ : Set (closedPoints U.1)) =
        ⋃ m : ℕ, {y : closedPoints U.1 | residueDegree f y.1 ≤ m} := by
      ext y
      simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_ofPred_eq, true_iff]
      exact ⟨_, le_rfl⟩
    exact Set.countable_univ_iff.1 (h ▸ Set.countable_iUnion fun m =>
      (finite_setOf_closedPoints_residueDegree_le f m).countable)
  have hqN : 1 < p ^ n := by
    rw [← hcard]
    exact Fintype.one_lt_card
  have hq : (1 : ℝ) < ((p ^ n : ℕ) : ℝ) := by exact_mod_cast hqN
  have := compactSpace_etaleFundamentalGroup U.1 x
  exact exists_norm_eq_pow_of_isIotaRealizable_restrictScalarsRep b
    (etaleFundamentalGroupMap f x).toMonoidHom.ker φ hcomm hD1
    (fun y : closedPoints U.1 => geometricFrobeniusFamily f x y) (fun y => residueDegree f y.1)
    hFr hdeg hfinpts hq
    (fun ι₁ m τ hτ => satisfiesFrobeniusTraceFormula_restrictScalarsRep_curve B U ℓ f j kbar p n
      hcard hℓp x φ hφ E b ι₁ τ hτ) ρ hρ ρ' hρ' ι' hreal hirr

end Stacks.EtaleCohomology

end
