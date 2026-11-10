module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PadicIntegerRingModel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonAffineLineLinear
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TwistedTraceIsogeny
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.LisseRepresentation

/-!
# Changing the lattice of `ℱ_{Res_b σ}` to one over the ring of integers

Let `σ : π₁(X, x̄) → GL_m(E)` with `E` finite over `ℚ_ℓ`. The sheaf
`Stacks.EtaleCohomology.restrictScalarsRepCoefficientSheaf` is built from an integral model
`P⁻¹ Res_b σ P` of `Res_b σ` over `ℤ_ℓ`, with the integral part `O` of `E` for this model acting;
its lattice need not be free over `O`. The model `σ'` of `σ` over the ring of integers `O_E`
(`Stacks.EtaleCohomology.modelRep`) has restriction of scalars `T Res_b σ T⁻¹`, and suitable
multiples `A = ℓᵏ T P` and `A' = ℓᵏ' P⁻¹ T⁻¹` are integral intertwiners with `A' A = A A' = ℓ^K`.
The twisted traces of Frobenius on the rational cohomology of the two sheaves agree.

## Main definitions

* `Stacks.EtaleCohomology.latticeChangeMatrix`: the integral intertwiner `ℓᵏ T P`.
* `Stacks.EtaleCohomology.latticeChangeMatrixInv`: the integral intertwiner `ℓᵏ' P⁻¹ T⁻¹`.

## Main results

* `Stacks.EtaleCohomology.exists_pow_smul_isIntegralMatrix`: some `ℓ`-power multiple of a matrix
  over `ℚ_ℓ` is integral.
* `Stacks.EtaleCohomology.trace_rationalIntegralRingHom_restrictScalarsRep_eq_model`: the twisted
  traces of Frobenius on `ℱ_{Res_b σ}` and on the sheaf of the model of `σ` over `O_E` agree, for
  the elements of `O ∩ O_E`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale Module Matrix

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- **Some `ℓ`-power multiple of a matrix over `ℚ_ℓ` is integral.** -/
public theorem exists_pow_smul_isIntegralMatrix {r : ℕ} (M : Matrix (Fin r) (Fin r) ℚ_[ℓ]) :
    ∃ k : ℕ, IsIntegralMatrix (((ℓ : ℚ_[ℓ]) ^ k) • M) := by
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (∑ i, ∑ j, ‖M i j‖)
    (Nat.one_lt_cast.2 (Fact.out : ℓ.Prime).one_lt : (1 : ℝ) < ℓ)
  refine ⟨N, fun i j ↦ ?_⟩
  rw [Matrix.smul_apply, smul_eq_mul, norm_mul, norm_pow, Padic.norm_p, inv_pow,
    inv_mul_le_iff₀ (pow_pos (Nat.cast_pos.2 (Fact.out : ℓ.Prime).pos) N), mul_one]
  exact ((Finset.single_le_sum (f := fun j ↦ ‖M i j‖) (fun _ _ ↦ norm_nonneg _)
    (Finset.mem_univ j)).trans (Finset.single_le_sum (f := fun i ↦ ∑ j, ‖M i j‖)
      (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ norm_nonneg _) (Finset.mem_univ i))).trans hN.le

section Intertwiner

variable {E : Type} [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]

attribute [local instance] padicIntAlgebraOfRat

local notation "𝒪" => integralClosure ℤ_[ℓ] E

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {d m : ℕ} (b : Basis (Fin d) ℚ_[ℓ] E) (σ : G →* GL (Fin m) E)
  (hσ : Continuous (restrictScalarsRep b σ))

/-- The conjugating matrix of the integral model of `Res_b σ`. -/
public abbrev integralModelConj : GL (Fin (m * d)) ℚ_[ℓ] :=
  (exists_conj_integral (restrictScalarsRep b σ) hσ).choose

/-- The exponent making `T P` integral. -/
public def latticeChangeExp : ℕ :=
  (exists_pow_smul_isIntegralMatrix
    (modelConjMatrix b σ hσ * (integralModelConj b σ hσ).val)).choose

/-- The exponent making `P⁻¹ T⁻¹` integral. -/
public def latticeChangeExpInv : ℕ :=
  (exists_pow_smul_isIntegralMatrix
    ((integralModelConj b σ hσ)⁻¹.val * modelConjMatrixInv b σ hσ)).choose

/-- **The intertwiner `ℓᵏ T P` from the integral model of `Res_b σ` to the model over `O_E`.** -/
public def latticeChangeMatrix : Matrix (Fin (m * d)) (Fin (m * d)) ℤ_[ℓ] :=
  (exists_pow_smul_isIntegralMatrix
    (modelConjMatrix b σ hσ * (integralModelConj b σ hσ).val)).choose_spec.lift

/-- **The intertwiner `ℓᵏ' P⁻¹ T⁻¹` back.** -/
public def latticeChangeMatrixInv : Matrix (Fin (m * d)) (Fin (m * d)) ℤ_[ℓ] :=
  (exists_pow_smul_isIntegralMatrix
    ((integralModelConj b σ hσ)⁻¹.val * modelConjMatrixInv b σ hσ)).choose_spec.lift

/-- The image of `ℓᵏ T P` over `ℚ_ℓ`. -/
public theorem map_latticeChangeMatrix :
    (PadicInt.Coe.ringHom (p := ℓ)).mapMatrix (latticeChangeMatrix b σ hσ) =
      ((ℓ : ℚ_[ℓ]) ^ latticeChangeExp b σ hσ) •
        (modelConjMatrix b σ hσ * (integralModelConj b σ hσ).val) :=
  IsIntegralMatrix.mapMatrix_lift _

/-- The image of `ℓᵏ' P⁻¹ T⁻¹` over `ℚ_ℓ`. -/
public theorem map_latticeChangeMatrixInv :
    (PadicInt.Coe.ringHom (p := ℓ)).mapMatrix (latticeChangeMatrixInv b σ hσ) =
      ((ℓ : ℚ_[ℓ]) ^ latticeChangeExpInv b σ hσ) •
        ((integralModelConj b σ hσ)⁻¹.val * modelConjMatrixInv b σ hσ) :=
  IsIntegralMatrix.mapMatrix_lift _

omit [FiniteDimensional ℚ_[ℓ] E] in
/-- The integral model of `Res_b σ`, read over `ℚ_ℓ`, is `P⁻¹ Res_b σ P`. -/
public theorem map_integralModel_val (g : G) :
    (PadicInt.Coe.ringHom (p := ℓ)).mapMatrix (integralModel (restrictScalarsRep b σ) hσ g).val =
      (integralModelConj b σ hσ)⁻¹.val * (restrictScalarsRep b σ g).val *
        (integralModelConj b σ hσ).val := by
  have h := congrArg Units.val (map_integralModel (restrictScalarsRep b σ) hσ g)
  simp only [Units.val_mul] at h
  exact h

/-- The restriction of scalars of the model of `σ` over `O_E`, read over `ℚ_ℓ`, is
`T Res_b σ T⁻¹`. -/
public theorem map_modelRestrictScalarsRep_val (g : G) :
    (PadicInt.Coe.ringHom (p := ℓ)).mapMatrix (modelRestrictScalarsRep b σ hσ g).val =
      modelConjMatrix b σ hσ * (restrictScalarsRep b σ g).val * modelConjMatrixInv b σ hσ := by
  change (modelRestrictScalarsRep b σ hσ g).val.map (algebraMap ℤ_[ℓ] ℚ_[ℓ]) = _
  rw [modelConjMatrix_mul_rep, Matrix.mul_assoc, modelConjMatrix_mul_inv, Matrix.mul_one]

/-- **`ℓᵏ T P` intertwines the integral model with the model over `O_E`.** -/
public theorem latticeChangeMatrix_mul (g : G) :
    latticeChangeMatrix b σ hσ * (integralModel (restrictScalarsRep b σ) hσ g).val =
      (modelRestrictScalarsRep b σ hσ g).val * latticeChangeMatrix b σ hσ := by
  apply mapMatrix_padicInt_injective
  rw [map_mul, map_mul, map_latticeChangeMatrix, map_integralModel_val,
    map_modelRestrictScalarsRep_val, Matrix.smul_mul, Matrix.mul_smul]
  congr 1
  calc modelConjMatrix b σ hσ * (integralModelConj b σ hσ).val *
        ((integralModelConj b σ hσ)⁻¹.val * (restrictScalarsRep b σ g).val *
          (integralModelConj b σ hσ).val)
      = modelConjMatrix b σ hσ * ((integralModelConj b σ hσ).val *
          (integralModelConj b σ hσ)⁻¹.val) * (restrictScalarsRep b σ g).val *
          (integralModelConj b σ hσ).val := by simp only [Matrix.mul_assoc]
    _ = modelConjMatrix b σ hσ * (restrictScalarsRep b σ g).val *
          (integralModelConj b σ hσ).val := by rw [Units.mul_inv, Matrix.mul_one]
    _ = _ := by
        rw [Matrix.mul_assoc (modelConjMatrix b σ hσ * _) (modelConjMatrixInv b σ hσ),
          ← Matrix.mul_assoc (modelConjMatrixInv b σ hσ), modelConjMatrixInv_mul,
          Matrix.one_mul, modelConjMatrix_mul_rep b σ hσ g]

/-- **`ℓᵏ' P⁻¹ T⁻¹` intertwines the model over `O_E` with the integral model.** -/
public theorem latticeChangeMatrixInv_mul (g : G) :
    latticeChangeMatrixInv b σ hσ * (modelRestrictScalarsRep b σ hσ g).val =
      (integralModel (restrictScalarsRep b σ) hσ g).val * latticeChangeMatrixInv b σ hσ := by
  apply mapMatrix_padicInt_injective
  rw [map_mul, map_mul, map_latticeChangeMatrixInv, map_integralModel_val,
    map_modelRestrictScalarsRep_val, Matrix.smul_mul, Matrix.mul_smul]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (modelConjMatrixInv b σ hσ) (modelConjMatrix b σ hσ),
    modelConjMatrixInv_mul, Matrix.one_mul, ← Matrix.mul_assoc (integralModelConj b σ hσ).val,
    Units.mul_inv, Matrix.one_mul]

/-- The total exponent `ℓ^K = ℓ^(k + k')`. -/
public abbrev latticeChangeDegree : ℕ := ℓ ^ (latticeChangeExpInv b σ hσ + latticeChangeExp b σ hσ)

/-- The total exponent `ℓ^K` is nonzero. -/
public theorem latticeChangeDegree_ne_zero : latticeChangeDegree b σ hσ ≠ 0 :=
  pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero

/-- The image over `ℚ_ℓ` of `N • 1` is `N • 1`. -/
theorem map_nsmul_one_padicInt (N : ℕ) :
    (PadicInt.Coe.ringHom (p := ℓ)).mapMatrix (N • (1 : Matrix (Fin (m * d)) (Fin (m * d)) ℤ_[ℓ])) =
      (N : ℚ_[ℓ]) • (1 : Matrix (Fin (m * d)) (Fin (m * d)) ℚ_[ℓ]) := by
  rw [map_nsmul, map_one, Nat.cast_smul_eq_nsmul]

/-- Integral matrices lifting `ℓ^a • M` and `ℓ^b • N` with `M * N = 1` multiply to `ℓ^(a + b)`. -/
private theorem mul_eq_pow_nsmul_one_of_mapMatrix {a b : ℕ}
    {M N : Matrix (Fin (m * d)) (Fin (m * d)) ℚ_[ℓ]}
    (A B : Matrix (Fin (m * d)) (Fin (m * d)) ℤ_[ℓ])
    (hA : (PadicInt.Coe.ringHom (p := ℓ)).mapMatrix A = ((ℓ : ℚ_[ℓ]) ^ a) • M)
    (hB : (PadicInt.Coe.ringHom (p := ℓ)).mapMatrix B = ((ℓ : ℚ_[ℓ]) ^ b) • N)
    (h : M * N = 1) : A * B = (ℓ ^ (a + b)) • (1 : Matrix (Fin (m * d)) (Fin (m * d)) ℤ_[ℓ]) := by
  apply mapMatrix_padicInt_injective
  rw [map_mul, hA, hB, map_nsmul_one_padicInt, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, h, Nat.cast_pow, pow_add]

/-- **The two intertwiners compose to `ℓ^K`**, one way. -/
public theorem latticeChangeMatrixInv_mul_latticeChangeMatrix :
    latticeChangeMatrixInv b σ hσ * latticeChangeMatrix b σ hσ =
      latticeChangeDegree b σ hσ • (1 : Matrix (Fin (m * d)) (Fin (m * d)) ℤ_[ℓ]) := by
  refine mul_eq_pow_nsmul_one_of_mapMatrix _ _ (map_latticeChangeMatrixInv b σ hσ)
    (map_latticeChangeMatrix b σ hσ) ?_
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (modelConjMatrixInv b σ hσ), modelConjMatrixInv_mul, Matrix.one_mul,
    Units.inv_mul]

/-- **The two intertwiners compose to `ℓ^K`**, the other way. -/
public theorem latticeChangeMatrix_mul_latticeChangeMatrixInv :
    latticeChangeMatrix b σ hσ * latticeChangeMatrixInv b σ hσ =
      latticeChangeDegree b σ hσ • (1 : Matrix (Fin (m * d)) (Fin (m * d)) ℤ_[ℓ]) := by
  rw [latticeChangeDegree, add_comm]
  refine mul_eq_pow_nsmul_one_of_mapMatrix _ _ (map_latticeChangeMatrix b σ hσ)
    (map_latticeChangeMatrixInv b σ hσ) ?_
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (integralModelConj b σ hσ).val, Units.mul_inv, Matrix.one_mul,
    modelConjMatrix_mul_inv]

/-- **`ℓᵏ T P` intertwines the actions of the elements of `O ∩ O_E`.** -/
public theorem latticeChangeMatrix_mul_conjIntegralLift
    (c : conjIntegralSubring (integralModelConj b σ hσ) (restrictScalarsScalarAlgHom b m)) (c' : 𝒪)
    (hc : (c : E) = (c' : E)) :
    latticeChangeMatrix b σ hσ *
        conjIntegralLift (integralModelConj b σ hσ) (restrictScalarsScalarAlgHom b m) c =
      coefficientScalarRingHom (padicIntegerRingBasisOf b) m c' * latticeChangeMatrix b σ hσ := by
  apply mapMatrix_padicInt_injective
  have hs : (PadicInt.Coe.ringHom (p := ℓ)).mapMatrix
      (coefficientScalarRingHom (padicIntegerRingBasisOf b) m c') =
      restrictScalarsMatrix (padicIntegerRingBasisRatOf b) (Matrix.scalar (Fin m) (c : E)) := by
    change (coefficientMatrixRingHom (padicIntegerRingBasisOf b) m (Matrix.scalar (Fin m) c')).map
      (algebraMap ℤ_[ℓ] ℚ_[ℓ]) = _
    rw [← restrictScalarsMatrix_map_padicIntegerRing, hc]
    congr 1
    ext i j
    by_cases h : i = j <;> simp [Matrix.scalar_apply, h]
  rw [map_mul, map_mul, map_latticeChangeMatrix, mapMatrix_conjIntegralLift, hs, Matrix.smul_mul,
    Matrix.mul_smul]
  congr 1
  have hα : restrictScalarsScalarAlgHom b m (c : E) =
      restrictScalarsMatrix b (Matrix.scalar (Fin m) (c : E)) := rfl
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (integralModelConj b σ hσ).val, Units.mul_inv, Matrix.one_mul, hα,
    ← Matrix.mul_assoc, modelConjMatrix_mul_scalar, Matrix.mul_assoc]

end Intertwiner

section Sheaf

variable {E : Type} [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]

attribute [local instance] padicIntAlgebraOfRat

local notation "𝒪" => integralClosure ℤ_[ℓ] E

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
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

local notation "e₀" => canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x

omit [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- Morphisms of the sheaves of representations along equal intertwiners agree. -/
theorem representationLAdicSheafMap_congr' {r r' : ℕ}
    {ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]} (hρ : Continuous ρ)
    {ρ' : EtaleFundamentalGroup X.1 x →* GL (Fin r') ℤ_[ℓ]} (hρ' : Continuous ρ')
    {A A' : Matrix (Fin r') (Fin r) ℤ_[ℓ]} (h : A = A')
    (hA : ∀ g, A * (ρ g).val = (ρ' g).val * A) (hA' : ∀ g, A' * (ρ g).val = (ρ' g).val * A') :
    representationLAdicSheafMap B X x e₀ hρ hρ' A hA =
      representationLAdicSheafMap B X x e₀ hρ hρ' A' hA' := by
  subst h
  rfl

variable {d : ℕ} (b : Basis (Fin d) ℚ_[ℓ] E) {m : ℕ}
  (σ : EtaleFundamentalGroup X.1 x →* GL (Fin m) E)
  (hσ : Continuous (restrictScalarsRep b σ))
  {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- **The twisted traces of Frobenius on `ℱ_{Res_b σ}` and on the sheaf of the model of `σ` over
`O_E` agree**, for the elements of `O ∩ O_E`. -/
public theorem trace_rationalIntegralRingHom_restrictScalarsRep_eq_model
    (c : conjIntegralSubring (representationSheafConj B X x (restrictScalarsRep b σ) hσ)
      (restrictScalarsScalarAlgHom b m)) (c' : 𝒪) (hc : (c : E) = (c' : E)) (i : ℤ) (N : ℕ) :
    haveI := compactSpace_etaleFundamentalGroup X.1 x
    LinearMap.trace ℚ_[ℓ] _
        ((restrictScalarsRepCoefficientSheaf B X x b σ hσ).rationalIntegralRingHom f j kbar i c ∘ₗ
          (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard
            (restrictScalarsRepCoefficientSheaf B X x b σ hσ).toLAdicSheaf i).hom ^ N) =
      LinearMap.trace ℚ_[ℓ] _
        (LAdicSheaf.rationalCohomologyMap f j kbar
            (representationLAdicSheafMap B X x e₀ (continuous_modelRestrictScalarsRep b σ hσ)
              (continuous_modelRestrictScalarsRep b σ hσ)
              (coefficientScalarRingHom (padicIntegerRingBasisOf b) m c')
              (fun g => coefficientScalarRingHom_commute (padicIntegerRingBasisOf b) m c'
                (modelRep b σ hσ g).val)) i ∘ₗ
          (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard
            (representationLAdicSheaf B X x e₀ (modelRestrictScalarsRep b σ hσ)
              (continuous_modelRestrictScalarsRep b σ hσ)) i).hom ^ N) := by
  have := compactSpace_etaleFundamentalGroup X.1 x
  have h1 := continuous_integralModel (restrictScalarsRep b σ) hσ
  have h2 := continuous_modelRestrictScalarsRep b σ hσ
  have hm1 := representationLAdicSheafMap_mul B X x e₀ h1 h2 h1 (latticeChangeMatrix b σ hσ)
    (latticeChangeMatrix_mul b σ hσ) (latticeChangeMatrixInv b σ hσ)
    (latticeChangeMatrixInv_mul b σ hσ)
  have hm2 := representationLAdicSheafMap_mul B X x e₀ h2 h1 h2 (latticeChangeMatrixInv b σ hσ)
    (latticeChangeMatrixInv_mul b σ hσ) (latticeChangeMatrix b σ hσ)
    (latticeChangeMatrix_mul b σ hσ)
  have hn1 := representationLAdicSheafMap_nsmul_one B X x e₀ h1 (latticeChangeDegree b σ hσ)
    (fun _ ↦ (Commute.one_left _).smul_left _)
  have hn2 := representationLAdicSheafMap_nsmul_one B X x e₀ h2 (latticeChangeDegree b σ hσ)
    (fun _ ↦ (Commute.one_left _).smul_left _)
  have hμ1 := representationLAdicSheafMap_mul B X x e₀ h1 h1 h2
    (conjIntegralLift (representationSheafConj B X x (restrictScalarsRep b σ) hσ)
      (restrictScalarsScalarAlgHom b m) c)
    (conjIntegralLift_mul_integralModel B X x (restrictScalarsRep b σ) hσ
      (restrictScalarsScalarAlgHom b m) (restrictScalarsScalarAlgHom_commute b σ) c)
    (latticeChangeMatrix b σ hσ) (latticeChangeMatrix_mul b σ hσ)
  have hμ2 := representationLAdicSheafMap_mul B X x e₀ h1 h2 h2 (latticeChangeMatrix b σ hσ)
    (latticeChangeMatrix_mul b σ hσ) (coefficientScalarRingHom (padicIntegerRingBasisOf b) m c')
    (fun g ↦ coefficientScalarRingHom_commute (padicIntegerRingBasisOf b) m c'
      (modelRep b σ hσ g).val)
  exact LAdicSheaf.trace_rationalMap_comp_rationalFrobenius_pow_of_isogeny f j kbar p q hcard _ _
    _ (latticeChangeDegree_ne_zero b σ hσ)
    (hm1.symm.trans ((representationLAdicSheafMap_congr' B X x h1 h1
      (latticeChangeMatrixInv_mul_latticeChangeMatrix b σ hσ) _ _).trans hn1))
    (hm2.symm.trans ((representationLAdicSheafMap_congr' B X x h2 h2
      (latticeChangeMatrix_mul_latticeChangeMatrixInv b σ hσ) _ _).trans hn2)) _ _
    (hμ2.symm.trans ((representationLAdicSheafMap_congr' B X x h1 h2
      (latticeChangeMatrix_mul_conjIntegralLift b σ hσ c c' hc) _ _).symm.trans hμ1)) i N

end Sheaf

end Stacks.EtaleCohomology

end
