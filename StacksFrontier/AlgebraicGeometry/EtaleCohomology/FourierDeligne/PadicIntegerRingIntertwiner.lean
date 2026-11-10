module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoefficientLatticeChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PadicIntegerRingValuation

/-!
# Integral intertwiners between `O_E`-models of a representation

Let `E` be a finite extension of `ℚ_ℓ` with ring of integers `O_E` and a `ℚ_ℓ`-basis `b`, and let
`σ : G → GL_m(E)` be a representation of a compact group with `Res_b σ` continuous. The sheaf
`ℱ_{Res_b σ}` of the integral part of `E`
(`Stacks.EtaleCohomology.restrictScalarsRepCoefficientSheaf`) is built from the integral model
`P⁻¹ Res_b σ P` of `Res_b σ`. For any other model `τ_O` of `σ` over
`O_E`, i.e. `τ_O ⊗ E = T⁻¹ σ T`, there are integral intertwiners `A`, `A'` between the restriction
of scalars `Res_β τ_O` along the basis `β` of `O_E` and the integral model, with
`A A' = A' A = ℓᵃ`, which intertwine the actions of the elements of `O ∩ O_E`
(`Stacks.EtaleCohomology.exists_integralModel_intertwiner_of_padicIntegerRing_model`): both are
`O_E`-lattices of the same representation, compared through the model of
`Stacks.EtaleCohomology.modelRep` and the lattice change of
`Stacks.EtaleCohomology.latticeChangeMatrix`.

Also: the values of an additive character of a finite group in `E` are roots of unity, hence
integral (`Stacks.EtaleCohomology.padicIntegerRingAddChar`). These are used to compare the
Fourier side of Laumon's argument with the Fourier family sheaf in piece L6 of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main definitions

* `Stacks.EtaleCohomology.padicIntegerRingAddChar`.

## Main results

* `Stacks.EtaleCohomology.exists_natCast_pow_mul_eq_padicIntegerRing`.
* `Stacks.EtaleCohomology.exists_map_eq_pow_smul_padicIntegerRing`.
* `Stacks.EtaleCohomology.exists_integralModel_intertwiner_of_padicIntegerRing_model`.
-/

@[expose] public noncomputable section

open Matrix Module

namespace Stacks.EtaleCohomology

variable {ℓ : ℕ} [Fact ℓ.Prime] {E : Type} [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]

attribute [local instance] padicIntAlgebraOfRat

local notation "𝒪" => integralClosure ℤ_[ℓ] E

section Lift

/-- **Every element of `E` has an `ℓ`-power multiple in `O_E`.** -/
theorem exists_natCast_pow_mul_eq_padicIntegerRing (e : E) :
    ∃ (k : ℕ) (o : 𝒪), algebraMap 𝒪 E o = (ℓ : E) ^ k * e := by
  obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := 𝒪) e
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  obtain ⟨c, t, ht⟩ := exists_dvd_natCast_pow_padicIntegerRing ℓ hs0
  have hs' : algebraMap 𝒪 E s ≠ 0 := fun h =>
    hs0 (IsFractionRing.injective 𝒪 E (h.trans (map_zero _).symm))
  refine ⟨c, a * t, ?_⟩
  have hℓ : (ℓ : E) ^ c = algebraMap 𝒪 E s * algebraMap 𝒪 E t := by
    rw [← map_mul, ← ht, map_pow, map_natCast]
  rw [hℓ, map_mul]
  field_simp

/-- **Every matrix over `E` has an `ℓ`-power multiple with entries in `O_E`.** -/
theorem exists_map_eq_pow_smul_padicIntegerRing {ι κ : Type*} [Finite ι] [Finite κ]
    (M : Matrix ι κ E) :
    ∃ (k : ℕ) (N : Matrix ι κ 𝒪), N.map (algebraMap 𝒪 E) = ((ℓ : E) ^ k) • M := by
  have := Fintype.ofFinite ι
  have := Fintype.ofFinite κ
  choose k o ho using fun i j => exists_natCast_pow_mul_eq_padicIntegerRing (ℓ := ℓ) (M i j)
  refine ⟨∑ i, ∑ j, k i j, Matrix.of fun i j => (ℓ : 𝒪) ^ (∑ i, ∑ j, k i j - k i j) * o i j, ?_⟩
  ext i j
  have hle : k i j ≤ ∑ i, ∑ j, k i j :=
    (Finset.single_le_sum (f := fun j => k i j) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j)).trans (Finset.single_le_sum (f := fun i => ∑ j, k i j)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  rw [Matrix.map_apply, Matrix.of_apply, map_mul, ho, map_pow, map_natCast, Matrix.smul_apply,
    smul_eq_mul, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]

omit [FiniteDimensional ℚ_[ℓ] E] in
/-- The values of an additive character of a finite group are integral over `ℤ_ℓ`: they are
roots of unity. -/
theorem isIntegral_addChar {k : Type*} [AddCommGroup k] [Finite k] (ψ : AddChar k E) (x : k) :
    IsIntegral ℤ_[ℓ] (ψ x) := by
  have := Fintype.ofFinite k
  have h : ψ x ^ Fintype.card k = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero, AddChar.map_zero_eq_one]
  refine IsIntegral.of_pow (Fintype.card_pos_iff.2 ⟨(0 : k)⟩) ?_
  rw [h]
  exact isIntegral_one

omit [FiniteDimensional ℚ_[ℓ] E] in
/-- **An additive character of a finite group with values in `E`, as a character with values in
`O_E`.** -/
def padicIntegerRingAddChar {k : Type*} [AddCommGroup k] [Fintype k] (ψ : AddChar k E) :
    AddChar k 𝒪 where
  toFun x := ⟨ψ x, isIntegral_addChar ψ x⟩
  map_zero_eq_one' := Subtype.ext (AddChar.map_zero_eq_one ψ)
  map_add_eq_mul' x y := Subtype.ext (AddChar.map_add_eq_mul ψ x y)

omit [FiniteDimensional ℚ_[ℓ] E] in
/-- The image in `E` of the value of `padicIntegerRingAddChar ψ` at `x` is `ψ x`. -/
@[simp]
theorem algebraMap_padicIntegerRingAddChar {k : Type*} [AddCommGroup k] [Fintype k]
    (ψ : AddChar k E) (x : k) : algebraMap 𝒪 E (padicIntegerRingAddChar ψ x) = ψ x :=
  rfl

end Lift

section Intertwiner

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {d m : ℕ} (b : Basis (Fin d) ℚ_[ℓ] E) (σ : G →* GL (Fin m) E)
  (hσ : Continuous (restrictScalarsRep b σ))

/-- **The model `σ'` of `σ` over `O_E` is conjugate to `σ` over `E`**, through the basis of the
model lattice: `σ'(g) = S⁻¹ σ(g) S`. -/
theorem map_modelRep_eq_conj (g : G) :
    (modelRep b σ hσ g).val.map (algebraMap 𝒪 E) =
      (modelBasisE b σ hσ).toMatrix (Pi.basisFun E (Fin m)) * (σ g).val *
        (Pi.basisFun E (Fin m)).toMatrix (modelBasisE b σ hσ) := by
  rw [map_modelRep, ← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
    (modelBasisE b σ hσ) (Pi.basisFun E (Fin m)) (modelBasisE b σ hσ) (Pi.basisFun E (Fin m)),
    LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']

/-- **An `O_E`-intertwiner from any `O_E`-model of `σ` to the model `σ'`**, and one back, composing
to a power of `ℓ` both ways. -/
theorem exists_intertwiner_modelRep (τO : G →* GL (Fin m) 𝒪) (T : GL (Fin m) E)
    (hT : ∀ g, (τO g).val.map (algebraMap 𝒪 E) = (T⁻¹ : GL (Fin m) E).val * (σ g).val * T.val) :
    ∃ (k : ℕ) (C C' : Matrix (Fin m) (Fin m) 𝒪),
      (∀ g, C * (τO g).val = (modelRep b σ hσ g).val * C) ∧
      (∀ g, C' * (modelRep b σ hσ g).val = (τO g).val * C') ∧
      C * C' = ((ℓ ^ k : ℕ) : Matrix (Fin m) (Fin m) 𝒪) ∧
      C' * C = ((ℓ ^ k : ℕ) : Matrix (Fin m) (Fin m) 𝒪) := by
  set Si := (modelBasisE b σ hσ).toMatrix (Pi.basisFun E (Fin m)) with hSi
  set S := (Pi.basisFun E (Fin m)).toMatrix (modelBasisE b σ hσ) with hS
  have hSSi : S * Si = 1 := Basis.toMatrix_mul_toMatrix_flip _ _
  have hSiS : Si * S = 1 := Basis.toMatrix_mul_toMatrix_flip _ _
  have hTT : T.val * (T⁻¹ : GL (Fin m) E).val = 1 := T.mul_inv
  have hTT' : (T⁻¹ : GL (Fin m) E).val * T.val = 1 := T.inv_mul
  obtain ⟨k, C, hC⟩ := exists_map_eq_pow_smul_padicIntegerRing (ℓ := ℓ) (Si * T.val)
  obtain ⟨k', C', hC'⟩ := exists_map_eq_pow_smul_padicIntegerRing (ℓ := ℓ)
    ((T⁻¹ : GL (Fin m) E).val * S)
  have hrep := map_modelRep_eq_conj b σ hσ
  have hnat : ∀ n : ℕ, ((n : Matrix (Fin m) (Fin m) 𝒪)).map (algebraMap 𝒪 E) =
      ((n : E)) • (1 : Matrix (Fin m) (Fin m) E) := by
    intro n
    have h := map_natCast ((algebraMap 𝒪 E).mapMatrix (m := Fin m)) n
    rw [RingHom.mapMatrix_apply] at h
    rw [h, Nat.cast_smul_eq_nsmul, nsmul_one]
  refine ⟨k + k', C, C', fun g => ?_, fun g => ?_, ?_, ?_⟩ <;>
    apply map_algebraMap_padicIntegerRing_injective <;> simp only
  · rw [Matrix.map_mul, Matrix.map_mul, hC, hT, hrep, Matrix.smul_mul, Matrix.mul_smul]
    congr 1
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc T.val, hTT, Matrix.one_mul, ← Matrix.mul_assoc S, hSSi,
      Matrix.one_mul]
  · rw [Matrix.map_mul, Matrix.map_mul, hC', hT, hrep, Matrix.smul_mul, Matrix.mul_smul]
    congr 1
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc S, hSSi, Matrix.one_mul, ← Matrix.mul_assoc T.val, hTT,
      Matrix.one_mul]
  · rw [Matrix.map_mul, hC, hC', hnat, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.mul_assoc, ← Matrix.mul_assoc T.val, hTT, Matrix.one_mul, hSiS, Nat.cast_pow,
      pow_add]
  · rw [Matrix.map_mul, hC, hC', hnat, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.mul_assoc, ← Matrix.mul_assoc S, hSSi, Matrix.one_mul, hTT', Nat.cast_pow, pow_add,
      mul_comm]

/-- `ℓ^{k'} P⁻¹ T⁻¹` intertwines the actions of the elements of `O ∩ O_E`, as `ℓᵏ T P` does. -/
theorem latticeChangeMatrixInv_mul_coefficientScalarRingHom
    (c : conjIntegralSubring (integralModelConj b σ hσ) (restrictScalarsScalarAlgHom b m)) (c' : 𝒪)
    (hc : (c : E) = (c' : E)) :
    latticeChangeMatrixInv b σ hσ * coefficientScalarRingHom (padicIntegerRingBasisOf b) m c' =
      conjIntegralLift (integralModelConj b σ hσ) (restrictScalarsScalarAlgHom b m) c *
        latticeChangeMatrixInv b σ hσ := by
  have h := latticeChangeMatrix_mul_conjIntegralLift b σ hσ c c' hc
  have hK : latticeChangeDegree b σ hσ •
      (latticeChangeMatrixInv b σ hσ * coefficientScalarRingHom (padicIntegerRingBasisOf b) m c') =
      latticeChangeDegree b σ hσ •
        (conjIntegralLift (integralModelConj b σ hσ) (restrictScalarsScalarAlgHom b m) c *
          latticeChangeMatrixInv b σ hσ) := by
    calc latticeChangeDegree b σ hσ •
          (latticeChangeMatrixInv b σ hσ *
            coefficientScalarRingHom (padicIntegerRingBasisOf b) m c')
        = latticeChangeMatrixInv b σ hσ *
            coefficientScalarRingHom (padicIntegerRingBasisOf b) m c' *
              (latticeChangeMatrix b σ hσ * latticeChangeMatrixInv b σ hσ) := by
          rw [latticeChangeMatrix_mul_latticeChangeMatrixInv, Matrix.mul_smul, Matrix.mul_one]
      _ = latticeChangeMatrixInv b σ hσ * latticeChangeMatrix b σ hσ *
            conjIntegralLift (integralModelConj b σ hσ) (restrictScalarsScalarAlgHom b m) c *
              latticeChangeMatrixInv b σ hσ := by
          rw [← Matrix.mul_assoc, Matrix.mul_assoc (latticeChangeMatrixInv b σ hσ), ← h,
            ← Matrix.mul_assoc]
      _ = _ := by
          rw [latticeChangeMatrixInv_mul_latticeChangeMatrix, Matrix.smul_mul, Matrix.one_mul,
            Matrix.smul_mul]
  refine Matrix.ext fun i j => ?_
  have hij := congrFun (congrFun hK i) j
  simp only [Matrix.smul_apply, nsmul_eq_mul] at hij
  refine mul_left_cancel₀ ?_ hij
  exact Nat.cast_ne_zero.2 (latticeChangeDegree_ne_zero b σ hσ)

/-- **Integral intertwiners between an `O_E`-model of `σ` and the integral model of `Res_b σ`**:
for `τ_O ⊗ E = T⁻¹ σ T`, matrices `A`, `A'` over `ℤ_ℓ` with
`A Res_β τ_O(g) = ρ₀(g) A`, `A' ρ₀(g) = Res_β τ_O(g) A'` (`ρ₀` the integral model of `Res_b σ`,
`β` the basis of `O_E` indexed like `b`), `A A' = A' A = ℓᵃ`, and intertwining the action of every
`c ∈ O ∩ O_E` on the integral model with its action on `O_E^m`. -/
theorem exists_integralModel_intertwiner_of_padicIntegerRing_model (τO : G →* GL (Fin m) 𝒪)
    (T : GL (Fin m) E)
    (hT : ∀ g, (τO g).val.map (algebraMap 𝒪 E) = (T⁻¹ : GL (Fin m) E).val * (σ g).val * T.val) :
    ∃ (a : ℕ) (A A' : Matrix (Fin (m * d)) (Fin (m * d)) ℤ_[ℓ]),
      (∀ g, A * coefficientMatrixRingHom (padicIntegerRingBasisOf b) m (τO g).val =
        (integralModel (restrictScalarsRep b σ) hσ g).val * A) ∧
      (∀ g, A' * (integralModel (restrictScalarsRep b σ) hσ g).val =
        coefficientMatrixRingHom (padicIntegerRingBasisOf b) m (τO g).val * A') ∧
      A * A' = ℓ ^ a • (1 : Matrix (Fin (m * d)) (Fin (m * d)) ℤ_[ℓ]) ∧
      A' * A = ℓ ^ a • (1 : Matrix (Fin (m * d)) (Fin (m * d)) ℤ_[ℓ]) ∧
      ∀ (c : conjIntegralSubring (integralModelConj b σ hσ) (restrictScalarsScalarAlgHom b m))
        (c' : 𝒪), (c : E) = (c' : E) →
        A * coefficientScalarRingHom (padicIntegerRingBasisOf b) m c' =
          conjIntegralLift (integralModelConj b σ hσ) (restrictScalarsScalarAlgHom b m) c * A ∧
        A' * conjIntegralLift (integralModelConj b σ hσ) (restrictScalarsScalarAlgHom b m) c =
          coefficientScalarRingHom (padicIntegerRingBasisOf b) m c' * A' := by
  obtain ⟨k, C, C', hC, hC', hCC', hC'C⟩ := exists_intertwiner_modelRep b σ hσ τO T hT
  set β := padicIntegerRingBasisOf b
  set R := coefficientMatrixRingHom β m
  set L := latticeChangeMatrix b σ hσ
  set L' := latticeChangeMatrixInv b σ hσ
  have hRn : R ((ℓ ^ k : ℕ) : Matrix (Fin m) (Fin m) 𝒪) =
      ℓ ^ k • (1 : Matrix (Fin (m * d)) (Fin (m * d)) ℤ_[ℓ]) := by
    rw [map_natCast, nsmul_one]
  have hMR : ∀ g, (modelRestrictScalarsRep b σ hσ g).val = R (modelRep b σ hσ g).val :=
    fun _ => rfl
  refine ⟨latticeChangeExpInv b σ hσ + latticeChangeExp b σ hσ + k, L' * R C, R C' * L,
    fun g => ?_, fun g => ?_, ?_, ?_, fun c c' hc => ⟨?_, ?_⟩⟩
  · rw [Matrix.mul_assoc, ← map_mul, hC, map_mul, ← hMR, ← Matrix.mul_assoc,
      latticeChangeMatrixInv_mul, Matrix.mul_assoc]
  · rw [Matrix.mul_assoc, latticeChangeMatrix_mul, hMR, ← Matrix.mul_assoc, ← map_mul, hC',
      map_mul, Matrix.mul_assoc]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (R C), ← map_mul, hCC', hRn, Matrix.smul_mul,
      Matrix.one_mul, Matrix.mul_smul, latticeChangeMatrixInv_mul_latticeChangeMatrix, smul_smul,
      ← pow_add, add_comm k]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc L, latticeChangeMatrix_mul_latticeChangeMatrixInv,
      Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, ← map_mul, hC'C, hRn, smul_smul,
      ← pow_add, add_comm (latticeChangeExpInv b σ hσ + latticeChangeExp b σ hσ) k]
  · rw [Matrix.mul_assoc, ← coefficientScalarRingHom_commute, ← Matrix.mul_assoc,
      latticeChangeMatrixInv_mul_coefficientScalarRingHom b σ hσ c c' hc, Matrix.mul_assoc]
  · rw [Matrix.mul_assoc, latticeChangeMatrix_mul_conjIntegralLift b σ hσ c c' hc,
      ← Matrix.mul_assoc, ← coefficientScalarRingHom_commute, Matrix.mul_assoc]

end Intertwiner

end Stacks.EtaleCohomology

end
