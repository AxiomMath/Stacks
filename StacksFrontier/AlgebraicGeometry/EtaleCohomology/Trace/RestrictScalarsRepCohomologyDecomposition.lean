module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafRationalIntertwiner
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RestrictScalarsBlockMatrices
public import StacksFrontier.LinearAlgebra.CharpolyDecomposition

/-!
# Frobenius characteristic polynomials of direct sums and of extensions of the coefficients

For `σ : π₁(X, x̄) → GL_m(E)` with `Res_b σ` continuous and finite-dimensional
`Hⁱ_c(X_k̄, ℱ_{Res_b σ} ⊗ ℚ_ℓ)`, let `restrictScalarsRepFrobeniusCharpoly b σ` be the
characteristic polynomial of the `E`-linear `π_X^*` on it.  Then:

* if `σ` is conjugate over `E` to a block sum of representations `σₜ`
  (`M (σ ⊗ eqv) M⁻¹ = ⨁ σₜ`), the `σₜ` have continuous restrictions of scalars, finite-dimensional
  cohomology, and `charpoly(σ) = ∏ charpoly(σₜ)`
  (`Stacks.EtaleCohomology.restrictScalarsRepFrobeniusCharpoly_eq_prod`);
* for a finite extension `E'` of `E` with a basis `b'` over `ℚ_ℓ`, `σ ⊗ E'` has continuous
  `Res_{b'}`, finite-dimensional cohomology, and its `E'`-linear Frobenius characteristic
  polynomial is the image of the `E`-linear one
  (`Stacks.EtaleCohomology.restrictScalarsRepFrobeniusCharpoly_map`):
  `Hⁱ_c(ℱ_{Res_{b'} (σ ⊗ E')}) = E' ⊗_E Hⁱ_c(ℱ_{Res_b σ})`.

These are read through the maps of the rational intertwiners
(`Stacks.EtaleCohomology.rationalIntertwinerCohomologyMap`) of the rows and columns of `M`, which
are `E`-linear and commute with `π_X^*`.  They give the purity of the fibres of a direct sum in
Laumon's proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main definitions

* `Stacks.EtaleCohomology.restrictScalarsRepFrobeniusCharpoly`.

## Main results

* `Stacks.EtaleCohomology.continuous_restrictScalarsRep_of_blockConj`,
  `Stacks.EtaleCohomology.finiteDimensional_of_blockConj`,
  `Stacks.EtaleCohomology.restrictScalarsRepFrobeniusCharpoly_eq_prod`.
* `Stacks.EtaleCohomology.continuous_restrictScalarsRep_map`,
  `Stacks.EtaleCohomology.finiteDimensional_map`,
  `Stacks.EtaleCohomology.restrictScalarsRepFrobeniusCharpoly_map`.

## Implementation notes

The statements consume objects defined in the standard model `HasDerivedCategory.standard` of the
derived category, which is therefore a local instance here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

variable {ℓ : ℕ} [Fact ℓ.Prime]

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
  {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar] (i : ℤ)
  (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-! ### Composites of rational intertwiners -/

section Composite

variable {r₁ r₂ r₃ : ℕ} {ρ₁ : EtaleFundamentalGroup X.1 x →* GL (Fin r₁) ℚ_[ℓ]}
  (hρ₁ : Continuous ρ₁) {ρ₂ : EtaleFundamentalGroup X.1 x →* GL (Fin r₂) ℚ_[ℓ]}
  (hρ₂ : Continuous ρ₂) {ρ₃ : EtaleFundamentalGroup X.1 x →* GL (Fin r₃) ℚ_[ℓ]}
  (hρ₃ : Continuous ρ₃)

/-- The maps of the rational intertwiners `A` and `A'` compose to that of `C` when `A' * A = C`. -/
theorem rationalIntertwinerCohomologyMap_apply_apply (A : Matrix (Fin r₂) (Fin r₁) ℚ_[ℓ])
    (hA : ∀ g, A * (ρ₁ g).val = (ρ₂ g).val * A) (A' : Matrix (Fin r₃) (Fin r₂) ℚ_[ℓ])
    (hA' : ∀ g, A' * (ρ₂ g).val = (ρ₃ g).val * A') (C : Matrix (Fin r₃) (Fin r₁) ℚ_[ℓ])
    (hC : ∀ g, C * (ρ₁ g).val = (ρ₃ g).val * C) (h : A' * A = C) (v) :
    rationalIntertwinerCohomologyMap B X x f j kbar i hρ₂ hρ₃ A' hA'
        (rationalIntertwinerCohomologyMap B X x f j kbar i hρ₁ hρ₂ A hA v) =
      rationalIntertwinerCohomologyMap B X x f j kbar i hρ₁ hρ₃ C hC v :=
  (LinearMap.congr_fun (rationalIntertwinerCohomologyMap_mul B X x f j kbar i hρ₁ hρ₂ hρ₃ A hA A'
    hA') v).symm.trans (LinearMap.congr_fun (rationalIntertwinerCohomologyMap_congr B X x f j kbar
      i hρ₁ hρ₃ _ hC h) v)

/-- The map of a rational intertwiner equal to `1` is the identity. -/
theorem rationalIntertwinerCohomologyMap_apply_of_eq_one (A : Matrix (Fin r₁) (Fin r₁) ℚ_[ℓ])
    (hA : ∀ g, A * (ρ₁ g).val = (ρ₁ g).val * A) (h : A = 1) (v) :
    rationalIntertwinerCohomologyMap B X x f j kbar i hρ₁ hρ₁ A hA v = v :=
  (LinearMap.congr_fun (rationalIntertwinerCohomologyMap_congr B X x f j kbar i hρ₁ hρ₁ hA
    (fun g => by rw [Matrix.one_mul, Matrix.mul_one]) h) v).trans
    (LinearMap.congr_fun (rationalIntertwinerCohomologyMap_one B X x f j kbar i hρ₁) v)

/-- The map of a rational intertwiner equal to `0` is zero. -/
theorem rationalIntertwinerCohomologyMap_apply_of_eq_zero (A : Matrix (Fin r₂) (Fin r₁) ℚ_[ℓ])
    (hA : ∀ g, A * (ρ₁ g).val = (ρ₂ g).val * A) (h : A = 0) (v) :
    rationalIntertwinerCohomologyMap B X x f j kbar i hρ₁ hρ₂ A hA v = 0 :=
  (LinearMap.congr_fun (rationalIntertwinerCohomologyMap_congr B X x f j kbar i hρ₁ hρ₂ hA
    (fun g => by rw [Matrix.zero_mul, Matrix.mul_zero]) h) v).trans
    (LinearMap.congr_fun (rationalIntertwinerCohomologyMap_zero B X x f j kbar i hρ₁ hρ₂) v)

/-- The maps of rational intertwiners `A` and `A'` compose to the identity when `A' * A = 1`. -/
private theorem rationalIntertwinerCohomologyMap_apply_apply_of_mul_eq_one
    (A : Matrix (Fin r₂) (Fin r₁) ℚ_[ℓ]) (hA : ∀ g, A * (ρ₁ g).val = (ρ₂ g).val * A)
    (A' : Matrix (Fin r₁) (Fin r₂) ℚ_[ℓ]) (hA' : ∀ g, A' * (ρ₂ g).val = (ρ₁ g).val * A')
    (h : A' * A = 1) (v) :
    rationalIntertwinerCohomologyMap B X x f j kbar i hρ₂ hρ₁ A' hA'
        (rationalIntertwinerCohomologyMap B X x f j kbar i hρ₁ hρ₂ A hA v) = v :=
  (rationalIntertwinerCohomologyMap_apply_apply B X x f j kbar i hρ₁ hρ₂ hρ₁ A hA A' hA' 1
    (fun g => by rw [Matrix.one_mul, Matrix.mul_one]) h v).trans
    (rationalIntertwinerCohomologyMap_apply_of_eq_one B X x f j kbar i hρ₁ 1 _ rfl v)

/-- The maps of rational intertwiners `A` and `A'` compose to zero when `A' * A = 0`. -/
private theorem rationalIntertwinerCohomologyMap_apply_apply_of_mul_eq_zero
    (A : Matrix (Fin r₂) (Fin r₁) ℚ_[ℓ]) (hA : ∀ g, A * (ρ₁ g).val = (ρ₂ g).val * A)
    (A' : Matrix (Fin r₃) (Fin r₂) ℚ_[ℓ]) (hA' : ∀ g, A' * (ρ₂ g).val = (ρ₃ g).val * A')
    (h : A' * A = 0) (v) :
    rationalIntertwinerCohomologyMap B X x f j kbar i hρ₂ hρ₃ A' hA'
        (rationalIntertwinerCohomologyMap B X x f j kbar i hρ₁ hρ₂ A hA v) = 0 :=
  (rationalIntertwinerCohomologyMap_apply_apply B X x f j kbar i hρ₁ hρ₂ hρ₃ A hA A' hA' 0
    (fun g => by rw [Matrix.zero_mul, Matrix.mul_zero]) h v).trans
    (rationalIntertwinerCohomologyMap_apply_of_eq_zero B X x f j kbar i hρ₁ hρ₃ 0 _ rfl v)

/-- The maps of a family of rational intertwiners summing to `1` sum to the identity. -/
private theorem sum_rationalIntertwinerCohomologyMap_apply {ι : Type*} [Fintype ι]
    (A : ι → Matrix (Fin r₁) (Fin r₁) ℚ_[ℓ])
    (hA : ∀ t g, A t * (ρ₁ g).val = (ρ₁ g).val * A t) (h : ∑ t, A t = 1) (w) :
    ∑ t, rationalIntertwinerCohomologyMap B X x f j kbar i hρ₁ hρ₁ (A t) (hA t) w = w :=
  (LinearMap.sum_apply Finset.univ
    (fun t => rationalIntertwinerCohomologyMap B X x f j kbar i hρ₁ hρ₁ (A t) (hA t)) w).symm.trans
    ((LinearMap.congr_fun (rationalIntertwinerCohomologyMap_sum B X x f j kbar i hρ₁ hρ₁
      Finset.univ _ hA) w).symm.trans
      (rationalIntertwinerCohomologyMap_apply_of_eq_one B X x f j kbar i hρ₁ _ _ h w))

end Composite

/-! ### The `E`-linear characteristic polynomial -/

section Charpoly

variable {E : Type} [Field E] [Algebra ℚ_[ℓ] E] {d : ℕ} (b : Module.Basis (Fin d) ℚ_[ℓ] E) {m : ℕ}
  (σ : EtaleFundamentalGroup X.1 x →* GL (Fin m) E) (hσ : Continuous (restrictScalarsRep b σ))

/-- **The characteristic polynomial of the `E`-linear `π_X^*` on
`Hⁱ_c(X_k̄, ℱ_{Res_b σ} ⊗ ℚ_ℓ)`**, for finite-dimensional cohomology. -/
def restrictScalarsRepFrobeniusCharpoly
    [FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j
      kbar (restrictScalarsRepCoefficientSheaf B X x b σ hσ).toLAdicSheaf i)] : Polynomial E :=
  letI := (restrictScalarsRepCoefficientSheaf B X x b σ hσ).rationalCohomologyModule f j kbar i E
  haveI := (restrictScalarsRepCoefficientSheaf B X x b σ hσ).rationalCohomologyModule_isScalarTower
    f j kbar i E (algebraMap_conjIntegralSubring_algebraMap _ _)
  haveI : FiniteDimensional E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j
      kbar (restrictScalarsRepCoefficientSheaf B X x b σ hσ).toLAdicSheaf i) :=
    Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E _
  LinearMap.charpoly ((restrictScalarsRepCoefficientSheaf B X x b σ
    hσ).rationalGeometricCompactlySupportedFrobenius f j kbar i E p q hcard)

end Charpoly

/-! ### Block decompositions -/

section Blocks

variable {E : Type} [Field E] [Algebra ℚ_[ℓ] E] {d : ℕ} (b : Module.Basis (Fin d) ℚ_[ℓ] E) {m : ℕ}
  {σ : EtaleFundamentalGroup X.1 x →* GL (Fin m) E} (hσ : Continuous (restrictScalarsRep b σ))
  {r : ℕ} {ms : Fin r → ℕ} {σs : ∀ t, EtaleFundamentalGroup X.1 x →* GL (Fin (ms t)) E}
  (eqv : Fin m ≃ Σ t, Fin (ms t)) (M : GL (Σ t, Fin (ms t)) E)
  (hM : ∀ g, (M : Matrix (Σ t, Fin (ms t)) (Σ t, Fin (ms t)) E) *
      Matrix.reindex eqv eqv (σ g).val *
      ((M⁻¹ : GL (Σ t, Fin (ms t)) E) : Matrix (Σ t, Fin (ms t)) (Σ t, Fin (ms t)) E) =
    Matrix.blockDiagonal' fun t => (σs t g).val)

omit [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [AlgebraicGeometry.IsNoetherian X.1] in
include hM in
/-- The restriction of scalars of the `t`-th block row of `M` intertwines `Res_b σ` with
`Res_b σₜ`. -/
theorem restrictScalarsRep_row_mul (t : Fin r) (g : EtaleFundamentalGroup X.1 x) :
    restrictScalarsMatrix b (blockConjRow eqv M t) * (restrictScalarsRep b σ g).val =
      (restrictScalarsRep b (σs t) g).val * restrictScalarsMatrix b (blockConjRow eqv M t) := by
  rw [restrictScalarsRep_val, restrictScalarsRep_val, ← restrictScalarsMatrix_mul,
    ← restrictScalarsMatrix_mul, blockConjRow_mul eqv M (hM g) t]

omit [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [AlgebraicGeometry.IsNoetherian X.1] in
include hM in
/-- The restriction of scalars of the `t`-th block column of `M` intertwines `Res_b σₜ` with
`Res_b σ`. -/
theorem restrictScalarsRep_col_mul (t : Fin r) (g : EtaleFundamentalGroup X.1 x) :
    restrictScalarsMatrix b (blockConjCol eqv M t) * (restrictScalarsRep b (σs t) g).val =
      (restrictScalarsRep b σ g).val * restrictScalarsMatrix b (blockConjCol eqv M t) := by
  rw [restrictScalarsRep_val, restrictScalarsRep_val, ← restrictScalarsMatrix_mul,
    ← restrictScalarsMatrix_mul, mul_blockConjCol eqv M (hM g) t]

omit [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [AlgebraicGeometry.IsNoetherian X.1] in
include hσ hM in
/-- **The blocks of a continuous representation have continuous restrictions of scalars.** -/
theorem continuous_restrictScalarsRep_of_blockConj (t : Fin r) :
    Continuous (restrictScalarsRep b (σs t)) := by
  refine continuous_restrictScalarsRep b (σs t) ?_
  have h : (fun g => restrictScalarsMatrix b (σs t g).val) = fun g =>
      restrictScalarsMatrix b (blockConjRow eqv M t) * (restrictScalarsRep b σ g).val *
        restrictScalarsMatrix b (blockConjCol eqv M t) := funext fun g => by
    rw [restrictScalarsRep_row_mul B X x b eqv M hM t g, Matrix.mul_assoc,
      ← restrictScalarsMatrix_mul, blockConjRow_mul_blockConjCol_self, restrictScalarsMatrix_one,
      Matrix.mul_one, restrictScalarsRep_val]
  rw [h]
  exact (continuous_const.matrix_mul (Units.continuous_val.comp hσ)).matrix_mul continuous_const

variable (hσs : ∀ t, Continuous (restrictScalarsRep b (σs t)))

include hM in
/-- **The blocks of a representation with finite-dimensional cohomology have finite-dimensional
cohomology.** -/
theorem finiteDimensional_of_blockConj
    [hV : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ
      f j kbar (restrictScalarsRepCoefficientSheaf B X x b σ hσ).toLAdicSheaf i)] (t : Fin r) :
    FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j
      kbar (restrictScalarsRepCoefficientSheaf B X x b (σs t) (hσs t)).toLAdicSheaf i) := by
  have := compactSpace_etaleFundamentalGroup X.1 x
  have : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ
      f j kbar (representationLAdicSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
        (integralModel (restrictScalarsRep b σ) hσ) (continuous_integralModel _ hσ)) i) := hV
  exact Module.Finite.of_surjective (rationalIntertwinerCohomologyMap B X x f j kbar i hσ (hσs t) _
    (restrictScalarsRep_row_mul B X x b eqv M hM t)) fun w =>
    ⟨rationalIntertwinerCohomologyMap B X x f j kbar i (hσs t) hσ _
      (restrictScalarsRep_col_mul B X x b eqv M hM t) w,
      rationalIntertwinerCohomologyMap_apply_apply_of_mul_eq_one B X x f j kbar i (hσs t) hσ _ _ _
        _ (by
          rw [← restrictScalarsMatrix_mul, blockConjRow_mul_blockConjCol_self,
            restrictScalarsMatrix_one]) w⟩

include hM in
/-- **The Frobenius characteristic polynomial of a block sum is the product of those of the
blocks.** -/
theorem restrictScalarsRepFrobeniusCharpoly_eq_prod
    [FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j
      kbar (restrictScalarsRepCoefficientSheaf B X x b σ hσ).toLAdicSheaf i)]
    [∀ t, FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
      j kbar (restrictScalarsRepCoefficientSheaf B X x b (σs t) (hσs t)).toLAdicSheaf i)] :
    restrictScalarsRepFrobeniusCharpoly B X x f j kbar i p q hcard b σ hσ =
      ∏ t, restrictScalarsRepFrobeniusCharpoly B X x f j kbar i p q hcard b (σs t) (hσs t) := by
  let := (restrictScalarsRepCoefficientSheaf B X x b σ hσ).rationalCohomologyModule f j kbar i E
  have := (restrictScalarsRepCoefficientSheaf B X x b σ hσ).rationalCohomologyModule_isScalarTower
    f j kbar i E (algebraMap_conjIntegralSubring_algebraMap _ _)
  have : FiniteDimensional E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j
      kbar (restrictScalarsRepCoefficientSheaf B X x b σ hσ).toLAdicSheaf i) :=
    Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E _
  let : ∀ t, Module E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar
      (restrictScalarsRepCoefficientSheaf B X x b (σs t) (hσs t)).toLAdicSheaf i) := fun t =>
    (restrictScalarsRepCoefficientSheaf B X x b (σs t) (hσs t)).rationalCohomologyModule f j kbar
      i E
  have : ∀ t, IsScalarTower ℚ_[ℓ] E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ
      f j kbar (restrictScalarsRepCoefficientSheaf B X x b (σs t) (hσs t)).toLAdicSheaf i) :=
    fun t => (restrictScalarsRepCoefficientSheaf B X x b (σs t)
      (hσs t)).rationalCohomologyModule_isScalarTower f j kbar i E
        (algebraMap_conjIntegralSubring_algebraMap _ _)
  have : ∀ t, FiniteDimensional E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ
      f j kbar (restrictScalarsRepCoefficientSheaf B X x b (σs t) (hσs t)).toLAdicSheaf i) :=
    fun t => Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E _
  let ι : ∀ t, LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar
      (restrictScalarsRepCoefficientSheaf B X x b (σs t) (hσs t)).toLAdicSheaf i →ₗ[E]
      LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar
        (restrictScalarsRepCoefficientSheaf B X x b σ hσ).toLAdicSheaf i := fun t =>
    { toFun := fun w => rationalIntertwinerCohomologyMap B X x f j kbar i (hσs t) hσ _
        (restrictScalarsRep_col_mul B X x b eqv M hM t) w
      map_add' := fun v w => map_add _ v w
      map_smul' := fun e w => rationalIntertwinerCohomologyMap_rationalRingHom B X x f j kbar i
        (hσs t) hσ _ (restrictScalarsScalarAlgHom_commute b (σs t)) _
        (restrictScalarsScalarAlgHom_commute b σ) _ (restrictScalarsRep_col_mul B X x b eqv M hM t)
        e e (restrictScalarsMatrix_mul_restrictScalarsScalarAlgHom b _ e) w }
  let π : ∀ t, LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar
      (restrictScalarsRepCoefficientSheaf B X x b σ hσ).toLAdicSheaf i →ₗ[E]
      LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar
        (restrictScalarsRepCoefficientSheaf B X x b (σs t) (hσs t)).toLAdicSheaf i := fun t =>
    { toFun := fun w => rationalIntertwinerCohomologyMap B X x f j kbar i hσ (hσs t) _
        (restrictScalarsRep_row_mul B X x b eqv M hM t) w
      map_add' := fun v w => map_add _ v w
      map_smul' := fun e w => rationalIntertwinerCohomologyMap_rationalRingHom B X x f j kbar i
        hσ (hσs t) _ (restrictScalarsScalarAlgHom_commute b σ) _
        (restrictScalarsScalarAlgHom_commute b (σs t)) _
        (restrictScalarsRep_row_mul B X x b eqv M hM t)
        e e (restrictScalarsMatrix_mul_restrictScalarsScalarAlgHom b _ e) w }
  refine LinearMap.charpoly_eq_prod_of_retractions ι π (fun t w => ?_) (fun t t' htt' w => ?_)
    (fun w => ?_) _ _ (fun t w => ?_)
  · exact rationalIntertwinerCohomologyMap_apply_apply_of_mul_eq_one B X x f j kbar i (hσs t) hσ
      _ (restrictScalarsRep_col_mul B X x b eqv M hM t) _
      (restrictScalarsRep_row_mul B X x b eqv M hM t) (by
        rw [← restrictScalarsMatrix_mul, blockConjRow_mul_blockConjCol_self,
          restrictScalarsMatrix_one]) w
  · exact rationalIntertwinerCohomologyMap_apply_apply_of_mul_eq_zero B X x f j kbar i (hσs t') hσ
      (hσs t) _ (restrictScalarsRep_col_mul B X x b eqv M hM t') _
      (restrictScalarsRep_row_mul B X x b eqv M hM t) (by
        rw [← restrictScalarsMatrix_mul, blockConjRow_mul_blockConjCol_of_ne eqv M htt',
          restrictScalarsMatrix_zero]) w
  · have h : ∀ t, ι t (π t w) = rationalIntertwinerCohomologyMap B X x f j kbar i hσ hσ
        (restrictScalarsMatrix b (blockConjCol eqv M t) *
          restrictScalarsMatrix b (blockConjRow eqv M t)) (fun g => by
            rw [Matrix.mul_assoc, restrictScalarsRep_row_mul B X x b eqv M hM t g,
              ← Matrix.mul_assoc, restrictScalarsRep_col_mul B X x b eqv M hM t g,
              Matrix.mul_assoc]) w := fun t =>
      rationalIntertwinerCohomologyMap_apply_apply B X x f j kbar i hσ (hσs t) hσ _
        (restrictScalarsRep_row_mul B X x b eqv M hM t) _
        (restrictScalarsRep_col_mul B X x b eqv M hM t)
        _ _ rfl w
    have hA : ∀ t g, (restrictScalarsMatrix b (blockConjCol eqv M t) *
        restrictScalarsMatrix b (blockConjRow eqv M t)) * (restrictScalarsRep b σ g).val =
        (restrictScalarsRep b σ g).val * (restrictScalarsMatrix b (blockConjCol eqv M t) *
          restrictScalarsMatrix b (blockConjRow eqv M t)) := fun t g => by
      rw [Matrix.mul_assoc, restrictScalarsRep_row_mul B X x b eqv M hM t g, ← Matrix.mul_assoc,
        restrictScalarsRep_col_mul B X x b eqv M hM t g, Matrix.mul_assoc]
    refine (Finset.sum_congr rfl fun t _ => h t).trans ?_
    refine sum_rationalIntertwinerCohomologyMap_apply B X x f j kbar i hσ _ hA ?_ w
    simp only [← restrictScalarsMatrix_mul]
    rw [← restrictScalarsMatrix_sum, sum_blockConjCol_mul_blockConjRow, restrictScalarsMatrix_one]
  · exact (rationalIntertwinerCohomologyMap_frobenius B X x f j kbar i (hσs t) hσ p q hcard _
      (restrictScalarsRep_col_mul B X x b eqv M hM t) w).symm

end Blocks

/-! ### Extension of the coefficient field -/

section Extension

variable {E E' : Type} [Field E] [Field E'] [Algebra ℚ_[ℓ] E] [Algebra ℚ_[ℓ] E'] [Algebra E E']
  [IsScalarTower ℚ_[ℓ] E E'] {d d' : ℕ} (b : Module.Basis (Fin d) ℚ_[ℓ] E)
  (b' : Module.Basis (Fin d') ℚ_[ℓ] E') {m : ℕ} (σ : EtaleFundamentalGroup X.1 x →* GL (Fin m) E)

omit [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [AlgebraicGeometry.IsNoetherian X.1] in
/-- `Res_{b'} (σ ⊗ E')` through `Res_b σ`: `∑ₜ cₜ J Res_b(σ) Πₜ`. -/
theorem restrictScalarsRep_map_eq_sum (g : EtaleFundamentalGroup X.1 x) :
    haveI := Module.Finite.of_basis b'
    haveI : FiniteDimensional E E' := Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E E'
    (restrictScalarsRep b' ((Matrix.GeneralLinearGroup.map (algebraMap E E')).comp σ) g).val =
      ∑ t, restrictScalarsScalarAlgHom b' m (Module.finBasis E E' t) *
        restrictScalarsInclusionMatrix b b' m * (restrictScalarsRep b σ g).val *
          restrictScalarsCoordMatrix b b' (Module.finBasis E E') m t := by
  have := Module.Finite.of_basis b'
  have : FiniteDimensional E E' := Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E E'
  conv_lhs => rw [← Matrix.mul_one (restrictScalarsRep b' _ g).val,
    ← sum_scalar_mul_inclusionMatrix_mul_coordMatrix b b' (Module.finBasis E E') m, Matrix.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← restrictScalarsScalarAlgHom_commute,
    Matrix.mul_assoc (restrictScalarsScalarAlgHom b' m _), restrictScalarsRep_val,
    restrictScalarsRep_val,
    show ((((Matrix.GeneralLinearGroup.map (algebraMap E E')).comp σ) g : GL (Fin m) E') :
      Matrix (Fin m) (Fin m) E') = (σ g).val.map (algebraMap E E') from rfl,
    ← restrictScalarsInclusionMatrix_mul b b' m (σ g).val]
  simp only [Matrix.mul_assoc]

variable {σ} (hσ : Continuous (restrictScalarsRep b σ))

omit [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [AlgebraicGeometry.IsNoetherian X.1] in
include hσ in
/-- **`Res_{b'} (σ ⊗ E')` is continuous when `Res_b σ` is.** -/
theorem continuous_restrictScalarsRep_map :
    Continuous
      (restrictScalarsRep b' ((Matrix.GeneralLinearGroup.map (algebraMap E E')).comp σ)) := by
  refine continuous_restrictScalarsRep b' _ ?_
  have h := funext (restrictScalarsRep_map_eq_sum B X x b b' σ)
  simp only [restrictScalarsRep_val] at h
  rw [h]
  exact continuous_finsetSum _ fun t _ =>
    (continuous_const.matrix_mul (Units.continuous_val.comp hσ)).matrix_mul continuous_const

variable (hσ' : Continuous
  (restrictScalarsRep b' ((Matrix.GeneralLinearGroup.map (algebraMap E E')).comp σ)))

omit [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [AlgebraicGeometry.IsNoetherian X.1] in
/-- The inclusion matrix of `E` in `E'` intertwines `Res_b σ` with `Res_{b'} (σ ⊗ E')`. -/
theorem restrictScalarsInclusionMatrix_mul_rep (g : EtaleFundamentalGroup X.1 x) :
    restrictScalarsInclusionMatrix b b' m * (restrictScalarsRep b σ g).val =
      (restrictScalarsRep b' ((Matrix.GeneralLinearGroup.map (algebraMap E E')).comp σ) g).val *
        restrictScalarsInclusionMatrix b b' m :=
  restrictScalarsInclusionMatrix_mul b b' m (σ g).val

omit [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [AlgebraicGeometry.IsNoetherian X.1] in
/-- The `t`-th coordinate matrix of `E'` over `E` intertwines `Res_{b'} (σ ⊗ E')` with
`Res_b σ`. -/
theorem restrictScalarsCoordMatrix_mul_rep {s : Type*} [Fintype s] (c : Module.Basis s E E') (t : s)
    (g : EtaleFundamentalGroup X.1 x) :
    restrictScalarsCoordMatrix b b' c m t *
        (restrictScalarsRep b' ((Matrix.GeneralLinearGroup.map (algebraMap E E')).comp σ) g).val =
      (restrictScalarsRep b σ g).val * restrictScalarsCoordMatrix b b' c m t :=
  restrictScalarsCoordMatrix_mul b b' c m t (σ g).val

omit [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [AlgebraicGeometry.IsNoetherian X.1] in
/-- Multiplication by `e ∈ E'` after the inclusion matrix of `E` in `E'` intertwines `Res_b σ`
with `Res_{b'} (σ ⊗ E')`. -/
theorem scalar_mul_inclusionMatrix_mul_rep (e : E') (g : EtaleFundamentalGroup X.1 x) :
    (restrictScalarsScalarAlgHom b' m e * restrictScalarsInclusionMatrix b b' m) *
        (restrictScalarsRep b σ g).val =
      (restrictScalarsRep b' ((Matrix.GeneralLinearGroup.map (algebraMap E E')).comp σ) g).val *
        (restrictScalarsScalarAlgHom b' m e * restrictScalarsInclusionMatrix b b' m) := by
  rw [Matrix.mul_assoc, restrictScalarsInclusionMatrix_mul_rep B X x, ← Matrix.mul_assoc,
    restrictScalarsScalarAlgHom_commute, Matrix.mul_assoc]

include hσ' in
/-- **`Hⁱ_c` of `ℱ_{Res_{b'} (σ ⊗ E')}` is finite-dimensional when that of `ℱ_{Res_b σ}` is.** -/
theorem finiteDimensional_map
    [hV : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ
      f j kbar (restrictScalarsRepCoefficientSheaf B X x b σ hσ).toLAdicSheaf i)] :
    FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar
      (restrictScalarsRepCoefficientSheaf B X x b'
        ((Matrix.GeneralLinearGroup.map (algebraMap E E')).comp σ) hσ').toLAdicSheaf i) := by
  have := compactSpace_etaleFundamentalGroup X.1 x
  have := Module.Finite.of_basis b'
  have : FiniteDimensional E E' := Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E E'
  have : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ
      f j kbar (representationLAdicSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
        (integralModel (restrictScalarsRep b σ) hσ) (continuous_integralModel _ hσ)) i) := hV
  set c := Module.finBasis E E'
  let Φ : (Fin (Module.finrank E E') → LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X
      ℓ f j kbar (representationLAdicSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
        (integralModel (restrictScalarsRep b σ) hσ) (continuous_integralModel _ hσ)) i) →ₗ[ℚ_[ℓ]]
      LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar
        (representationLAdicSheaf B X x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
          (integralModel _ hσ') (continuous_integralModel _ hσ')) i :=
    { toFun := fun v => ∑ t, rationalIntertwinerCohomologyMap B X x f j kbar i hσ hσ' _
        (scalar_mul_inclusionMatrix_mul_rep B X x b b' (c t)) (v t)
      map_add' := fun v w => by simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
      map_smul' := fun a v => by simp only [Pi.smul_apply, map_smul, Finset.smul_sum,
        RingHom.id_apply] }
  refine Module.Finite.of_surjective Φ fun w => ⟨fun t => rationalIntertwinerCohomologyMap B X x f
    j kbar i hσ' hσ _ (restrictScalarsCoordMatrix_mul_rep B X x b b' c t) w, ?_⟩
  have hA : ∀ t g, (restrictScalarsScalarAlgHom b' m (c t) * restrictScalarsInclusionMatrix b b' m *
      restrictScalarsCoordMatrix b b' c m t) *
        (restrictScalarsRep b' ((Matrix.GeneralLinearGroup.map (algebraMap E E')).comp σ) g).val =
      (restrictScalarsRep b' ((Matrix.GeneralLinearGroup.map (algebraMap E E')).comp σ) g).val *
        (restrictScalarsScalarAlgHom b' m (c t) * restrictScalarsInclusionMatrix b b' m *
          restrictScalarsCoordMatrix b b' c m t) := fun t g => by
    rw [Matrix.mul_assoc, restrictScalarsCoordMatrix_mul_rep B X x, ← Matrix.mul_assoc,
      scalar_mul_inclusionMatrix_mul_rep B X x, Matrix.mul_assoc]
  show ∑ t, rationalIntertwinerCohomologyMap B X x f j kbar i hσ hσ' _
    (scalar_mul_inclusionMatrix_mul_rep B X x b b' (c t)) (rationalIntertwinerCohomologyMap B X x f
      j kbar i hσ' hσ _ (restrictScalarsCoordMatrix_mul_rep B X x b b' c t) w) = w
  refine (Finset.sum_congr rfl fun t _ => rationalIntertwinerCohomologyMap_apply_apply B X x f j
    kbar i hσ' hσ hσ' _ (restrictScalarsCoordMatrix_mul_rep B X x b b' c t) _
    (scalar_mul_inclusionMatrix_mul_rep B X x b b' (c t)) _ (hA t) rfl w).trans ?_
  exact sum_rationalIntertwinerCohomologyMap_apply B X x f j kbar i hσ' _ hA
    (sum_scalar_mul_inclusionMatrix_mul_coordMatrix b b' c m) w

/-- **The Frobenius characteristic polynomial after extending the coefficients from `E` to `E'`
is the image of that over `E`.** -/
theorem restrictScalarsRepFrobeniusCharpoly_map
    [FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j
      kbar (restrictScalarsRepCoefficientSheaf B X x b σ hσ).toLAdicSheaf i)]
    [FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j
      kbar (restrictScalarsRepCoefficientSheaf B X x b'
        ((Matrix.GeneralLinearGroup.map (algebraMap E E')).comp σ) hσ').toLAdicSheaf i)] :
    restrictScalarsRepFrobeniusCharpoly B X x f j kbar i p q hcard b'
        ((Matrix.GeneralLinearGroup.map (algebraMap E E')).comp σ) hσ' =
      (restrictScalarsRepFrobeniusCharpoly B X x f j kbar i p q hcard b σ hσ).map
        (algebraMap E E') := by
  have := Module.Finite.of_basis b'
  have : FiniteDimensional E E' := Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E E'
  set c := Module.finBasis E E'
  set σ' := (Matrix.GeneralLinearGroup.map (algebraMap E E')).comp σ
  let := (restrictScalarsRepCoefficientSheaf B X x b σ hσ).rationalCohomologyModule f j kbar i E
  have := (restrictScalarsRepCoefficientSheaf B X x b σ hσ).rationalCohomologyModule_isScalarTower
    f j kbar i E (algebraMap_conjIntegralSubring_algebraMap _ _)
  have : FiniteDimensional E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j
      kbar (restrictScalarsRepCoefficientSheaf B X x b σ hσ).toLAdicSheaf i) :=
    Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E _
  let := (restrictScalarsRepCoefficientSheaf B X x b' σ' hσ').rationalCohomologyModule f j kbar i E'
  have := (restrictScalarsRepCoefficientSheaf B X x b' σ'
    hσ').rationalCohomologyModule_isScalarTower f j kbar i E'
    (algebraMap_conjIntegralSubring_algebraMap _ _)
  have : FiniteDimensional E' (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j
      kbar (restrictScalarsRepCoefficientSheaf B X x b' σ' hσ').toLAdicSheaf i) :=
    Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E' _
  let Ψ : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar
      (restrictScalarsRepCoefficientSheaf B X x b σ hσ).toLAdicSheaf i →+
      LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar
        (restrictScalarsRepCoefficientSheaf B X x b' σ' hσ').toLAdicSheaf i :=
    (rationalIntertwinerCohomologyMap B X x f j kbar i hσ hσ' _
      (restrictScalarsInclusionMatrix_mul_rep B X x b b')).toAddMonoidHom
  let pr : Fin (Module.finrank E E') → (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X
      ℓ f j kbar (restrictScalarsRepCoefficientSheaf B X x b' σ' hσ').toLAdicSheaf i →+
      LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar
        (restrictScalarsRepCoefficientSheaf B X x b σ hσ).toLAdicSheaf i) := fun t =>
    (rationalIntertwinerCohomologyMap B X x f j kbar i hσ' hσ _
      (restrictScalarsCoordMatrix_mul_rep B X x b b' c t)).toAddMonoidHom
  have hsmul : ∀ (e : E') (w : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j
      kbar (restrictScalarsRepCoefficientSheaf B X x b' σ' hσ').toLAdicSheaf i),
      e • w = rationalIntertwinerCohomologyMap B X x f j kbar i hσ' hσ' _
        (restrictScalarsScalarAlgHom_commute b' σ' e) w := fun e w =>
    rationalRingHom_representationSheafCommutantCoefficientSheaf B X x f j kbar i hσ' _ _ e w
  refine LinearMap.charpoly_eq_map_of_scalarExtension c Ψ (fun e v => ?_) pr (fun t u v => ?_)
    (fun w => ?_) _ _ (fun v => ?_)
  · exact rationalIntertwinerCohomologyMap_rationalRingHom B X x f j kbar i hσ hσ' _
      (restrictScalarsScalarAlgHom_commute b σ) _ (restrictScalarsScalarAlgHom_commute b' σ') _
      (restrictScalarsInclusionMatrix_mul_rep B X x b b') e (algebraMap E E' e)
      (restrictScalarsInclusionMatrix_mul_scalar b b' m e) v
  · have h1 := rationalIntertwinerCohomologyMap_apply_apply B X x f j kbar i hσ hσ' hσ' _
      (restrictScalarsInclusionMatrix_mul_rep B X x b b') _
      (restrictScalarsScalarAlgHom_commute b' σ' (c u)) _
      (scalar_mul_inclusionMatrix_mul_rep B X x b b' (c u)) rfl v
    have hm := restrictScalarsCoordMatrix_mul_scalar_mul_inclusionMatrix b b' c m t u
    rw [Matrix.mul_assoc] at hm
    refine (congrArg (pr t) (hsmul (c u) (Ψ v))).trans ((congrArg _ h1).trans ?_)
    split_ifs with htu
    · exact rationalIntertwinerCohomologyMap_apply_apply_of_mul_eq_one B X x f j kbar i hσ hσ' _
        (scalar_mul_inclusionMatrix_mul_rep B X x b b' (c u)) _
        (restrictScalarsCoordMatrix_mul_rep B X x b b' c t) (hm.trans (ite_eq_left htu)) v
    · exact rationalIntertwinerCohomologyMap_apply_apply_of_mul_eq_zero B X x f j kbar i hσ hσ'
        hσ _ (scalar_mul_inclusionMatrix_mul_rep B X x b b' (c u)) _
        (restrictScalarsCoordMatrix_mul_rep B X x b b' c t) (hm.trans (ite_eq_right htu)) v
  · have hA : ∀ t g, (restrictScalarsScalarAlgHom b' m (c t) *
        restrictScalarsInclusionMatrix b b' m * restrictScalarsCoordMatrix b b' c m t) *
          (restrictScalarsRep b' σ' g).val =
        (restrictScalarsRep b' σ' g).val * (restrictScalarsScalarAlgHom b' m (c t) *
          restrictScalarsInclusionMatrix b b' m * restrictScalarsCoordMatrix b b' c m t) :=
      fun t g => by
        rw [Matrix.mul_assoc, restrictScalarsCoordMatrix_mul_rep B X x, ← Matrix.mul_assoc,
          scalar_mul_inclusionMatrix_mul_rep B X x, Matrix.mul_assoc]
    have h : ∀ t, c t • Ψ (pr t w) = rationalIntertwinerCohomologyMap B X x f j kbar i hσ' hσ' _
        (hA t) w := fun t => by
      refine (hsmul (c t) _).trans ?_
      refine ((congrArg _ (rationalIntertwinerCohomologyMap_apply_apply B X x f j kbar i hσ' hσ
        hσ' _ (restrictScalarsCoordMatrix_mul_rep B X x b b' c t) _
        (restrictScalarsInclusionMatrix_mul_rep B X x b b') _ (fun g => by
          rw [Matrix.mul_assoc, restrictScalarsCoordMatrix_mul_rep B X x, ← Matrix.mul_assoc,
            restrictScalarsInclusionMatrix_mul_rep B X x, Matrix.mul_assoc]) rfl w)).trans ?_)
      refine (rationalIntertwinerCohomologyMap_apply_apply B X x f j kbar i hσ' hσ' hσ' _ _ _
        (restrictScalarsScalarAlgHom_commute b' σ' (c t)) _ (hA t) ?_ w)
      rw [Matrix.mul_assoc]
    refine (Finset.sum_congr rfl fun t _ => h t).trans ?_
    exact sum_rationalIntertwinerCohomologyMap_apply B X x f j kbar i hσ' _ hA
      (sum_scalar_mul_inclusionMatrix_mul_coordMatrix b b' c m) w
  · exact (rationalIntertwinerCohomologyMap_frobenius B X x f j kbar i hσ hσ' p q hcard _
      (restrictScalarsInclusionMatrix_mul_rep B X x b b') v).symm

end Extension

end Stacks.EtaleCohomology

end
