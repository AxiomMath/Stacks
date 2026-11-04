module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Instances.Matrix

/-!
# Restriction of scalars of matrix representations

For a finite extension `E/F` with an `F`-basis `b` of `E` (of size `d`), an `m × n` matrix over
`E` is an `(m d) × (n d)` matrix over `F`: each entry `x` is replaced by the matrix of
multiplication by `x` in the basis `b` (`Algebra.leftMulMatrix`), the index `(i, l)` being
`finProdFinEquiv (i, l)`.  This is multiplicative, so a representation `σ : G → GL_m(E)` gives
`Res_b σ : G → GL_{m d}(F)`, the restriction of scalars of `σ`.

On a matrix with entries in `F`, restriction of scalars is `M ⊗ 1_d`; in particular a
representation `ρ : G → GL_r(F)` is a direct summand of `Res_b (ρ ⊗ E)`.

## Main definitions

* `Stacks.EtaleCohomology.restrictScalarsMatrix`, `restrictScalarsMonoidHom`,
  `restrictScalarsRep`.
-/

@[expose] public noncomputable section

open Matrix

namespace Stacks.EtaleCohomology

variable {F E : Type*} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)

/-- **Restriction of scalars of a matrix**: the `(m d) × (n d)` matrix over `F` whose
`(i, l), (j, l')` entry is the `(l, l')` entry of the matrix of multiplication by `M i j` in the
basis `b`. -/
public def restrictScalarsMatrix {m n : ℕ} (M : Matrix (Fin m) (Fin n) E) :
    Matrix (Fin (m * d)) (Fin (n * d)) F :=
  Matrix.of fun p q => Algebra.leftMulMatrix b (M (finProdFinEquiv.symm p).1
    (finProdFinEquiv.symm q).1) (finProdFinEquiv.symm p).2 (finProdFinEquiv.symm q).2

@[simp]
public theorem restrictScalarsMatrix_apply {m n : ℕ} (M : Matrix (Fin m) (Fin n) E) (i : Fin m)
    (l : Fin d) (j : Fin n) (l' : Fin d) :
    restrictScalarsMatrix b M (finProdFinEquiv (i, l)) (finProdFinEquiv (j, l')) =
      Algebra.leftMulMatrix b (M i j) l l' := by
  simp only [restrictScalarsMatrix, Matrix.of_apply, Equiv.symm_apply_apply]

/-- A sum over `Fin (m * d)` splits as a double sum over `Fin m` and `Fin d`. -/
private theorem sum_finProdFinEquiv {α : Type*} [AddCommMonoid α] {m : ℕ} (f : Fin (m * d) → α) :
    ∑ p, f p = ∑ i, ∑ l, f (finProdFinEquiv (i, l)) := by
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]

public theorem restrictScalarsMatrix_mul {m n o : ℕ} (M : Matrix (Fin m) (Fin n) E)
    (N : Matrix (Fin n) (Fin o) E) :
    restrictScalarsMatrix b (M * N) = restrictScalarsMatrix b M * restrictScalarsMatrix b N := by
  ext p q
  obtain ⟨⟨i, l⟩, rfl⟩ := finProdFinEquiv.surjective p
  obtain ⟨⟨j, l'⟩, rfl⟩ := finProdFinEquiv.surjective q
  rw [restrictScalarsMatrix_apply, Matrix.mul_apply (M := restrictScalarsMatrix b M),
    sum_finProdFinEquiv]
  simp only [restrictScalarsMatrix_apply]
  rw [Matrix.mul_apply, map_sum, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, Matrix.mul_apply]

public theorem restrictScalarsMatrix_one {m : ℕ} :
    restrictScalarsMatrix b (1 : Matrix (Fin m) (Fin m) E) = 1 := by
  ext p q
  obtain ⟨⟨i, l⟩, rfl⟩ := finProdFinEquiv.surjective p
  obtain ⟨⟨j, l'⟩, rfl⟩ := finProdFinEquiv.surjective q
  rw [restrictScalarsMatrix_apply]
  by_cases hij : i = j
  · subst hij
    by_cases hl : l = l' <;> simp [Matrix.one_apply, hl]
  · simp [hij]

/-- On a matrix with entries in `F`, restriction of scalars is `M ⊗ 1_d`. -/
public theorem restrictScalarsMatrix_map_algebraMap {m n : ℕ} (M : Matrix (Fin m) (Fin n) F)
    (i : Fin m) (l : Fin d) (j : Fin n) (l' : Fin d) :
    restrictScalarsMatrix b (M.map (algebraMap F E)) (finProdFinEquiv (i, l))
      (finProdFinEquiv (j, l')) = M i j * (1 : Matrix (Fin d) (Fin d) F) l l' := by
  rw [restrictScalarsMatrix_apply, Matrix.map_apply, AlgHom.commutes,
    Algebra.algebraMap_eq_smul_one, Matrix.smul_apply, smul_eq_mul]

/-- Restriction of scalars as a monoid homomorphism of square matrices. -/
public def restrictScalarsMonoidHom (m : ℕ) :
    Matrix (Fin m) (Fin m) E →* Matrix (Fin (m * d)) (Fin (m * d)) F where
  toFun := restrictScalarsMatrix b
  map_one' := restrictScalarsMatrix_one b
  map_mul' := restrictScalarsMatrix_mul b

/-- **The restriction of scalars `Res_b σ : G → GL_{m d}(F)` of a representation
`σ : G → GL_m(E)`.** -/
public def restrictScalarsRep {G : Type*} [Monoid G] {m : ℕ} (σ : G →* GL (Fin m) E) :
    G →* GL (Fin (m * d)) F :=
  (Units.map (restrictScalarsMonoidHom b m)).comp σ

@[simp]
public theorem restrictScalarsRep_val {G : Type*} [Monoid G] {m : ℕ} (σ : G →* GL (Fin m) E)
    (g : G) : (restrictScalarsRep b σ g).val = restrictScalarsMatrix b (σ g).val :=
  rfl

section Summand

variable {r : ℕ} (l₀ : Fin d)

/-- The inclusion `F^r → F^{r d}` onto the coordinates `(i, l₀)`. -/
public def summandInclusion : Matrix (Fin (r * d)) (Fin r) F :=
  Matrix.of fun p j => if (finProdFinEquiv.symm p).1 = j ∧ (finProdFinEquiv.symm p).2 = l₀ then 1
    else 0

/-- The projection `F^{r d} → F^r` onto the coordinates `(i, l₀)`. -/
public def summandProjection : Matrix (Fin r) (Fin (r * d)) F :=
  Matrix.of fun j p => if (finProdFinEquiv.symm p).1 = j ∧ (finProdFinEquiv.symm p).2 = l₀ then 1
    else 0

public theorem summandProjection_mul_summandInclusion :
    summandProjection l₀ * summandInclusion l₀ = (1 : Matrix (Fin r) (Fin r) F) := by
  ext i j
  rw [Matrix.mul_apply, sum_finProdFinEquiv]
  simp only [summandProjection, summandInclusion, Matrix.of_apply, Equiv.symm_apply_apply,
    mul_ite, mul_one, mul_zero, ite_and]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, eq_comm]

/-- `M ⊗ 1` maps the summand `(i, l₀)` by `M`. -/
public theorem restrictScalarsMatrix_map_mul_summandInclusion (M : Matrix (Fin r) (Fin r) F) :
    restrictScalarsMatrix b (M.map (algebraMap F E)) * summandInclusion l₀ =
      summandInclusion l₀ * M := by
  ext p j
  obtain ⟨⟨i, l⟩, rfl⟩ := finProdFinEquiv.surjective p
  rw [Matrix.mul_apply, sum_finProdFinEquiv, Matrix.mul_apply]
  simp only [restrictScalarsMatrix_map_algebraMap, summandInclusion, Matrix.of_apply,
    Equiv.symm_apply_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_and, ite_mul,
    one_mul, zero_mul]
  by_cases hl : l = l₀ <;> simp [hl, Finset.sum_ite_eq', Finset.sum_ite_eq]

public theorem summandProjection_mul_restrictScalarsMatrix_map (M : Matrix (Fin r) (Fin r) F) :
    summandProjection l₀ * restrictScalarsMatrix b (M.map (algebraMap F E)) =
      M * summandProjection l₀ := by
  ext j q
  obtain ⟨⟨i, l⟩, rfl⟩ := finProdFinEquiv.surjective q
  rw [Matrix.mul_apply, sum_finProdFinEquiv, Matrix.mul_apply]
  simp only [restrictScalarsMatrix_map_algebraMap, summandProjection, Matrix.of_apply,
    Equiv.symm_apply_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_and, ite_mul,
    one_mul, zero_mul]
  by_cases hl : l = l₀ <;> simp [hl, Finset.sum_ite_eq', Finset.sum_ite_eq]

end Summand

section Continuity

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace F]
  [IsTopologicalRing F]

omit [IsTopologicalRing F] in
/-- `Res_b σ` is continuous as soon as its matrix entries are. -/
public theorem continuous_restrictScalarsRep {m : ℕ} (σ : G →* GL (Fin m) E)
    (h : Continuous fun g => restrictScalarsMatrix b (σ g).val) :
    Continuous (restrictScalarsRep b σ) := by
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  have : (fun g => ((restrictScalarsRep b σ g)⁻¹ : GL (Fin (m * d)) F).val) =
      (fun g => restrictScalarsMatrix b (σ g).val) ∘ fun g => g⁻¹ := by
    funext g
    simp [restrictScalarsRep, ← map_inv]
    rfl
  rw [this]
  exact h.comp continuous_inv

omit [Group G] [IsTopologicalGroup G] in
/-- `Res_b (ρ ⊗ E)` is continuous for continuous `ρ`. -/
public theorem continuous_restrictScalarsMatrix_map {r : ℕ} {ρ : G → Matrix (Fin r) (Fin r) F}
    (hρ : Continuous ρ) :
    Continuous fun g => restrictScalarsMatrix b ((ρ g).map (algebraMap F E)) := by
  refine continuous_pi fun p => continuous_pi fun q => ?_
  obtain ⟨⟨i, l⟩, rfl⟩ := finProdFinEquiv.surjective p
  obtain ⟨⟨j, l'⟩, rfl⟩ := finProdFinEquiv.surjective q
  simp only [restrictScalarsMatrix_map_algebraMap]
  exact (hρ.matrix_elem i j).mul continuous_const

end Continuity

end Stacks.EtaleCohomology

end
