module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationCoefficients
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.Topology.Instances.Matrix

/-!
# Tensor products of lisse sheaves

On a connected scheme the tensor product `ℱ_ρ ⊗ ℱ_{ρ'}` of the lisse sheaves of two representations
of `π₁(X, x̄)` is the sheaf of the Kronecker product `ρ ⊗ ρ'`, whose traces are the products of the
traces. This file builds the Kronecker product of representations with values in `GL_r(R)` over
any commutative ring (continuous when `R` is a topological ring, e.g. `R = ℚ_ℓ`), and for
representations with coefficients in a finite free `ℤ_ℓ`-algebra `O` the `O`-sheaf of `ρ ⊗ ρ'`,
whose stalk endomorphisms have `O`-trace `tr ρ(g) · tr ρ'(g)` [SGA 4½, Rapport, 1.2], [Weil II,
1.1.1]. These are the sheaves `ℱ^{⊗ 2i}` of Deligne's Rankin argument [Weil II, 1.5.2] and the
twists `pr₁^* ℱ ⊗ L_ψ` of the Fourier transform.

## Main definitions

* `Stacks.EtaleCohomology.kroneckerMonoidHom`: `(A, B) ↦ A ⊗ₖ B` on `M_r × M_s → M_{rs}`.
* `Stacks.EtaleCohomology.kroneckerRepresentation`: the representation `ρ ⊗ ρ'`.
* `Stacks.EtaleCohomology.coefficientKronecker`: the Kronecker product read on restrictions of
  scalars.

## Main results

* `Stacks.EtaleCohomology.trace_kroneckerRepresentation`: `tr (ρ ⊗ ρ')(g) = tr ρ(g) tr ρ'(g)`.
* `Stacks.EtaleCohomology.continuous_kroneckerRepresentation`: continuity over a topological ring.
* `Stacks.EtaleCohomology.continuous_restrictScalarsRepresentation_kroneckerRepresentation`:
  continuity of the restriction of scalars of `ρ ⊗ ρ'`.
* `Stacks.EtaleCohomology.trace_kroneckerRepresentation_stalkEnd`: the `O`-trace on the stalks of
  the tensor product sheaf.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale

open scoped Matrix Kronecker

universe u

namespace Stacks.EtaleCohomology

section Kronecker

variable {G R : Type*} [Group G] [CommRing R] {r s : ℕ}

/-- The Kronecker product `(A, B) ↦ A ⊗ₖ B` of square matrices, flattened to `Fin (r * s)`, as a
monoid homomorphism. -/
public def kroneckerMonoidHom :
    Matrix (Fin r) (Fin r) R × Matrix (Fin s) (Fin s) R →*
      Matrix (Fin (r * s)) (Fin (r * s)) R where
  toFun p := Matrix.reindex finProdFinEquiv finProdFinEquiv (p.1 ⊗ₖ p.2)
  map_one' := by
    rw [Prod.fst_one, Prod.snd_one, Matrix.one_kronecker_one]
    exact (Matrix.reindexAlgEquiv R R finProdFinEquiv).map_one
  map_mul' p q := by
    rw [Prod.fst_mul, Prod.snd_mul, Matrix.mul_kronecker_mul]
    exact (Matrix.reindexAlgEquiv R R finProdFinEquiv).map_mul _ _

/-- `kroneckerMonoidHom` sends `(A, B)` to the reindexed Kronecker product `A ⊗ₖ B`. -/
public theorem kroneckerMonoidHom_apply (p : Matrix (Fin r) (Fin r) R × Matrix (Fin s) (Fin s) R) :
    kroneckerMonoidHom p = Matrix.reindex finProdFinEquiv finProdFinEquiv (p.1 ⊗ₖ p.2) :=
  rfl

/-- **The tensor product `ρ ⊗ ρ'` of two representations**, `g ↦ ρ(g) ⊗ₖ ρ'(g)`. -/
public def kroneckerRepresentation (ρ : G →* GL (Fin r) R) (ρ' : G →* GL (Fin s) R) :
    G →* GL (Fin (r * s)) R :=
  (Units.map kroneckerMonoidHom).comp (MulEquiv.prodUnits.symm.toMonoidHom.comp (ρ.prod ρ'))

variable (ρ : G →* GL (Fin r) R) (ρ' : G →* GL (Fin s) R)

/-- The matrix of `(ρ ⊗ ρ')(g)` is the reindexed Kronecker product `ρ(g) ⊗ₖ ρ'(g)`. -/
public theorem kroneckerRepresentation_val (g : G) :
    (kroneckerRepresentation ρ ρ' g).val =
      Matrix.reindex finProdFinEquiv finProdFinEquiv ((ρ g).val ⊗ₖ (ρ' g).val) :=
  rfl

/-- The matrix of `(ρ ⊗ ρ')(g)⁻¹` is the reindexed Kronecker product `ρ(g)⁻¹ ⊗ₖ ρ'(g)⁻¹`. -/
public theorem kroneckerRepresentation_inv_val (g : G) :
    ((kroneckerRepresentation ρ ρ' g)⁻¹).val =
      Matrix.reindex finProdFinEquiv finProdFinEquiv (((ρ g)⁻¹).val ⊗ₖ ((ρ' g)⁻¹).val) :=
  rfl

/-- Reindexing a square matrix along an equivalence does not change its trace. -/
theorem trace_reindex {m n : Type*} [Fintype m] [Fintype n] (e : m ≃ n) (A : Matrix m m R) :
    (Matrix.reindex e e A).trace = A.trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.reindex_apply, Matrix.submatrix_apply]
  exact e.symm.sum_comp fun i => A i i

/-- **The trace of `ρ ⊗ ρ'` is the product of the traces.** -/
public theorem trace_kroneckerRepresentation (g : G) :
    (kroneckerRepresentation ρ ρ' g).val.trace = (ρ g).val.trace * (ρ' g).val.trace := by
  rw [kroneckerRepresentation_val, trace_reindex, Matrix.trace_kronecker]

/-- The reindexed Kronecker product of two continuous matrix-valued maps is continuous. -/
theorem continuous_kronecker_reindex {Y : Type*} [TopologicalSpace Y] [TopologicalSpace R]
    [IsTopologicalRing R] {A : Y → Matrix (Fin r) (Fin r) R} {B : Y → Matrix (Fin s) (Fin s) R}
    (hA : Continuous A) (hB : Continuous B) :
    Continuous fun y => Matrix.reindex finProdFinEquiv finProdFinEquiv (A y ⊗ₖ B y) :=
  Continuous.matrix_reindex (continuous_matrix fun (i : Fin r × Fin s) (j : Fin r × Fin s) =>
    (hA.matrix_elem i.1 j.1).mul (hB.matrix_elem i.2 j.2)) _ _

/-- **`ρ ⊗ ρ'` is continuous** when `ρ` and `ρ'` are, over a topological ring. -/
public theorem continuous_kroneckerRepresentation [TopologicalSpace G] [TopologicalSpace R]
    [IsTopologicalRing R] (hρ : Continuous ρ) (hρ' : Continuous ρ') :
    Continuous (kroneckerRepresentation ρ ρ') :=
  Units.continuous_iff.2
    ⟨continuous_kronecker_reindex (Units.continuous_val.comp hρ) (Units.continuous_val.comp hρ'),
      continuous_kronecker_reindex (Units.continuous_coe_inv.comp hρ)
        (Units.continuous_coe_inv.comp hρ')⟩

end Kronecker

/-! ### Restriction of scalars of a Kronecker product -/

section Coefficients

variable {R O : Type*} [CommRing R] [CommRing O] [Algebra R O] {d : ℕ}
  (b : Module.Basis (Fin d) R O) {r s : ℕ}

/-- The Kronecker product of `O`-matrices read on their restrictions of scalars to `R`: the entry
at `((i, i'), k), ((j, j'), l)` is `∑ₘ P_{(i,k),(j,m)} Q_{(i',m),(j',l)}`, the `(k, l)` entry of
the product of the multiplication matrices of `M i j` and `N i' j'`. -/
public def coefficientKronecker (P : Matrix (Fin (r * d)) (Fin (r * d)) R)
    (Q : Matrix (Fin (s * d)) (Fin (s * d)) R) :
    Matrix (Fin (r * s * d)) (Fin (r * s * d)) R := fun a c =>
  ∑ m : Fin d, P (finProdFinEquiv ((finProdFinEquiv.symm (finProdFinEquiv.symm a).1).1,
      (finProdFinEquiv.symm a).2))
    (finProdFinEquiv ((finProdFinEquiv.symm (finProdFinEquiv.symm c).1).1, m)) *
    Q (finProdFinEquiv ((finProdFinEquiv.symm (finProdFinEquiv.symm a).1).2, m))
      (finProdFinEquiv ((finProdFinEquiv.symm (finProdFinEquiv.symm c).1).2,
        (finProdFinEquiv.symm c).2))

/-- **The restriction of scalars of `M ⊗ₖ N` is `coefficientKronecker` of the restrictions of
scalars.** -/
public theorem coefficientMatrixRingHom_kroneckerMonoidHom (M : Matrix (Fin r) (Fin r) O)
    (N : Matrix (Fin s) (Fin s) O) :
    coefficientMatrixRingHom b (r * s) (kroneckerMonoidHom (M, N)) =
      coefficientKronecker (coefficientMatrixRingHom b r M) (coefficientMatrixRingHom b s N) := by
  ext a c
  obtain ⟨⟨I, k⟩, rfl⟩ := finProdFinEquiv.surjective a
  obtain ⟨⟨J, l⟩, rfl⟩ := finProdFinEquiv.surjective c
  obtain ⟨⟨i, i'⟩, rfl⟩ := finProdFinEquiv.surjective I
  obtain ⟨⟨j, j'⟩, rfl⟩ := finProdFinEquiv.surjective J
  rw [coefficientMatrixRingHom_apply, coefficientKronecker]
  simp only [Equiv.symm_apply_apply, kroneckerMonoidHom_apply, Matrix.reindex_apply,
    Matrix.submatrix_apply, Matrix.kroneckerMap_apply, map_mul, Matrix.mul_apply,
    coefficientMatrixRingHom_apply]

/-- `coefficientKronecker` is jointly continuous. -/
public theorem continuous_coefficientKronecker {Y : Type*} [TopologicalSpace Y] [TopologicalSpace R]
    [IsTopologicalRing R] {P : Y → Matrix (Fin (r * d)) (Fin (r * d)) R}
    {Q : Y → Matrix (Fin (s * d)) (Fin (s * d)) R} (hP : Continuous P) (hQ : Continuous Q) :
    Continuous fun y => coefficientKronecker (P y) (Q y) :=
  continuous_matrix fun _ _ => continuous_finsetSum _ fun _ _ =>
    (hP.matrix_elem _ _).mul (hQ.matrix_elem _ _)

end Coefficients

/-! ### The tensor product of `O`-sheaves of representations -/

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  {ℓ : ℕ} [Fact ℓ.Prime] {r s : ℕ}
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
  {O : Type} [CommRing O] [Algebra ℤ_[ℓ] O] {d : ℕ} (b : Module.Basis (Fin d) ℤ_[ℓ] O)
  (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) O)
  (ρ' : EtaleFundamentalGroup X.1 x →* GL (Fin s) O)

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
/-- **The restriction of scalars of `ρ ⊗ ρ'` is continuous** when those of `ρ` and `ρ'` are. -/
public theorem continuous_restrictScalarsRepresentation_kroneckerRepresentation
    (hρ : Continuous (restrictScalarsRepresentation B X x b ρ))
    (hρ' : Continuous (restrictScalarsRepresentation B X x b ρ')) :
    Continuous (restrictScalarsRepresentation B X x b (kroneckerRepresentation ρ ρ')) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (continuous_coefficientKronecker (Units.continuous_val.comp hρ)
      (Units.continuous_val.comp hρ')).congr fun g =>
        (coefficientMatrixRingHom_kroneckerMonoidHom b _ _).symm
  · exact (continuous_coefficientKronecker (Units.continuous_coe_inv.comp hρ)
      (Units.continuous_coe_inv.comp hρ')).congr fun g =>
        (coefficientMatrixRingHom_kroneckerMonoidHom b _ _).symm

variable (hρρ' : Continuous (restrictScalarsRepresentation B X x b (kroneckerRepresentation ρ ρ')))

/-- **The trace on the tensor product `ℱ_ρ ⊗ ℱ_{ρ'}`**: an endomorphism of the geometric point acts
on the stalk of the sheaf of `ρ ⊗ ρ'` with `O`-trace `tr ρ(g) · tr ρ'(g)`. -/
public theorem trace_kroneckerRepresentation_stalkEnd {s' : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s' ≅ finiteEtaleFiberFunctor x) (a : GeometricPoint.Hom s' s')
    (σ : EtaleFundamentalGroup X.1 s') (hσ : σ.hom = finiteEtaleFiberMap a) :
    LinearMap.trace O _
        ((coefficientRepresentationSheaf B X x b (kroneckerRepresentation ρ ρ') hρρ').stalkEnd a) =
      (ρ (etaleFundamentalGroupMulEquiv t σ)).val.trace *
        (ρ' (etaleFundamentalGroupMulEquiv t σ)).val.trace := by
  rw [trace_coefficientRepresentationSheaf_stalkEnd B X x b _ hρρ' t a σ hσ,
    trace_kroneckerRepresentation]

end Stacks.EtaleCohomology
