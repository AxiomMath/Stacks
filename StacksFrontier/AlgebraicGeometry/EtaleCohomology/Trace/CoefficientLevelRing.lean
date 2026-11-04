module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationCoefficients
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.Trace.Defs

/-!
# The finite coefficient rings `O ⊗ ℤ/ℓᵏ` of an `O`-sheaf

Let `O` be a finite free `ℤ_ℓ`-algebra with basis `b` of rank `d`. The `k`-th level of the
`O`-sheaf of a representation `π₁ → GL_m(O)` is a sheaf of modules over the finite ring
`Λ'_k = ℤ/ℓᵏ ⊗_{ℤ_ℓ} O`, free over `ℤ/ℓᵏ` of rank `d`; its stalks `(ℤ/ℓᵏ)^{md}` are free of
rank `m` over `Λ'_k`. We define the ring `Λ'_k` and its action on `(ℤ/ℓᵏ)^{md}`, and prove the
trace identity `Tr_{ℤ/ℓᵏ}(c · φ) = Tr_{Λ'_k/(ℤ/ℓᵏ)}(c · Tr_{Λ'_k} φ)` for a `Λ'_k`-linear
endomorphism `φ` of a finite free `Λ'_k`-module.

## Main definitions

* `Stacks.EtaleCohomology.coeffLevelRing`: the ring `ℤ/ℓᵏ ⊗_{ℤ_ℓ} O`.
* `Stacks.EtaleCohomology.coeffLevelMatrix`: its action on `(ℤ/ℓᵏ)^{md}`.
* `Stacks.EtaleCohomology.coeffLevelVecEquiv`: `(ℤ/ℓᵏ)^{md} ≃ (Λ'_k)^m`, linear over `Λ'_k`.

## Main results

* `Stacks.EtaleCohomology.trace_restrictScalars_eq_trace_trace`: the trace of a linear map
  after restriction of scalars along a finite free extension.
* `Stacks.EtaleCohomology.trace_restrictScalars_smul_eq`: the same for the twisted trace
  `Tr_R(c · φ)`.
* `Stacks.EtaleCohomology.coeffLevelVecEquiv_mulVec`: `coeffLevelVecEquiv` is linear over
  `ℤ/ℓᵏ ⊗ O`.
-/

@[expose] public noncomputable section

open scoped TensorProduct Matrix

namespace Stacks.EtaleCohomology

/-! ### Traces after restriction of scalars -/

section TraceRestrict

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  {P : Type*} [AddCommGroup P] [Module S P] [Module R P] [IsScalarTower R S P]

/-- **The trace of a linear map after restriction of scalars along a finite free extension**:
`Tr_R(φ) = Tr_{S/R}(Tr_S(φ))` for `φ` an `S`-linear endomorphism of a finite free `S`-module,
computed in a basis `b` of `S` over `R` and a basis `c` of `P` over `S`. -/
public theorem trace_restrictScalars_eq_trace_trace_of_basis {ι κ : Type*} [Finite ι]
    [Finite κ] (b : Module.Basis ι R S) (c : Module.Basis κ S P) (φ : P →ₗ[S] P) :
    LinearMap.trace R P (φ.restrictScalars R) = Algebra.trace R S (LinearMap.trace S P φ) := by
  classical
  have := Fintype.ofFinite ι
  have := Fintype.ofFinite κ
  rw [LinearMap.trace_eq_matrix_trace R (b.smulTower c), LinearMap.trace_eq_matrix_trace S c,
    Matrix.trace, Matrix.trace, map_sum, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Algebra.trace_eq_matrix_trace b, Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.diag, LinearMap.toMatrix_apply, Module.Basis.smulTower_apply,
    Module.Basis.smulTower_repr_mk, LinearMap.restrictScalars_apply, LinearMap.map_smul_of_tower,
    Algebra.leftMulMatrix_eq_repr_mul]
  rw [c.repr.map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]

/-- **The trace of a linear map after restriction of scalars along a finite free extension.** -/
public theorem trace_restrictScalars_eq_trace_trace [Module.Free R S] [Module.Finite R S]
    [Module.Free S P] [Module.Finite S P] (φ : P →ₗ[S] P) :
    LinearMap.trace R P (φ.restrictScalars R) = Algebra.trace R S (LinearMap.trace S P φ) := by
  classical
  exact trace_restrictScalars_eq_trace_trace_of_basis (Module.Free.chooseBasis R S)
    (Module.Free.chooseBasis S P) φ

/-- **Twisted traces after restriction of scalars**: `Tr_R(c · φ) = Tr_{S/R}(c · Tr_S(φ))`. -/
public theorem trace_restrictScalars_smul_eq [Module.Free R S] [Module.Finite R S]
    [Module.Free S P] [Module.Finite S P] (c : S) (φ : P →ₗ[S] P) :
    LinearMap.trace R P ((c • φ).restrictScalars R) =
      Algebra.trace R S (c * LinearMap.trace S P φ) := by
  rw [trace_restrictScalars_eq_trace_trace, map_smul, smul_eq_mul]

end TraceRestrict

/-! ### The ring `ℤ/ℓᵏ ⊗_{ℤ_ℓ} O` -/

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- The `ℤ_ℓ`-algebra structure of `ℤ/ℓᵏ`, through the reduction `ℤ_ℓ → ℤ/ℓᵏ`. -/
public abbrev zmodPowAlgebra (k : ℕ) : Algebra ℤ_[ℓ] (ZMod (ℓ ^ k)) :=
  (PadicInt.toZModPow k).toAlgebra

attribute [local instance] zmodPowAlgebra

variable (O : Type) [CommRing O] [Algebra ℤ_[ℓ] O]

/-- **The finite coefficient ring `ℤ/ℓᵏ ⊗_{ℤ_ℓ} O`** of the `k`-th level of an `O`-sheaf. -/
public def coeffLevelRing (k : ℕ) : Type := ZMod (ℓ ^ k) ⊗[ℤ_[ℓ]] O

/-- The commutative ring structure of `ℤ/ℓᵏ ⊗_{ℤ_ℓ} O`. -/
public instance coeffLevelRing.instCommRing (k : ℕ) : CommRing (coeffLevelRing ℓ O k) :=
  inferInstanceAs (CommRing (ZMod (ℓ ^ k) ⊗[ℤ_[ℓ]] O))

/-- The `ℤ/ℓᵏ`-algebra structure of `ℤ/ℓᵏ ⊗_{ℤ_ℓ} O`. -/
public instance coeffLevelRing.instAlgebra (k : ℕ) :
    Algebra (ZMod (ℓ ^ k)) (coeffLevelRing ℓ O k) :=
  inferInstanceAs (Algebra (ZMod (ℓ ^ k)) (ZMod (ℓ ^ k) ⊗[ℤ_[ℓ]] O))

/-- The image `1 ⊗ o` of an element of `O`. -/
public def coeffLevelRing.of (k : ℕ) : O →+* coeffLevelRing ℓ O k :=
  (Algebra.TensorProduct.includeRight : O →ₐ[ℤ_[ℓ]] ZMod (ℓ ^ k) ⊗[ℤ_[ℓ]] O).toRingHom

variable {O} {d : ℕ} (b : Module.Basis (Fin d) ℤ_[ℓ] O)

/-- The basis `1 ⊗ bᵢ` of `ℤ/ℓᵏ ⊗ O` over `ℤ/ℓᵏ`. -/
public def coeffLevelBasis (k : ℕ) : Module.Basis (Fin d) (ZMod (ℓ ^ k)) (coeffLevelRing ℓ O k) :=
  Algebra.TensorProduct.basis (ZMod (ℓ ^ k)) b

/-- The `i`-th element of `coeffLevelBasis` is `1 ⊗ bᵢ`. -/
public theorem coeffLevelBasis_apply (k : ℕ) (i : Fin d) :
    coeffLevelBasis ℓ b k i = coeffLevelRing.of ℓ O k (b i) :=
  Algebra.TensorProduct.basis_apply b i

/-- The coordinates of `1 ⊗ o` in the basis `1 ⊗ b` are the reductions of those of `o` in `b`. -/
public theorem coeffLevelBasis_repr_of (k : ℕ) (o : O) (i : Fin d) :
    (coeffLevelBasis ℓ b k).repr (coeffLevelRing.of ℓ O k o) i =
      PadicInt.toZModPow k (b.repr o i) := by
  show (Algebra.TensorProduct.basis (ZMod (ℓ ^ k)) b).repr (1 ⊗ₜ o) i = _
  rw [Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply]
  rfl

/-- `ℤ/ℓᵏ ⊗_{ℤ_ℓ} O` is free over `ℤ/ℓᵏ` when `O` is free over `ℤ_ℓ`. -/
public instance coeffLevelRing.instFree (k : ℕ) [Module.Free ℤ_[ℓ] O] :
    Module.Free (ZMod (ℓ ^ k)) (coeffLevelRing ℓ O k) :=
  inferInstanceAs (Module.Free (ZMod (ℓ ^ k)) (ZMod (ℓ ^ k) ⊗[ℤ_[ℓ]] O))

/-- `ℤ/ℓᵏ ⊗_{ℤ_ℓ} O` is finite over `ℤ/ℓᵏ` when `O` is finite over `ℤ_ℓ`. -/
public instance coeffLevelRing.instFinite (k : ℕ) [Module.Finite ℤ_[ℓ] O] :
    Module.Finite (ZMod (ℓ ^ k)) (coeffLevelRing ℓ O k) :=
  inferInstanceAs (Module.Finite (ZMod (ℓ ^ k)) (ZMod (ℓ ^ k) ⊗[ℤ_[ℓ]] O))

/-- `ℤ/ℓᵏ ⊗_{ℤ_ℓ} O` is a finite ring when `O` is finite over `ℤ_ℓ`. -/
public instance coeffLevelRing.finite (k : ℕ) [NeZero (ℓ ^ k)] [Module.Finite ℤ_[ℓ] O] :
    Finite (coeffLevelRing ℓ O k) :=
  Module.finite_of_finite (ZMod (ℓ ^ k))

/-! ### The action on `(ℤ/ℓᵏ)^{md}` -/

variable (m : ℕ)

/-- The scalar matrices of `ℤ_ℓ` are scalar after restriction of scalars. -/
public theorem coefficientScalarRingHom_algebraMap (c : ℤ_[ℓ]) :
    coefficientScalarRingHom b m (algebraMap ℤ_[ℓ] O c) =
      algebraMap ℤ_[ℓ] (Matrix (Fin (m * d)) (Fin (m * d)) ℤ_[ℓ]) c := by
  ext p q
  obtain ⟨⟨i, l⟩, rfl⟩ := finProdFinEquiv.surjective p
  obtain ⟨⟨j, l'⟩, rfl⟩ := finProdFinEquiv.surjective q
  rw [coefficientScalarRingHom, RingHom.comp_apply, coefficientMatrixRingHom_apply,
    Matrix.scalar_apply, Matrix.diagonal_apply]
  by_cases hij : i = j <;> by_cases hll : l = l' <;>
    simp [AlgHom.commutes, Matrix.algebraMap_matrix_apply, hij, hll]

/-- The reduction modulo `ℓᵏ` of the action of `O` on `ℤ_ℓ^{md}` through the scalar matrices,
as a map of `ℤ_ℓ`-algebras. -/
public def coeffScalarLevelAlgHom (k : ℕ) :
    O →ₐ[ℤ_[ℓ]] Matrix (Fin (m * d)) (Fin (m * d)) (ZMod (ℓ ^ k)) :=
  { (PadicInt.toZModPow k).mapMatrix.comp (coefficientScalarRingHom b m) with
    commutes' := fun c => by
      change (coefficientScalarRingHom b m (algebraMap ℤ_[ℓ] O c)).map (PadicInt.toZModPow k) = _
      rw [coefficientScalarRingHom_algebraMap]
      ext p q
      simp only [Matrix.map_apply, Matrix.algebraMap_matrix_apply]
      split_ifs <;> first | rfl | simp }

/-- `coeffScalarLevelAlgHom` is the reduction modulo `ℓᵏ` of the scalar matrix of `o`. -/
public theorem coeffScalarLevelAlgHom_apply (k : ℕ) (o : O) :
    coeffScalarLevelAlgHom ℓ b m k o =
      (coefficientScalarRingHom b m o).map (PadicInt.toZModPow k) :=
  rfl

/-- **The action of `ℤ/ℓᵏ ⊗ O` on `(ℤ/ℓᵏ)^{md}`**, by matrices. -/
public def coeffLevelMatrix (k : ℕ) :
    coeffLevelRing ℓ O k →ₐ[ZMod (ℓ ^ k)] Matrix (Fin (m * d)) (Fin (m * d)) (ZMod (ℓ ^ k)) :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _) (coeffScalarLevelAlgHom ℓ b m k)
    fun _ _ => Algebra.commutes' _ _

/-- `1 ⊗ o` acts through the reduction modulo `ℓᵏ` of the scalar matrix of `o`. -/
public theorem coeffLevelMatrix_of (k : ℕ) (o : O) :
    coeffLevelMatrix ℓ b m k (coeffLevelRing.of ℓ O k o) =
      (coefficientScalarRingHom b m o).map (PadicInt.toZModPow k) :=
  (Algebra.TensorProduct.lift_tmul _ _ _ (1 : ZMod (ℓ ^ k)) o).trans
    (by rw [map_one, one_mul]; rfl)

/-- The elements of `ℤ/ℓᵏ` act by scalar matrices. -/
public theorem coeffLevelMatrix_algebraMap (k : ℕ) (a : ZMod (ℓ ^ k)) :
    coeffLevelMatrix ℓ b m k (algebraMap _ _ a) = Matrix.scalar _ a := by
  rw [AlgHom.commutes]
  rfl

include b in
/-- **The trace of `1 ⊗ z` over `ℤ/ℓᵏ` is the reduction of the trace of `z` over `ℤ_ℓ`.** -/
public theorem algebraTrace_coeffLevelRing_of (k : ℕ) (z : O) :
    Algebra.trace (ZMod (ℓ ^ k)) (coeffLevelRing ℓ O k) (coeffLevelRing.of ℓ O k z) =
      PadicInt.toZModPow k (Algebra.trace ℤ_[ℓ] O z) := by
  classical
  rw [Algebra.trace_eq_matrix_trace (coeffLevelBasis ℓ b k), Algebra.trace_eq_matrix_trace b]
  refine Eq.trans ?_ (AddMonoidHom.map_trace (PadicInt.toZModPow k).toAddMonoidHom _).symm
  congr 1
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    coeffLevelBasis_apply, ← map_mul, coeffLevelBasis_repr_of]
  rfl

/-! ### `(ℤ/ℓᵏ)^{md}` is free of rank `m` over `ℤ/ℓᵏ ⊗ O` -/

/-- **`(ℤ/ℓᵏ)^{md} ≃ (ℤ/ℓᵏ ⊗ O)^m`**: the coordinates indexed by `(i, l)` are the coordinates of
the `i`-th entry in the basis `1 ⊗ b`. -/
public def coeffLevelVecEquiv (k : ℕ) :
    (Fin (m * d) → ZMod (ℓ ^ k)) ≃ₗ[ZMod (ℓ ^ k)] (Fin m → coeffLevelRing ℓ O k) :=
  (LinearEquiv.funCongrLeft (ZMod (ℓ ^ k)) (ZMod (ℓ ^ k)) finProdFinEquiv).trans
    ((LinearEquiv.curry (ZMod (ℓ ^ k)) (ZMod (ℓ ^ k)) (Fin m) (Fin d)).trans
      (LinearEquiv.piCongrRight fun _ => (coeffLevelBasis ℓ b k).equivFun.symm))

/-- The `i`-th entry of `coeffLevelVecEquiv w` has the coordinates `w (i, l)` in the basis
`1 ⊗ b`. -/
public theorem coeffLevelVecEquiv_apply (k : ℕ) (w : Fin (m * d) → ZMod (ℓ ^ k)) (i : Fin m) :
    coeffLevelVecEquiv ℓ b m k w i =
      (coeffLevelBasis ℓ b k).equivFun.symm fun l => w (finProdFinEquiv (i, l)) :=
  rfl

/-- On reductions of integral vectors, `coeffLevelVecEquiv` is the reduction of
`coefficientVecEquiv`. -/
public theorem coeffLevelVecEquiv_reduce (k : ℕ) (w : Fin (m * d) → ℤ_[ℓ]) :
    coeffLevelVecEquiv ℓ b m k (fun p => PadicInt.toZModPow k (w p)) =
      fun i => coeffLevelRing.of ℓ O k (coefficientVecEquiv b m w i) := by
  funext i
  apply (coeffLevelBasis ℓ b k).repr.injective
  ext l
  rw [coeffLevelVecEquiv_apply, coeffLevelBasis_repr_of, coefficientVecEquiv_apply,
    ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply, ← Module.Basis.equivFun_apply,
    LinearEquiv.apply_symm_apply]

/-- **`coeffLevelVecEquiv` is linear over `ℤ/ℓᵏ ⊗ O`**: the action of `c` through
`coeffLevelMatrix` is multiplication by `c`. -/
public theorem coeffLevelVecEquiv_mulVec (k : ℕ) (c : coeffLevelRing ℓ O k)
    (w : Fin (m * d) → ZMod (ℓ ^ k)) :
    coeffLevelVecEquiv ℓ b m k (coeffLevelMatrix ℓ b m k c *ᵥ w) =
      c • coeffLevelVecEquiv ℓ b m k w := by
  have key : ∀ (o : O) (w : Fin (m * d) → ZMod (ℓ ^ k)),
      coeffLevelVecEquiv ℓ b m k (coeffLevelMatrix ℓ b m k (coeffLevelRing.of ℓ O k o) *ᵥ w) =
        coeffLevelRing.of ℓ O k o • coeffLevelVecEquiv ℓ b m k w := by
    intro o w
    obtain ⟨w', rfl⟩ : ∃ w' : Fin (m * d) → ℤ_[ℓ], (fun p => PadicInt.toZModPow k (w' p)) = w :=
      ⟨fun p => (ZMod.ringHom_surjective (PadicInt.toZModPow k) (w p)).choose,
        funext fun p => (ZMod.ringHom_surjective (PadicInt.toZModPow k) (w p)).choose_spec⟩
    have hmv : coeffLevelMatrix ℓ b m k (coeffLevelRing.of ℓ O k o) *ᵥ
        (fun p => PadicInt.toZModPow k (w' p)) =
        fun p => PadicInt.toZModPow k ((coefficientScalarRingHom b m o *ᵥ w') p) := by
      rw [coeffLevelMatrix_of]
      funext p
      exact (RingHom.map_mulVec (PadicInt.toZModPow k) _ w' p).symm
    rw [hmv, coeffLevelVecEquiv_reduce, coeffLevelVecEquiv_reduce, coefficientVecEquiv_scalar]
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  let L₁ : coeffLevelRing ℓ O k →ₗ[ZMod (ℓ ^ k)] (Fin m → coeffLevelRing ℓ O k) :=
    { toFun := fun c => coeffLevelVecEquiv ℓ b m k (coeffLevelMatrix ℓ b m k c *ᵥ w)
      map_add' := fun c c' => by rw [map_add, Matrix.add_mulVec, map_add]
      map_smul' := fun a c => by
        rw [map_smul, Matrix.smul_mulVec, map_smul]
        rfl }
  let L₂ : coeffLevelRing ℓ O k →ₗ[ZMod (ℓ ^ k)] (Fin m → coeffLevelRing ℓ O k) :=
    (LinearMap.toSpanSingleton (coeffLevelRing ℓ O k) _
      (coeffLevelVecEquiv ℓ b m k w)).restrictScalars (ZMod (ℓ ^ k))
  have h : L₁ = L₂ := (coeffLevelBasis ℓ b k).ext fun i => by
    rw [coeffLevelBasis_apply]
    exact key (b i) w
  exact LinearMap.congr_fun h c

end Stacks.EtaleCohomology

end
