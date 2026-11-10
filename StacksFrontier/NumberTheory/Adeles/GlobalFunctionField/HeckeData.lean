module

public import StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.HeckeStability

/-!
# The data of the Hecke operators exist at every place of a function field

The Hecke operator `T_v` of `Stacks.Adeles.heckeOperator` is the explicit finite sum
```
T_v(f)(x) = f (diag (π_v⁻¹, 1) * x) + ∑_{i = 1}^{q_v} f ((1, 0; -π_v⁻¹ λ_i, π_v⁻¹) * x),
```
and its data — a uniformizer `π_v`, a system `λ_1, …, λ_{q_v}` of representatives of `κ_v`, and
the adelic matrices which are the displayed matrices at `v` and the identity elsewhere — are
characterized by `Stacks.Adeles.IsHeckeDataAt`. We show that these data exist at every place of
a function field `K` over a finite field, so that the eigenvalue equations
`Stacks.Adeles.IsHeckeEigenvalueAt` are never vacuous there.

## Main definitions

* `Stacks.Adeles.GlobalFunctionField.localMatrix` — the adelic matrix with prescribed component
  at one place and the identity matrix at every other place.
* `Stacks.Adeles.GlobalFunctionField.localGL` — the embedding `GL₂(K_v) → GL₂(A)` it induces.

## Main results

* `Stacks.Adeles.GlobalFunctionField.isLocalMatrixAt_localGL` — `localGL v m` is `m` at `v`
  and the identity elsewhere.
* `Stacks.Adeles.GlobalFunctionField.exists_isResidueSystem` — a system of representatives of
  the (finite) residue field `κ_v` indexed by `Fin q_v`.
* `Stacks.Adeles.GlobalFunctionField.exists_isHeckeDataAt` — the data of `T_v` exist at every
  place.
-/

@[expose] public noncomputable section

open Matrix

universe u

namespace Stacks.Adeles.GlobalFunctionField

section KFree

variable {K : Type u} [Field K] (v : Place K)

open scoped Classical in
/-- The adelic matrix whose component at `v` is `m` and whose component at every other place is
the identity matrix. -/
public def localMatrix (m : Matrix (Fin 2) (Fin 2) v.completion) :
    Matrix (Fin 2) (Fin 2) (AdeleRing K) := fun i j =>
  ⟨Function.update (fun w : Place K => (1 : Matrix (Fin 2) (Fin 2) w.completion) i j) v (m i j),
    (Set.finite_singleton v).subset fun w hw => by
      by_contra h
      apply hw
      change Function.update (fun w : Place K => (1 : Matrix (Fin 2) (Fin 2) w.completion) i j)
        v (m i j) w ∈ (w.integers : Set w.completion)
      rw [Function.update_of_ne (by simpa using h), Matrix.one_apply]
      split_ifs
      · exact w.integers.one_mem
      · exact w.integers.zero_mem⟩

variable {v}

open scoped Classical in
/-- The component of `localMatrix v m` at `v` is `m`. -/
public theorem localMatrix_apply_self (m : Matrix (Fin 2) (Fin 2) v.completion) (i j : Fin 2) :
    (localMatrix v m i j) v = m i j :=
  Function.update_self (β := fun w : Place K => w.completion) v (m i j)
    (fun w : Place K => (1 : Matrix (Fin 2) (Fin 2) w.completion) i j)

open scoped Classical in
/-- The component of `localMatrix v m` at a place `w ≠ v` is the identity matrix. -/
public theorem localMatrix_apply_ne {w : Place K} (hw : w ≠ v)
    (m : Matrix (Fin 2) (Fin 2) v.completion) (i j : Fin 2) :
    (localMatrix v m i j) w = (1 : Matrix (Fin 2) (Fin 2) w.completion) i j :=
  Function.update_of_ne (β := fun w : Place K => w.completion) hw (m i j)
    (fun w : Place K => (1 : Matrix (Fin 2) (Fin 2) w.completion) i j)

/-- Evaluating `localMatrix v m` at `v` gives `m`. -/
public theorem mapMatrix_evalAt_localMatrix_self (m : Matrix (Fin 2) (Fin 2) v.completion) :
    (evalAt K v).mapMatrix (localMatrix v m) = m := by
  ext i j
  exact localMatrix_apply_self m i j

/-- Evaluating `localMatrix v m` at a place `w ≠ v` gives the identity matrix. -/
public theorem mapMatrix_evalAt_localMatrix_ne {w : Place K} (hw : w ≠ v)
    (m : Matrix (Fin 2) (Fin 2) v.completion) :
    (evalAt K w).mapMatrix (localMatrix v m) = 1 := by
  ext i j
  exact localMatrix_apply_ne hw m i j

variable (v) in
/-- `localMatrix v` as a monoid homomorphism `M₂(K_v) → M₂(A)`. -/
public def localMatrixHom :
    Matrix (Fin 2) (Fin 2) v.completion →* Matrix (Fin 2) (Fin 2) (AdeleRing K) where
  toFun := localMatrix v
  map_one' := matrix_ext_evalAt fun w => by
    by_cases hw : w = v
    · subst hw
      rw [mapMatrix_evalAt_localMatrix_self, map_one]
    · rw [mapMatrix_evalAt_localMatrix_ne hw, map_one]
  map_mul' m m' := matrix_ext_evalAt fun w => by
    by_cases hw : w = v
    · subst hw
      rw [map_mul, mapMatrix_evalAt_localMatrix_self, mapMatrix_evalAt_localMatrix_self,
        mapMatrix_evalAt_localMatrix_self]
    · rw [map_mul, mapMatrix_evalAt_localMatrix_ne hw, mapMatrix_evalAt_localMatrix_ne hw,
        mapMatrix_evalAt_localMatrix_ne hw, one_mul]

variable (v) in
/-- The embedding `GL₂(K_v) → GL₂(A)`, `m ↦` (`m` at `v`, the identity elsewhere). -/
public def localGL : GL (Fin 2) v.completion →* GL (Fin 2) (AdeleRing K) :=
  Units.map (localMatrixHom v)

/-- `localGL v m` has component `m` at `v` and the identity at every other place. -/
public theorem isLocalMatrixAt_localGL (m : GL (Fin 2) v.completion) :
    IsLocalMatrixAt v (m : Matrix (Fin 2) (Fin 2) v.completion) (localGL v m) :=
  ⟨fun i j => localMatrix_apply_self _ i j, fun _ hw i j => localMatrix_apply_ne hw _ i j⟩

end KFree

variable (k : Type u) [Field k] [Finite k] {K : Type u} [Field K] [Algebra k K]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]

include k

/-- The residue field `κ_v = O_v/(π_v)` of the completion at a place of a function field is
finite. -/
public theorem finite_residueField_integers (v : Place K) :
    Finite (IsLocalRing.ResidueField v.integers) := by
  have := finite_residueField k v
  refine Nat.finite_of_card_ne_zero ?_
  change v.residueCard ≠ 0
  rw [Place.residueCard_eq_resCard]
  exact Nat.card_pos.ne'

/-- A system of representatives of `κ_v = O_v/(π)` indexed by `Fin q_v`, at a place of a
function field and for a uniformizer `π`. -/
public theorem exists_isResidueSystem (v : Place K) {π : v.integers}
    (hπ : Place.IsUniformizer v π) :
    ∃ lam : Fin v.residueCard → v.integers, Place.IsResidueSystem v π lam := by
  have := finite_residueField_integers k v
  have hmem : ∀ a b : v.integers,
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal v.integers) a =
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal v.integers) b ↔ a - b ∈ Ideal.span {π} := by
    intro a b
    rw [hπ]
    exact Ideal.Quotient.eq
  let e : Fin v.residueCard ≃ (v.integers ⧸ IsLocalRing.maximalIdeal v.integers) :=
    (Finite.equivFin (IsLocalRing.ResidueField v.integers)).symm
  choose lam hlam using fun i => Ideal.Quotient.mk_surjective (e i)
  refine ⟨lam, fun a => ⟨e.symm (Ideal.Quotient.mk _ a), (hmem _ _).1 ?_, fun j hj => ?_⟩⟩
  · rw [hlam, Equiv.apply_symm_apply]
  · rw [Equiv.eq_symm_apply, ← hlam j]
    exact ((hmem _ _).2 hj).symm

/-- **The data of `T_v` exist at every place of a function field**: a uniformizer `π`, a system
`lam` of representatives of `κ_v`, and adelic matrices `g₀`, `g i` which are `diag (π⁻¹, 1)` and
`(1, 0; -π⁻¹ λ_i, π⁻¹)` at `v` and the identity elsewhere. -/
public theorem exists_isHeckeDataAt (v : Place K) :
    ∃ (π : v.integers) (lam : Fin v.residueCard → v.integers) (g₀ : GL (Fin 2) (AdeleRing K))
      (g : Fin v.residueCard → GL (Fin 2) (AdeleRing K)), IsHeckeDataAt v π lam g₀ g := by
  have hπ := Place.isUniformizer_unif (isDiscrete k v)
  set π : v.integers := ⟨v.coeRingHom v.unif, Place.coeRingHom_unif_mem_integers (isDiscrete k v)⟩
  have hπ0 : (π : v.completion) ≠ 0 := coe_ne_zero_of_isUniformizer k hπ
  obtain ⟨lam, hlam⟩ := exists_isResidueSystem k v hπ
  have hdet₀ : (Matrix.diagonal ![(π : v.completion)⁻¹, 1]).det ≠ 0 := by
    simp [Matrix.det_diagonal, Fin.prod_univ_two, hπ0]
  have hdet : ∀ i, (!![1, 0; -((π : v.completion)⁻¹ * (lam i : v.completion)),
      (π : v.completion)⁻¹]).det ≠ 0 := fun i => by
    simp [Matrix.det_fin_two_of, hπ0]
  exact ⟨π, lam, localGL v (GeneralLinearGroup.mkOfDetNeZero _ hdet₀),
    fun i => localGL v (GeneralLinearGroup.mkOfDetNeZero _ (hdet i)),
    ⟨hπ, hlam, isLocalMatrixAt_localGL _, fun i => isLocalMatrixAt_localGL _⟩⟩

end Stacks.Adeles.GlobalFunctionField

end
