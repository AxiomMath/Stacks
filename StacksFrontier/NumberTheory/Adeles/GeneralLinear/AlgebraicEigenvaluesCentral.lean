module

public import StacksFrontier.NumberTheory.Adeles.GeneralLinear.AlgebraicEigenvaluesTwist

/-!
# The Hecke operator `T_{v,n}` and the central character

Let `K` be a function field over a finite field `k`. On a left `GL_n(O)`-invariant function `F`
on `GL_n(A)`, the Hecke operator `T_{v,n}` is translation by the central element `ϖ_v⁻¹`:
`T_{v,n} F (x) = F (ϖ_v⁻¹ x)`. Indeed, for `L = x⁻¹ (O_w^n)_w` the unique lattice `L'` with
`m_v L_v ⊆ L'_v ⊆ L_v` of index `q_v ^ n` is `m_v L_v = ϖ_v L_v`, which is
`(ϖ_v x⁻¹) (O_w^n)_w`.

## Main results

* `Stacks.Adeles.GeneralLinear.heckeOperatorGL_top` — `T_{v,n} F (x) = F (ϖ_v⁻¹ x)`.
-/

@[expose] public noncomputable section

open Matrix

universe u w

namespace Stacks.Adeles.GeneralLinear

open Stacks.Adeles.GlobalFunctionField Stacks.Drinfeld.Lattice

section Scalar

variable {K : Type u} [Field K] {n : ℕ}

/-- The component at `w` of the scalar matrix of an idele `z` is the scalar matrix of `z_w`. -/
public theorem glAt_scalarGL_val (z : (AdeleRing K)ˣ) (w : Place K) :
    (glAt K n w (scalarGL n z)).val = Matrix.scalar (Fin n) ((z : AdeleRing K) w) := by
  change (evalAt K w).mapMatrix
    (algebraMap (AdeleRing K) (Matrix (Fin n) (Fin n) (AdeleRing K)) (z : AdeleRing K)) = _
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.algebraMap_matrix_apply,
    Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs
  · rfl
  · exact map_zero _

/-- The scalar matrix of an idele whose component at `w` is `1` has component `1` at `w`. -/
public theorem glAt_scalarGL_eq_one {z : (AdeleRing K)ˣ} {w : Place K}
    (hz : (z : AdeleRing K) w = 1) : glAt K n w (scalarGL n z) = 1 := by
  ext1
  rw [glAt_scalarGL_val, hz, Units.val_one, map_one]

/-- Membership in the translate `g Λ` when `g⁻¹` is the scalar matrix of `b`:
`x ∈ g Λ ↔ b x ∈ Λ`. -/
private theorem mem_translate_of_inv_val {v : Place K} {g : GL (Fin n) v.completion}
    {b : v.completion} (hg : (g⁻¹ : GL (Fin n) v.completion).val = Matrix.scalar (Fin n) b)
    {Λ : Submodule v.integers (Fin n → v.completion)} {x : Fin n → v.completion} :
    x ∈ translate g Λ ↔ (fun i => b * x i) ∈ Λ := by
  rw [mem_translate, hg, Matrix.scalar_apply]
  have : Matrix.diagonal (fun _ : Fin n => b) *ᵥ x = fun i => b * x i := by
    funext i
    rw [Matrix.mulVec_diagonal]
  rw [this]

end Scalar

variable (k : Type u) [Field k] [Finite k] {K : Type u} [Field K] [Algebra k K]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K] {n : ℕ}

/-- The component of `ϖ_v⁻¹` (the idele `unifInvIdele k v`) at a place `w ≠ v` is `1`. -/
public theorem unifInvIdele_apply_ne {v w : Place K} (h : w ≠ v) :
    ((unifInvIdele k v : (AdeleRing K)ˣ) : AdeleRing K) w = 1 := by
  rw [unifInvIdele, localIdele_apply_ne h]

/-- The component of the inverse of `ϖ_v⁻¹` at a place `w ≠ v` is `1`. -/
public theorem unifInvIdele_inv_apply_ne {v w : Place K} (h : w ≠ v) :
    (((unifInvIdele k v)⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) w = 1 := by
  have := idele_mul_inv_apply (unifInvIdele k v) w
  rwa [unifInvIdele_apply_ne k h, one_mul] at this

/-- The component of `ϖ_v⁻¹` at `v` is the inverse of the image of the uniformizer. -/
public theorem unifInvIdele_apply_self (v : Place K) :
    ((unifInvIdele k v : (AdeleRing K)ˣ) : AdeleRing K) v = (v.coeRingHom v.unif)⁻¹ := by
  rw [unifInvIdele, localIdele_apply_self]

/-- The component of the inverse of `ϖ_v⁻¹` at `v` is the image of the uniformizer. -/
public theorem unifInvIdele_inv_apply_self (v : Place K) :
    (((unifInvIdele k v)⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) v = v.coeRingHom v.unif := by
  have h0 : v.coeRingHom v.unif ≠ 0 :=
    (_root_.map_ne_zero _).2 (Place.unif_ne_zero (isDiscrete k v))
  have := idele_mul_inv_apply (unifInvIdele k v) v
  rw [unifInvIdele_apply_self k] at this
  rw [← mul_right_inj' (inv_ne_zero h0), this, inv_mul_cancel₀ h0]

include k in
/-- The order of the image of the uniformizer is `1`. -/
private theorem ordC_coeRingHom_unif (v : Place K) : v.ordC (v.coeRingHom v.unif) = 1 := by
  rw [Place.ordC_coeRingHom (isDiscrete k v) (Place.unif_ne_zero (isDiscrete k v)),
    Place.ord_unif (isDiscrete k v)]

/-- `ϖ_v O_v^n` has index `q_v ^ n` in `O_v^n`. -/
private theorem relIndex_translate_unif_stdLattice (v : Place K) :
    (translate (glAt K n v (scalarGL n (unifInvIdele k v)⁻¹))
      (stdLattice v n)).toAddSubgroup.relIndex (stdLattice v n).toAddSubgroup =
      v.residueCard ^ n := by
  set g := glAt K n v (scalarGL n (unifInvIdele k v)⁻¹)
  have hval : g.val = Matrix.scalar (Fin n) (v.coeRingHom v.unif) := by
    rw [glAt_scalarGL_val, unifInvIdele_inv_apply_self]
  have hint : ∀ i j, g.val i j ∈ v.integers := by
    intro i j
    rw [hval, Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs
    · exact Place.coeRingHom_unif_mem_integers (isDiscrete k v)
    · exact v.integers.zero_mem
  obtain ⟨-, h⟩ := relIndex_translate_stdLattice (isDiscrete k v) g hint
  rw [h, hval, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  congr 1
  have h0 : v.coeRingHom v.unif ≠ 0 :=
    (_root_.map_ne_zero _).2 (Place.unif_ne_zero (isDiscrete k v))
  have := ordC_prod (isDiscrete k v) (Finset.univ : Finset (Fin n))
    (fun _ => v.coeRingHom v.unif) (fun _ _ => h0)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
  rw [this]
  simp [ordC_coeRingHom_unif k]

/-- `ϖ_v⁻¹`, as a scalar matrix, maps a lattice `Λ ⊆ K_v^n` onto `m_v Λ`. -/
private theorem translate_unif_eq_smul (v : Place K)
    (Λ : Submodule v.integers (Fin n → v.completion)) :
    translate (glAt K n v (scalarGL n (unifInvIdele k v)⁻¹)) Λ =
      IsLocalRing.maximalIdeal v.integers • Λ := by
  set π : v.integers := ⟨v.coeRingHom v.unif, Place.coeRingHom_unif_mem_integers (isDiscrete k v)⟩
  have h0 : (π : v.completion) ≠ 0 :=
    (_root_.map_ne_zero _).2 (Place.unif_ne_zero (isDiscrete k v))
  rw [← Place.isUniformizer_unif (isDiscrete k v), Submodule.ideal_span_singleton_smul]
  have hinv : ((glAt K n v (scalarGL n (unifInvIdele k v)⁻¹))⁻¹ : GL (Fin n) v.completion).val =
      Matrix.scalar (Fin n) (π : v.completion)⁻¹ := by
    rw [← map_inv, ← map_inv, inv_inv, glAt_scalarGL_val, unifInvIdele_apply_self]
  ext x
  rw [mem_translate_of_inv_val hinv, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · intro hx
    refine ⟨_, hx, funext fun i => ?_⟩
    change (π : v.completion) * ((π : v.completion)⁻¹ * x i) = x i
    rw [mul_inv_cancel_left₀ h0]
  · rintro ⟨y, hy, rfl⟩
    convert hy using 1
    funext i
    change (π : v.completion)⁻¹ * ((π : v.completion) * y i) = y i
    rw [inv_mul_cancel_left₀ h0]

/-- **`T_{v,n}` is translation by `ϖ_v⁻¹`**: for a left `GL_n(O)`-invariant function `F`,
`T_{v,n} F (x) = F (ϖ_v⁻¹ x)`, with `ϖ_v⁻¹` the scalar matrix of `unifInvIdele k v`. -/
public theorem heckeOperatorGL_top {Λ : Type w} [AddCommMonoid Λ]
    (F : GL (Fin n) (AdeleRing K) → Λ) (hF : ∀ κ x, F (mapO K n κ * x) = F x) (v : Place K)
    (x : GL (Fin n) (AdeleRing K)) :
    heckeOperatorGL v n F x = F (scalarGL n (unifInvIdele k v) * x) := by
  classical
  set s := scalarGL n (unifInvIdele k v)
  set L := x⁻¹ • AdelicLattice.standard K n
  set L₀ := scalarGL n (unifInvIdele k v)⁻¹ • L
  have hout : ∀ w, w ≠ v → L₀.lattice w = L.lattice w := by
    intro w hw
    rw [AdelicLattice.smul_lattice, glAt_scalarGL_eq_one (unifInvIdele_inv_apply_ne k hw),
      translate_one]
  have hv : L₀.lattice v = IsLocalRing.maximalIdeal v.integers • L.lattice v := by
    rw [AdelicLattice.smul_lattice]
    exact translate_unif_eq_smul k v _
  have hidx : (L₀.lattice v).toAddSubgroup.relIndex (L.lattice v).toAddSubgroup =
      v.residueCard ^ n := by
    have hc : glAt K n v (scalarGL n (unifInvIdele k v)⁻¹) * glAt K n v x⁻¹ =
        glAt K n v x⁻¹ * glAt K n v (scalarGL n (unifInvIdele k v)⁻¹) := by
      rw [← map_mul, ← map_mul, scalarGL_mul_comm]
    rw [AdelicLattice.smul_lattice, AdelicLattice.smul_lattice,
      AdelicLattice.standard_lattice, ← translate_mul, hc, translate_mul, relIndex_translate]
    exact relIndex_translate_unif_stdLattice k v
  have hnb : IsHeckeNeighbourGL v n L L₀ :=
    ⟨hout, hv.ge, hv ▸ Submodule.smul_le_right, hidx⟩
  have huniq : ∀ L' : AdelicLattice K n, IsHeckeNeighbourGL v n L L' → L' = L₀ := by
    rintro L' ⟨h₁, h₂, h₃, h₄⟩
    have hq : 0 < v.residueCard ^ n := pow_pos (by
      rw [Place.residueCard_eq_resCard]; exact resCard_pos k v) n
    refine AdelicLattice.ext (funext fun w => ?_)
    by_cases hw : w = v
    · subst hw
      rw [hv] at hidx ⊢
      have hmul := AddSubgroup.relIndex_mul_relIndex _ _ _
        ((Submodule.toAddSubgroup_le _ _).2 h₂) ((Submodule.toAddSubgroup_le _ _).2 h₃)
      rw [hidx, h₄] at hmul
      have h1 := Nat.eq_of_mul_eq_mul_right hq (hmul.trans (one_mul _).symm)
      exact le_antisymm ((Submodule.toAddSubgroup_le _ _).1 (AddSubgroup.relIndex_eq_one.1 h1)) h₂
    · rw [h₁ w hw, hout w hw]
  rw [heckeOperatorGL, finsum_eq_single _ ⟨L₀, hnb⟩ fun L' hL' =>
    absurd (Subtype.ext (huniq L'.1 L'.2)) hL']
  have hrep := latticeRep_smul_standard k L₀
  have hstab : x * s * latticeRep L₀ ∈
      MulAction.stabilizer (GL (Fin n) (AdeleRing K)) (AdelicLattice.standard K n) := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, hrep, mul_smul, ← mul_smul s, ← map_mul,
      mul_inv_cancel, map_one, one_smul, smul_inv_smul]
  rw [AdelicLattice.stabilizer_standard, MonoidHom.mem_range] at hstab
  obtain ⟨κ, hκ⟩ := hstab
  have hR : latticeRep L₀ = (x * s)⁻¹ * mapO K n κ := by
    rw [hκ]
    group
  have heq : (latticeRep L₀)⁻¹ = mapO K n κ⁻¹ * (s * x) := by
    rw [show s * x = x * s from scalarGL_mul_comm _ _, hR, map_inv]
    group
  rw [heq, hF]

end Stacks.Adeles.GeneralLinear

end
