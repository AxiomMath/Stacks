module

public import Mathlib.LinearAlgebra.Projectivization.Basic
public import StacksFrontier.NumberTheory.Drinfeld.Lattice.Local

/-!
# The index-`q_v` sublattices of a lattice in `K_v^2`

Let `v` be a place of a function field `K` over a finite field, with completion `K_v`, ring of
integers `O_v`, uniformizer `π` and residue field `κ_v` of cardinality `q_v`. For an
`O_v`-lattice `Λ ⊆ K_v^2`, the lattices `Λ'` with `π Λ ⊆ Λ' ⊆ Λ` of index `q_v` in `Λ` are
the *Hecke sublattices* of `Λ`. We show:

* for the standard lattice `O_v^2`, they are exactly the lattices `M_j O_v^2`, where `M_j` runs
  through the `q_v + 1` matrices `diag (π, 1)` and `(1, 0; λ_i, π)` (`λ_i` a system of
  representatives of `κ_v`), with `M_j` pairwise giving different lattices. These `M_j` are the
  inverses of the local matrices of the base's explicit formula for the Hecke operator `T_v`
  (`Stacks.Adeles.GlobalFunctionField.heckeLocalInv`);
* the reduction `Λ' ↦ Λ' / π O_v^2 ⊆ κ_v^2` maps them bijectively onto the lines of `κ_v^2`;
* for an arbitrary lattice `Λ = h O_v^2` they are the lattices `h M_j O_v^2`, there are exactly
  `q_v + 1` of them, and they are in bijection with the lines of `Λ / π Λ ≅ κ_v^2`.

## Main definitions

* `Stacks.Drinfeld.Lattice.IsHeckeSublattice` — `m_v Λ ⊆ Λ' ⊆ Λ` with `[Λ : Λ'] = q_v`.
* `Stacks.Drinfeld.Lattice.heckeLocalGL` — the matrices `M_j` as elements of `GL₂(K_v)`.
* `Stacks.Drinfeld.Lattice.reduction` — the image of `Λ' ∩ O_v^2` in `κ_v^2`.
* `Stacks.Drinfeld.Lattice.heckeLine` — the lines `κ_v (0, 1)` and `κ_v (1, λ̄_i)` of `κ_v^2`.

## Main results

* `Stacks.Drinfeld.Lattice.isHeckeSublattice_stdLattice_iff` — the Hecke sublattices of `O_v^2`
  are the `M_j O_v^2`.
* `Stacks.Drinfeld.Lattice.reduction_heckeSublattice` and
  `Stacks.Drinfeld.Lattice.heckeLine_bijective` — `M_j O_v^2 / π O_v^2` is the line
  `heckeLine j`, and every line arises exactly once.
* `Stacks.Drinfeld.Lattice.bijective_heckeSublattice_translate` — for `Λ = h O_v^2`,
  `j ↦ h M_j O_v^2` is a bijection onto the Hecke sublattices of `Λ`.
* `Stacks.Drinfeld.Lattice.heckeSublatticeEquivLine` — the bijection between the Hecke
  sublattices of `Λ = h O_v^2` and the lines of `κ_v^2`, given by reduction modulo `π` in the
  coordinates `h`.
* `Stacks.Drinfeld.Lattice.card_heckeSublattice` — every lattice in `K_v^2` has exactly
  `q_v + 1` Hecke sublattices.
-/

@[expose] public noncomputable section

open Matrix

universe u

namespace Stacks.Drinfeld.Lattice

open Stacks.Adeles Stacks.Adeles.GlobalFunctionField

section General

variable {K : Type u} [Field K] {v : Place K} {n : ℕ}

/-- `Λ'` is a Hecke sublattice of `Λ`: `m_v Λ ⊆ Λ' ⊆ Λ` (`m_v = π O_v` the maximal ideal) and
`Λ'` has index `q_v = #κ_v` in `Λ`. -/
public def IsHeckeSublattice (Λ Λ' : Submodule v.integers (Fin n → v.completion)) : Prop :=
  IsLocalRing.maximalIdeal v.integers • Λ ≤ Λ' ∧ Λ' ≤ Λ ∧
    Λ'.toAddSubgroup.relIndex Λ.toAddSubgroup = v.residueCard

/-- Translating by `h ∈ GL_n(K_v)` preserves Hecke sublattices. -/
public theorem isHeckeSublattice_translate_iff (h : GL (Fin n) v.completion)
    {Λ Λ' : Submodule v.integers (Fin n → v.completion)} :
    IsHeckeSublattice (translate h Λ) (translate h Λ') ↔ IsHeckeSublattice Λ Λ' := by
  have hsmul : IsLocalRing.maximalIdeal v.integers • translate h Λ =
      translate h (IsLocalRing.maximalIdeal v.integers • Λ) := (Submodule.map_smul'' _ _ _).symm
  have hinj : Function.Injective
      ((Matrix.toLin' h.val).restrictScalars v.integers).toAddMonoidHom := by
    intro x y hxy
    simpa [Matrix.toLin'_apply, mulVec_inv_mulVec] using
      congrArg (fun z => (h⁻¹ : GL (Fin n) v.completion).val *ᵥ z) hxy
  have hidx : (translate h Λ').toAddSubgroup.relIndex (translate h Λ).toAddSubgroup =
      Λ'.toAddSubgroup.relIndex Λ.toAddSubgroup := by
    rw [translate, translate, Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ hinj
  rw [IsHeckeSublattice, IsHeckeSublattice, hsmul, translate_le_translate_iff,
    translate_le_translate_iff, hidx]

/-- If `A ⊆ B ⊆ C` and `A`, `B` have the same nonzero index in `C`, then `A = B`. -/
public theorem eq_of_le_of_relIndex_eq {A B C : Submodule v.integers (Fin n → v.completion)}
    (hAB : A ≤ B) (hBC : B ≤ C)
    (h : A.toAddSubgroup.relIndex C.toAddSubgroup = B.toAddSubgroup.relIndex C.toAddSubgroup)
    (h0 : B.toAddSubgroup.relIndex C.toAddSubgroup ≠ 0) : A = B := by
  have hmul := AddSubgroup.relIndex_mul_relIndex A.toAddSubgroup B.toAddSubgroup C.toAddSubgroup
    ((Submodule.toAddSubgroup_le _ _).2 hAB) ((Submodule.toAddSubgroup_le _ _).2 hBC)
  rw [h] at hmul
  have h1 : A.toAddSubgroup.relIndex B.toAddSubgroup = 1 :=
    Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero h0) (hmul.trans (one_mul _).symm)
  exact le_antisymm hAB ((Submodule.toAddSubgroup_le _ _).1 (AddSubgroup.relIndex_eq_one.1 h1))

/-- An index computed by a surjection onto the residue field. -/
public theorem relIndex_eq_residueCard_of {A B : AddSubgroup (Fin n → v.completion)}
    (ψ : B →+ IsLocalRing.ResidueField v.integers) (hψ : Function.Surjective ψ)
    (hker : ∀ x : B, ψ x = 0 ↔ (x : Fin n → v.completion) ∈ A) :
    A.relIndex B = v.residueCard := by
  have hk : A.addSubgroupOf B = ψ.ker := by
    ext x
    rw [AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_ker, hker]
  rw [AddSubgroup.relIndex, hk, AddSubgroup.index]
  exact Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective ψ hψ).toEquiv

/-- The map `O_v^n → K_v^n` is injective. -/
public theorem injective_stdLattice_map : Function.Injective
    ((Algebra.linearMap v.integers v.completion).compLeft (Fin n)) := fun _ _ h =>
  funext fun i => Subtype.ext (congrFun h i)

/-- Reduction modulo `m_v`, `O_v^n → κ_v^n`. -/
public def reduce : stdLattice v n →ₗ[v.integers] (Fin n → IsLocalRing.ResidueField v.integers) :=
  ((Algebra.linearMap v.integers (IsLocalRing.ResidueField v.integers)).compLeft (Fin n)).comp
    (LinearEquiv.ofInjective _ injective_stdLattice_map).symm.toLinearMap

/-- The `i`-th coordinate of `reduce x` is the residue of `x i`. -/
public theorem reduce_apply (x : stdLattice v n) (i : Fin n) :
    reduce x i = IsLocalRing.residue v.integers ⟨x.1 i, mem_stdLattice.1 x.2 i⟩ := by
  let e := LinearEquiv.ofInjective _ (injective_stdLattice_map (v := v) (n := n))
  have h : (x : Fin n → v.completion) =
      (Algebra.linearMap v.integers v.completion).compLeft (Fin n) (e.symm x) :=
    (congrArg Subtype.val (e.apply_symm_apply x)).symm.trans
      (LinearEquiv.ofInjective_apply _ (e.symm x))
  show algebraMap v.integers (IsLocalRing.ResidueField v.integers) (e.symm x i) = _
  rw [IsLocalRing.ResidueField.algebraMap_eq]
  congr 1
  exact Subtype.ext (congrFun h i).symm

/-- If `x i = a`, then the `i`-th coordinate of `reduce x` is the residue of `a`. -/
public theorem reduce_apply_of_eq (x : stdLattice v n) (i : Fin n) {a : v.integers}
    (h : x.1 i = a) : reduce x i = IsLocalRing.residue v.integers a := by
  rw [reduce_apply]
  congr 1
  exact Subtype.ext h

/-- `(a, b) ∈ O_v^2` when `a, b ∈ O_v`. -/
public theorem vec2_mem_stdLattice {a b : v.completion} (ha : a ∈ v.integers)
    (hb : b ∈ v.integers) : ![a, b] ∈ stdLattice v 2 :=
  mem_stdLattice.2 (Fin.forall_fin_two.2 ⟨by simpa using ha, by simpa using hb⟩)

/-- Translation by `h` as a bijection between the Hecke sublattices of `Λ` and of `h Λ`. -/
public def heckeTranslateEquiv (h : GL (Fin n) v.completion)
    (Λ : Submodule v.integers (Fin n → v.completion)) :
    {Λ' // IsHeckeSublattice Λ Λ'} ≃ {Λ' // IsHeckeSublattice (translate h Λ) Λ'} where
  toFun Λ' := ⟨translate h Λ'.1, (isHeckeSublattice_translate_iff h).2 Λ'.2⟩
  invFun Λ'' := ⟨translate h⁻¹ Λ''.1, (isHeckeSublattice_translate_iff h).1 (by
    rw [← translate_mul, mul_inv_cancel, translate_one]
    exact Λ''.2)⟩
  left_inv Λ' := Subtype.ext (translate_inv_translate h Λ'.1)
  right_inv Λ'' := Subtype.ext (by
    change translate h (translate h⁻¹ Λ''.1) = Λ''.1
    rw [← translate_mul, mul_inv_cancel, translate_one])

/-- The reduction `(Λ' ∩ O_v^n) / m_v O_v^n ⊆ κ_v^n` of an `O_v`-submodule `Λ'` of `K_v^n`. -/
public def reduction (Λ' : Submodule v.integers (Fin n → v.completion)) :
    Submodule v.integers (Fin n → IsLocalRing.ResidueField v.integers) :=
  (Λ'.comap (stdLattice v n).subtype).map reduce

/-- `y` lies in the reduction of `Λ'` exactly when it is the reduction of some
`x ∈ Λ' ∩ O_v^n`. -/
public theorem mem_reduction {Λ' : Submodule v.integers (Fin n → v.completion)}
    {y : Fin n → IsLocalRing.ResidueField v.integers} :
    y ∈ reduction Λ' ↔ ∃ x : stdLattice v n, (x : Fin n → v.completion) ∈ Λ' ∧ reduce x = y := by
  simp [reduction]

end General

section Local

variable {K : Type u} [Field K] {v : Place K}

/-- `z ∈ (π)` exactly when `π⁻¹ z ∈ O_v`. -/
public theorem mem_span_iff_inv_mul_mem {π : v.integers} (hπ0 : (π : v.completion) ≠ 0)
    (z : v.integers) : z ∈ Ideal.span {π} ↔ (π : v.completion)⁻¹ * z ∈ v.integers := by
  constructor
  · intro hz
    rw [mul_comm]
    exact div_mem_integers_of_mem_span hz hπ0
  · intro hz
    refine Ideal.mem_span_singleton'.2 ⟨⟨_, hz⟩, Subtype.ext ?_⟩
    show (π : v.completion)⁻¹ * z * π = z
    rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ hπ0, one_mul]

/-- `z ≡ 0` in `κ_v` exactly when `π⁻¹ z ∈ O_v`. -/
public theorem residue_eq_zero_iff_inv_mul_mem {π : v.integers} (hπ : Place.IsUniformizer v π)
    (hπ0 : (π : v.completion) ≠ 0) (z : v.integers) :
    IsLocalRing.residue v.integers z = 0 ↔ (π : v.completion)⁻¹ * z ∈ v.integers := by
  rw [IsLocalRing.residue_eq_zero_iff, ← hπ, mem_span_iff_inv_mul_mem hπ0]

variable {π : v.completion} (hπ0 : π ≠ 0) {q : ℕ} (lam : Fin q → v.completion)

/-- The matrices `M_j = diag (π, 1)` and `(1, 0; λ_i, π)` as elements of `GL₂(K_v)`; they are
the inverses of the local matrices `diag (π⁻¹, 1)` and `(1, 0; -π⁻¹ λ_i, π⁻¹)` of the formula
for the Hecke operator `T_v`. -/
public def heckeLocalGL (j : Option (Fin q)) : GL (Fin 2) v.completion :=
  ⟨heckeLocalInv v π lam j, heckeLocal v π lam j,
    _root_.mul_eq_one_comm.1 (heckeLocal_mul_inv hπ0 lam j), heckeLocal_mul_inv hπ0 lam j⟩

/-- The matrix underlying `heckeLocalGL j` is `M_j`. -/
public theorem heckeLocalGL_val (j : Option (Fin q)) :
    (heckeLocalGL hπ0 lam j).val = heckeLocalInv v π lam j := rfl

/-- The matrix underlying `(heckeLocalGL j)⁻¹` is `M_j⁻¹`. -/
public theorem heckeLocalGL_inv_val (j : Option (Fin q)) :
    (heckeLocalGL hπ0 lam j)⁻¹.val = heckeLocal v π lam j := rfl

/-- The lattice `M_j O_v^2`. -/
public def heckeSublattice (j : Option (Fin q)) : Submodule v.integers (Fin 2 → v.completion) :=
  translate (heckeLocalGL hπ0 lam j) (stdLattice v 2)

/-- `x ∈ diag (π, 1) O_v^2` exactly when `π⁻¹ x₀ ∈ O_v` and `x₁ ∈ O_v`. -/
public theorem mem_heckeSublattice_none {x : Fin 2 → v.completion} :
    x ∈ heckeSublattice hπ0 lam none ↔ π⁻¹ * x 0 ∈ v.integers ∧ x 1 ∈ v.integers := by
  rw [heckeSublattice, mem_translate, heckeLocalGL_inv_val, mem_stdLattice, Fin.forall_fin_two]
  simp [heckeLocal, mulVec, dotProduct, Fin.sum_univ_two]

/-- `x ∈ (1, 0; λ_i, π) O_v^2` exactly when `x₀ ∈ O_v` and `π⁻¹ (x₁ - λ_i x₀) ∈ O_v`. -/
public theorem mem_heckeSublattice_some {i : Fin q} {x : Fin 2 → v.completion} :
    x ∈ heckeSublattice hπ0 lam (some i) ↔
      x 0 ∈ v.integers ∧ π⁻¹ * (x 1 - lam i * x 0) ∈ v.integers := by
  rw [heckeSublattice, mem_translate, heckeLocalGL_inv_val, mem_stdLattice, Fin.forall_fin_two]
  simp only [heckeLocal, mulVec, dotProduct, Fin.sum_univ_two, of_apply, cons_val', cons_val_zero,
    cons_val_one, empty_val', cons_val_fin_one, one_mul, zero_mul, add_zero]
  rw [show -(π⁻¹ * lam i) * x 0 + π⁻¹ * x 1 = π⁻¹ * (x 1 - lam i * x 0) by ring]

end Local

section FunctionField

variable (k : Type u) [Field k] [Finite k] {K : Type u} [Field K] [Algebra k K]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]

variable {v : Place K} {π : v.integers} {q : ℕ} {lam : Fin q → v.integers}

include k in
/-- `M_j O_v^2` is a Hecke sublattice of `O_v^2`. -/
public theorem isHeckeSublattice_heckeSublattice (hπ : Place.IsUniformizer v π)
    (hlam : Place.IsResidueSystem v π lam) (j : Option (Fin q)) :
    IsHeckeSublattice (stdLattice v 2)
      (heckeSublattice (coe_ne_zero_of_isUniformizer k hπ)
        (fun i => (lam i : v.completion)) j) := by
  have hπ0 := coe_ne_zero_of_isUniformizer k hπ
  set Λj := heckeSublattice hπ0 (fun i => (lam i : v.completion)) j
  have hle : Λj ≤ stdLattice v 2 := by
    intro x hx
    refine mem_stdLattice.2 (Fin.forall_fin_two.2 ?_)
    cases j with
    | none =>
      obtain ⟨h0, h1⟩ := (mem_heckeSublattice_none hπ0 _).1 hx
      refine ⟨?_, h1⟩
      rw [show x 0 = (π : v.completion) * ((π : v.completion)⁻¹ * x 0) by field_simp]
      exact mul_mem π.2 h0
    | some i =>
      obtain ⟨h0, h1⟩ := (mem_heckeSublattice_some hπ0 _).1 hx
      refine ⟨h0, ?_⟩
      have : x 1 = (π : v.completion) * ((π : v.completion)⁻¹ * (x 1 - lam i * x 0)) +
          lam i * x 0 := by field_simp; ring
      rw [this]
      exact add_mem (mul_mem π.2 h1) (mul_mem (lam i).2 h0)
  have hsmul : IsLocalRing.maximalIdeal v.integers • stdLattice v 2 ≤ Λj := by
    refine Submodule.smul_le.2 fun r hr x hx => ?_
    rw [← hπ] at hr
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    have hx' := mem_stdLattice.1 hx
    have hsm : ∀ i, ((c * π) • x) i = (c : v.completion) * π * x i := fun i => rfl
    cases j with
    | none =>
      refine (mem_heckeSublattice_none hπ0 _).2 ⟨?_, ?_⟩
      · rw [hsm, show (π : v.completion)⁻¹ * (c * π * x 0) = c * x 0 by field_simp]
        exact mul_mem c.2 (hx' 0)
      · rw [hsm]
        exact mul_mem (mul_mem c.2 π.2) (hx' 1)
    | some i =>
      refine (mem_heckeSublattice_some hπ0 _).2 ⟨?_, ?_⟩
      · rw [hsm]
        exact mul_mem (mul_mem c.2 π.2) (hx' 0)
      · rw [hsm, hsm, show (π : v.completion)⁻¹ * (c * π * x 1 - lam i * (c * π * x 0)) =
          c * (x 1 - lam i * x 0) by field_simp]
        exact mul_mem c.2 (sub_mem (hx' 1) (mul_mem (lam i).2 (hx' 0)))
  refine ⟨hsmul, hle, ?_⟩
  have hc : ∀ (x : (stdLattice v 2).toAddSubgroup) (l : Fin 2),
      (x : Fin 2 → v.completion) l ∈ v.integers := fun x l => mem_stdLattice.1 x.2 l
  let coord : Fin 2 → ((stdLattice v 2).toAddSubgroup →+ v.integers) := fun l =>
    { toFun := fun x => ⟨(x : Fin 2 → v.completion) l, hc x l⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hcoord : ∀ l x, ((coord l x : v.integers) : v.completion) = (x : Fin 2 → v.completion) l :=
    fun _ _ => rfl
  cases j with
  | none =>
    let ψ := (IsLocalRing.residue v.integers).toAddMonoidHom.comp (coord 0)
    refine relIndex_eq_residueCard_of ψ (fun a => ?_) (fun x => ?_)
    · obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective a
      refine ⟨⟨![(a : v.completion), 0], mem_stdLattice.2 (Fin.forall_fin_two.2
        ⟨a.2, v.integers.zero_mem⟩)⟩, ?_⟩
      rfl
    · show IsLocalRing.residue v.integers (coord 0 x) = 0 ↔ _
      rw [residue_eq_zero_iff_inv_mul_mem hπ hπ0, hcoord]
      exact ⟨fun h => (mem_heckeSublattice_none hπ0 _).2 ⟨h, hc x 1⟩,
        fun h => ((mem_heckeSublattice_none hπ0 _).1 h).1⟩
  | some i =>
    let ψ := (IsLocalRing.residue v.integers).toAddMonoidHom.comp
      (coord 1 - (AddMonoidHom.mulLeft (lam i)).comp (coord 0))
    refine relIndex_eq_residueCard_of ψ (fun a => ?_) (fun x => ?_)
    · obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective a
      refine ⟨⟨![0, (a : v.completion)], mem_stdLattice.2 (Fin.forall_fin_two.2
        ⟨v.integers.zero_mem, a.2⟩)⟩, ?_⟩
      show IsLocalRing.residue v.integers (coord 1 _ - lam i * coord 0 _) = _
      congr 1
      ext
      simp [hcoord]
    · show IsLocalRing.residue v.integers (coord 1 x - lam i * coord 0 x) = 0 ↔ _
      rw [residue_eq_zero_iff_inv_mul_mem hπ hπ0]
      push_cast
      rw [hcoord, hcoord]
      exact ⟨fun h => (mem_heckeSublattice_some hπ0 _).2 ⟨hc x 0, h⟩,
        fun h => ((mem_heckeSublattice_some hπ0 _).1 h).2⟩


/-- Two indices of a residue system whose representatives are congruent modulo `π` coincide. -/
private theorem eq_of_sub_mem_span (hlam : Place.IsResidueSystem v π lam) {i i' : Fin q}
    (h : lam i - lam i' ∈ Ideal.span {π}) : i = i' := by
  obtain ⟨i₀, -, huniq⟩ := hlam (lam i)
  rw [huniq i (by simp), huniq i' h]

include k in
/-- The lattices `M_j O_v^2` are pairwise distinct. -/
public theorem heckeSublattice_injective (hπ : Place.IsUniformizer v π)
    (hlam : Place.IsResidueSystem v π lam) :
    Function.Injective (heckeSublattice (coe_ne_zero_of_isUniformizer k hπ)
      (fun i => (lam i : v.completion))) := by
  have hπ0 := coe_ne_zero_of_isUniformizer k hπ
  have hvec : ∀ i, ![1, (lam i : v.completion)] ∈
      heckeSublattice hπ0 (fun i => (lam i : v.completion)) (some i) := fun i =>
    (mem_heckeSublattice_some hπ0 _).2 ⟨by simp, by simp⟩
  have hnone : ∀ i, ![1, (lam i : v.completion)] ∉
      heckeSublattice hπ0 (fun i => (lam i : v.completion)) none := fun i h => by
    have := ((mem_heckeSublattice_none hπ0 _).1 h).1
    simp only [Matrix.cons_val_zero, mul_one] at this
    exact inv_notMem_integers hπ hπ0 this
  intro j j' hjj'
  cases j with
  | none =>
    cases j' with
    | none => rfl
    | some i => exact absurd (hjj'.symm.le (hvec i)) (hnone i)
  | some i =>
    cases j' with
    | none => exact absurd (hjj'.le (hvec i)) (hnone i)
    | some i' =>
      have h := (mem_heckeSublattice_some hπ0 _).1 (hjj'.le (hvec i))
      have h2 : lam i - lam i' ∈ Ideal.span {π} := by
        rw [mem_span_iff_inv_mul_mem hπ0]
        simpa using h.2
      exact congrArg some (eq_of_sub_mem_span hlam h2)

include k in
/-- **The Hecke sublattices of `O_v^2`**: the lattices `Λ'` with `π O_v^2 ⊆ Λ' ⊆ O_v^2` of index
`q_v` are exactly the `q_v + 1` lattices `M_j O_v^2`, `M_j = diag (π, 1)`, `(1, 0; λ_i, π)`. -/
public theorem isHeckeSublattice_stdLattice_iff (hπ : Place.IsUniformizer v π)
    (hlam : Place.IsResidueSystem v π lam) {Λ' : Submodule v.integers (Fin 2 → v.completion)} :
    IsHeckeSublattice (stdLattice v 2) Λ' ↔
      ∃ j, Λ' = heckeSublattice (coe_ne_zero_of_isUniformizer k hπ)
        (fun i => (lam i : v.completion)) j := by
  have hπ0 := coe_ne_zero_of_isUniformizer k hπ
  refine ⟨fun hΛ' => ?_, by rintro ⟨j, rfl⟩; exact isHeckeSublattice_heckeSublattice k hπ hlam j⟩
  obtain ⟨h1, h2, h3⟩ := hΛ'
  have hq0 : v.residueCard ≠ 0 := by
    rw [Place.residueCard_eq_of_isResidueSystem hπ hlam]
    obtain ⟨i, -⟩ := hlam 0
    exact Nat.pos_iff_ne_zero.1 (Fin.pos i)
  have hidx := fun j => (isHeckeSublattice_heckeSublattice k hπ hlam j).2.2
  have hsa : ∀ (c : v.integers) (y : Fin 2 → v.completion) (l : Fin 2),
      (c • y) l = (c : v.completion) * y l := fun _ _ _ => rfl
  have hsm : ∀ w : Fin 2 → v.completion, (π : v.completion)⁻¹ * w 0 ∈ v.integers →
      (π : v.completion)⁻¹ * w 1 ∈ v.integers → w ∈ Λ' := by
    intro w hw0 hw1
    have hw' : (fun l => (π : v.completion)⁻¹ * w l) ∈ stdLattice v 2 :=
      mem_stdLattice.2 (Fin.forall_fin_two.2 ⟨hw0, hw1⟩)
    have hπm : π ∈ IsLocalRing.maximalIdeal v.integers := hπ ▸ Ideal.subset_span rfl
    convert h1 (Submodule.smul_mem_smul hπm hw') using 1
    funext l
    rw [hsa]
    field_simp
  by_cases hA : ∃ x ∈ Λ', (π : v.completion)⁻¹ * x 0 ∉ v.integers
  · obtain ⟨x, hx, hx0⟩ := hA
    have hxO := mem_stdLattice.1 (h2 hx)
    have hunit : IsUnit (⟨x 0, hxO 0⟩ : v.integers) := by
      by_contra hnu
      apply hx0
      refine (mem_span_iff_inv_mul_mem hπ0 (⟨x 0, hxO 0⟩ : v.integers)).1 ?_
      rwa [hπ, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    have hu : ((hunit.unit⁻¹ : v.integersˣ) : v.integers) * (⟨x 0, hxO 0⟩ : v.integers) = 1 :=
      hunit.val_inv_mul
    let c : v.integers := ((hunit.unit⁻¹ : v.integersˣ) : v.integers)
    let t : v.integers := c * ⟨x 1, hxO 1⟩
    obtain ⟨i, hi, -⟩ := hlam t
    have hy : c • x ∈ Λ' := Λ'.smul_mem _ hx
    have hy0 : (c • x) 0 = 1 := by rw [hsa]; exact congrArg Subtype.val hu
    have hy1 : (c • x) 1 = t := rfl
    have hti : (π : v.completion)⁻¹ * ((t : v.completion) - lam i) ∈ v.integers := by
      simpa using (mem_span_iff_inv_mul_mem hπ0 _).1 hi
    have hle : heckeSublattice hπ0 (fun i => (lam i : v.completion)) (some i) ≤ Λ' := by
      intro z hz
      obtain ⟨hz0, hz1⟩ := (mem_heckeSublattice_some hπ0 _).1 hz
      have hw : z - (⟨z 0, hz0⟩ : v.integers) • (c • x) ∈ Λ' := by
        apply hsm
        · rw [Pi.sub_apply, hsa, hy0]
          simp
        · rw [Pi.sub_apply, hsa, hy1]
          have : (π : v.completion)⁻¹ * (z 1 - z 0 * t) =
              (π : v.completion)⁻¹ * (z 1 - lam i * z 0) -
                z 0 * ((π : v.completion)⁻¹ * ((t : v.completion) - lam i)) := by ring
          rw [this]
          exact sub_mem hz1 (mul_mem hz0 hti)
      have := Λ'.add_mem hw (Λ'.smul_mem ⟨z 0, hz0⟩ hy)
      rwa [sub_add_cancel] at this
    exact ⟨some i, (eq_of_le_of_relIndex_eq hle h2 ((hidx _).trans h3.symm)
      (h3 ▸ hq0)).symm⟩
  · push Not at hA
    have hle : Λ' ≤ heckeSublattice hπ0 (fun i => (lam i : v.completion)) none := fun x hx =>
      (mem_heckeSublattice_none hπ0 _).2 ⟨hA x hx, mem_stdLattice.1 (h2 hx) 1⟩
    exact ⟨none, eq_of_le_of_relIndex_eq hle
      (isHeckeSublattice_heckeSublattice k hπ hlam none).2.1 (h3.trans (hidx none).symm)
      (by rwa [hidx])⟩

include k in
/-- `j ↦ M_j O_v^2` is a bijection from `Option (Fin q_v)` onto the Hecke sublattices of
`O_v^2`. -/
public theorem bijective_heckeSublattice (hπ : Place.IsUniformizer v π)
    (hlam : Place.IsResidueSystem v π lam) :
    Function.Bijective fun j : Option (Fin q) =>
      (⟨heckeSublattice (coe_ne_zero_of_isUniformizer k hπ) (fun i => (lam i : v.completion)) j,
        isHeckeSublattice_heckeSublattice k hπ hlam j⟩ :
        {Λ' // IsHeckeSublattice (stdLattice v 2) Λ'}) :=
  ⟨fun _ _ h => heckeSublattice_injective k hπ hlam (congrArg Subtype.val h),
    fun Λ' => by
      obtain ⟨j, hj⟩ := (isHeckeSublattice_stdLattice_iff k hπ hlam).1 Λ'.2
      exact ⟨j, Subtype.ext hj.symm⟩⟩

include k in
/-- **The Hecke sublattices of `h O_v^2`**: for `h ∈ GL₂(K_v)`, the lattices `Λ'` with
`π h O_v^2 ⊆ Λ' ⊆ h O_v^2` of index `q_v` are exactly the `q_v + 1` pairwise distinct lattices
`h M_j O_v^2`, `M_j = diag (π, 1)`, `(1, 0; λ_i, π)`. -/
public theorem bijective_heckeSublattice_translate (hπ : Place.IsUniformizer v π)
    (hlam : Place.IsResidueSystem v π lam) (h : GL (Fin 2) v.completion) :
    Function.Bijective fun j : Option (Fin q) =>
      (⟨translate (h * heckeLocalGL (coe_ne_zero_of_isUniformizer k hπ)
          (fun i => (lam i : v.completion)) j) (stdLattice v 2), by
        rw [translate_mul]
        exact (isHeckeSublattice_translate_iff h).2
          (isHeckeSublattice_heckeSublattice k hπ hlam j)⟩ :
        {Λ' // IsHeckeSublattice (translate h (stdLattice v 2)) Λ'}) := by
  convert (heckeTranslateEquiv h (stdLattice v 2)).bijective.comp
    (bijective_heckeSublattice k hπ hlam) using 1
  funext j
  exact Subtype.ext (translate_mul _ _ _)

include k in
/-- **Every lattice in `K_v^2` has exactly `q_v + 1` Hecke sublattices.** -/
public theorem card_heckeSublattice {Λ : Submodule v.integers (Fin 2 → v.completion)}
    (hΛ : Λ.IsLattice v.completion) :
    Nat.card {Λ' // IsHeckeSublattice Λ Λ'} = v.residueCard + 1 := by
  obtain ⟨h, rfl⟩ := exists_eq_translate_stdLattice (isDiscrete k v) hΛ
  have hπ := Place.isUniformizer_unif (isDiscrete k v)
  obtain ⟨lam, hlam⟩ := exists_isResidueSystem k v hπ
  rw [← Nat.card_eq_of_bijective _ (bijective_heckeSublattice_translate k hπ hlam h),
    Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_fin]

variable (lam) in
/-- The lines `κ_v (0, 1)` and `κ_v (1, λ̄_i)` of `κ_v^2`. -/
public def heckeLine : Option (Fin q) →
    Projectivization (IsLocalRing.ResidueField v.integers)
      (Fin 2 → IsLocalRing.ResidueField v.integers)
  | none => Projectivization.mk _ ![0, 1] fun h => by simpa using congrFun h 1
  | some i => Projectivization.mk _ ![1, IsLocalRing.residue v.integers (lam i)]
      fun h => by simpa using congrFun h 0

include k in
/-- **The lines of `κ_v^2`**: `κ_v (0, 1)` and the `κ_v (1, λ̄_i)` are all the lines of `κ_v^2`,
each exactly once. -/
public theorem heckeLine_bijective (hπ : Place.IsUniformizer v π)
    (hlam : Place.IsResidueSystem v π lam) : Function.Bijective (heckeLine lam) := by
  have hres : ∀ a b : v.integers, IsLocalRing.residue v.integers a =
      IsLocalRing.residue v.integers b ↔ a - b ∈ Ideal.span {π} := fun a b => by
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, hπ]
  constructor
  · intro j j' hjj'
    cases j with
    | none =>
      cases j' with
      | none => rfl
      | some i =>
        obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff _ _ _ _ _).1 hjj'
        have := congrFun ha 0
        simp [Units.smul_def] at this
    | some i =>
      cases j' with
      | none =>
        obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff _ _ _ _ _).1 hjj'
        have := congrFun ha 0
        simp at this
      | some i' =>
        obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff _ _ _ _ _).1 hjj'
        have h0 := congrFun ha 0
        have h1 := congrFun ha 1
        simp only [Pi.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
        rw [Units.smul_def, smul_eq_mul, mul_one] at h0
        rw [Units.smul_def, smul_eq_mul, h0, one_mul] at h1
        have h2 : lam i - lam i' ∈ Ideal.span {π} := (hres _ _).1 h1.symm
        exact congrArg some (eq_of_sub_mem_span hlam h2)
  · intro p
    obtain ⟨w, hw, rfl⟩ : ∃ w hw, Projectivization.mk _ w hw = p :=
      ⟨p.rep, p.rep_nonzero, p.mk_rep⟩
    by_cases h0 : w 0 = 0
    · have h1 : w 1 ≠ 0 := fun h1 => hw (funext (Fin.forall_fin_two.2 ⟨h0, h1⟩))
      refine ⟨none, (Projectivization.mk_eq_mk_iff _ _ _ _ _).2
        ⟨Units.mk0 (w 1)⁻¹ (inv_ne_zero h1), funext (Fin.forall_fin_two.2 ⟨?_, ?_⟩)⟩⟩
      · simp [h0]
      · simp [Units.smul_def, h1]
    · obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (w 1 / w 0)
      obtain ⟨i, hi, -⟩ := hlam a
      have hr : IsLocalRing.residue v.integers (lam i) = w 1 / w 0 := by
        rw [← ha]
        exact ((hres _ _).2 hi).symm
      refine ⟨some i, (Projectivization.mk_eq_mk_iff _ _ _ _ _).2
        ⟨Units.mk0 (w 0)⁻¹ (inv_ne_zero h0), funext (Fin.forall_fin_two.2 ⟨?_, ?_⟩)⟩⟩
      · simp [Units.smul_def, h0]
      · simp [Units.smul_def, hr]
        field_simp

variable (lam) in
/-- The vector `(0, 1)` for `j = none` and `(1, λ̄_i)` for `j = i`, spanning `heckeLine j`. -/
public def heckeLineVec : Option (Fin q) → Fin 2 → IsLocalRing.ResidueField v.integers
  | none => ![0, 1]
  | some i => ![1, IsLocalRing.residue v.integers (lam i)]

include k in
/-- The reduction of `diag (π, 1) O_v^2` is contained in the line `κ_v (0, 1)`. -/
public theorem reduction_heckeSublattice_none_le (hπ : Place.IsUniformizer v π) :
    reduction (heckeSublattice (coe_ne_zero_of_isUniformizer k hπ)
        (fun i => (lam i : v.completion)) none) ≤
      (Submodule.span (IsLocalRing.ResidueField v.integers) {heckeLineVec lam none}).restrictScalars
        v.integers := by
  have hπ0 := coe_ne_zero_of_isUniformizer k hπ
  intro y hy
  rw [Submodule.restrictScalars_mem, Submodule.mem_span_singleton]
  obtain ⟨x, hx, rfl⟩ := mem_reduction.1 hy
  have hx0 := ((mem_heckeSublattice_none hπ0 _).1 hx).1
  refine ⟨IsLocalRing.residue v.integers ⟨x.1 1, mem_stdLattice.1 x.2 1⟩,
    funext (Fin.forall_fin_two.2 ⟨?_, ?_⟩)⟩
  · simp only [heckeLineVec, Pi.smul_apply, Matrix.cons_val_zero, smul_eq_mul, mul_zero]
    rw [reduce_apply_of_eq x 0 (a := ⟨x.1 0, mem_stdLattice.1 x.2 0⟩) rfl]
    exact ((residue_eq_zero_iff_inv_mul_mem hπ hπ0
      (⟨x.1 0, mem_stdLattice.1 x.2 0⟩ : v.integers)).2 hx0).symm
  · simp [heckeLineVec, reduce_apply]

include k in
/-- The line `κ_v (0, 1)` is contained in the reduction of `diag (π, 1) O_v^2`. -/
public theorem le_reduction_heckeSublattice_none (hπ : Place.IsUniformizer v π) :
    (Submodule.span (IsLocalRing.ResidueField v.integers) {heckeLineVec lam none}).restrictScalars
        v.integers ≤
      reduction (heckeSublattice (coe_ne_zero_of_isUniformizer k hπ)
        (fun i => (lam i : v.completion)) none) := by
  have hπ0 := coe_ne_zero_of_isUniformizer k hπ
  intro y hy
  rw [Submodule.restrictScalars_mem, Submodule.mem_span_singleton] at hy
  obtain ⟨a, rfl⟩ := hy
  obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective (R := v.integers) a
  refine mem_reduction.2 ⟨⟨_, vec2_mem_stdLattice v.integers.zero_mem b.2⟩,
    (mem_heckeSublattice_none hπ0 _).2 ⟨by simp, by simp⟩,
    funext (Fin.forall_fin_two.2 ⟨?_, ?_⟩)⟩
  · rw [reduce_apply_of_eq _ _ (a := 0) (by simp)]
    simp [heckeLineVec]
  · rw [reduce_apply_of_eq _ _ (a := b) (by simp)]
    simp [heckeLineVec]

include k in
/-- The reduction of `(1, 0; λ_i, π) O_v^2` is contained in the line `κ_v (1, λ̄_i)`. -/
public theorem reduction_heckeSublattice_some_le (hπ : Place.IsUniformizer v π) (i : Fin q) :
    reduction (heckeSublattice (coe_ne_zero_of_isUniformizer k hπ)
        (fun i => (lam i : v.completion)) (some i)) ≤
      (Submodule.span (IsLocalRing.ResidueField v.integers)
        {heckeLineVec lam (some i)}).restrictScalars v.integers := by
  have hπ0 := coe_ne_zero_of_isUniformizer k hπ
  intro y hy
  rw [Submodule.restrictScalars_mem, Submodule.mem_span_singleton]
  obtain ⟨x, hx, rfl⟩ := mem_reduction.1 hy
  have hx1 := ((mem_heckeSublattice_some hπ0 _).1 hx).2
  obtain ⟨x0, hx0e⟩ : ∃ x0 : v.integers, (x0 : v.completion) = x.1 0 :=
    ⟨⟨x.1 0, mem_stdLattice.1 x.2 0⟩, rfl⟩
  obtain ⟨x1, hx1e⟩ : ∃ x1 : v.integers, (x1 : v.completion) = x.1 1 :=
    ⟨⟨x.1 1, mem_stdLattice.1 x.2 1⟩, rfl⟩
  have hz0 : (π : v.completion)⁻¹ * ((x1 - lam i * x0 : v.integers) : v.completion) ∈
      v.integers := by
    have e : ((x1 - lam i * x0 : v.integers) : v.completion) =
        (x1 : v.completion) - lam i * x0 := rfl
    rw [e, hx0e, hx1e]
    exact hx1
  have hz := (residue_eq_zero_iff_inv_mul_mem hπ hπ0 (x1 - lam i * x0)).2 hz0
  rw [map_sub, map_mul, sub_eq_zero] at hz
  refine ⟨IsLocalRing.residue v.integers x0, funext (Fin.forall_fin_two.2 ⟨?_, ?_⟩)⟩
  · simp only [heckeLineVec, Pi.smul_apply, Matrix.cons_val_zero, smul_eq_mul, mul_one]
    rw [reduce_apply_of_eq x 0 hx0e.symm]
  · simp only [heckeLineVec, Pi.smul_apply, Matrix.cons_val_one, Matrix.cons_val_zero,
      smul_eq_mul]
    rw [reduce_apply_of_eq x 1 hx1e.symm, hz]
    exact mul_comm _ _

include k in
/-- The line `κ_v (1, λ̄_i)` is contained in the reduction of `(1, 0; λ_i, π) O_v^2`. -/
public theorem le_reduction_heckeSublattice_some (hπ : Place.IsUniformizer v π) (i : Fin q) :
    (Submodule.span (IsLocalRing.ResidueField v.integers)
        {heckeLineVec lam (some i)}).restrictScalars v.integers ≤
      reduction (heckeSublattice (coe_ne_zero_of_isUniformizer k hπ)
        (fun i => (lam i : v.completion)) (some i)) := by
  have hπ0 := coe_ne_zero_of_isUniformizer k hπ
  intro y hy
  rw [Submodule.restrictScalars_mem, Submodule.mem_span_singleton] at hy
  obtain ⟨a, rfl⟩ := hy
  obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective (R := v.integers) a
  have hmem : ![(b : v.completion), (lam i : v.completion) * b] ∈
      heckeSublattice hπ0 (fun i => (lam i : v.completion)) (some i) := by
    refine (mem_heckeSublattice_some hπ0 _).2 ⟨?_, ?_⟩
    · rw [Matrix.cons_val_zero]
      exact b.2
    · have e : (π : v.completion)⁻¹ * ((lam i : v.completion) * b -
          (lam i : v.completion) * ![(b : v.completion), (lam i : v.completion) * b] 0) = 0 := by
        rw [Matrix.cons_val_zero]
        ring
      rw [Matrix.cons_val_one, Matrix.cons_val_zero, e]
      exact v.integers.zero_mem
  refine mem_reduction.2 ⟨⟨_, vec2_mem_stdLattice b.2 (mul_mem (lam i).2 b.2)⟩, hmem,
    funext (Fin.forall_fin_two.2 ⟨?_, ?_⟩)⟩
  · rw [reduce_apply_of_eq _ 0 (a := b) rfl]
    simp [heckeLineVec]
  · rw [reduce_apply_of_eq _ 1 (a := lam i * b) rfl]
    simp [heckeLineVec, mul_comm]

include k in
/-- **Reduction modulo `π` sends `M_j O_v^2` to the line `heckeLine j`**:
`M_j O_v^2 / π O_v^2 ⊆ κ_v^2` is `κ_v (0, 1)` for `j = none` and `κ_v (1, λ̄_i)` for `j = i`. -/
public theorem reduction_heckeSublattice (hπ : Place.IsUniformizer v π) (j : Option (Fin q)) :
    reduction (heckeSublattice (coe_ne_zero_of_isUniformizer k hπ)
        (fun i => (lam i : v.completion)) j) =
      (heckeLine lam j).submodule.restrictScalars v.integers := by
  cases j with
  | none =>
    rw [heckeLine, Projectivization.submodule_mk]
    exact le_antisymm (reduction_heckeSublattice_none_le k hπ)
      (le_reduction_heckeSublattice_none k hπ)
  | some i =>
    rw [heckeLine, Projectivization.submodule_mk]
    exact le_antisymm (reduction_heckeSublattice_some_le k hπ i)
      (le_reduction_heckeSublattice_some k hπ i)

include k in
/-- **Hecke sublattices of `O_v^2` and lines of `κ_v^2`**: the bijection sending a Hecke
sublattice `Λ'` of `O_v^2` to the line `Λ' / π O_v^2` of `κ_v^2`
(see `reduction_heckeSublatticeEquivLine`). -/
public def heckeSublatticeEquivLine (hπ : Place.IsUniformizer v π)
    (hlam : Place.IsResidueSystem v π lam) :
    {Λ' // IsHeckeSublattice (stdLattice v 2) Λ'} ≃
      Projectivization (IsLocalRing.ResidueField v.integers)
        (Fin 2 → IsLocalRing.ResidueField v.integers) :=
  (Equiv.ofBijective _ (bijective_heckeSublattice k hπ hlam)).symm.trans
    (Equiv.ofBijective _ (heckeLine_bijective k hπ hlam))

include k in
/-- The line attached to a Hecke sublattice `Λ'` of `O_v^2` is its reduction
`Λ' / π O_v^2 ⊆ κ_v^2`. -/
public theorem reduction_heckeSublatticeEquivLine (hπ : Place.IsUniformizer v π)
    (hlam : Place.IsResidueSystem v π lam) (Λ' : {Λ' // IsHeckeSublattice (stdLattice v 2) Λ'}) :
    (heckeSublatticeEquivLine k hπ hlam Λ').submodule.restrictScalars v.integers =
      reduction Λ'.1 := by
  obtain ⟨j, rfl⟩ := (bijective_heckeSublattice k hπ hlam).2 Λ'
  rw [heckeSublatticeEquivLine, Equiv.trans_apply, Equiv.ofBijective_symm_apply_apply,
    Equiv.ofBijective_apply, reduction_heckeSublattice k hπ j]

include k in
/-- **Hecke sublattices of `Λ = h O_v^2` and lines of `Λ / π Λ ≅ κ_v^2`**: the bijection sending
a Hecke sublattice `Λ'` of `h O_v^2` to the line `h⁻¹ Λ' / π O_v^2` of `κ_v^2`. -/
public def heckeSublatticeEquivLineOf (hπ : Place.IsUniformizer v π)
    (hlam : Place.IsResidueSystem v π lam) (h : GL (Fin 2) v.completion) :
    {Λ' // IsHeckeSublattice (translate h (stdLattice v 2)) Λ'} ≃
      Projectivization (IsLocalRing.ResidueField v.integers)
      (Fin 2 → IsLocalRing.ResidueField v.integers) :=
  (heckeTranslateEquiv h (stdLattice v 2)).symm.trans (heckeSublatticeEquivLine k hπ hlam)

include k in
/-- The line attached to a Hecke sublattice `Λ'` of `h O_v^2` is the reduction
`h⁻¹ Λ' / π O_v^2 ⊆ κ_v^2`. -/
public theorem reduction_heckeSublatticeEquivLineOf (hπ : Place.IsUniformizer v π)
    (hlam : Place.IsResidueSystem v π lam) (h : GL (Fin 2) v.completion)
    (Λ' : {Λ' // IsHeckeSublattice (translate h (stdLattice v 2)) Λ'}) :
    (heckeSublatticeEquivLineOf k hπ hlam h Λ').submodule.restrictScalars v.integers =
      reduction (translate h⁻¹ Λ'.1) :=
  reduction_heckeSublatticeEquivLine k hπ hlam _

end FunctionField

end Stacks.Drinfeld.Lattice

end
