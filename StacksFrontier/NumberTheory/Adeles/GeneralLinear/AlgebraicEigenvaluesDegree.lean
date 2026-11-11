module

public import StacksFrontier.NumberTheory.Adeles.GeneralLinear.AlgebraicEigenvaluesLocal
public import StacksFrontier.NumberTheory.Adeles.GeneralLinear.Reduction.Defs
public import StacksFrontier.NumberTheory.Drinfeld.UnitEigenform

/-!
# The degree of an element of `GL_n(A)`

Let `K` be a function field over a finite field `k`. The degree of `x ∈ GL_n(A)` is the degree
of the divisor of the idele `det x`, `deg x = deg (div (det x))`. It is a homomorphism to `ℤ`,
trivial on `GL_n(O)` and on `GL_n(K)` (the degree of a principal divisor is zero). The Hecke
neighbours of a lattice shift it by a fixed amount: if `L'` is summed over by `T_{v,i}` at
`x⁻¹ (O_w^n)_w` and `g (O_w^n)_w = L'`, then `deg g⁻¹ = deg x - i deg v`, since `x g` lies in
`GL_n(O_w)` at `w ≠ v` and `x_v g_v O_v^n` has index `q_v ^ i` in `O_v^n`.

## Main definitions

* `Stacks.Adeles.GeneralLinear.degGL` — the degree `deg (div (det x))` of `x ∈ GL_n(A)`.

## Main results

* `Stacks.Adeles.GeneralLinear.degGL_mapO`, `Stacks.Adeles.GeneralLinear.degGL_mapK` — the
  degree vanishes on `GL_n(O)` and on `GL_n(K)`.
* `Stacks.Adeles.GeneralLinear.degGL_latticeRep_inv` — the shift of the degree along the Hecke
  neighbours of type `i` at `v`.
-/

@[expose] public noncomputable section

open Matrix

universe u w

namespace Stacks.Adeles.GeneralLinear

open Stacks.Adeles.GlobalFunctionField Stacks.Drinfeld.Lattice

variable (k : Type u) [Field k] [Finite k] {K : Type u} [Field K] [Algebra k K]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K] {n : ℕ}

variable (K) in
/-- The degree of `x ∈ GL_n(A)`: the degree of the divisor of the idele `det x`. -/
public def degGL (x : GL (Fin n) (AdeleRing K)) : ℤ :=
  Stacks.Drinfeld.divisorDegree k K (idelDiv k K (Matrix.GeneralLinearGroup.det x))

/-- The degree is multiplicative: `deg (x y) = deg x + deg y`. -/
public theorem degGL_mul (x y : GL (Fin n) (AdeleRing K)) :
    degGL k K (x * y) = degGL k K x + degGL k K y := by
  rw [degGL, map_mul, idelDiv_mul, map_add]
  rfl

/-- `deg 1 = 0`. -/
public theorem degGL_one : degGL k K (1 : GL (Fin n) (AdeleRing K)) = 0 := by
  rw [degGL, map_one, idelDiv_one, map_zero]

/-- `deg x⁻¹ = - deg x`. -/
public theorem degGL_inv (x : GL (Fin n) (AdeleRing K)) : degGL k K x⁻¹ = -degGL k K x := by
  have h := degGL_mul k x⁻¹ x
  rw [inv_mul_cancel, degGL_one] at h
  omega

/-- An idele that is a unit of the integral adeles has divisor `0`. -/
public theorem idelDiv_eq_zero_of_integral (c : (AdeleRing K)ˣ)
    (h₁ : (c : AdeleRing K) ∈ integralAdeles K) (h₂ : ((c⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) ∈
      integralAdeles K) : idelDiv k K c = 0 := by
  ext v
  rw [idelDiv_apply, Finsupp.coe_zero, Pi.zero_apply]
  have hv := isDiscrete k v
  have a₁ := ordC_nonneg_of_mem hv (h₁ v) (idele_apply_ne_zero c v)
  have a₂ := ordC_nonneg_of_mem hv (h₂ v) (idele_apply_ne_zero c⁻¹ v)
  rw [ordC_inv_idele k] at a₂
  omega

/-- The degree vanishes on `GL_n(O)`. -/
public theorem degGL_mapO (κ : GL (Fin n) (integralAdeles K)) : degGL k K (mapO K n κ) = 0 := by
  rw [degGL, idelDiv_eq_zero_of_integral k, map_zero]
  · change ((mapO K n κ).val).det ∈ integralAdeles K
    rw [show (mapO K n κ).val = (integralAdeles K).subtype.mapMatrix κ.val from rfl,
      ← RingHom.map_det]
    exact (κ.val.det).2
  · change ((mapO K n κ)⁻¹.val).det ∈ integralAdeles K
    rw [← map_inv, show (mapO K n κ⁻¹).val = (integralAdeles K).subtype.mapMatrix κ⁻¹.val from rfl,
      ← RingHom.map_det]
    exact (κ⁻¹.val.det).2

/-- The degree vanishes on `GL_n(K)`: the determinant of `γ ∈ GL_n(K)` is a principal idele,
whose divisor is principal, of degree `0`. -/
public theorem degGL_mapK (γ : GL (Fin n) (principalAdeles K)) : degGL k K (mapK K n γ) = 0 := by
  have hmem : ((Matrix.GeneralLinearGroup.det (mapK K n γ) : (AdeleRing K)ˣ) : AdeleRing K) ∈
      principalAdeles K := by
    change ((mapK K n γ).val).det ∈ principalAdeles K
    rw [show (mapK K n γ).val = (principalAdeles K).subtype.mapMatrix γ.val from rfl,
      ← RingHom.map_det]
    exact (γ.val.det).2
  obtain ⟨c, hc⟩ := mem_principalAdeles.1 hmem
  have hc0 : c ≠ 0 := by
    rintro rfl
    obtain ⟨v⟩ := nonempty_place k (K := K)
    exact idele_apply_ne_zero _ v (by rw [hc v, map_zero])
  have heq : Matrix.GeneralLinearGroup.det (mapK K n γ) = diagUnit k hc0 :=
    Units.ext (RestrictedProduct.ext _ _ fun v => by
      rw [hc v, coe_diagUnit, GlobalFunctionField.diag_apply])
  rw [degGL, heq, idelDiv_diagUnit, Stacks.Drinfeld.divisorDegree_principalDivisor k hc0]

/-- The component at `v` of `det x` is the determinant of the component `x_v`. -/
public theorem det_apply (x : GL (Fin n) (AdeleRing K)) (v : Place K) :
    ((Matrix.GeneralLinearGroup.det x : (AdeleRing K)ˣ) : AdeleRing K) v =
      (glAt K n v x).val.det :=
  RingHom.map_det (evalAt K v) x.val

include k in
/-- `latticeRep L` maps the standard lattice to `L`. -/
public theorem latticeRep_smul_standard (L : AdelicLattice K n) :
    latticeRep L • AdelicLattice.standard K n = L := by
  have h := AdelicLattice.exists_smul_standard k L
  rw [latticeRep, dif_pos h]
  exact h.choose_spec

/-- Translation by `g ∈ GL_n(K_v)` preserves indices of lattices. -/
public theorem relIndex_translate {v : Place K} (g : GL (Fin n) v.completion)
    (A B : Submodule v.integers (Fin n → v.completion)) :
    (translate g A).toAddSubgroup.relIndex (translate g B).toAddSubgroup =
      A.toAddSubgroup.relIndex B.toAddSubgroup := by
  have hinj : Function.Injective
      ((Matrix.toLin' g.val).restrictScalars v.integers).toAddMonoidHom := by
    intro x y hxy
    simpa [Matrix.toLin'_apply, mulVec_inv_mulVec] using
      congrArg (fun z => (g⁻¹ : GL (Fin n) v.completion).val *ᵥ z) hxy
  rw [translate, translate, Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup]
  exact AddSubgroup.relIndex_map_map_of_injective _ _ hinj

include k in
/-- At a place `v`, if `g O_v^n ⊆ O_v^n` has index `q_v ^ i`, then `ord_v (det g) = i`. -/
public theorem ordC_det_eq_of_relIndex {v : Place K} (g : GL (Fin n) v.completion) {i : ℕ}
    (hle : translate g (stdLattice v n) ≤ stdLattice v n)
    (hi : (translate g (stdLattice v n)).toAddSubgroup.relIndex (stdLattice v n).toAddSubgroup =
      v.residueCard ^ i) : v.ordC g.val.det = i := by
  obtain ⟨h0, hidx⟩ := relIndex_translate_stdLattice (isDiscrete k v) g
    ((translate_stdLattice_le_iff g).1 hle)
  rw [hi] at hidx
  have hq : 2 ≤ v.residueCard := by
    rw [Place.residueCard_eq_resCard]
    exact one_lt_resCard k v
  have := Nat.pow_right_injective hq hidx
  omega

/-- **Shift of the degree along the Hecke neighbours**: if `L'` is summed over by `T_{v,i}` at
`x⁻¹ (O_w^n)_w`, then the divisor of `det (x · latticeRep L')` is `i · v`. -/
public theorem idelDiv_det_mul_latticeRep {v : Place K} {i : ℕ} (x : GL (Fin n) (AdeleRing K))
    {L' : AdelicLattice K n}
    (hL' : IsHeckeNeighbourGL v i (x⁻¹ • AdelicLattice.standard K n) L') :
    idelDiv k K (Matrix.GeneralLinearGroup.det (x * latticeRep L')) = Finsupp.single v (i : ℤ) := by
  classical
  obtain ⟨hout, -, hle, hidx⟩ := hL'
  have hL := latticeRep_smul_standard k L'
  have htr : ∀ w, translate (glAt K n w (x * latticeRep L')) (stdLattice w n) =
      translate (glAt K n w x) (L'.lattice w) := by
    intro w
    rw [map_mul, translate_mul]
    conv_rhs => rw [← hL]
    rfl
  have hstd : ∀ w, translate (glAt K n w x) ((x⁻¹ • AdelicLattice.standard K n).lattice w) =
      stdLattice w n := by
    intro w
    rw [AdelicLattice.smul_lattice, AdelicLattice.standard_lattice, ← translate_mul, ← map_mul,
      mul_inv_cancel, map_one, translate_one]
  ext w
  rw [idelDiv_apply, det_apply, Finsupp.single_apply]
  by_cases hw : w = v
  · subst hw
    rw [if_pos rfl]
    refine ordC_det_eq_of_relIndex k _ ?_ ?_
    · rw [htr, ← hstd w]
      exact translate_mono _ hle
    · rw [htr, ← hstd w, relIndex_translate, hidx]
  · rw [if_neg (Ne.symm hw)]
    have heq : translate (glAt K n w (x * latticeRep L')) (stdLattice w n) = stdLattice w n := by
      rw [htr, hout w hw, hstd w]
    refine ordC_det_eq_of_relIndex k _ heq.le ?_
    rw [heq, AddSubgroup.relIndex_self, pow_zero]

/-- **Shift of the degree along the Hecke neighbours**: if `L'` is summed over by `T_{v,i}` at
`x⁻¹ (O_w^n)_w`, then `deg (latticeRep L')⁻¹ = deg x - i deg v`. -/
public theorem degGL_latticeRep_inv {v : Place K} {i : ℕ} (x : GL (Fin n) (AdeleRing K))
    {L' : AdelicLattice K n}
    (hL' : IsHeckeNeighbourGL v i (x⁻¹ • AdelicLattice.standard K n) L') :
    degGL k K (latticeRep L')⁻¹ =
      degGL k K x - (i : ℤ) * (Stacks.Drinfeld.placeDegree k K v : ℤ) := by
  have h : degGL k K (x * latticeRep L') = (i : ℤ) * (Stacks.Drinfeld.placeDegree k K v : ℤ) := by
    rw [degGL, idelDiv_det_mul_latticeRep k x hL', Stacks.Drinfeld.divisorDegree,
      Finsupp.linearCombination_single, smul_eq_mul]
  have h2 : (latticeRep L')⁻¹ = (x * latticeRep L')⁻¹ * x := by group
  rw [h2, degGL_mul, degGL_inv, h]
  ring

end Stacks.Adeles.GeneralLinear

end
