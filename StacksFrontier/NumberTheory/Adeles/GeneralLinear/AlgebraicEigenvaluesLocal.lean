module

public import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
public import StacksFrontier.NumberTheory.Drinfeld.Lattice.Local

/-!
# The index of a translate of the standard lattice

Let `v` be a discrete place of a field `K`, with completion `K_v`, ring of integers `O_v` and
residue field of cardinality `q_v`. For `g ∈ GL_n(K_v)` with entries in `O_v`, the lattice
`g O_v^n` has index `q_v ^ {ord_v (det g)}` in `O_v^n`. The proof goes through the Smith normal
form over the discrete valuation ring `O_v`: `O_v^n / g O_v^n ≅ ∏ O_v / (a_i)` with
`det g = u ∏ a_i`, `u` a unit, and `O_v / (a)` has `q_v ^ {ord_v a}` elements, the index of
`ϖ^{ord a} O_v` in `O_v`.

## Main results

* `Stacks.Drinfeld.Lattice.index_span_singleton`: `#(O_v / (a)) = q_v ^ {ord_v a}`.
* `Stacks.Drinfeld.Lattice.index_range_eq`: for an injective endomorphism `φ` of `O_v^ι`,
  `#(O_v^ι / φ O_v^ι) = q_v ^ {ord_v (det φ)}`.
* `Stacks.Drinfeld.Lattice.relIndex_translate_stdLattice`: `[O_v^n : g O_v^n] =
  q_v ^ {ord_v (det g)}` for `g ∈ GL_n(K_v)` with entries in `O_v`.
-/

@[expose] public noncomputable section

open Matrix

universe u

namespace Stacks.Drinfeld.Lattice

open Stacks.Adeles Module

variable {K : Type u} [Field K] {v : Place K}

/-- At a discrete place the order of `1` is `0`. -/
public theorem ordC_one_of_isDiscrete (hv : v.IsDiscrete) : v.ordC (1 : v.completion) = 0 := by
  have h := Place.ordC_mul hv (one_ne_zero (α := v.completion)) (one_ne_zero (α := v.completion))
  rw [one_mul] at h
  omega

/-- The order of a finite product of nonzero elements of `K_v` is the sum of their orders. -/
public theorem ordC_prod (hv : v.IsDiscrete) {ι : Type*} (s : Finset ι) (f : ι → v.completion)
    (hf : ∀ i ∈ s, f i ≠ 0) : v.ordC (∏ i ∈ s, f i) = ∑ i ∈ s, v.ordC (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ordC_one_of_isDiscrete hv]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      Place.ordC_mul hv (hf a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.2 fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

/-- A nonzero element of `O_v` has nonnegative order. -/
public theorem ordC_nonneg_of_mem (hv : v.IsDiscrete) {a : v.completion} (ha : a ∈ v.integers)
    (ha0 : a ≠ 0) : 0 ≤ v.ordC a :=
  ((Place.mem_ball_iff_ordC hv (m := 0)).1 (Place.mem_ball_zero_iff.2 ha)).resolve_left ha0

/-- A unit of `O_v` has order `0`. -/
public theorem ordC_unit (hv : v.IsDiscrete) (w : v.integersˣ) :
    v.ordC ((w : v.integers) : v.completion) = 0 := by
  have h1 : ((w : v.integers) : v.completion) * ((w⁻¹ : v.integersˣ) : v.integers) = 1 := by
    have := congrArg (fun x : v.integers => (x : v.completion)) w.mul_inv
    simpa only [MulMemClass.coe_mul, OneMemClass.coe_one] using this
  have hw0 : ((w : v.integers) : v.completion) ≠ 0 := left_ne_zero_of_mul_eq_one h1
  have hw0' : ((w⁻¹ : v.integersˣ) : v.integers) ≠ (0 : v.completion) :=
    right_ne_zero_of_mul_eq_one h1
  have h := Place.ordC_mul hv hw0 hw0'
  rw [h1, ordC_one_of_isDiscrete hv] at h
  have := ordC_nonneg_of_mem hv (w : v.integers).2 hw0
  have := ordC_nonneg_of_mem hv ((w⁻¹ : v.integersˣ) : v.integers).2 hw0'
  omega

/-- `ϖ^m O_v` has index `q_v ^ m` in `O_v`. -/
public theorem relIndex_ball_natCast (hv : v.IsDiscrete) (m : ℕ) :
    (v.ball m).relIndex (v.ball 0) = v.residueCard ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : v.ball ((m + 1 : ℕ) : ℤ) ≤ v.ball (m : ℤ) := Place.ball_anti hv (by omega)
    have h2 : v.ball (m : ℤ) ≤ v.ball 0 := Place.ball_anti hv (by omega)
    rw [← AddSubgroup.relIndex_mul_relIndex _ _ _ h1 h2, ih, pow_succ, mul_comm]
    congr 1
    push_cast
    exact Place.relIndex_ball hv m

/-- The ideal `(a)` of `O_v`, `a ≠ 0`, has index `q_v ^ {ord_v a}`. -/
public theorem index_span_singleton (hv : v.IsDiscrete) {a : v.integers} (ha : a ≠ 0) :
    (Ideal.span {a} : Ideal v.integers).toAddSubgroup.index =
      v.residueCard ^ (v.ordC (a : v.completion)).toNat := by
  have ha0 : (a : v.completion) ≠ 0 := fun h => ha (Subtype.ext h)
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (ordC_nonneg_of_mem hv a.2 ha0)
  let φ : v.integers →+ v.completion := v.integers.subtype.toAddMonoidHom
  have hφ : Function.Injective φ := Subtype.val_injective
  have htop : (⊤ : AddSubgroup v.integers).map φ = v.ball 0 := by
    ext z
    simp only [AddSubgroup.mem_map, AddSubgroup.mem_top, true_and, Place.mem_ball_zero_iff]
    exact ⟨by rintro ⟨y, rfl⟩; exact y.2, fun h => ⟨⟨z, h⟩, rfl⟩⟩
  have hspan : (Ideal.span {a} : Ideal v.integers).toAddSubgroup.map φ =
      v.ball (v.ordC (a : v.completion)) := by
    ext z
    simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨y, ⟨r, rfl⟩, rfl⟩
      have := (Place.mul_mem_ball_iff hv ha0 (m := 0) (y := (r : v.completion))).2
        (Place.mem_ball_zero_iff.2 r.2)
      rw [zero_add] at this
      change ((r * a : v.integers) : v.completion) ∈ _
      rwa [MulMemClass.coe_mul, mul_comm]
    · intro hz
      have hr : (a : v.completion)⁻¹ * z ∈ v.integers := by
        rw [← Place.mem_ball_zero_iff, ← Place.mul_mem_ball_iff hv ha0, zero_add,
          mul_inv_cancel_left₀ ha0]
        exact hz
      refine ⟨⟨_, hr⟩ * a, ⟨⟨_, hr⟩, rfl⟩, ?_⟩
      change (((⟨_, hr⟩ : v.integers) * a : v.integers) : v.completion) = z
      rw [MulMemClass.coe_mul]
      change (a : v.completion)⁻¹ * z * a = z
      rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ ha0, one_mul]
  rw [← AddSubgroup.relIndex_top_right, ← AddSubgroup.relIndex_map_map_of_injective _ _ hφ, hspan,
    htop, hm, Int.toNat_natCast, relIndex_ball_natCast hv]

/-- **Index and determinant over `O_v`**: for an injective `O_v`-linear endomorphism `φ` of
`O_v^ι`, the image `φ O_v^ι` has index `q_v ^ {ord_v (det φ)}` in `O_v^ι`. -/
public theorem index_range_eq (hv : v.IsDiscrete) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : (ι → v.integers) →ₗ[v.integers] (ι → v.integers)) (hφ : Function.Injective φ) :
    (LinearMap.range φ).toAddSubgroup.index =
      v.residueCard ^ (v.ordC ((LinearMap.det φ : v.integers) : v.completion)).toNat := by
  haveI := isDiscreteValuationRing_integers hv
  let N := LinearMap.range φ
  let e : (ι → v.integers) ≃ₗ[v.integers] N := LinearEquiv.ofInjective φ hφ
  have h : Module.finrank v.integers N = Module.finrank v.integers (ι → v.integers) :=
    e.finrank_eq.symm
  let b := Pi.basisFun v.integers ι
  let a := Submodule.smithNormalFormCoeffs b h
  let b' := Submodule.smithNormalFormTopBasis b h
  let ab := Submodule.smithNormalFormBotBasis b h
  have ab_eq := Submodule.smithNormalFormBotBasis_def b h
  let e' : (ι → v.integers) ≃ₗ[v.integers] N := b'.equiv ab (Equiv.refl _)
  let f : (ι → v.integers) →ₗ[v.integers] (ι → v.integers) :=
    N.subtype ∘ₗ (e' : (ι → v.integers) →ₗ[v.integers] N)
  have ha : ∀ i, f (b' i) = a i • b' i := by
    intro i
    change ((b'.equiv ab (Equiv.refl _) (b' i) : N) : ι → v.integers) = _
    rw [b'.equiv_apply, Equiv.refl_apply]
    exact ab_eq i
  have hdetf : LinearMap.det f = ∏ i, a i := by
    rw [← LinearMap.det_toMatrix b', ← Matrix.det_diagonal]
    congr 1
    ext i j
    rw [LinearMap.toMatrix_apply, ha, map_smul, Basis.repr_self, Finsupp.smul_single,
      smul_eq_mul, mul_one]
    by_cases hij : i = j
    · rw [hij, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
  have hφe : φ = N.subtype ∘ₗ (e : (ι → v.integers) →ₗ[v.integers] N) := LinearMap.ext fun _ => rfl
  obtain ⟨w, hw⟩ : Associated (LinearMap.det φ) (LinearMap.det f) := by
    rw [hφe]
    exact LinearMap.associated_det_comp_equiv N.subtype e e'
  have ha0 : ∀ i, ((a i : v.integers) : v.completion) ≠ 0 := fun i h0 =>
    Submodule.smithNormalFormCoeffs_ne_zero b h i (Subtype.ext h0)
  have hnn : ∀ i, 0 ≤ v.ordC ((a i : v.integers) : v.completion) := fun i =>
    ordC_nonneg_of_mem hv (a i).2 (ha0 i)
  have hkey : ((LinearMap.det φ : v.integers) : v.completion) * ((w : v.integers) : v.completion) =
      ∏ i, ((a i : v.integers) : v.completion) := by
    have := congrArg (fun x : v.integers => (x : v.completion)) hw
    simpa only [MulMemClass.coe_mul, hdetf, SubmonoidClass.coe_finset_prod] using this
  have hP0 : ∏ i, ((a i : v.integers) : v.completion) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => ha0 i
  rw [← hkey] at hP0
  have hord : v.ordC ((LinearMap.det φ : v.integers) : v.completion) =
      ∑ i, v.ordC ((a i : v.integers) : v.completion) := by
    have h1 := Place.ordC_mul hv (left_ne_zero_of_mul hP0) (right_ne_zero_of_mul hP0)
    rw [hkey, ordC_prod hv _ _ fun i _ => ha0 i, ordC_unit hv, add_zero] at h1
    exact h1.symm
  have hcard : ∀ i, Nat.card (v.integers ⧸ Ideal.span {a i}) =
      v.residueCard ^ (v.ordC ((a i : v.integers) : v.completion)).toNat := fun i =>
    index_span_singleton hv fun h0 => ha0 i (by rw [h0]; rfl)
  have hidx : (LinearMap.range φ).toAddSubgroup.index = Nat.card ((ι → v.integers) ⧸ N) :=
    (Submodule.cardQuot_apply N).symm
  have hpi : Nat.card ((ι → v.integers) ⧸ N) =
      ∏ i, Nat.card (v.integers ⧸ Ideal.span {a i}) := by
    rw [Nat.card_congr (Submodule.quotientEquivPiSpan N b h).toEquiv, Nat.card_pi]
  have hsum : (v.ordC ((LinearMap.det φ : v.integers) : v.completion)).toNat =
      ∑ i, (v.ordC ((a i : v.integers) : v.completion)).toNat := by
    rw [hord]
    zify
    rw [Int.toNat_of_nonneg (Finset.sum_nonneg fun i _ => hnn i)]
    exact Finset.sum_congr rfl fun i _ => (Int.toNat_of_nonneg (hnn i)).symm
  rw [hidx, hpi, Finset.prod_congr rfl fun i _ => hcard i, Finset.prod_pow_eq_pow_sum, hsum]

variable {n : ℕ}

/-- The integral matrix of `g ∈ GL_n(K_v)` with entries in `O_v`. -/
public def integralMatrix (g : GL (Fin n) v.completion) (hg : ∀ i j, g.val i j ∈ v.integers) :
    Matrix (Fin n) (Fin n) v.integers :=
  Matrix.of fun i j => ⟨g.val i j, hg i j⟩

/-- The determinant of the integral matrix of `g` is `det g`. -/
public theorem coe_det_integralMatrix (g : GL (Fin n) v.completion)
    (hg : ∀ i j, g.val i j ∈ v.integers) :
    ((integralMatrix g hg).det : v.completion) = g.val.det := by
  have := RingHom.map_det v.integers.subtype (integralMatrix g hg)
  rw [show v.integers.subtype.mapMatrix (integralMatrix g hg) = g.val by ext i j; rfl] at this
  exact this

/-- The inclusion `O_v^n → K_v^n` intertwines the integral matrix of `g` with `g`. -/
private theorem compLeft_mulVec (g : GL (Fin n) v.completion)
    (hg : ∀ i j, g.val i j ∈ v.integers) (y : Fin n → v.integers) :
    (Algebra.linearMap v.integers v.completion).compLeft (Fin n) ((integralMatrix g hg) *ᵥ y) =
      g.val *ᵥ (Algebra.linearMap v.integers v.completion).compLeft (Fin n) y := by
  funext i
  change (((integralMatrix g hg *ᵥ y) i : v.integers) : v.completion) =
    ∑ j, g.val i j * (y j : v.completion)
  simp only [Matrix.mulVec, dotProduct, AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul]
  rfl

/-- **Index of a translate of the standard lattice**: for `g ∈ GL_n(K_v)` with entries in `O_v`
at a discrete place, `ord_v (det g) ≥ 0` and `[O_v^n : g O_v^n] = q_v ^ {ord_v (det g)}`. -/
public theorem relIndex_translate_stdLattice (hv : v.IsDiscrete) (g : GL (Fin n) v.completion)
    (hg : ∀ i j, g.val i j ∈ v.integers) :
    0 ≤ v.ordC g.val.det ∧
      (translate g (stdLattice v n)).toAddSubgroup.relIndex (stdLattice v n).toAddSubgroup =
        v.residueCard ^ (v.ordC g.val.det).toNat := by
  set A := integralMatrix g hg
  set ι := (Algebra.linearMap v.integers v.completion).compLeft (Fin n)
  have hι : Function.Injective ι := fun _ _ h => funext fun i => Subtype.ext (congrFun h i)
  have hdet0 : (A.det : v.completion) ≠ 0 := by
    rw [coe_det_integralMatrix]
    exact Matrix.GeneralLinearGroup.det_ne_zero g
  refine ⟨by rw [← coe_det_integralMatrix g hg]; exact ordC_nonneg_of_mem hv A.det.2 hdet0, ?_⟩
  have hφ : Function.Injective (Matrix.mulVecLin A) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    apply hι
    have h1 : g.val *ᵥ ι y = 0 := by
      rw [← compLeft_mulVec g hg]
      change ι (A *ᵥ y) = 0
      rw [show A *ᵥ y = 0 from hy, map_zero]
    rw [map_zero]
    simpa [mulVec_inv_mulVec] using congrArg (fun z => (g⁻¹ : GL (Fin n) v.completion).val *ᵥ z) h1
  have htr : translate g (stdLattice v n) = (LinearMap.range (Matrix.mulVecLin A)).map ι := by
    ext x
    simp only [translate, stdLattice, Submodule.mem_map, LinearMap.mem_range,
      LinearMap.coe_restrictScalars, Matrix.toLin'_apply, Matrix.mulVecLin_apply]
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨A *ᵥ y, ⟨y, rfl⟩, compLeft_mulVec g hg y⟩
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨ι y, ⟨y, rfl⟩, (compLeft_mulVec g hg y).symm⟩
  have hstd : stdLattice v n = (⊤ : Submodule v.integers (Fin n → v.integers)).map ι := by
    rw [Submodule.map_top]
    rfl
  rw [htr, hstd, Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup,
    AddSubgroup.relIndex_map_map_of_injective _ _
      (show Function.Injective (ι : (Fin n → v.integers) →+ (Fin n → v.completion)) from hι),
    Submodule.top_toAddSubgroup, AddSubgroup.relIndex_top_right, index_range_eq hv _ hφ,
    ← Matrix.toLin'_apply', LinearMap.det_toLin', coe_det_integralMatrix g hg]

end Stacks.Drinfeld.Lattice

end
