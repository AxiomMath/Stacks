module

public import StacksFrontier.NumberTheory.Drinfeld.SupersingularCurve
public import StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.HeckeData

/-!
# A nonzero unramified cusp form for `y² + y = x³ + x + 1` over `𝔽₂`

Let `K` be the function field of `E : y² + y = x³ + x + 1` over `𝔽₂`, `P₀` a place with
`x ∈ 𝔪_{P₀}`, and `x_E ∈ GL₂(A)` the matrix `(x, 0; y, 1)` at `P₀` and the identity elsewhere.
The automorphism `α : x ↦ x + 1, y ↦ y + x` moves `x_E` out of the double coset
`S = Z(A) GL₂(O) x_E GL₂(K)`: the lattice `{ξ ∈ K² | x_E ξ ∈ O²}` is `𝔽₂²` (from
`L(2∞) = 𝔽₂ + 𝔽₂ x`), which forces any `γ ∈ GL₂(K)` with `α(x_E) ∈ Z(A) GL₂(O) x_E γ` to have
determinant `1`, and then the determinants disagree at `P₀`. Hence `1_S - 1_S ∘ α` is a nonzero
function; it is cuspidal (`Stacks.Drinfeld.starCusp_sub_comp_glMap`, class number one).

## Main results

* `Stacks.Drinfeld.SupersingularCurve.isLat_xE_iff'` — the lattice of `x_E` is `𝔽₂²`.
* `Stacks.Drinfeld.SupersingularCurve.isLat_glMap`, `isLat_mapO_mul`, `isLat_mul_mapK`,
  `isLat_scalarGL_mul` — its behaviour under `α`, `GL₂(O)`, `GL₂(K)` and integral scalars.
* `Stacks.Drinfeld.SupersingularCurve.placeComap_alpha_P0_ne` — `α` moves `P₀`.
* `Stacks.Drinfeld.SupersingularCurve.glMap_alpha_xE_notMem` — `α(x_E) ∉ S`.
* `Stacks.Drinfeld.SupersingularCurve.cuspFormsCentralChar_ne_bot` — `C(Ω) ≠ 0` for `K`.
-/

@[expose] public noncomputable section

open Polynomial Matrix Stacks.Adeles Stacks.Adeles.GlobalFunctionField

namespace Stacks.Drinfeld.SupersingularCurve

/-- The image of `κ ∈ K` in the completion at `v` is integral if and only if `κ` lies in the
valuation ring of `v`. -/
public theorem coeRingHom_mem_integers_iff (v : Place K) (κ : K) :
    v.coeRingHom κ ∈ v.integers ↔ κ ∈ v.1 := by
  rw [Place.integers, Valuation.mem_valuationSubring_iff, Place.valued_coeRingHom,
    ValuationSubring.valuation_le_one_iff]

/-- A place `P₀` at which `x` vanishes. -/
public theorem exists_P0 : ∃ v : Place K, x ∈ v.1 ∧ v.1.valuation x < 1 := by
  obtain ⟨v, hv, hlt⟩ := exists_place_of_prime (f := X) prime_X
  exact ⟨v, hv, by simpa using hlt⟩

/-- A place `P₀` of `K` at which `x` vanishes, chosen by `exists_P0`. -/
public def P0 : Place K := exists_P0.choose

/-- `x` is integral at `P₀`. -/
public theorem x_mem_P0 : x ∈ P0.1 := exists_P0.choose_spec.1

/-- `x` lies in the maximal ideal of `P₀`. -/
public theorem valuation_x_P0 : P0.1.valuation x < 1 := exists_P0.choose_spec.2

/-- `y` is integral at `P₀`. -/
public theorem y_mem_P0 : y ∈ P0.1 := y_mem_of_x_mem x_mem_P0

/-- An element of the valuation ring of `P₀` has valuation at most `1`. -/
public theorem valuation_le_one_P0 {z : K} (hz : z ∈ P0.1) : P0.1.valuation z ≤ 1 :=
  (ValuationSubring.valuation_le_one_iff _ _).2 hz

/-- If `m` lies in the maximal ideal of `P₀`, then `1 + m` has valuation `1` at `P₀`. -/
public theorem valuation_one_add_P0 {m : K} (hm : P0.1.valuation m < 1) :
    P0.1.valuation (1 + m) = 1 := by
  rw [Valuation.map_add_eq_of_lt_left _ (by rwa [map_one]), map_one]

/-- `x³ + x + 1` has valuation `1` at `P₀`. -/
public theorem valuation_cub_P0 : P0.1.valuation (x ^ 3 + x + 1) = 1 := by
  rw [add_comm, valuation_one_add_P0]
  refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ valuation_x_P0)
  rw [map_pow]
  exact pow_lt_one₀ zero_le valuation_x_P0 (by norm_num)

/-- The automorphism `α` moves `P₀`. -/
public theorem placeComap_alpha_P0_ne : placeComap alpha P0 ≠ P0 := by
  intro h
  have hlt : ∀ z : K, z ≠ 0 → (P0.1.valuation z < 1 ↔ z⁻¹ ∉ P0.1) := by
    intro z hz
    rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, not_le,
      one_lt_inv₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hz))]
  have h1 : P0.1.valuation (x + 1) < 1 := by
    rw [hlt _ x_add_one_ne_zero, ← alphaHom_x, ← alpha_apply, ← map_inv₀,
      ← mem_placeComap alpha, h]
    exact (hlt x x_ne_zero).1 valuation_x_P0
  have h2 : P0.1.valuation 1 < 1 := by
    have := lt_of_le_of_lt (Valuation.map_sub _ (x + 1) x) (max_lt h1 valuation_x_P0)
    rwa [add_sub_cancel_left] at this
  rw [map_one] at h2
  exact lt_irrefl _ h2

/-- The matrix `(x, 0; y, 1) ∈ GL₂(K)`. -/
public def gammaE : GL (Fin 2) K where
  val := !![x, 0; y, 1]
  inv := !![x⁻¹, 0; -(y * x⁻¹), 1]
  val_inv := by
    rw [mul_fin_two, one_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [x_ne_zero]
  inv_val := by
    rw [mul_fin_two, one_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [x_ne_zero]

/-- `x_E`: the matrix `(x, 0; y, 1)` at `P₀` and the identity elsewhere. -/
public def xE : GL (Fin 2) (AdeleRing K) :=
  localGL P0 (Matrix.GeneralLinearGroup.map P0.coeRingHom gammaE)

/-- At `P₀`, the entries of `x_E` are those of `(x, 0; y, 1)`. -/
public theorem xE_apply_P0 (i j : Fin 2) :
    ((xE : Matrix (Fin 2) (Fin 2) (AdeleRing K)) i j) P0 = P0.coeRingHom (!![x, 0; y, 1] i j) :=
  localMatrix_apply_self _ i j

/-- Away from `P₀`, `x_E` is the identity matrix. -/
public theorem xE_apply_ne {v : Place K} (hv : v ≠ P0) (i j : Fin 2) :
    ((xE : Matrix (Fin 2) (Fin 2) (AdeleRing K)) i j) v =
      (1 : Matrix (Fin 2) (Fin 2) v.completion) i j :=
  localMatrix_apply_ne hv _ i j

/-- The lattice condition: `ξ ∈ K²` (as principal adeles) with `g ξ ∈ O²`. -/
public def IsLat (g : GL (Fin 2) (AdeleRing K)) (ξ : Fin 2 → AdeleRing K) : Prop :=
  (∀ i, ξ i ∈ principalAdeles K) ∧
    ∀ i, ((g : Matrix (Fin 2) (Fin 2) (AdeleRing K)) *ᵥ ξ) i ∈ integralAdeles K

/-- The component at `v` of `g ξ`, for `g ∈ GL₂(A)` and `ξ ∈ A²`. -/
public theorem mulVec_apply_place (g : GL (Fin 2) (AdeleRing K)) (ξ : Fin 2 → AdeleRing K)
    (i : Fin 2) (v : Place K) :
    ((g : Matrix (Fin 2) (Fin 2) (AdeleRing K)) *ᵥ ξ) i v =
      (g : Matrix (Fin 2) (Fin 2) (AdeleRing K)) i 0 v * ξ 0 v +
        (g : Matrix (Fin 2) (Fin 2) (AdeleRing K)) i 1 v * ξ 1 v := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The component at `P₀` of `x_E κ`, for `κ ∈ K²` viewed as a vector of principal adeles. -/
public theorem mulVec_xE_P0 (κ : Fin 2 → K) (i : Fin 2) :
    ((xE : Matrix (Fin 2) (Fin 2) (AdeleRing K)) *ᵥ fun i => diag (ZMod 2) K (κ i)) i P0 =
      P0.coeRingHom (!![x, 0; y, 1] i 0 * κ 0 + !![x, 0; y, 1] i 1 * κ 1) := by
  rw [mulVec_apply_place, xE_apply_P0, xE_apply_P0]
  simp only [GlobalFunctionField.diag_apply, map_add, map_mul]

/-- Away from `P₀`, the components of `x_E κ` are those of `κ`. -/
public theorem mulVec_xE_ne {v : Place K} (hv : v ≠ P0) (κ : Fin 2 → K) (i : Fin 2) :
    ((xE : Matrix (Fin 2) (Fin 2) (AdeleRing K)) *ᵥ fun i => diag (ZMod 2) K (κ i)) i v =
      v.coeRingHom (κ i) := by
  rw [mulVec_apply_place, xE_apply_ne hv, xE_apply_ne hv]
  fin_cases i <;> simp [GlobalFunctionField.diag_apply, Matrix.one_apply]

/-- The constant `d ∈ 𝔽₂` as an adele. -/
public abbrev cst (d : ZMod 2) : AdeleRing K := diag (ZMod 2) K (algebraMap (ZMod 2) K d)

/-- Every element of `𝔽₂` is `0` or `1`. -/
public theorem zmod_two_cases (t : ZMod 2) : t = 0 ∨ t = 1 := by revert t; decide

/-- Every `t ∈ 𝔽₂` satisfies `t * t + t = 0`. -/
public theorem zmod_two_mul_self_add (t : ZMod 2) : t * t + t = 0 := by revert t; decide

/-- The place at infinity is not `P₀`. -/
public theorem infPlace_ne_P0 : infPlace ≠ P0 := fun h => x_notMem_infPlace (h ▸ x_mem_P0)

/-- An element `k` integral away from `P₀` with `x k` integral at `P₀` has `x k ∈ 𝔽₂ + 𝔽₂ x`. -/
public theorem exists_eq_add_mul_x_of_mul_x_mem {k : K} (hv : ∀ v : Place K, v ≠ P0 → k ∈ v.1)
    (hP : x * k ∈ P0.1) :
    ∃ c d : ZMod 2, x * k = algebraMap (ZMod 2) K c + algebraMap (ZMod 2) K d * x := by
  refine eq_add_mul_x_of_mem _ (fun v hxv => ?_) (fun hz => ?_)
  · by_cases hvP : v = P0
    · subst hvP
      exact hP
    · exact mul_mem hxv (hv v hvP)
  · have hk : k ≠ 0 := fun h0 => hz (by rw [h0, mul_zero])
    rw [Place.ord_mul _ x_ne_zero hk, ord_infPlace_x]
    have := (Place.ord_nonneg_iff (isDiscrete (ZMod 2) infPlace) hk).2 (hv _ infPlace_ne_P0)
    omega

/-- If `c y + c₂` lies in `𝔪_{P₀}` for `c, c₂ ∈ 𝔽₂`, then `c = c₂ = 0`. -/
public theorem eq_zero_of_valuation_P0_lt {c c₂ : ZMod 2}
    (hval : P0.1.valuation (algebraMap (ZMod 2) K c * y + algebraMap (ZMod 2) K c₂) < 1) :
    c = 0 ∧ c₂ = 0 := by
  have hc : c = 0 := by
    rcases zmod_two_cases c with hc | hc
    · exact hc
    exfalso
    subst hc
    rw [map_one, one_mul] at hval
    have hsq : algebraMap (ZMod 2) K c₂ * algebraMap (ZMod 2) K c₂ +
        algebraMap (ZMod 2) K c₂ = 0 := by
      rw [← map_mul, ← map_add, zmod_two_mul_self_add, map_zero]
    have hprod : (y + algebraMap (ZMod 2) K c₂) * (y + algebraMap (ZMod 2) K c₂ + 1) =
        x ^ 3 + x + 1 := by
      linear_combination y_sq_add_y + hsq + (y * algebraMap (ZMod 2) K c₂) * two_eq_zero
    have hv := congrArg P0.1.valuation hprod
    rw [map_mul, valuation_cub_P0] at hv
    have hle := valuation_le_one_P0 (add_mem (add_mem y_mem_P0 (algebraMap_mem_place P0 c₂))
      P0.1.one_mem)
    refine lt_irrefl (1 : P0.1.ValueGroup) ?_
    calc (1 : P0.1.ValueGroup) = _ := hv.symm
      _ ≤ P0.1.valuation (y + algebraMap (ZMod 2) K c₂) := mul_le_of_le_one_right' hle
      _ < 1 := hval
  subst hc
  rw [map_zero, zero_mul, zero_add] at hval
  refine ⟨rfl, ?_⟩
  rcases zmod_two_cases c₂ with h | h
  · exact h
  · subst h
    rw [map_one, map_one] at hval
    exact absurd hval (lt_irrefl _)

/-- Constant vectors lie in the lattice of `x_E`. -/
public theorem isLat_xE_of_forall_eq_algebraMap (κ : Fin 2 → K)
    (h : ∀ i, ∃ d : ZMod 2, κ i = algebraMap (ZMod 2) K d) :
    IsLat xE (fun i => diag (ZMod 2) K (κ i)) := by
  obtain ⟨d₀, hd₀⟩ := h 0
  obtain ⟨d₁, hd₁⟩ := h 1
  have hP : ∀ i, !![x, 0; y, 1] i 0 * κ 0 + !![x, 0; y, 1] i 1 * κ 1 ∈ P0.1 := by
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · simpa [hd₀] using mul_mem x_mem_P0 (algebraMap_mem_place P0 d₀)
    · simpa [hd₀, hd₁] using add_mem (mul_mem y_mem_P0 (algebraMap_mem_place P0 d₀))
        (algebraMap_mem_place P0 d₁)
  have hc : ∀ i, ∀ v : Place K, κ i ∈ v.1 := by
    refine Fin.forall_fin_two.2 ⟨fun v => ?_, fun v => ?_⟩
    · rw [hd₀]
      exact algebraMap_mem_place v d₀
    · rw [hd₁]
      exact algebraMap_mem_place v d₁
  refine ⟨fun i => ⟨κ i, fun v => rfl⟩, fun i v => ?_⟩
  by_cases hvP : v = P0
  · subst hvP
    rw [mulVec_xE_P0, coeRingHom_mem_integers_iff]
    exact hP i
  · rw [mulVec_xE_ne hvP, coeRingHom_mem_integers_iff]
    exact hc i v

/-- **The lattice of `x_E` is `𝔽₂²`.** -/
public theorem isLat_xE_iff (κ : Fin 2 → K) :
    IsLat xE (fun i => diag (ZMod 2) K (κ i)) ↔
      ∀ i, ∃ d : ZMod 2, κ i = algebraMap (ZMod 2) K d := by
  refine ⟨fun ⟨_, h⟩ => ?_, isLat_xE_of_forall_eq_algebraMap κ⟩
  have hP : ∀ i, !![x, 0; y, 1] i 0 * κ 0 + !![x, 0; y, 1] i 1 * κ 1 ∈ P0.1 := fun i => by
    have := h i P0
    rwa [mulVec_xE_P0, coeRingHom_mem_integers_iff] at this
  have hv : ∀ i, ∀ v : Place K, v ≠ P0 → κ i ∈ v.1 := fun i v hv => by
    have := h i v
    rwa [mulVec_xE_ne hv, coeRingHom_mem_integers_iff] at this
  have h0P : x * κ 0 ∈ P0.1 := by simpa using hP 0
  have h1P : y * κ 0 + κ 1 ∈ P0.1 := by simpa using hP 1
  obtain ⟨c, d, hcd⟩ := exists_eq_add_mul_x_of_mul_x_mem (hv 0) h0P
  obtain ⟨c₂, d₂, hcd₂⟩ := exists_eq_add_mul_x_of_mul_x_mem (hv 1) (by
    rw [show x * κ 1 = x * (y * κ 0 + κ 1) - y * (x * κ 0) by ring]
    exact sub_mem (mul_mem x_mem_P0 h1P) (mul_mem y_mem_P0 h0P))
  have e : algebraMap (ZMod 2) K c * y + algebraMap (ZMod 2) K c₂ =
      x * ((y * κ 0 + κ 1) - (algebraMap (ZMod 2) K d * y + algebraMap (ZMod 2) K d₂)) := by
    linear_combination (-y) * hcd - hcd₂
  have hval : P0.1.valuation (algebraMap (ZMod 2) K c * y + algebraMap (ZMod 2) K c₂) < 1 := by
    rw [e, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (valuation_le_one_P0 (sub_mem h1P
      (add_mem (mul_mem (algebraMap_mem_place P0 d) y_mem_P0) (algebraMap_mem_place P0 d₂)))))
      valuation_x_P0
  obtain ⟨rfl, rfl⟩ := eq_zero_of_valuation_P0_lt hval
  have hk : ∀ {k : K} {d : ZMod 2},
      x * k = algebraMap (ZMod 2) K 0 + algebraMap (ZMod 2) K d * x →
        ∃ d, k = algebraMap (ZMod 2) K d := fun {_ d} h =>
    ⟨d, mul_left_cancel₀ x_ne_zero (by rw [h, map_zero, zero_add, mul_comm])⟩
  exact Fin.forall_fin_two.2 ⟨hk hcd, hk hcd₂⟩

/-- A matrix with entries in a subring maps vectors with entries in the subring to such vectors. -/
private theorem mulVec_mem_of_forall_mem (S : Subring (AdeleRing K))
    {M : Matrix (Fin 2) (Fin 2) (AdeleRing K)} {ξ : Fin 2 → AdeleRing K}
    (hM : ∀ i j, M i j ∈ S) (hξ : ∀ i, ξ i ∈ S) (i : Fin 2) : (M *ᵥ ξ) i ∈ S := by
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  exact add_mem (mul_mem (hM _ _) (hξ _)) (mul_mem (hM _ _) (hξ _))

/-- A matrix with entries in a subring has determinant in the subring. -/
private theorem det_mem_of_forall_mem (S : Subring (AdeleRing K))
    {M : Matrix (Fin 2) (Fin 2) (AdeleRing K)} (hM : ∀ i j, M i j ∈ S) : M.det ∈ S := by
  rw [Matrix.det_fin_two]
  exact sub_mem (mul_mem (hM 0 0) (hM 1 1)) (mul_mem (hM 0 1) (hM 1 0))

/-- If `g' g = 1` in `GL₂(A)`, then `g'` undoes the action of `g` on `A²`. -/
private theorem mulVec_mulVec_of_mul_eq_one {g' g : GL (Fin 2) (AdeleRing K)} (h : g' * g = 1)
    (ξ : Fin 2 → AdeleRing K) :
    (g' : Matrix (Fin 2) (Fin 2) (AdeleRing K)) *ᵥ
      ((g : Matrix (Fin 2) (Fin 2) (AdeleRing K)) *ᵥ ξ) = ξ := by
  rw [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, h,
    Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]

/-- Integral vectors. -/
public def IntVec (w : Fin 2 → AdeleRing K) : Prop := ∀ i, w i ∈ integralAdeles K

/-- An integral matrix maps integral vectors to integral vectors. -/
public theorem IntVec.mulVec {M : Matrix (Fin 2) (Fin 2) (AdeleRing K)} (hM : IsIntMat M)
    {w : Fin 2 → AdeleRing K} (hw : IntVec w) : IntVec (M *ᵥ w) :=
  mulVec_mem_of_forall_mem _ hM hw

/-- The lattice of `g` is unchanged by left multiplication by an element of `GL₂(O)`. -/
public theorem isLat_mapO_mul (κ : GL (Fin 2) (integralAdeles K)) (g : GL (Fin 2) (AdeleRing K))
    (ξ : Fin 2 → AdeleRing K) : IsLat (mapO κ * g) ξ ↔ IsLat g ξ := by
  have e' : ((mapO κ * g : GL (Fin 2) (AdeleRing K)) : Matrix (Fin 2) (Fin 2) (AdeleRing K)) *ᵥ ξ =
      (mapO κ : Matrix (Fin 2) (Fin 2) (AdeleRing K)) *ᵥ
        (g : Matrix (Fin 2) (Fin 2) (AdeleRing K)) *ᵥ ξ := by
    rw [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul]
  have e : (g : Matrix (Fin 2) (Fin 2) (AdeleRing K)) *ᵥ ξ =
      (mapO κ⁻¹ : Matrix (Fin 2) (Fin 2) (AdeleRing K)) *ᵥ
        ((mapO κ * g : GL (Fin 2) (AdeleRing K)) : Matrix (Fin 2) (Fin 2) (AdeleRing K)) *ᵥ ξ := by
    rw [e']
    exact (mulVec_mulVec_of_mul_eq_one (by simp : mapO κ⁻¹ * mapO κ = 1) _).symm
  refine and_congr_right' ⟨fun h => ?_, fun h => ?_⟩
  · rw [e]
    exact IntVec.mulVec (isIntMat_mapO κ⁻¹) h
  · rw [e']
    exact IntVec.mulVec (isIntMat_mapO κ) h

/-- The lattice of `g` is unchanged by left multiplication by an integral unit scalar. -/
public theorem isLat_scalarGL_mul {o : (AdeleRing K)ˣ} (ho : IsIntUnit o)
    (g : GL (Fin 2) (AdeleRing K)) (ξ : Fin 2 → AdeleRing K) :
    IsLat (scalarGL o * g) ξ ↔ IsLat g ξ := by
  obtain ⟨κ, hκ⟩ := exists_mapO_upperGL ho ho
  rw [scalarGL_eq_upperGL, ← hκ, isLat_mapO_mul]

/-- An element of `GL₂(K)` maps vectors of principal adeles to vectors of principal adeles. -/
public theorem principal_mulVec_mapK (γ : GL (Fin 2) (principalAdeles K)) {ξ : Fin 2 → AdeleRing K}
    (hξ : ∀ i, ξ i ∈ principalAdeles K) :
    ∀ i, ((mapK γ : Matrix (Fin 2) (Fin 2) (AdeleRing K)) *ᵥ ξ) i ∈ principalAdeles K :=
  mulVec_mem_of_forall_mem _ (fun i j => by rw [coe_mapK_apply]; exact (γ i j).2) hξ

/-- For `γ ∈ GL₂(K)`, `ξ` lies in the lattice of `g γ` if and only if `γ ξ` lies in the lattice of
`g`. -/
public theorem isLat_mul_mapK (g : GL (Fin 2) (AdeleRing K)) (γ : GL (Fin 2) (principalAdeles K))
    (ξ : Fin 2 → AdeleRing K) :
    IsLat (g * mapK γ) ξ ↔ IsLat g ((mapK γ : Matrix (Fin 2) (Fin 2) (AdeleRing K)) *ᵥ ξ) := by
  have e : ((g * mapK γ : GL (Fin 2) (AdeleRing K)) : Matrix (Fin 2) (Fin 2) (AdeleRing K)) *ᵥ ξ =
      (g : Matrix (Fin 2) (Fin 2) (AdeleRing K)) *ᵥ
        ((mapK γ : Matrix (Fin 2) (Fin 2) (AdeleRing K)) *ᵥ ξ) := by
    rw [Matrix.mulVec_mulVec, Matrix.GeneralLinearGroup.coe_mul]
  have e2 : ξ = (mapK γ⁻¹ : Matrix (Fin 2) (Fin 2) (AdeleRing K)) *ᵥ
      ((mapK γ : Matrix (Fin 2) (Fin 2) (AdeleRing K)) *ᵥ ξ) := by
    exact (mulVec_mulVec_of_mul_eq_one (by simp : mapK γ⁻¹ * mapK γ = 1) _).symm
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨principal_mulVec_mapK γ h1, fun i => by have := h2 i; rwa [e] at this⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => ?_, fun i => ?_⟩
    · rw [e2]
      exact principal_mulVec_mapK γ⁻¹ h1 i
    · rw [e]
      exact h2 i

/-- Applying `σ` to the entries of `g` conjugates the action of `g` on `A²` by `σ`. -/
public theorem mulVec_glMap (σ : K ≃+* K) (g : GL (Fin 2) (AdeleRing K)) (ξ : Fin 2 → AdeleRing K)
    (i : Fin 2) : ((glMap σ g : Matrix (Fin 2) (Fin 2) (AdeleRing K)) *ᵥ ξ) i =
      adeleMap σ
        (((g : Matrix (Fin 2) (Fin 2) (AdeleRing K)) *ᵥ fun j => adeleMap σ.symm (ξ j)) i) := by
  rw [Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct, Fin.sum_univ_two, Fin.sum_univ_two,
    map_add, map_mul, map_mul, glMap_apply, glMap_apply, adeleMap_adeleMap_symm,
    adeleMap_adeleMap_symm]

/-- `ξ` lies in the lattice of `σ(g)` if and only if `σ⁻¹(ξ)` lies in the lattice of `g`. -/
public theorem isLat_glMap (σ : K ≃+* K) (g : GL (Fin 2) (AdeleRing K)) (ξ : Fin 2 → AdeleRing K) :
    IsLat (glMap σ g) ξ ↔ IsLat g fun j => adeleMap σ.symm (ξ j) := by
  refine and_congr (forall_congr' fun i => ?_) (forall_congr' fun i => ?_)
  · exact (adeleMap_mem_principalAdeles_iff σ.symm).symm
  · rw [mulVec_glMap, adeleMap_mem_integralAdeles_iff]

/-- The lattice of `x_E` consists of the vectors of constant adeles `cst d`, `d ∈ 𝔽₂`. -/
public theorem isLat_xE_iff' (ξ : Fin 2 → AdeleRing K) :
    IsLat xE ξ ↔ ∀ i, ∃ d : ZMod 2, ξ i = cst d := by
  constructor
  · intro h
    choose κ hκ using fun i => h.1 i
    have hξ : ξ = fun i => diag (ZMod 2) K (κ i) := funext fun i =>
      RestrictedProduct.ext _ _ fun v => hκ i v
    rw [hξ, isLat_xE_iff] at h
    intro i
    obtain ⟨d, hd⟩ := h i
    exact ⟨d, (congrFun hξ i).trans (by simp only [hd])⟩
  · intro h
    choose d hd using h
    rw [show ξ = fun i => diag (ZMod 2) K (algebraMap (ZMod 2) K (d i)) from funext hd,
      isLat_xE_iff]
    exact fun i => ⟨d i, rfl⟩

/-- The double coset `Z(A) GL₂(O) x_E GL₂(K)`. -/
public abbrev S : Set (GL (Fin 2) (AdeleRing K)) := centralDoubleCoset xE

/-- `σ` maps the principal adele of `z` to the principal adele of `σ z`. -/
public theorem adeleMap_diag (σ : K ≃+* K) (z : K) :
    adeleMap σ (diag (ZMod 2) K z) = diag (ZMod 2) K (σ z) :=
  RestrictedProduct.ext _ _ fun w => by
    rw [adeleMap_apply, GlobalFunctionField.diag_apply, GlobalFunctionField.diag_apply]
    exact completionEquiv_coeRingHom σ (v := placeComap σ w) (w := w) rfl z

/-- A ring automorphism of `K` fixes the elements of `𝔽₂`. -/
public theorem ringEquiv_algebraMap_zmod (σ : K ≃+* K) (d : ZMod 2) :
    σ (algebraMap (ZMod 2) K d) = algebraMap (ZMod 2) K d := by
  rcases zmod_two_cases d with rfl | rfl <;> simp

/-- `σ` fixes the constant adeles. -/
public theorem adeleMap_cst (σ : K ≃+* K) (d : ZMod 2) : adeleMap σ (cst d) = cst d := by
  rw [adeleMap_diag, ringEquiv_algebraMap_zmod]

/-- The constant adele of `0 ∈ 𝔽₂` is `0`. -/
public theorem cst_zero : (cst 0 : AdeleRing K) = 0 := by simp [cst]

/-- The constant adele of `1 ∈ 𝔽₂` is `1`. -/
public theorem cst_one : (cst 1 : AdeleRing K) = 1 := by simp [cst]

/-- The component at `v` of the determinant of `g ∈ GL₂(A)`. -/
public theorem det_apply_place (g : GL (Fin 2) (AdeleRing K)) (v : Place K) :
    ((Matrix.GeneralLinearGroup.det g : (AdeleRing K)ˣ) : AdeleRing K) v =
      (g : Matrix (Fin 2) (Fin 2) (AdeleRing K)) 0 0 v *
          (g : Matrix (Fin 2) (Fin 2) (AdeleRing K)) 1 1 v -
        (g : Matrix (Fin 2) (Fin 2) (AdeleRing K)) 0 1 v *
          (g : Matrix (Fin 2) (Fin 2) (AdeleRing K)) 1 0 v := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  rfl

/-- Away from `P₀`, the determinant of `x_E` is `1`. -/
public theorem det_xE_ne {v : Place K} (hv : v ≠ P0) :
    ((Matrix.GeneralLinearGroup.det xE : (AdeleRing K)ˣ) : AdeleRing K) v = 1 := by
  rw [det_apply_place, xE_apply_ne hv, xE_apply_ne hv, xE_apply_ne hv, xE_apply_ne hv]
  simp

/-- At `P₀`, the determinant of `x_E` is `x`. -/
public theorem det_xE_P0 :
    ((Matrix.GeneralLinearGroup.det xE : (AdeleRing K)ˣ) : AdeleRing K) P0 = P0.coeRingHom x := by
  rw [det_apply_place, xE_apply_P0, xE_apply_P0, xE_apply_P0, xE_apply_P0]
  simp

/-- The determinant of `σ(g)` is `σ` applied to the determinant of `g`. -/
public theorem det_glMap (σ : K ≃+* K) (g : GL (Fin 2) (AdeleRing K)) :
    ((Matrix.GeneralLinearGroup.det (glMap σ g) : (AdeleRing K)ˣ) : AdeleRing K) =
      adeleMap σ ((Matrix.GeneralLinearGroup.det g : (AdeleRing K)ˣ) : AdeleRing K) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply,
    RingHom.map_det]
  rfl

/-- The divisor of a principal idele has norm `1`. -/
public theorem divNorm_idelDiv_of_principal {u : (AdeleRing K)ˣ}
    (hu : (u : AdeleRing K) ∈ principalAdeles K) : divNorm K (idelDiv (ZMod 2) K u) = 1 := by
  obtain ⟨z, hz⟩ := hu
  have hdz : (u : AdeleRing K) = diag (ZMod 2) K z := RestrictedProduct.ext _ _ fun v => hz v
  have hz0 : z ≠ 0 := fun h0 => by
    have h1 : (1 : AdeleRing K) = 0 := by
      rw [← Units.inv_mul u, hdz, h0, map_zero, mul_zero]
    have := congrArg (fun a : AdeleRing K => a (nonempty_place (ZMod 2) (K := K)).some) h1
    simp at this
  have : u = diagUnit (ZMod 2) hz0 := Units.ext hdz
  rw [this, idelDiv_diagUnit, divNorm_principalDivisor (ZMod 2) hz0]

/-- The determinant of an element of `GL₂(K)` is a principal adele. -/
public theorem det_mapK_mem (γ : GL (Fin 2) (principalAdeles K)) :
    ((Matrix.GeneralLinearGroup.det (mapK γ) : (AdeleRing K)ˣ) : AdeleRing K) ∈
      principalAdeles K := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  exact det_mem_of_forall_mem _ fun i j => by rw [coe_mapK_apply]; exact (γ i j).2

/-- The determinant of an element of `GL₂(O)` is an integral adele. -/
public theorem det_mapO_mem (κ : GL (Fin 2) (integralAdeles K)) :
    ((Matrix.GeneralLinearGroup.det (mapO κ) : (AdeleRing K)ˣ) : AdeleRing K) ∈
      integralAdeles K := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  exact det_mem_of_forall_mem _ (isIntMat_mapO κ)

/-- The determinant of the scalar matrix of `c` is `c * c`. -/
public theorem det_scalarGL (c : (AdeleRing K)ˣ) :
    Matrix.GeneralLinearGroup.det (scalarGL c) = c * c := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, scalarGL_eq_upperGL, coe_upperGL,
    Matrix.det_fin_two_of, mul_zero, sub_zero, Units.val_mul]

/-- The constant adele of `d ∈ 𝔽₂` is a unit if and only if `d = 1`. -/
public theorem isUnit_cst_iff (d : ZMod 2) : IsUnit (cst d : AdeleRing K) ↔ d = 1 := by
  rcases zmod_two_cases d with rfl | rfl
  · rw [cst_zero, isUnit_zero_iff]
    refine ⟨fun h => ?_, fun h => absurd h (by decide)⟩
    have := congrArg (fun a : AdeleRing K => a P0) h
    simp at this
  · simp [cst_one]

/-- The constant adele of a product is the product of the constant adeles. -/
public theorem cst_mul (d e : ZMod 2) : (cst (d * e) : AdeleRing K) = cst d * cst e := by
  simp only [cst, map_mul]

/-- The constant adele of a difference is the difference of the constant adeles. -/
public theorem cst_sub (d e : ZMod 2) : (cst (d - e) : AdeleRing K) = cst d - cst e := by
  simp only [cst, map_sub]

/-- A matrix of `GL₂(A)` mapping the constant vectors to constant vectors has constant
entries. -/
public theorem exists_cst_of_isLat_xE (N : GL (Fin 2) (AdeleRing K))
    (h : ∀ ξ : Fin 2 → AdeleRing K, (∀ i, ∃ d : ZMod 2, ξ i = cst d) →
      IsLat xE ((N : Matrix (Fin 2) (Fin 2) (AdeleRing K)) *ᵥ ξ)) (i j : Fin 2) :
    ∃ d : ZMod 2, (N : Matrix (Fin 2) (Fin 2) (AdeleRing K)) i j = cst d := by
  classical
  have hξ : ∀ i, ∃ d : ZMod 2, (Pi.single j 1 : Fin 2 → AdeleRing K) i = cst d := fun i => by
    by_cases hij : i = j
    · subst hij
      exact ⟨1, by rw [Pi.single_eq_same, cst_one]⟩
    · exact ⟨0, by rw [Pi.single_eq_of_ne hij, cst_zero]⟩
  obtain ⟨d, hd⟩ := (isLat_xE_iff' _).1 (h _ hξ) i
  refine ⟨d, ?_⟩
  rw [← hd]
  fin_cases j <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- A matrix of `GL₂(A)` mapping the constant vectors to constant vectors has determinant
`1`. -/
public theorem det_eq_one_of_isLat_xE (N : GL (Fin 2) (AdeleRing K))
    (h : ∀ ξ : Fin 2 → AdeleRing K, (∀ i, ∃ d : ZMod 2, ξ i = cst d) →
      IsLat xE ((N : Matrix (Fin 2) (Fin 2) (AdeleRing K)) *ᵥ ξ)) :
    ((Matrix.GeneralLinearGroup.det N : (AdeleRing K)ˣ) : AdeleRing K) = 1 := by
  choose d hd using exists_cst_of_isLat_xE N h
  have he : ((Matrix.GeneralLinearGroup.det N : (AdeleRing K)ˣ) : AdeleRing K) =
      cst (d 0 0 * d 1 1 - d 0 1 * d 1 0) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, hd, hd, hd, hd, cst_sub,
      cst_mul, cst_mul]
  have hu : IsUnit (cst (d 0 0 * d 1 1 - d 0 1 * d 1 0) : AdeleRing K) :=
    he ▸ (Matrix.GeneralLinearGroup.det N).isUnit
  rw [he, (isUnit_cst_iff _).1 hu, cst_one]

/-- An idele `U` equal to `σ(c)` has a divisor of the same norm as that of `c`. -/
public theorem divNorm_idelDiv_of_val_eq_adeleMap (σ : K ≃+* K) {U c : (AdeleRing K)ˣ}
    (h : (U : AdeleRing K) = adeleMap σ (c : AdeleRing K)) :
    divNorm K (idelDiv (ZMod 2) K U) = divNorm K (idelDiv (ZMod 2) K c) := by
  have : U = Units.map (adeleMap σ).toMonoidHom c := Units.ext h
  rw [this, divNorm_idelDiv_units_map_adeleMap]

/-- If `c * c * O * D * G` and `D` have divisors of the same norm, where `O` has divisor `0` and
the divisor of `G` has norm `1`, then the divisor of `c` has norm `1`. -/
public theorem divNorm_eq_one_of_mul {c O D G : (AdeleRing K)ˣ} (hO : idelDiv (ZMod 2) K O = 0)
    (hG : divNorm K (idelDiv (ZMod 2) K G) = 1)
    (h : divNorm K (idelDiv (ZMod 2) K (c * c * O * D * G)) = divNorm K (idelDiv (ZMod 2) K D)) :
    divNorm K (idelDiv (ZMod 2) K c) = 1 := by
  rw [idelDiv_mul, idelDiv_mul, idelDiv_mul, idelDiv_mul, divNorm_add (ZMod 2),
    divNorm_add (ZMod 2), divNorm_add (ZMod 2), divNorm_add (ZMod 2), hO, divNorm_zero, hG,
    mul_one, mul_one] at h
  have hpos := divNorm_pos (ZMod 2) (idelDiv (ZMod 2) K c)
  have hpe := divNorm_pos (ZMod 2) (idelDiv (ZMod 2) K D)
  have h2 : divNorm K (idelDiv (ZMod 2) K c) * divNorm K (idelDiv (ZMod 2) K c) = 1 := by
    rwa [mul_left_eq_self₀, or_iff_left hpe.ne'] at h
  nlinarith

/-- The determinant of `α(x_E) ∈ c GL₂(O) x_E GL₂(K)` forces `|div c| = 1`. -/
public theorem divNorm_idelDiv_eq_one_of_glMap_alpha_xE {c : (AdeleRing K)ˣ}
    {κ : GL (Fin 2) (integralAdeles K)} {γ : GL (Fin 2) (principalAdeles K)}
    (he : glMap alpha xE = scalarGL c * mapO κ * xE * mapK γ) :
    divNorm K (idelDiv (ZMod 2) K c) = 1 := by
  have hα := divNorm_idelDiv_of_val_eq_adeleMap alpha (det_glMap alpha xE)
  have hdet3 : Matrix.GeneralLinearGroup.det (glMap alpha xE) =
      c * c * Matrix.GeneralLinearGroup.det (mapO κ) * Matrix.GeneralLinearGroup.det xE *
        Matrix.GeneralLinearGroup.det (mapK γ) :=
    (congrArg Matrix.GeneralLinearGroup.det he).trans (by simp only [map_mul, det_scalarGL])
  exact divNorm_eq_one_of_mul (idelDiv_det_mapO (ZMod 2) κ)
    (divNorm_idelDiv_of_principal (det_mapK_mem γ))
    ((congrArg (fun u => divNorm K (idelDiv (ZMod 2) K u)) hdet3).symm.trans hα)

/-- An idele of norm `1` is an integral unit times a principal idele (class number one). -/
public theorem exists_isIntUnit_isPrincUnit_of_divNorm {c : (AdeleRing K)ˣ}
    (hc1 : divNorm K (idelDiv (ZMod 2) K c) = 1) :
    ∃ o d : (AdeleRing K)ˣ, IsIntUnit o ∧ IsPrincUnit d ∧ c = o * d := by
  obtain ⟨κ₀, hκ₀, hdivc⟩ := exists_principalDivisor_eq hc1
  refine ⟨c * (diagUnit (ZMod 2) hκ₀)⁻¹, diagUnit (ZMod 2) hκ₀, ?_, ?_, by group⟩
  · have ho0 : idelDiv (ZMod 2) K (c * (diagUnit (ZMod 2) hκ₀)⁻¹) = 0 := by
      rw [idelDiv_mul, idelDiv_inv, idelDiv_diagUnit, hdivc, add_neg_cancel]
    obtain ⟨o', ho'⟩ := exists_integralUnit_of_idelDiv_eq_zero (ZMod 2) ho0
    refine ⟨ho' ▸ (o' : integralAdeles K).2, ?_⟩
    have : (((c * (diagUnit (ZMod 2) hκ₀)⁻¹)⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) =
        ((o'⁻¹ : (integralAdeles K)ˣ) : integralAdeles K) :=
      Units.inv_eq_of_mul_eq_one_right (by rw [← ho']; exact congrArg Subtype.val o'.mul_inv)
    rw [this]; exact (o'⁻¹ : (integralAdeles K)ˣ).1.2
  · refine ⟨⟨κ₀, fun v => rfl⟩, ⟨κ₀⁻¹, fun v => ?_⟩⟩
    have : (((diagUnit (ZMod 2) hκ₀)⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) = diag (ZMod 2) K κ₀⁻¹ :=
      Units.inv_eq_of_mul_eq_one_right
        (by rw [coe_diagUnit, ← map_mul, mul_inv_cancel₀ hκ₀, map_one])
    rw [this]; rfl

/-- If `a` is `1` at `σ⁻¹(w)`, then `σ(a)` is `1` at `w`. -/
public theorem adeleMap_apply_eq_one {σ : K ≃+* K} {a : AdeleRing K} {w : Place K}
    (h : a (placeComap σ w) = 1) : adeleMap σ a w = 1 := by
  rw [adeleMap_apply, h, map_one]

/-- The component at `v` of a product of four adeles. -/
public theorem mul_mul_mul_apply (a b c d : AdeleRing K) (v : Place K) :
    (a * b * (c * d)) v = (a v * b v) * (c v * d v) := by
  simp only [RestrictedProduct.mul_apply]

/-- The final contradiction: valuations at `P₀`. -/
public theorem false_of_one_eq_mul {u u' : P0.completion} (hu : Valued.v u ≤ 1)
    (hu' : Valued.v u' ≤ 1) (h : (1 : P0.completion) = (u * u) * (u' * P0.coeRingHom x)) :
    False := by
  have hv := congrArg Valued.v h
  rw [map_one, map_mul, map_mul, map_mul, Place.valued_coeRingHom] at hv
  refine lt_irrefl (1 : P0.1.ValueGroup) ?_
  calc (1 : P0.1.ValueGroup) = _ := hv
    _ ≤ P0.1.valuation x := by
        rw [← mul_assoc]
        exact mul_le_of_le_one_left' (mul_le_one' (mul_le_one' hu hu) hu')
    _ < 1 := valuation_x_P0

/-- `α(x_E)` is not of the form `o κ x_E γ` with `o` an integral unit. -/
public theorem glMap_alpha_xE_ne {o : (AdeleRing K)ˣ} (ho : IsIntUnit o)
    (κ : GL (Fin 2) (integralAdeles K)) (γ : GL (Fin 2) (principalAdeles K)) :
    glMap alpha xE ≠ scalarGL o * (mapO κ * xE * mapK γ) := by
  intro he2
  have hlat : ∀ ξ : Fin 2 → AdeleRing K, (∀ i, ∃ d : ZMod 2, ξ i = cst d) →
      IsLat xE ((mapK γ : Matrix (Fin 2) (Fin 2) (AdeleRing K)) *ᵥ ξ) := by
    intro ξ hξ
    have h1 : IsLat xE fun j => adeleMap alpha.symm (ξ j) := by
      rw [isLat_xE_iff']
      intro i
      obtain ⟨d, hd⟩ := hξ i
      exact ⟨d, by rw [hd, adeleMap_cst]⟩
    have h2 : IsLat (glMap alpha xE) ξ := (isLat_glMap alpha xE ξ).2 h1
    have h3 : IsLat (scalarGL o * (mapO κ * xE * mapK γ)) ξ :=
      Eq.mp (congrArg (fun g => IsLat g ξ) he2) h2
    exact (isLat_mapO_mul κ xE _).1 ((isLat_mul_mapK (mapO κ * xE) γ ξ).1
      ((isLat_scalarGL_mul ho _ ξ).1 h3))
  have hN1 := det_eq_one_of_isLat_xE _ hlat
  have hL : ((Matrix.GeneralLinearGroup.det (glMap alpha xE) : (AdeleRing K)ˣ) : AdeleRing K) P0 =
      1 := (congrArg (fun a : AdeleRing K => a P0) (det_glMap alpha xE)).trans
        (adeleMap_apply_eq_one (det_xE_ne placeComap_alpha_P0_ne))
  have hR : ((Matrix.GeneralLinearGroup.det (scalarGL o * (mapO κ * xE * mapK γ)) :
      (AdeleRing K)ˣ) : AdeleRing K) = (o : AdeleRing K) * o *
        (((Matrix.GeneralLinearGroup.det (mapO κ) : (AdeleRing K)ˣ) : AdeleRing K) *
          ((Matrix.GeneralLinearGroup.det xE : (AdeleRing K)ˣ) : AdeleRing K)) := by
    simp only [map_mul, det_scalarGL, Units.val_mul, hN1, mul_one]
  have hR' := (congrArg (fun g : GL (Fin 2) (AdeleRing K) =>
    ((Matrix.GeneralLinearGroup.det g : (AdeleRing K)ˣ) : AdeleRing K) P0) he2).trans
      ((congrArg (fun a : AdeleRing K => a P0) hR).trans (mul_mul_mul_apply _ _ _ _ P0))
  refine false_of_one_eq_mul (ho.1 P0) (det_mapO_mem κ P0) ?_
  refine hL.symm.trans (hR'.trans ?_)
  rw [det_xE_P0]

section Generic

variable {L : Type*} [Field L]

/-- If `g = c A X γ` with `c = o d` and `γ₀ ∈ GL₂(K)` the scalar matrix of `d`, then
`g = o (A X (γ γ₀))`: the principal factor of the scalar moves into the `GL₂(K)` factor. -/
public theorem eq_scalarGL_mul_mapK_of_eq {g A X : GL (Fin 2) (AdeleRing L)}
    {c o d : (AdeleRing L)ˣ}
    {γ γ₀ : GL (Fin 2) (principalAdeles L)} (he : g = scalarGL c * A * X * mapK γ)
    (hc : c = o * d) (hγ₀ : mapK γ₀ = upperGL d d 0) :
    g = scalarGL o * (A * X * mapK (γ * γ₀)) := by
  rw [he, hc, map_mul, map_mul, hγ₀, ← scalarGL_eq_upperGL]
  simp only [mul_assoc]
  congr 1
  rw [scalarGL_mul_comm d]
  simp only [mul_assoc]

end Generic

/-- **`α` moves `x_E` out of the double coset `S`.** -/
public theorem glMap_alpha_xE_notMem : glMap alpha xE ∉ S := by
  intro hS
  obtain ⟨c, κ, γ, he⟩ := hS
  obtain ⟨o, d, ho, hd, hc⟩ :=
    exists_isIntUnit_isPrincUnit_of_divNorm (divNorm_idelDiv_eq_one_of_glMap_alpha_xE he)
  obtain ⟨γ₀, hγ₀⟩ := exists_mapK_upperGL hd hd
  exact glMap_alpha_xE_ne ho κ (γ * γ₀) (eq_scalarGL_mul_mapK_of_eq he hc hγ₀)

/-- **A nonzero unramified cusp form on `y² + y = x³ + x + 1`.** For `Ω` algebraically closed of
characteristic `≠ 2`, the module `C(Ω)` of unramified cusp forms on `GL₂` over `K` with
`q_v · U_v f = f` at every place is nonzero. -/
public theorem cuspFormsCentralChar_ne_bot {Ω : Type*} [Field Ω] [IsAlgClosed Ω]
    (hp : IsUnit (ringChar (ZMod 2) : Ω)) : cuspFormsCentralChar K Ω ≠ ⊥ := by
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq ((Nat.card (ZMod 2) : ℕ) : Ω) two_pos
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero, Nat.card_zmod] at hc
    rw [ZMod.ringChar_zmod_n] at hp
    exact hp.ne_zero hc.symm
  exact cuspFormsCentralChar_ne_bot_of_glMap_notMem (ZMod 2) alpha
    (exists_isIntUnit_isPrincUnit (ZMod 2) alpha fun _ hD => exists_principalDivisor_eq hD)
    glMap_alpha_xE_notMem hp (c := Units.mk0 c hc0) hc

end Stacks.Drinfeld.SupersingularCurve

end
