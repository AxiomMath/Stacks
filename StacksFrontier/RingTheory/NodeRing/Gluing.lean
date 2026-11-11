module

public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Transvection
public import StacksFrontier.RingTheory.NodalCurve

/-!
# Finite projective modules over the node ring

Let `k` be a field and let `R = {f ∈ k[x] ∣ f(0) = f(1)}` be the node ring (`nodeRing k`).
For a square matrix `φ` over `k` indexed by a finite type `ι`, the *glued module*

`glued φ = {v ∈ k[x]^ι ∣ v(1) = φ · v(0)}`

is an `R`-submodule of `k[x]^ι`: it is the module obtained from the free `k[x]`-module `k[x]^ι`
by identifying its fibres at `0` and `1` through `φ`. This file shows:

* `NodeRing.exists_linearEquiv_glued`: every finite projective `R`-module is isomorphic to
  `glued φ` for some `n` and some `φ ∈ GL_n(k)`;
* `NodeRing.card_eq_and_det_eq_of_linearEquiv`: if `glued φ ≅ glued ψ` with `φ, ψ` invertible,
  then `φ` and `ψ` have the same size and the same determinant;
* `NodeRing.gluedEquivOfConj`: `glued φ ≅ glued ψ` whenever `G(1) φ = ψ G(0)` for a matrix `G`
  over `k[x]` with unit determinant;
* `NodeRing.exists_gluedEquiv_diagonal`: every `glued φ` with `φ` invertible is isomorphic to
  `glued (diagonal D)` with `∏ D = det φ`, so it is a direct sum of the line bundles
  `lineMod u = {f ∣ f(1) = u f(0)}`;
* `NodeRing.lineModProdEquiv`: `L_u ⊕ L_v ≅ L_{uv} ⊕ R` for `u ≠ 0`.

These are the module-theoretic inputs for the computation `K₀(R) ≅ k^* ⊕ ℤ` of
Stacks, Example 10.55.5 (tag `00JG`).
-/

@[expose] public noncomputable section

open Polynomial Matrix

namespace NodeRing

variable {k : Type*} [Field k]

/-! ### Evaluating vectors and matrices of polynomials -/

/-- Evaluate a vector of polynomials at `a`. -/
def evalVec {ι : Type*} (a : k) (v : ι → k[X]) : ι → k := fun i => (v i).eval a

@[simp]
lemma evalVec_apply {ι : Type*} (a : k) (v : ι → k[X]) (i : ι) :
    evalVec a v i = (v i).eval a := rfl

lemma evalVec_add {ι : Type*} (a : k) (v w : ι → k[X]) :
    evalVec a (v + w) = evalVec a v + evalVec a w := by
  funext i; simp

lemma evalVec_zero {ι : Type*} (a : k) : evalVec a (0 : ι → k[X]) = 0 := by
  funext i; simp

lemma evalVec_smul {ι : Type*} (a : k) (r : nodeRing k) (v : ι → k[X]) :
    evalVec a (r • v) = (r : k[X]).eval a • evalVec a v := by
  funext i; simp [Subring.smul_def]

lemma evalVec_single {ι : Type*} [DecidableEq ι] (a : k) (j : ι) (p : k[X]) :
    evalVec a (Pi.single j p) = Pi.single j (p.eval a) := by
  funext i
  rcases eq_or_ne i j with rfl | hij
  · simp
  · simp [hij]

lemma evalVec_mulVec {ι ι' : Type*} [Fintype ι] (a : k) (G : Matrix ι' ι k[X])
    (v : ι → k[X]) : evalVec a (G *ᵥ v) = G.map (eval a) *ᵥ evalVec a v := by
  funext i
  have := RingHom.map_mulVec (evalRingHom a) G v i
  simp only [coe_evalRingHom] at this
  exact this

lemma map_eval_mul {l m n : Type*} [Fintype m] (a : k) (G : Matrix l m k[X])
    (H : Matrix m n k[X]) : (G * H).map (eval a) = G.map (eval a) * H.map (eval a) := by
  simpa using Matrix.map_mul (L := G) (M := H) (f := evalRingHom a)

lemma map_eval_one {n : Type*} [DecidableEq n] (a : k) :
    (1 : Matrix n n k[X]).map (eval a) = 1 :=
  Matrix.map_one _ (eval_zero) (eval_one)

/-- Two matrices are equal if they agree on every vector. -/
lemma matrix_eq_of_mulVec_eq {α : Type*} [CommRing α] {m n : Type*} [Fintype n]
    {M N : Matrix m n α} (h : ∀ w, M *ᵥ w = N *ᵥ w) : M = N := by
  classical
  ext i j
  simpa [mulVec_single_one] using congrFun (h (Pi.single j 1)) i

/-! ### The element `s = x(x - 1)` -/

lemma X_mul_X_sub_one_ne_zero : (X * (X - 1) : k[X]) ≠ 0 :=
  mul_ne_zero X_ne_zero (by simpa using X_sub_C_ne_zero (1 : k))

lemma eval_zero_X_mul_X_sub_one : (X * (X - 1) : k[X]).eval 0 = 0 := by simp

lemma eval_one_X_mul_X_sub_one : (X * (X - 1) : k[X]).eval 1 = 0 := by simp

/-- A polynomial vanishing at `0` and `1` is divisible by `x(x - 1)`. -/
lemma X_mul_X_sub_one_dvd {a : k[X]} (h0 : a.eval 0 = 0) (h1 : a.eval 1 = 0) :
    X * (X - 1) ∣ a := by
  have hX : X ∣ a := by rw [X_dvd_iff, coeff_zero_eq_eval_zero]; exact h0
  obtain ⟨b, rfl⟩ := hX
  have hb : b.eval 1 = 0 := by simpa using h1
  have : X - C 1 ∣ b := dvd_iff_isRoot.mpr hb
  rw [C_1] at this
  exact mul_dvd_mul_left X this

/-! ### The glued modules -/

/-- The *glued module* `glued φ = {v ∈ k[x]^ι ∣ v(1) = φ · v(0)}` attached to a square matrix
`φ` over `k`, as a module over the node ring. -/
def glued {ι : Type*} [Fintype ι] (φ : Matrix ι ι k) : Submodule (nodeRing k) (ι → k[X]) where
  carrier := {v | evalVec 1 v = φ *ᵥ evalVec 0 v}
  add_mem' {v w} hv hw := by
    simp only [Set.mem_ofPred_eq] at hv hw ⊢
    rw [evalVec_add, evalVec_add, hv, hw, mulVec_add]
  zero_mem' := by simp [evalVec_zero]
  smul_mem' r v hv := by
    simp only [Set.mem_ofPred_eq] at hv ⊢
    rw [evalVec_smul, evalVec_smul, hv, mulVec_smul, (mem_nodeRing_iff _).1 r.2]

variable {ι ι' : Type*} [Fintype ι] [Fintype ι']

lemma mem_glued {φ : Matrix ι ι k} {v : ι → k[X]} :
    v ∈ glued φ ↔ evalVec 1 v = φ *ᵥ evalVec 0 v := Iff.rfl

lemma mem_glued_of_evalVec_eq_zero {φ : Matrix ι ι k} {v : ι → k[X]}
    (h0 : evalVec 0 v = 0) (h1 : evalVec 1 v = 0) : v ∈ glued φ := by
  rw [mem_glued, h0, h1, mulVec_zero]

lemma single_mem_glued [DecidableEq ι] (φ : Matrix ι ι k) (j : ι) {p : k[X]}
    (h0 : p.eval 0 = 0) (h1 : p.eval 1 = 0) : Pi.single j p ∈ glued φ :=
  mem_glued_of_evalVec_eq_zero (by rw [evalVec_single, h0, Pi.single_zero])
    (by rw [evalVec_single, h1, Pi.single_zero])

/-- Multiplication by a matrix `G` over `k[x]` maps `glued φ` to `glued ψ` when
`G(1) φ = ψ G(0)`. -/
lemma mulVec_mem_glued {φ : Matrix ι ι k} {ψ : Matrix ι' ι' k} (G : Matrix ι' ι k[X])
    (h : G.map (eval 1) * φ = ψ * G.map (eval 0)) {v : ι → k[X]} (hv : v ∈ glued φ) :
    G *ᵥ v ∈ glued ψ := by
  rw [mem_glued] at hv ⊢
  rw [evalVec_mulVec, evalVec_mulVec, hv, mulVec_mulVec, h, ← mulVec_mulVec]

/-- The `R`-linear map `glued φ → glued ψ` given by multiplication by `G`. -/
def gluedMap {φ : Matrix ι ι k} {ψ : Matrix ι' ι' k} (G : Matrix ι' ι k[X])
    (h : G.map (eval 1) * φ = ψ * G.map (eval 0)) : glued φ →ₗ[nodeRing k] glued ψ where
  toFun v := ⟨G *ᵥ (v : ι → k[X]), mulVec_mem_glued G h v.2⟩
  map_add' v w := Subtype.ext (by simp [mulVec_add])
  map_smul' r v := Subtype.ext (by simp [mulVec_smul])

@[simp]
lemma coe_gluedMap {φ : Matrix ι ι k} {ψ : Matrix ι' ι' k} (G : Matrix ι' ι k[X])
    (h : G.map (eval 1) * φ = ψ * G.map (eval 0)) (v : glued φ) :
    ((gluedMap G h v : glued ψ) : ι' → k[X]) = G *ᵥ (v : ι → k[X]) := rfl

/-- **Conjugation.** If `G` is a matrix over `k[x]` with unit determinant and
`G(1) φ = ψ G(0)`, then `glued φ ≅ glued ψ`. -/
def gluedEquivOfConj [DecidableEq ι] {φ ψ : Matrix ι ι k} (G : Matrix ι ι k[X])
    (hG : IsUnit G.det) (h : G.map (eval 1) * φ = ψ * G.map (eval 0)) :
    glued φ ≃ₗ[nodeRing k] glued ψ :=
  have h1 : (G⁻¹).map (eval 1) * G.map (eval 1) = 1 := by
    rw [← map_eval_mul, nonsing_inv_mul G hG, map_eval_one]
  have h0 : G.map (eval 0) * (G⁻¹).map (eval 0) = 1 := by
    rw [← map_eval_mul, mul_nonsing_inv G hG, map_eval_one]
  have h' : (G⁻¹).map (eval 1) * ψ = φ * (G⁻¹).map (eval 0) := by
    calc (G⁻¹).map (eval 1) * ψ
        = (G⁻¹).map (eval 1) * ψ * (G.map (eval 0) * (G⁻¹).map (eval 0)) := by
          rw [h0, Matrix.mul_one]
      _ = (G⁻¹).map (eval 1) * (ψ * G.map (eval 0)) * (G⁻¹).map (eval 0) := by
          simp only [Matrix.mul_assoc]
      _ = (G⁻¹).map (eval 1) * (G.map (eval 1) * φ) * (G⁻¹).map (eval 0) := by rw [h]
      _ = φ * (G⁻¹).map (eval 0) := by
          rw [← Matrix.mul_assoc ((G⁻¹).map (eval 1)), h1, Matrix.one_mul]
  LinearEquiv.ofLinearMap (gluedMap G h) (gluedMap G⁻¹ h')
    (LinearMap.ext fun v => Subtype.ext (by
      simp [mulVec_mulVec, mul_nonsing_inv G hG]))
    (LinearMap.ext fun v => Subtype.ext (by
      simp [mulVec_mulVec, nonsing_inv_mul G hG]))

/-! ### Lifting vectors from the fibre at `0` -/

/-- The vector `w + x (φ w - w)`, an element of `glued φ` with value `w` at `0`. -/
def liftVec (φ : Matrix ι ι k) (w : ι → k) : ι → k[X] :=
  fun i => C (w i) + C ((φ *ᵥ w) i - w i) * X

lemma evalVec_zero_liftVec (φ : Matrix ι ι k) (w : ι → k) :
    evalVec 0 (liftVec φ w) = w := by
  funext i; simp [liftVec]

lemma evalVec_one_liftVec (φ : Matrix ι ι k) (w : ι → k) :
    evalVec 1 (liftVec φ w) = φ *ᵥ w := by
  funext i; simp [liftVec]

lemma liftVec_mem_glued (φ : Matrix ι ι k) (w : ι → k) : liftVec φ w ∈ glued φ := by
  rw [mem_glued, evalVec_one_liftVec, evalVec_zero_liftVec]

/-! ### Linear maps out of a glued module are given by matrices -/

omit [Fintype ι'] in
/-- Every `R`-linear map `glued φ → k[x]^ι'` (with `φ` invertible) is multiplication by a
matrix over `k[x]`. -/
theorem exists_matrix_eq_of_linearMap [DecidableEq ι] {φ : Matrix ι ι k} (hφ : IsUnit φ.det)
    (f : glued φ →ₗ[nodeRing k] (ι' → k[X])) :
    ∃ G : Matrix ι' ι k[X], ∀ v : glued φ, f v = G *ᵥ (v : ι → k[X]) := by
  classical
  set s : k[X] := X * (X - 1) with hs
  have hs0 : s ≠ 0 := X_mul_X_sub_one_ne_zero
  have hs0' : s.eval 0 = 0 := eval_zero_X_mul_X_sub_one
  have hs1' : s.eval 1 = 0 := eval_one_X_mul_X_sub_one
  let sR : nodeRing k := ⟨s, X_mul_X_sub_one_mem_nodeRing k⟩
  let tR : nodeRing k := ⟨s * X, Stacks.NodalCurve.mul_mem_nodeRing k X⟩
  let e : ι → glued φ := fun j => ⟨Pi.single j s, single_mem_glued φ j hs0' hs1'⟩
  let e' : ι → glued φ := fun j =>
    ⟨Pi.single j (s * X), single_mem_glued φ j (by simp [hs0']) (by simp [hs1'])⟩
  let g : ι → ι' → k[X] := fun j => f (e j)
  -- `f (s x e_j) = x f (s e_j)`
  have h1 : ∀ j i, f (e' j) i = X * g j i := by
    intro j i
    have key : sR • e' j = tR • e j := by
      refine Subtype.ext (funext fun l => ?_)
      rcases eq_or_ne l j with rfl | hl
      · simp [e, e', sR, tR, Subring.smul_def]; ring
      · simp [e, e', sR, tR, Subring.smul_def, hl]
    have hi := congrFun (congrArg f key) i
    rw [f.map_smul, f.map_smul] at hi
    simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul, sR, tR] at hi
    apply mul_left_cancel₀ hs0
    rw [hi, ← mul_assoc]
  -- `s f(v) = G' v`
  let G' : Matrix ι' ι k[X] := Matrix.of fun i j => g j i
  have h2 : ∀ v : glued φ, ∀ i, s * f v i = (G' *ᵥ (v : ι → k[X])) i := by
    intro v i
    let c : ι → k := fun j => ((v : ι → k[X]) j).eval 1 - ((v : ι → k[X]) j).eval 0
    have hr : ∀ j, (v : ι → k[X]) j - C (c j) * X ∈ nodeRing k := by
      intro j; rw [mem_nodeRing_iff]; simp [c]
    let r : ι → nodeRing k := fun j => ⟨_, hr j⟩
    let cR : ι → nodeRing k := fun j => Stacks.NodalCurve.constToNodeRing k (c j)
    have hcR : ∀ j, (cR j : k[X]) = C (c j) := fun j => rfl
    have hdecomp : sR • v = ∑ j, (r j • e j + cR j • e' j) := by
      refine Subtype.ext (funext fun l => ?_)
      simp only [SetLike.val_smul, Subring.smul_def, Submodule.coe_sum, Submodule.coe_add,
        Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, e, e', sR, r, hcR]
      rw [Finset.sum_eq_single l]
      · simp; ring
      · intro j _ hj; simp [Ne.symm hj]
      · simp
    have hi := congrFun (congrArg f hdecomp) i
    rw [map_sum, f.map_smul] at hi
    simp only [map_add, f.map_smul, Finset.sum_apply, Pi.add_apply, Pi.smul_apply,
      Subring.smul_def, smul_eq_mul, sR, h1, hcR] at hi
    rw [hi]
    simp only [mulVec, dotProduct, G', Matrix.of_apply, r, g]
    refine Finset.sum_congr rfl fun j _ => ?_
    have : (v : ι → k[X]) j = ((v : ι → k[X]) j - C (c j) * X) + C (c j) * X := by ring
    conv_rhs => rw [this]
    ring
  -- `G'` vanishes at `0` and at `1`
  have hG0 : G'.map (eval 0) = 0 := by
    refine matrix_eq_of_mulVec_eq fun w => ?_
    rw [zero_mulVec, ← evalVec_zero_liftVec φ w, ← evalVec_mulVec]
    funext i
    rw [evalVec_apply, ← h2 ⟨liftVec φ w, liftVec_mem_glued φ w⟩ i]
    simp [hs0']
  have hG1 : G'.map (eval 1) = 0 := by
    refine matrix_eq_of_mulVec_eq fun w => ?_
    have hw : w = φ *ᵥ (φ⁻¹ *ᵥ w) := by rw [mulVec_mulVec, mul_nonsing_inv φ hφ, one_mulVec]
    rw [zero_mulVec, hw, ← evalVec_one_liftVec φ (φ⁻¹ *ᵥ w), ← evalVec_mulVec]
    funext i
    rw [evalVec_apply, ← h2 ⟨liftVec φ _, liftVec_mem_glued φ _⟩ i]
    simp [hs1']
  have hdiv : ∀ i j, s ∣ G' i j := fun i j =>
    X_mul_X_sub_one_dvd (congrFun (congrFun hG0 i) j) (congrFun (congrFun hG1 i) j)
  choose G hG using hdiv
  refine ⟨Matrix.of G, fun v => ?_⟩
  funext i
  apply mul_left_cancel₀ hs0
  rw [h2 v i]
  simp only [mulVec, dotProduct, Matrix.of_apply, hG, Finset.mul_sum, mul_assoc]

/-! ### Rigidity: the size and the determinant are invariants -/

omit [Fintype ι'] in
/-- Two matrices agreeing on the vectors `s e_j` are equal. -/
lemma matrix_eq_of_mulVec_single_eq [DecidableEq ι] {M N : Matrix ι' ι k[X]}
    (h : ∀ j, M *ᵥ Pi.single j (X * (X - 1)) = N *ᵥ Pi.single j (X * (X - 1))) : M = N := by
  refine Matrix.ext fun i j => ?_
  have := congrFun (h j) i
  simp only [mulVec_single, Pi.smul_apply, col_apply, op_smul_eq_mul] at this
  exact mul_right_cancel₀ X_mul_X_sub_one_ne_zero this

/-- **Rigidity.** If `glued φ ≅ glued ψ` with `φ` and `ψ` invertible, then `φ` and `ψ` have the
same size and the same determinant. -/
theorem card_eq_and_det_eq_of_linearEquiv [DecidableEq ι] [DecidableEq ι']
    {φ : Matrix ι ι k} {ψ : Matrix ι' ι' k} (hφ : IsUnit φ.det) (hψ : IsUnit ψ.det)
    (e : glued φ ≃ₗ[nodeRing k] glued ψ) :
    Fintype.card ι = Fintype.card ι' ∧ φ.det = ψ.det := by
  obtain ⟨G, hG⟩ := exists_matrix_eq_of_linearMap hφ ((glued ψ).subtype ∘ₗ e.toLinearMap)
  obtain ⟨H, hH⟩ := exists_matrix_eq_of_linearMap hψ ((glued φ).subtype ∘ₗ e.symm.toLinearMap)
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    Submodule.coe_subtype] at hG hH
  have hs0 : (X * (X - 1) : k[X]).eval 0 = 0 := eval_zero_X_mul_X_sub_one
  have hs1 : (X * (X - 1) : k[X]).eval 1 = 0 := eval_one_X_mul_X_sub_one
  have hHG : H * G = 1 := by
    refine matrix_eq_of_mulVec_single_eq fun j => ?_
    let v : glued φ := ⟨_, single_mem_glued φ j hs0 hs1⟩
    rw [one_mulVec, ← mulVec_mulVec]
    change H *ᵥ (G *ᵥ (v : ι → k[X])) = v
    rw [← hG v, ← hH (e v), LinearEquiv.symm_apply_apply]
  have hGH : G * H = 1 := by
    refine matrix_eq_of_mulVec_single_eq fun j => ?_
    let v : glued ψ := ⟨_, single_mem_glued ψ j hs0 hs1⟩
    rw [one_mulVec, ← mulVec_mulVec]
    change G *ᵥ (H *ᵥ (v : ι' → k[X])) = v
    rw [← hH v, ← hG (e.symm v), LinearEquiv.apply_symm_apply]
  have hcard : Fintype.card ι = Fintype.card ι' := by
    let eA : (ι → k[X]) ≃ₗ[k[X]] (ι' → k[X]) :=
      LinearEquiv.ofLinearMap G.mulVecLin H.mulVecLin
        (LinearMap.ext fun v => by simp [mulVec_mulVec, hGH])
        (LinearMap.ext fun v => by simp [mulVec_mulVec, hHG])
    simpa [Module.finrank_fintype_fun_eq_card] using eA.finrank_eq
  refine ⟨hcard, ?_⟩
  -- the relation `G(1) φ = ψ G(0)`
  have hrel : G.map (eval 1) * φ = ψ * G.map (eval 0) := by
    refine matrix_eq_of_mulVec_eq fun w => ?_
    let v : glued φ := ⟨liftVec φ w, liftVec_mem_glued φ w⟩
    have hm := (e v).2
    rw [mem_glued, hG v, evalVec_mulVec, evalVec_mulVec] at hm
    change G.map (eval 1) *ᵥ evalVec 1 (liftVec φ w) =
      ψ *ᵥ (G.map (eval 0) *ᵥ evalVec 0 (liftVec φ w)) at hm
    rw [evalVec_one_liftVec, evalVec_zero_liftVec] at hm
    rw [← mulVec_mulVec, hm, mulVec_mulVec]
  -- reindex to square matrices
  let σ : ι ≃ ι' := Fintype.equivOfCardEq hcard
  let G₂ : Matrix ι ι k[X] := G.submatrix σ id
  let H₂ : Matrix ι ι k[X] := H.submatrix id σ
  have hHG₂ : H₂ * G₂ = 1 := by
    simp only [H₂, G₂, submatrix_mul_equiv, hHG, submatrix_id_id]
  have hunit : IsUnit G₂.det := by
    refine IsUnit.of_mul_eq_one_right H₂.det ?_
    rw [← det_mul, hHG₂, det_one]
  obtain ⟨c, hc, hcG⟩ := Polynomial.isUnit_iff.mp hunit
  have hev : ∀ a : k, (G₂.map (eval a)).det = c := by
    intro a
    have := RingHom.map_det (evalRingHom a) G₂
    rw [← hcG] at this
    simpa using this.symm
  have hrel₂ : G₂.map (eval 1) * φ = ψ.submatrix σ σ * G₂.map (eval 0) := by
    have := congrArg (fun M => M.submatrix σ id) hrel
    rw [submatrix_mul _ _ σ id id Function.bijective_id,
      submatrix_mul _ _ σ σ id σ.bijective, submatrix_id_id] at this
    simpa [G₂, submatrix_map] using this
  have hdet := congrArg Matrix.det hrel₂
  rw [det_mul, det_mul, hev, hev, det_submatrix_equiv_self] at hdet
  exact mul_left_cancel₀ hc.ne_zero (by rw [hdet, mul_comm])

/-! ### Every finite projective module is a glued module -/

/-- **Classification.** Every finite projective module over the node ring is isomorphic to a
glued module `glued φ`, with `φ` an invertible `n × n` matrix over `k`.

Write `P` as a direct summand of `R^m`, cut out by an idempotent matrix `E` over `R`. Over the
principal ideal domain `k[x]` the image of `E` is free, with a basis `B` and coordinates `C`
(so `C B = 1` and `B C = E`); the module `P` is then the set of `c ∈ k[x]^n` with `B c ∈ R^m`,
which is `glued (C(1) B(0))`. -/
theorem exists_linearEquiv_glued (P : Type*) [AddCommGroup P] [Module (nodeRing k) P]
    [Module.Finite (nodeRing k) P] [Module.Projective (nodeRing k) P] :
    ∃ (n : ℕ) (φ : Matrix (Fin n) (Fin n) k), IsUnit φ.det ∧
      Nonempty (P ≃ₗ[nodeRing k] glued φ) := by
  classical
  obtain ⟨m, π, hπ⟩ := Module.Finite.exists_fin' (nodeRing k) P
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property π LinearMap.id hπ
  have hσ' : ∀ p, π (σ p) = p := fun p => LinearMap.congr_fun hσ p
  let ι : nodeRing k →+* k[X] := (nodeRing k).subtype
  let ER : Matrix (Fin m) (Fin m) (nodeRing k) := LinearMap.toMatrix' (σ ∘ₗ π)
  have hER : ∀ v, ER *ᵥ v = σ (π v) := fun v => by
    simp [ER, LinearMap.toMatrix'_mulVec]
  let E : Matrix (Fin m) (Fin m) k[X] := ER.map ι
  let incl : (Fin m → nodeRing k) → (Fin m → k[X]) := fun v i => (v i : k[X])
  have hincl_inj : Function.Injective incl := fun v w h =>
    funext fun i => Subtype.ext (congrFun h i)
  have hincl01 : ∀ v, evalVec 0 (incl v) = evalVec 1 (incl v) := fun v =>
    funext fun i => (mem_nodeRing_iff _).1 (v i).2
  have hE : ∀ v, E *ᵥ incl v = incl (σ (π v)) := by
    intro v; funext i
    rw [← hER]
    exact (RingHom.map_mulVec ι ER v i).symm
  have hEE : E * E = E := by
    have : ER * ER = ER := by
      simp only [ER, ← LinearMap.toMatrix'_comp]
      congr 1
      exact LinearMap.ext fun v => by simp [hσ']
    simp only [E, ← Matrix.map_mul, this]
  have hE01 : E.map (eval 1) = E.map (eval 0) := by
    refine Matrix.ext fun i j => ?_
    exact ((mem_nodeRing_iff _).1 (ER i j).2).symm
  let W : Submodule k[X] (Fin m → k[X]) := LinearMap.range E.mulVecLin
  obtain ⟨n, b⟩ := Submodule.basisOfPid (Pi.basisFun k[X] (Fin m)) W
  let B : Matrix (Fin m) (Fin n) k[X] := Matrix.of fun i j => (b j : Fin m → k[X]) i
  let Cl : (Fin m → k[X]) →ₗ[k[X]] (Fin n → k[X]) :=
    b.equivFun.toLinearMap ∘ₗ E.mulVecLin.rangeRestrict
  let Cm : Matrix (Fin n) (Fin m) k[X] := LinearMap.toMatrix' Cl
  have hB : ∀ c, B *ᵥ c = ((b.equivFun.symm c : W) : Fin m → k[X]) := by
    intro c; funext i
    simp [B, mulVec, dotProduct, Module.Basis.equivFun_symm_apply, Finset.sum_apply, mul_comm]
  have hC : ∀ v, Cm *ᵥ v = b.equivFun (E.mulVecLin.rangeRestrict v) := fun v => by
    simp [Cm, Cl, LinearMap.toMatrix'_mulVec]
  have hBC : B * Cm = E := matrix_eq_of_mulVec_eq fun v => by
    rw [← mulVec_mulVec, hC, hB, LinearEquiv.symm_apply_apply]
    rfl
  have hCB : Cm * B = 1 := matrix_eq_of_mulVec_eq fun c => by
    rw [← mulVec_mulVec, one_mulVec, hC]
    have hW : E.mulVecLin.rangeRestrict (B *ᵥ c) = b.equivFun.symm c := by
      apply Subtype.ext
      change E *ᵥ (B *ᵥ c) = _
      rw [hB]
      obtain ⟨w, hw⟩ := (b.equivFun.symm c).2
      rw [← hw, mulVecLin_apply, mulVec_mulVec, hEE]
    rw [hW, LinearEquiv.apply_symm_apply]
  -- evaluations at `0` and `1`
  have hBC0 : B.map (eval 0) * Cm.map (eval 0) = E.map (eval 0) := by
    rw [← map_eval_mul, hBC]
  have hBC1 : B.map (eval 1) * Cm.map (eval 1) = E.map (eval 0) := by
    rw [← map_eval_mul, hBC, hE01]
  have hCB0 : Cm.map (eval 0) * B.map (eval 0) = 1 := by
    rw [← map_eval_mul, hCB, map_eval_one]
  have hCB1 : Cm.map (eval 1) * B.map (eval 1) = 1 := by
    rw [← map_eval_mul, hCB, map_eval_one]
  let φ : Matrix (Fin n) (Fin n) k := Cm.map (eval 1) * B.map (eval 0)
  have hφinv : φ * (Cm.map (eval 0) * B.map (eval 1)) = 1 := by
    calc φ * (Cm.map (eval 0) * B.map (eval 1))
        = Cm.map (eval 1) * (B.map (eval 0) * Cm.map (eval 0)) * B.map (eval 1) := by
          simp only [φ, Matrix.mul_assoc]
      _ = Cm.map (eval 1) * (B.map (eval 1) * Cm.map (eval 1)) * B.map (eval 1) := by
          rw [hBC0, hBC1]
      _ = 1 := by
          rw [← Matrix.mul_assoc, hCB1, Matrix.one_mul, hCB1]
  have hdet : IsUnit φ.det :=
    IsUnit.of_mul_eq_one (Cm.map (eval 0) * B.map (eval 1)).det
      (by rw [← det_mul, hφinv, det_one])
  have hB1φ : B.map (eval 1) * φ = B.map (eval 0) := by
    calc B.map (eval 1) * φ = (B.map (eval 1) * Cm.map (eval 1)) * B.map (eval 0) := by
          simp only [φ, Matrix.mul_assoc]
      _ = (B.map (eval 0) * Cm.map (eval 0)) * B.map (eval 0) := by rw [hBC1, hBC0]
      _ = B.map (eval 0) := by rw [Matrix.mul_assoc, hCB0, Matrix.mul_one]
  have hφC0 : φ * Cm.map (eval 0) = Cm.map (eval 1) * E.map (eval 0) := by
    simp only [φ, Matrix.mul_assoc, hBC0]
  -- the forward map
  have hfwd : ∀ p, Cm *ᵥ incl (σ p) ∈ glued φ := by
    intro p
    have hx : E *ᵥ incl (σ p) = incl (σ p) := by rw [hE, hσ']
    have hx1 : E.map (eval 0) *ᵥ evalVec 1 (incl (σ p)) = evalVec 1 (incl (σ p)) := by
      conv_rhs => rw [← hx]
      rw [evalVec_mulVec, hE01]
    rw [mem_glued, evalVec_mulVec, evalVec_mulVec, mulVec_mulVec, hφC0, ← mulVec_mulVec,
      hincl01, hx1]
  -- the backward map
  have hbwd : ∀ c ∈ glued φ, ∀ i, (B *ᵥ c) i ∈ nodeRing k := by
    intro c hc i
    rw [mem_nodeRing_iff]
    have h : evalVec 0 (B *ᵥ c) = evalVec 1 (B *ᵥ c) := by
      rw [evalVec_mulVec, evalVec_mulVec, mem_glued.1 hc, mulVec_mulVec, hB1φ]
    exact congrFun h i
  let restr : glued φ → (Fin m → nodeRing k) := fun c i =>
    ⟨(B *ᵥ (c : Fin n → k[X])) i, hbwd c c.2 i⟩
  have hincl_restr : ∀ c, incl (restr c) = B *ᵥ (c : Fin n → k[X]) := fun c => rfl
  have hincl_add : ∀ v w, incl (v + w) = incl v + incl w := fun v w => by
    funext i; simp [incl]
  have hincl_smul : ∀ (r : nodeRing k) v, incl (r • v) = r • incl v := fun r v => by
    funext i; simp [incl, Subring.smul_def]
  refine ⟨n, φ, hdet, ⟨
    { toFun := fun p => ⟨Cm *ᵥ incl (σ p), hfwd p⟩
      map_add' := fun p q => Subtype.ext (by simp [hincl_add, mulVec_add])
      map_smul' := fun r p => Subtype.ext (by simp [hincl_smul, mulVec_smul])
      invFun := fun c => π (restr c)
      left_inv := fun p => ?_
      right_inv := fun c => ?_ }⟩⟩
  · have : restr ⟨Cm *ᵥ incl (σ p), hfwd p⟩ = σ p := by
      apply hincl_inj
      rw [hincl_restr]
      change B *ᵥ (Cm *ᵥ incl (σ p)) = incl (σ p)
      rw [mulVec_mulVec, hBC, hE, hσ']
    simp only
    rw [this, hσ']
  · apply Subtype.ext
    change Cm *ᵥ incl (σ (π (restr c))) = c
    rw [← hE, hincl_restr, mulVec_mulVec, mulVec_mulVec, ← hBC, Matrix.mul_assoc,
      Matrix.mul_assoc, hCB, Matrix.mul_one, hCB, one_mulVec]

/-! ### Block sums -/

lemma mem_glued_fromBlocks {φ : Matrix ι ι k} {ψ : Matrix ι' ι' k} {v : ι ⊕ ι' → k[X]} :
    v ∈ glued (fromBlocks φ 0 0 ψ) ↔
      (fun i => v (Sum.inl i)) ∈ glued φ ∧ (fun i => v (Sum.inr i)) ∈ glued ψ := by
  simp only [mem_glued, fromBlocks_mulVec, zero_mulVec, add_zero, zero_add]
  constructor
  · intro h
    exact ⟨funext fun i => congrFun h (Sum.inl i), funext fun i => congrFun h (Sum.inr i)⟩
  · rintro ⟨h1, h2⟩
    funext i
    rcases i with i | i
    exacts [congrFun h1 i, congrFun h2 i]

/-- `glued (φ ⊕ ψ) ≅ glued φ × glued ψ`. -/
def gluedFromBlocksEquiv (φ : Matrix ι ι k) (ψ : Matrix ι' ι' k) :
    glued (fromBlocks φ 0 0 ψ) ≃ₗ[nodeRing k] glued φ × glued ψ where
  toFun v := (⟨_, (mem_glued_fromBlocks.1 v.2).1⟩, ⟨_, (mem_glued_fromBlocks.1 v.2).2⟩)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun p := ⟨Sum.elim p.1.1 p.2.1, mem_glued_fromBlocks.2 ⟨p.1.2, p.2.2⟩⟩
  left_inv v := Subtype.ext (funext fun i => by rcases i with i | i <;> rfl)
  right_inv p := rfl

lemma isUnit_det_fromBlocks {φ : Matrix ι ι k} {ψ : Matrix ι' ι' k} [DecidableEq ι]
    [DecidableEq ι'] (hφ : IsUnit φ.det) (hψ : IsUnit ψ.det) :
    IsUnit (fromBlocks φ 0 0 ψ).det := by
  rw [det_fromBlocks_zero₂₁]; exact hφ.mul hψ

/-! ### Line bundles and diagonal glued modules -/

/-- The line bundle `L_u = {f ∈ k[x] ∣ f(1) = u f(0)}` over the node ring. -/
def lineMod (u : k) : Submodule (nodeRing k) k[X] where
  carrier := {f | f.eval 1 = u * f.eval 0}
  add_mem' {f g} hf hg := by
    simp only [Set.mem_ofPred_eq, eval_add] at hf hg ⊢
    rw [hf, hg, mul_add]
  zero_mem' := by simp
  smul_mem' r f hf := by
    simp only [Set.mem_ofPred_eq, Subring.smul_def, smul_eq_mul, eval_mul] at hf ⊢
    rw [hf, (mem_nodeRing_iff _).1 r.2]
    ring

lemma mem_lineMod {u : k} {f : k[X]} : f ∈ lineMod u ↔ f.eval 1 = u * f.eval 0 := Iff.rfl

lemma mem_glued_diagonal [DecidableEq ι] {D : ι → k} {v : ι → k[X]} :
    v ∈ glued (diagonal D) ↔ ∀ i, v i ∈ lineMod (D i) := by
  simp only [mem_glued, funext_iff, mulVec_diagonal, evalVec_apply, mem_lineMod]

/-- `glued (diagonal D) ≅ ∏ᵢ L_{D i}`. -/
def gluedDiagonalEquiv [DecidableEq ι] (D : ι → k) :
    glued (diagonal D) ≃ₗ[nodeRing k] ((i : ι) → lineMod (D i)) where
  toFun v i := ⟨v.1 i, mem_glued_diagonal.1 v.2 i⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun w := ⟨fun i => w i, mem_glued_diagonal.2 fun i => (w i).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `L_1 ≅ R`. -/
def lineModOneEquiv : lineMod (1 : k) ≃ₗ[nodeRing k] nodeRing k where
  toFun f := ⟨f, by rw [mem_nodeRing_iff, ((mem_lineMod).1 f.2), one_mul]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun r := ⟨r, by rw [mem_lineMod, one_mul, ((mem_nodeRing_iff _).1 r.2)]⟩
  left_inv f := rfl
  right_inv r := rfl

/-! ### The relation `L_u ⊕ L_v ≅ L_{uv} ⊕ R` -/

/-- A path `G(x)` in `SL₂(k[x])` from `!![0, 1; -1, 0]` to `!![0, u; -u⁻¹, 0]`. -/
def swapPath (u : k) : Matrix (Fin 2) (Fin 2) k[X] :=
  let α : k[X] := C 1 + C (u - 1) * X
  let β : k[X] := -1 + C (1 - u⁻¹) * X
  !![1 + α * β, α * (2 + α * β); β, 1 + α * β]

lemma det_swapPath (u : k) : (swapPath u).det = 1 := by
  simp only [swapPath, det_fin_two_of]
  ring

lemma swapPath_rel {u : k} (hu : u ≠ 0) (v : k) :
    (swapPath u).map (eval 1) * diagonal ![u, v] =
      diagonal ![u * v, 1] * (swapPath u).map (eval 0) := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [swapPath, Matrix.mul_apply, diagonal_apply] <;> field_simp <;>
    first | ring1 | (left; ring1)

/-- `glued (diag(u, v)) ≅ glued (diag(uv, 1))` for `u ≠ 0`. -/
def gluedDiagonalPairEquiv {u : k} (hu : u ≠ 0) (v : k) :
    glued (diagonal ![u, v]) ≃ₗ[nodeRing k] glued (diagonal ![u * v, 1]) :=
  gluedEquivOfConj (swapPath u) (by rw [det_swapPath]; exact isUnit_one) (swapPath_rel hu v)

/-- **`L_u ⊕ L_v ≅ L_{uv} ⊕ L_1`** for `u ≠ 0`. -/
def lineModProdEquiv {u : k} (hu : u ≠ 0) (v : k) :
    (lineMod u × lineMod v) ≃ₗ[nodeRing k] (lineMod (u * v) × lineMod (1 : k)) :=
  ((LinearEquiv.piFinTwo (nodeRing k) fun i => lineMod (![u, v] i)).symm.trans
    (gluedDiagonalEquiv ![u, v]).symm).trans
    ((gluedDiagonalPairEquiv hu v).trans ((gluedDiagonalEquiv ![u * v, 1]).trans
      (LinearEquiv.piFinTwo (nodeRing k) fun i => lineMod (![u * v, 1] i))))

/-! ### Reduction to diagonal form -/

/-- A matrix `γ` over `k` *joined to `1`*: there is `G` over `k[x]` with unit determinant,
`G(0) = 1` and `G(1) = γ`. -/
def JoinedFromOne {n : Type*} [Fintype n] [DecidableEq n] (γ : Matrix n n k) : Prop :=
  ∃ G : Matrix n n k[X], IsUnit G.det ∧ G.map (eval 0) = 1 ∧ G.map (eval 1) = γ

/-- A matrix `γ` over `k` *joined to `1`* in the reverse direction: `G(0) = γ`, `G(1) = 1`. -/
def JoinedToOne {n : Type*} [Fintype n] [DecidableEq n] (γ : Matrix n n k) : Prop :=
  ∃ G : Matrix n n k[X], IsUnit G.det ∧ G.map (eval 0) = γ ∧ G.map (eval 1) = 1

lemma map_eval_transvection {n : Type*} [DecidableEq n] (i j : n) (p : k[X])
    (a : k) : (transvection i j p).map (eval a) = transvection i j (p.eval a) := by
  refine Matrix.ext fun x y => ?_
  simp only [transvection, map_apply, Matrix.add_apply, one_apply, single_apply]
  split_ifs <;> simp_all

lemma joinedFromOne_prod {n : Type*} [Fintype n] [DecidableEq n]
    (L : List (TransvectionStruct n k)) :
    JoinedFromOne (L.map TransvectionStruct.toMatrix).prod := by
  induction L with
  | nil => exact ⟨1, by simp, map_eval_one 0, by simp⟩
  | cons t L ih =>
    obtain ⟨G, hG, hG0, hG1⟩ := ih
    refine ⟨transvection t.i t.j (C t.c * X) * G, ?_, ?_, ?_⟩
    · rw [det_mul, det_transvection_of_ne _ _ t.hij, one_mul]; exact hG
    · rw [map_eval_mul, map_eval_transvection, hG0]; simp
    · rw [map_eval_mul, map_eval_transvection, hG1]; simp [TransvectionStruct.toMatrix]

lemma joinedToOne_prod {n : Type*} [Fintype n] [DecidableEq n]
    (L : List (TransvectionStruct n k)) :
    JoinedToOne (L.map TransvectionStruct.toMatrix).prod := by
  induction L with
  | nil => exact ⟨1, by simp, by simp, map_eval_one 1⟩
  | cons t L ih =>
    obtain ⟨G, hG, hG0, hG1⟩ := ih
    refine ⟨transvection t.i t.j (C t.c * (1 - X)) * G, ?_, ?_, ?_⟩
    · rw [det_mul, det_transvection_of_ne _ _ t.hij, one_mul]; exact hG
    · rw [map_eval_mul, map_eval_transvection, hG0]; simp [TransvectionStruct.toMatrix]
    · rw [map_eval_mul, map_eval_transvection, hG1]; simp

lemma det_prod_transvectionStruct {n : Type*} [Fintype n] [DecidableEq n]
    (L : List (TransvectionStruct n k)) : (L.map TransvectionStruct.toMatrix).prod.det = 1 := by
  induction L with
  | nil => simp
  | cons t L ih => rw [List.map_cons, List.prod_cons, det_mul, TransvectionStruct.det, ih, one_mul]

/-- **Diagonal form.** For `φ` invertible, `glued φ ≅ glued (diagonal D)` with `∏ D = det φ`. -/
theorem exists_gluedEquiv_diagonal {n : ℕ} (φ : Matrix (Fin n) (Fin n) k) :
    ∃ D : Fin n → k, ∏ i, D i = φ.det ∧
      Nonempty (glued φ ≃ₗ[nodeRing k] glued (diagonal D)) := by
  obtain ⟨L, L', D, hφ⟩ := Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec φ
  obtain ⟨G, hG, hG0, hG1⟩ := joinedFromOne_prod L
  obtain ⟨G', hG', hG0', hG1'⟩ := joinedToOne_prod L'
  have e1 : glued (diagonal D * (L'.map TransvectionStruct.toMatrix).prod) ≃ₗ[nodeRing k]
      glued φ :=
    gluedEquivOfConj G hG (by rw [hG0, hG1, Matrix.mul_one, hφ, Matrix.mul_assoc])
  have e2 : glued (diagonal D * (L'.map TransvectionStruct.toMatrix).prod) ≃ₗ[nodeRing k]
      glued (diagonal D) :=
    gluedEquivOfConj G' hG' (by rw [hG1', hG0', Matrix.one_mul])
  refine ⟨D, ?_, ⟨e1.symm.trans e2⟩⟩
  rw [hφ, det_mul, det_mul, det_prod_transvectionStruct, det_prod_transvectionStruct, one_mul,
    mul_one, det_diagonal]

end NodeRing
