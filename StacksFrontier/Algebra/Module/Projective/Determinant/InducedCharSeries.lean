module

public import StacksFrontier.Algebra.Module.Projective.Determinant.CharSeries
public import StacksFrontier.Algebra.Module.Projective.Determinant.Endomorphism
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# The characteristic series of an induced endomorphism

Let `ψ` be an endomorphism of a finite projective module `M`. The *induced* endomorphism of
`M ^ (f + 1)` is the cyclic shift `(v₀, …, v_f) ↦ (ψ v_f, v₀, …, v_{f - 1})`: it permutes the
copies of `M` cyclically, and going once around the cycle is `ψ`. It is the action of a generator
of a cyclic group of order `f + 1` on a representation induced from the subgroup of index `f + 1`.
Its determinant is

`det(1 - t Ind ψ) = det(1 - t ^ (f + 1) ψ)`,

and so its characteristic series is `det(1 - Ind ψ T ^ d) = det(1 - ψ T ^ (d (f + 1)))`. This is
the computation of the local factor of a finite direct image: the stalk at a geometric point over
a closed point `x` of the direct image along a finite morphism is the sum, over the closed points
`y` above `x`, of `[κ(y) : κ(x)]` copies of the stalk at `y` permuted cyclically by the Frobenius
of `x`, whose `[κ(y) : κ(x)]`-th power is the Frobenius of `y`.

## Main definitions

* `ProjectiveDeterminant.inducedEnd`: the induced endomorphism.

## Main results

* `ProjectiveDeterminant.det_one_sub_smul_inducedEnd`: `det(1 - t Ind ψ) = det(1 - t ^ (f + 1) ψ)`.
* `ProjectiveDeterminant.charSeries_inducedEnd`:
  `det(1 - Ind ψ T ^ d) = det(1 - ψ T ^ (d (f + 1)))`.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace ProjectiveDeterminant

universe u v w

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- The induced endomorphism `(v₀, …, v_f) ↦ (ψ v_f, v₀, …, v_{f - 1})` of `M ^ (f + 1)`. -/
public def inducedEnd (f : ℕ) (ψ : M →ₗ[R] M) : (Fin (f + 1) → M) →ₗ[R] (Fin (f + 1) → M) where
  toFun v := Fin.cons (ψ (v (Fin.last f))) fun i => v (Fin.castSucc i)
  map_add' v w := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' c v := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- The zeroth coordinate of `inducedEnd f ψ v` is `ψ (v (Fin.last f))`. -/
@[simp]
public theorem inducedEnd_apply_zero (f : ℕ) (ψ : M →ₗ[R] M) (v : Fin (f + 1) → M) :
    inducedEnd f ψ v 0 = ψ (v (Fin.last f)) := rfl

/-- The coordinate `i.succ` of `inducedEnd f ψ v` is `v i.castSucc`. -/
@[simp]
public theorem inducedEnd_apply_succ (f : ℕ) (ψ : M →ₗ[R] M) (v : Fin (f + 1) → M) (i : Fin f) :
    inducedEnd f ψ v i.succ = v i.castSucc := rfl

variable [Module.Finite R M] [Module.Projective R M]

omit [Module.Finite R M] in
/-- A finite power of a projective module is projective. -/
theorem projective_finPi (n : ℕ) : Module.Projective R (Fin n → M) :=
  Module.Projective.of_equiv (DFinsupp.linearEquivFunOnFintype (R := R) (M := fun _ : Fin n => M))

attribute [local instance] projective_finPi

/-- A lower unipotent endomorphism `(x, y) ↦ (x, y + C x)` has determinant `1`. -/
theorem det_lowerUnipotent {N : Type*} [AddCommGroup N] [Module R N] [Module.Finite R N]
    [Module.Projective R N] (C : M →ₗ[R] N) :
    det (LinearMap.id + (LinearMap.inr R M N).comp (C.comp (LinearMap.fst R M N))) = 1 := by
  have h := det_one_add_comp_comm (R := R) (M := M) (N := M × N)
    ((LinearMap.inr R M N).comp C) (LinearMap.fst R M N)
  have h1 : (LinearMap.fst R M N).comp ((LinearMap.inr R M N).comp C) = 0 := by
    ext x
    simp
  rw [h1, add_zero, det_linearMap_id] at h
  rw [← h, LinearMap.comp_assoc]

/-- **`det(1 - t Ind ψ) = det(1 - t ^ (f + 1) ψ)`.** -/
public theorem det_one_sub_smul_inducedEnd (f : ℕ) (ψ : M →ₗ[R] M) (t : R) :
    det (LinearMap.id - t • inducedEnd f ψ) = det (LinearMap.id - t ^ (f + 1) • ψ) := by
  induction f generalizing ψ with
  | zero =>
    let e : (Fin (0 + 1) → M) ≃ₗ[R] M := LinearEquiv.funUnique (Fin 1) R M
    rw [← det_linearEquiv_conj e]
    congr 1
    refine LinearMap.ext fun m => ?_
    simp [e, LinearEquiv.conj_apply, inducedEnd]
  | succ f ih =>
    let e := Fin.consLinearEquiv R (fun _ : Fin (f + 1 + 1) => M)
    -- the Schur factorization in the splitting `M × M ^ (f + 1)`
    let C : M →ₗ[R] (Fin (f + 1) → M) := -t • (LinearMap.pi fun i =>
      if i = 0 then LinearMap.id else 0)
    let Bm : (Fin (f + 1) → M) →ₗ[R] M := -t • ψ.comp (LinearMap.proj (Fin.last f))
    let D : (Fin (f + 1) → M) →ₗ[R] (Fin (f + 1) → M) :=
      LinearMap.id - t • inducedEnd f (t • ψ)
    have hfac : e.symm.conj (LinearMap.id - t • inducedEnd (f + 1) ψ) =
        (LinearMap.id + (LinearMap.inr R M _).comp (C.comp (LinearMap.fst R M _))).comp
          ((LinearMap.inl R M _).comp ((LinearMap.id.comp (LinearMap.fst R M _)) +
            Bm.comp (LinearMap.snd R M _)) +
          (LinearMap.inr R M _).comp (D.comp (LinearMap.snd R M _))) := by
      apply LinearMap.ext
      rintro ⟨x, y⟩
      apply e.injective
      simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply]
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [e, Bm, C, D, inducedEnd, sub_eq_add_neg]
      · refine Fin.cases ?_ (fun k => ?_) j
        · simp [e, Bm, C, D, inducedEnd, sub_eq_add_neg, smul_smul]
        · simp [e, Bm, C, D, inducedEnd, sub_eq_add_neg, Fin.succ_ne_zero]
    rw [← det_linearEquiv_conj e.symm, hfac, det_comp, det_lowerUnipotent, det_blockTriangular,
      det_linearMap_id, one_mul, one_mul, ih, smul_smul, ← pow_succ]

/-- Conjugating by an equivalence that intertwines `f` and `g` turns `f` into `g`. -/
private theorem conj_eq_of_comp_eq {A : Type*} [CommRing A] {P Q : Type*} [AddCommGroup P]
    [AddCommGroup Q] [Module A P] [Module A Q] (e : P ≃ₗ[A] Q) {f : P →ₗ[A] P} {g : Q →ₗ[A] Q}
    (h : e.toLinearMap ∘ₗ f = g ∘ₗ e.toLinearMap) : e.conj f = g := by
  refine LinearMap.ext fun w => ?_
  simpa [LinearEquiv.conj_apply] using LinearMap.congr_fun h (e.symm w)

/-- **The characteristic series of an induced endomorphism**:
`det(1 - Ind ψ T ^ d) = det(1 - ψ T ^ (d (f + 1)))`. -/
public theorem charSeries_inducedEnd (f : ℕ) (ψ : M →ₗ[R] M) (d : ℕ) :
    charSeries (inducedEnd f ψ) d = charSeries ψ (d * (f + 1)) := by
  let A := PowerSeries R
  let e : A ⊗[R] (Fin (f + 1) → M) ≃ₗ[A] (Fin (f + 1) → A ⊗[R] M) :=
    TensorProduct.piRight R A A fun _ => M
  have hcomm : e.toLinearMap ∘ₗ (inducedEnd f ψ).baseChange A =
      inducedEnd f (ψ.baseChange A) ∘ₗ e.toLinearMap := by
    refine TensorProduct.AlgebraTensorModule.ext fun a v => ?_
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [e, inducedEnd]
  have hconj := conj_eq_of_comp_eq e hcomm
  change det (LinearMap.id - (PowerSeries.X ^ d : A) • (inducedEnd f ψ).baseChange A) =
    det (LinearMap.id - (PowerSeries.X ^ (d * (f + 1)) : A) • ψ.baseChange A)
  rw [← det_linearEquiv_conj e, map_sub, LinearEquiv.conj_id, map_smul, hconj,
    det_one_sub_smul_inducedEnd, ← pow_mul]

/-! ### Block diagonal endomorphisms -/

section Pi

/-- The block diagonal endomorphism of a product with blocks `ψ i`. -/
public def piDiag {ι : Type*} {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    (ψ : ∀ i, V i →ₗ[R] V i) : (∀ i, V i) →ₗ[R] (∀ i, V i) :=
  LinearMap.pi fun i => (ψ i).comp (LinearMap.proj i)

/-- The `i`-th coordinate of `piDiag ψ v` is `ψ i (v i)`. -/
@[simp]
public theorem piDiag_apply {ι : Type*} {V : ι → Type*} [∀ i, AddCommGroup (V i)]
    [∀ i, Module R (V i)] (ψ : ∀ i, V i →ₗ[R] V i) (v : ∀ i, V i) (i : ι) :
    piDiag ψ v i = ψ i (v i) := rfl

omit [Module.Finite R M] in
/-- A finite product of projective modules is projective. -/
public theorem projective_pi {ι : Type*} [Fintype ι] {V : ι → Type*} [∀ i, AddCommGroup (V i)]
    [∀ i, Module R (V i)] [∀ i, Module.Projective R (V i)] :
    Module.Projective R (∀ i, V i) := by
  classical
  exact Module.Projective.of_equiv (DFinsupp.linearEquivFunOnFintype (R := R) (M := V))

attribute [local instance] projective_pi

/-- **The determinant of a block diagonal endomorphism is the product of the determinants of the
blocks.** -/
public theorem det_piDiag : ∀ (ι : Type w) [Fintype ι] (V : ι → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, Module R (V i)] [∀ i, Module.Finite R (V i)] [∀ i, Module.Projective R (V i)]
    (ψ : ∀ i, V i →ₗ[R] V i), det (piDiag ψ) = ∏ i, det (ψ i) := by
  refine Fintype.induction_empty_option ?_ ?_ ?_
  · intro α β _ e h V _ _ _ _ ψ
    let : Fintype α := Fintype.ofEquiv β e.symm
    let E : (∀ a, V (e a)) ≃ₗ[R] (∀ b, V b) := LinearEquiv.piCongrLeft R V e
    have hc : E.symm.conj (piDiag ψ) = piDiag fun a => ψ (e a) := by
      refine LinearMap.ext fun v => ?_
      apply E.injective
      funext b
      obtain ⟨a, rfl⟩ := e.surjective b
      rw [LinearEquiv.conj_apply, LinearEquiv.symm_symm]
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
        piDiag_apply]
      show ψ (e a) ((Equiv.piCongrLeft V e v) (e a)) =
        (Equiv.piCongrLeft V e (fun a => ψ (e a) (v a))) (e a)
      rw [Equiv.piCongrLeft_apply_apply, Equiv.piCongrLeft_apply_apply]
    rw [← det_linearEquiv_conj E.symm, hc, h (fun a => V (e a)) fun a => ψ (e a)]
    exact Fintype.prod_equiv e _ _ fun a => rfl
  · intro V _ _ _ _ ψ
    rw [show piDiag ψ = LinearMap.id from LinearMap.ext fun v => Subsingleton.elim _ _,
      det_linearMap_id, Finset.univ_eq_empty, Finset.prod_empty]
  · intro α _ h V _ _ _ _ ψ
    let E : (∀ i : Option α, V i) ≃ₗ[R] V none × (∀ a : α, V (some a)) :=
      LinearEquiv.piOptionEquivProd R
    have hc : E.conj (piDiag ψ) = (ψ none).prodMap (piDiag fun a => ψ (some a)) := by
      refine LinearMap.ext fun v => ?_
      apply E.symm.injective
      funext i
      cases i <;> simp [E, LinearEquiv.conj_apply, LinearEquiv.piOptionEquivProd,
        Equiv.piOptionEquivProd]
    rw [← det_linearEquiv_conj E, hc, det_prodMap, h, Fintype.prod_option]

/-- **The characteristic series of a block diagonal endomorphism is the product of those of the
blocks.** -/
public theorem charSeries_piDiag {ι : Type w} [Fintype ι] (V : ι → Type v)
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] [∀ i, Module.Finite R (V i)]
    [∀ i, Module.Projective R (V i)] (ψ : ∀ i, V i →ₗ[R] V i) (d : ℕ) :
    charSeries (piDiag ψ) d = ∏ i, charSeries (ψ i) d := by
  classical
  let A := PowerSeries R
  let e : A ⊗[R] (∀ i, V i) ≃ₗ[A] (∀ i, A ⊗[R] V i) := TensorProduct.piRight R A A V
  have hcomm : e.toLinearMap ∘ₗ (piDiag ψ).baseChange A =
      piDiag (fun i => (ψ i).baseChange A) ∘ₗ e.toLinearMap := by
    refine TensorProduct.AlgebraTensorModule.ext fun a v => ?_
    funext i
    simp [e]
  have h1 : e.conj (LinearMap.id - (PowerSeries.X ^ d : A) • (piDiag ψ).baseChange A) =
      piDiag fun i => LinearMap.id - (PowerSeries.X ^ d : A) • (ψ i).baseChange A := by
    rw [map_sub, LinearEquiv.conj_id, map_smul, conj_eq_of_comp_eq e hcomm]
    refine LinearMap.ext fun w => funext fun i => ?_
    simp
  change det (LinearMap.id - (PowerSeries.X ^ d : A) • (piDiag ψ).baseChange A) =
    ∏ i, det (LinearMap.id - (PowerSeries.X ^ d : A) • (ψ i).baseChange A)
  rw [← det_linearEquiv_conj e, h1, det_piDiag]

end Pi

/-! ### Cyclic decompositions -/

section Cyclic

attribute [local instance] projective_pi

variable {W : Type v} [AddCommGroup W] [Module R W] [Module.Finite R W] [Module.Projective R W]
  {J : Type w} [Fintype J] (V : J → Type v) [∀ j, AddCommGroup (V j)] [∀ j, Module R (V j)]
  [∀ j, Module.Finite R (V j)] [∀ j, Module.Projective R (V j)]

/-- The map `(w_{j,i}) ↦ ∑_j ∑_{i ≤ m_j} Φ ^ i (ι_j w_{j,i})` attached to a family of "base"
maps `ι_j : V_j → W` and lengths `m_j + 1`. -/
public def cyclicMap (Φ : W →ₗ[R] W) (m : J → ℕ) (ι : ∀ j, V j →ₗ[R] W) :
    (∀ j, Fin (m j + 1) → V j) →ₗ[R] W :=
  ∑ j, ∑ i : Fin (m j + 1), (Φ ^ (i : ℕ)) ∘ₗ ι j ∘ₗ (LinearMap.proj i ∘ₗ LinearMap.proj j)

omit [Module.Finite R W] [Module.Projective R W] [∀ j, Module.Finite R (V j)]
  [∀ j, Module.Projective R (V j)] in
/-- `cyclicMap V Φ m ι` sends `(w_{j,i})` to `∑_j ∑_{i ≤ m_j} Φ ^ i (ι_j (w_{j,i}))`. -/
public theorem cyclicMap_apply (Φ : W →ₗ[R] W) (m : J → ℕ) (ι : ∀ j, V j →ₗ[R] W)
    (w : ∀ j, Fin (m j + 1) → V j) :
    cyclicMap V Φ m ι w = ∑ j, ∑ i : Fin (m j + 1), (Φ ^ (i : ℕ)) (ι j (w j i)) := by
  simp [cyclicMap]

/-- **The characteristic series of an endomorphism with a cyclic decomposition.** Suppose
`W = ⊕_j ⊕_{i ≤ m_j} Φ ^ i (ι_j V_j)`, i.e. `cyclicMap` is bijective, and that `Φ ^ (m_j + 1)`
preserves each `ι_j V_j`, acting there by `ψ_j`. Then
`det(1 - Φ T ^ d) = ∏_j det(1 - ψ_j T ^ (d (m_j + 1)))`. -/
public theorem charSeries_eq_prod_of_cyclicMap_bijective (Φ : W →ₗ[R] W) (m : J → ℕ)
    (ι : ∀ j, V j →ₗ[R] W) (ψ : ∀ j, V j →ₗ[R] V j)
    (hψ : ∀ j, (Φ ^ (m j + 1)) ∘ₗ ι j = ι j ∘ₗ ψ j)
    (hE : Function.Bijective (cyclicMap V Φ m ι)) (d : ℕ) :
    charSeries Φ d = ∏ j, charSeries (ψ j) (d * (m j + 1)) := by
  let E := LinearEquiv.ofBijective (cyclicMap V Φ m ι) hE
  have hc : E.symm.conj Φ = piDiag fun j => inducedEnd (m j) (ψ j) := by
    refine LinearMap.ext fun w => ?_
    apply E.injective
    rw [LinearEquiv.conj_apply, LinearEquiv.symm_symm]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, E,
      LinearEquiv.ofBijective_apply, cyclicMap_apply, map_sum, piDiag_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_succ]
    simp only [Fin.val_last, Fin.val_castSucc, Fin.val_zero, pow_zero, Module.End.one_apply,
      Fin.val_succ, inducedEnd_apply_zero, inducedEnd_apply_succ]
    have h1 := LinearMap.congr_fun (hψ j) (w j (Fin.last (m j)))
    simp only [LinearMap.comp_apply] at h1
    rw [← Module.End.mul_apply, ← pow_succ', h1, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Module.End.mul_apply, ← pow_succ']
  rw [← charSeries_conj E.symm, hc, charSeries_piDiag]
  exact Finset.prod_congr rfl fun j _ => charSeries_inducedEnd (m j) (ψ j) d

end Cyclic

end ProjectiveDeterminant

end
