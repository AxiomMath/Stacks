module

public import StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.ConverseTheorem.FourierExpansion
public import StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.ConverseTheorem.UnramifiedTwist
public import StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.HeckeData

/-!
# The Hecke recursion for the Whittaker coefficients of an eigenform

Let `f` be an eigenform on `GL₂(A)` (Stacks, the notation before Tag 03VT): an unramified cusp
form with `T_v f = t_v f` and `U_v f = u_v f` at every place. Let `ψ` be a nontrivial adelic
character and `W` the Whittaker function of `f` with respect to `ψ`
(`Stacks.Adeles.GlobalFunctionField.whittaker`). We show:

* `W` is left `GL₂(O)`-invariant, satisfies `W(x n(z)) = ψ(z) W(x)`, and inherits the eigenvalue
  equations: `W(g₀ x) + ∑ᵢ W(gᵢ x) = t_v W(x)` and `W(a x) = u_v W(x)` for the matrices of `T_v`
  and `U_v`;
* the value `W(diag(y, 1))` depends only on the divisor `D` of the idele `y`; call it `c(D)`;
* `c(D) = 0` unless `ψ` is trivial on `A(D)`;
* for `ψ` trivial on `A(D)` the coefficients satisfy the Hecke recursion
  `t_v c(D) = q_v c(D - v) + u_v c(D + v)`;
* consequently `c` is determined by its value at the divisor `W₀` of `ψ`, that value is nonzero,
  and two eigenforms with the same eigenvalues are proportional (multiplicity one).

The recursion comes from the `q_v + 1` matrices of `T_v` applied to `diag(y, 1)`: the matrix
`diag(π⁻¹, 1)` lowers the divisor at `v`, the one matrix `(1, 0; -π⁻¹λ, π⁻¹)` with `λ ≡ 0`
is `U_v` followed by raising the divisor at `v`, and each of the `q_v - 1` others is, up to
`GL₂(O)` on the left, `diag(y', 1) n(z)` with `div y' = D - v` and `z ∈ A(D)`, on which `ψ` is
trivial. Along the powers of `v` this is the recursion of
`Stacks.Adeles.GlobalFunctionField.heckeSeq` with `d = q_v u_v`, whose generating series is the
local `L`-factor `(1 - t_v X + q_v u_v X²)⁻¹`.

## Main definitions

* `Stacks.Adeles.GlobalFunctionField.whittakerDiv` — `c(D) = W(diag(y_D, 1))`.
* `Stacks.Adeles.GlobalFunctionField.lowerGL`, `Stacks.Adeles.GlobalFunctionField.swapGL` —
  the local matrices `(1, 0; c, 1)` and `(-π λ⁻², λ⁻¹; λ⁻¹, 0)` of the computation.

## Main results

* `Stacks.Adeles.GlobalFunctionField.IsUnramifiedCuspForm.whittaker_diagGL` — `W(diag(y, 1))`
  depends only on `div y`.
* `Stacks.Adeles.GlobalFunctionField.IsUnramifiedCuspForm.whittakerDiv_eq_zero` — `c(D) = 0`
  unless `ψ(A(D)) = 1`.
* `Stacks.Adeles.GlobalFunctionField.IsEigenform.whittakerDiv_recursion` — the Hecke recursion.
* `Stacks.Adeles.GlobalFunctionField.eq_zero_of_hecke_recursion` — uniqueness for the recursion.
* `Stacks.Adeles.GlobalFunctionField.IsEigenform.exists_centralChar` — the central character.
* `Stacks.Adeles.GlobalFunctionField.IsEigenform.whittakerDiv_ne_zero` — `c(W₀) ≠ 0`.
* `Stacks.Adeles.GlobalFunctionField.IsEigenform.exists_eq_mul_of_eigenvalues_eq` —
  multiplicity one.

## References

* H. Jacquet, R. P. Langlands, *Automorphic forms on GL(2)*, LNM 114, §3 and §6.
* [Stacks Project, Tag 03VU](https://stacks.math.columbia.edu/tag/03VU)
-/

@[expose] public noncomputable section

open Matrix

universe u w

namespace Stacks.Adeles.GlobalFunctionField

section LocalGL

variable {F : Type*} [Field F]

/-- The lower unipotent matrix `(1, 0; c, 1)`. -/
public def lowerGL (c : F) : GL (Fin 2) F where
  val := !![1, 0; c, 1]
  inv := !![1, 0; -c, 1]
  val_inv := by
    rw [mul_fin_two, one_fin_two]; ext i j; fin_cases i <;> fin_cases j <;> simp
  inv_val := by
    rw [mul_fin_two, one_fin_two]; ext i j; fin_cases i <;> fin_cases j <;> simp

/-- The matrix of `lowerGL c` is `(1, 0; c, 1)`. -/
@[simp]
public theorem coe_lowerGL (c : F) : ((lowerGL c : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
    !![1, 0; c, 1] := rfl

/-- The matrix of the inverse of `lowerGL c` is `(1, 0; -c, 1)`. -/
public theorem coe_lowerGL_inv (c : F) :
    (((lowerGL c)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, 0; -c, 1] := rfl

/-- The matrix `(-π λ⁻², λ⁻¹; λ⁻¹, 0)`, with inverse `(0, λ; λ, π)`. -/
public def swapGL (π : F) {l : F} (hl : l ≠ 0) : GL (Fin 2) F where
  val := !![-(π * l⁻¹ * l⁻¹), l⁻¹; l⁻¹, 0]
  inv := !![0, l; l, π]
  val_inv := by
    rw [mul_fin_two, one_fin_two]
    ext i j; fin_cases i <;> fin_cases j <;> simp [hl]
    field_simp
    ring
  inv_val := by
    rw [mul_fin_two, one_fin_two]
    ext i j; fin_cases i <;> fin_cases j <;> simp [hl]
    field_simp
    ring

/-- The matrix of `swapGL π hl` is `(-π λ⁻², λ⁻¹; λ⁻¹, 0)`. -/
@[simp]
public theorem coe_swapGL (π : F) {l : F} (hl : l ≠ 0) :
    ((swapGL π hl : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![-(π * l⁻¹ * l⁻¹), l⁻¹; l⁻¹, 0] := rfl

/-- The matrix of the inverse of `swapGL π hl` is `(0, λ; λ, π)`. -/
public theorem coe_swapGL_inv (π : F) {l : F} (hl : l ≠ 0) :
    (((swapGL π hl)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, l; l, π] := rfl

end LocalGL

section KFree

variable {K : Type u} [Field K]

/-- The matrix of `diagGL o` is `diag(o, 1)`. -/
@[simp]
public theorem coe_diagGL {R : Type*} [CommRing R] (o : Rˣ) :
    ((diagGL o : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = !![(o : R), 0; 0, 1] := rfl

/-- `diag(a b, 1) = diag(a, 1) diag(b, 1)`. -/
public theorem diagGL_mul {R : Type*} [CommRing R] (a b : Rˣ) :
    diagGL (a * b) = diagGL a * diagGL b := by
  ext i j
  rw [Matrix.GeneralLinearGroup.coe_mul, coe_diagGL, coe_diagGL, coe_diagGL, mul_fin_two]
  fin_cases i <;> fin_cases j <;> simp

/-- The component at `w` of a product of ideles is the product of the components. -/
public theorem idele_mul_apply (a b : (AdeleRing K)ˣ) (w : Place K) :
    ((a * b : (AdeleRing K)ˣ) : AdeleRing K) w = (a : AdeleRing K) w * (b : AdeleRing K) w := rfl

/-- The component at `w` of `diag(y, 1)` is `diag(y_w, 1)`. -/
public theorem localMat_diagGL (w : Place K) (y : (AdeleRing K)ˣ) :
    localMat K w (diagGL y) = !![(y : AdeleRing K) w, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The component at `w` of `n(z) = (1, z; 0, 1)` is `(1, z_w; 0, 1)`. -/
public theorem localMat_upperRightHom (w : Place K) (z : AdeleRing K) :
    localMat K w (GeneralLinearGroup.upperRightHom z) = !![1, z w; 0, 1] := by
  rw [upperRightHom_eq_upperGL]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The component at `w` of the scalar matrix `c` is the scalar matrix `c_w`. -/
public theorem localMat_scalarGL (w : Place K) (c : (AdeleRing K)ˣ) :
    localMat K w (scalarGL c) = !![(c : AdeleRing K) w, 0; 0, (c : AdeleRing K) w] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [localMat, coe_scalarGL]

/-- The component at `v` of `localGL v m` is `m`. -/
public theorem localMat_localGL_self (v : Place K) (m : GL (Fin 2) v.completion) :
    localMat K v (localGL v m) = m :=
  mapMatrix_evalAt_localMatrix_self (m : Matrix (Fin 2) (Fin 2) v.completion)

/-- The component at a place `w ≠ v` of `localGL v m` is the identity. -/
public theorem localMat_localGL_ne {v w : Place K} (hw : w ≠ v) (m : GL (Fin 2) v.completion) :
    localMat K w (localGL v m) = 1 :=
  mapMatrix_evalAt_localMatrix_ne hw (m : Matrix (Fin 2) (Fin 2) v.completion)

/-- If `x` has component `m` at `v` and the identity elsewhere, its component at `v` is `m`. -/
public theorem localMat_of_isLocalMatrixAt_self {v : Place K}
    {m : Matrix (Fin 2) (Fin 2) v.completion} {x : GL (Fin 2) (AdeleRing K)}
    (h : IsLocalMatrixAt v m x) : localMat K v x = m :=
  mapMatrix_evalAt_self_of_isLocalMatrixAt h

/-- If `x` has component `m` at `v` and the identity elsewhere, its component at a place
`w ≠ v` is the identity. -/
public theorem localMat_of_isLocalMatrixAt_ne {v w : Place K}
    {m : Matrix (Fin 2) (Fin 2) v.completion} {x : GL (Fin 2) (AdeleRing K)}
    (h : IsLocalMatrixAt v m x) (hw : w ≠ v) : localMat K w x = 1 :=
  mapMatrix_evalAt_ne_of_isLocalMatrixAt h hw

/-- The identity matrix is integral at `w`. -/
public theorem isIntMat_one (w : Place K) : IsIntMat w (1 : Matrix (Fin 2) (Fin 2) w.completion) :=
  fun i j => by
    rw [Matrix.one_apply]
    split_ifs
    exacts [w.integers.one_mem, w.integers.zero_mem]

/-- A local matrix which is integral with integral inverse lies in `GL₂(O)`. -/
public theorem exists_mapO_eq_localGL {v : Place K} (m : GL (Fin 2) v.completion)
    (h : IsIntMat v (m : Matrix (Fin 2) (Fin 2) v.completion))
    (h' : IsIntMat v ((m⁻¹ : GL (Fin 2) v.completion) : Matrix (Fin 2) (Fin 2) v.completion)) :
    ∃ κ : GL (Fin 2) (integralAdeles K), mapO κ = localGL v m := by
  refine exists_mapO_of_isIntMat _ (fun w => ?_) (fun w => ?_)
  · by_cases hw : w = v
    · subst hw; rw [localMat_localGL_self]; exact h
    · rw [localMat_localGL_ne hw]; exact isIntMat_one w
  · rw [← map_inv]
    by_cases hw : w = v
    · subst hw; rw [localMat_localGL_self]; exact h'
    · rw [localMat_localGL_ne hw]; exact isIntMat_one w

end KFree

variable (k : Type u) [Field k] [Finite k] {K : Type u} [Field K] [Algebra k K]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
variable {Λ : Type w} [Field Λ]

section Valuations

include k

/-- The divisor of the idele `z` at `v`, `1` elsewhere, is `ord_v(z) · v`. -/
public theorem idelDiv_localIdele (v : Place K) {z : v.completion} (hz : z ≠ 0) :
    idelDiv k K (localIdele v hz) = Finsupp.single v (v.ordC z) := by
  classical
  ext w
  rw [idelDiv_apply]
  by_cases hw : w = v
  · subst hw
    rw [localIdele_apply_self, Finsupp.single_eq_same]
  · rw [localIdele_apply_ne hw, ordC_one k, Finsupp.single_apply, if_neg (Ne.symm hw)]

/-- A uniformizer `π` of `O_v` has `ord_v(π) = 1`. -/
public theorem ordC_of_isUniformizer {v : Place K} {π : v.integers}
    (hπ : Place.IsUniformizer v π) : v.ordC (π : v.completion) = 1 :=
  ordC_eq_of_valued_eq (isDiscrete k v) (coe_ne_zero_of_isUniformizer k hπ) (by
    rw [valued_eq_unifVal_of_isUniformizer (isDiscrete k v) hπ, zpow_one])

omit [Field k] [Finite k] [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
  [FunctionField k K] in
/-- A unit of `O_v` has valuation `1`. -/
public theorem valued_eq_one_of_isUnit {v : Place K} {l : v.integers} (hl : IsUnit l) :
    Valued.v (l : v.completion) = 1 :=
  (Place.integers_valuation_eq_one_iff l).1 ((ValuationSubring.valuation_eq_one_iff _ l).1 hl)

/-- For a uniformizer `π` and a unit `λ` of `O_v`, `ord_v(-π⁻¹ λ²) = -1`. -/
public theorem ordC_neg_inv_mul_mul {v : Place K} {π : v.integers}
    (hπ : Place.IsUniformizer v π) {l : v.integers} (hl : IsUnit l) :
    v.ordC (-((π : v.completion)⁻¹ * (l : v.completion) * (l : v.completion))) = -1 := by
  have hπ0 := coe_ne_zero_of_isUniformizer k hπ
  have hl0 : (l : v.completion) ≠ 0 := by exact_mod_cast hl.ne_zero
  refine ordC_eq_of_valued_eq (isDiscrete k v)
    (neg_ne_zero.2 (mul_ne_zero (mul_ne_zero (inv_ne_zero hπ0) hl0) hl0)) ?_
  rw [Valuation.map_neg, map_mul, map_mul, map_inv₀, valued_eq_one_of_isUnit k hl,
    valued_eq_unifVal_of_isUniformizer (isDiscrete k v) hπ, mul_one, mul_one, zpow_neg_one]

end Valuations

section WhittakerProperties

variable {f : GL (Fin 2) (AdeleRing K) → Λ} {ψ : AddChar (AdeleRing K) Λ}

/-- `W` is left `GL₂(O)`-invariant. -/
public theorem IsUnramifiedCuspForm.whittaker_mapO_mul (hf : IsUnramifiedCuspForm f)
    (κ : GL (Fin 2) (integralAdeles K)) (x : GL (Fin 2) (AdeleRing K)) :
    whittaker k K ψ f (mapO κ * x) = whittaker k K ψ f x := by
  simp only [whittaker, fourierCoeff]
  congr 1
  ext y
  rw [mul_assoc (mapO κ)]
  congr 1
  exact hf.left_invariant _ κ

/-- The integrand of the Whittaker function is periodic for some lattice. -/
public theorem IsUnramifiedCuspForm.exists_isPeriodic_whittaker (hf : IsUnramifiedCuspForm f)
    (hψ : IsAdelicChar k K ψ) (x : GL (Fin 2) (AdeleRing K)) (ξ : K) :
    ∃ D : Place K →₀ ℤ, IsPeriodic
      (fun y => f (x * GeneralLinearGroup.upperRightHom y) * ψ (diag k K ξ * y))
      (principal k K ⊔ adeleLattice K D) := by
  obtain ⟨D, hD⟩ := IsUnramifiedCuspForm.exists_isPeriodic k hf x
  exact hD.exists_mul_mulShift k hψ ξ

/-- `W(x n(z)) = ψ(z) W(x)`. -/
public theorem IsUnramifiedCuspForm.whittaker_mul_upperRightHom [NeZero (ringChar k : Λ)]
    (hf : IsUnramifiedCuspForm f) (hψ : IsAdelicChar k K ψ) (x : GL (Fin 2) (AdeleRing K))
    (z : AdeleRing K) :
    whittaker k K ψ f (x * GeneralLinearGroup.upperRightHom z) = ψ z * whittaker k K ψ f x := by
  obtain ⟨D, hD⟩ := IsUnramifiedCuspForm.exists_isPeriodic_whittaker k hf hψ x (-1)
  simp only [whittaker, fourierCoeff]
  rw [← adeleAvg_comp_add_right k hD z, ← adeleAvg_const_mul k _ (hD.comp_add_right z)]
  congr 1
  ext y
  have hz : ψ z ≠ 0 := (AddChar.val_isUnit ψ z).ne_zero
  have e1 : x * GeneralLinearGroup.upperRightHom z * GeneralLinearGroup.upperRightHom y =
      x * GeneralLinearGroup.upperRightHom (y + z) := by
    rw [mul_assoc, ← AddChar.map_add_eq_mul, add_comm z y]
  have e2 : ψ (diag k K (-1) * y) = ψ z * ψ (diag k K (-1) * (y + z)) := by
    rw [map_neg, map_one, neg_one_mul, neg_one_mul, neg_add, AddChar.map_add_eq_mul,
      AddChar.map_neg_eq_inv ψ z, mul_left_comm, mul_inv_cancel₀ hz, mul_one]
  rw [e1, e2]
  ring

/-- `W` inherits `T_v f = t f`: `W(g₀ x) + ∑ᵢ W(gᵢ x) = t W(x)`. -/
public theorem IsUnramifiedCuspForm.whittaker_hecke [NeZero (ringChar k : Λ)]
    (hf : IsUnramifiedCuspForm f) (hψ : IsAdelicChar k K ψ) {v : Place K} {t : Λ}
    (ht : IsHeckeEigenvalueAt v f t) {q : ℕ} {π : v.integers} {lam : Fin q → v.integers}
    {g₀ : GL (Fin 2) (AdeleRing K)} {g : Fin q → GL (Fin 2) (AdeleRing K)}
    (hd : IsHeckeDataAt v π lam g₀ g) (x : GL (Fin 2) (AdeleRing K)) :
    whittaker k K ψ f (g₀ * x) + ∑ i, whittaker k K ψ f (g i * x) = t * whittaker k K ψ f x := by
  classical
  set F : GL (Fin 2) (AdeleRing K) → AdeleRing K → Λ := fun x' y =>
    f (x' * GeneralLinearGroup.upperRightHom y) * ψ (diag k K (-1) * y) with hF
  have hW : ∀ x', whittaker k K ψ f x' = adeleAvg k K (F x') := fun x' => rfl
  have hper : ∀ x', ∃ D : Place K →₀ ℤ,
      IsPeriodic (F x') (principal k K ⊔ adeleLattice K D) :=
    fun x' => IsUnramifiedCuspForm.exists_isPeriodic_whittaker k hf hψ x' (-1)
  obtain ⟨D, hD⟩ := hper x
  obtain ⟨D₀, hD₀⟩ := hper (g₀ * x)
  obtain ⟨D₁, hD₁⟩ := exists_isPeriodic_sum k Finset.univ (fun i => F (g i * x))
    (fun i => hper (g i * x))
  have hpt : (fun y => t * F x y) = fun y => F (g₀ * x) y + ∑ i ∈ Finset.univ, F (g i * x) y := by
    funext y
    simp only [hF]
    rw [← mul_assoc, ← ht π lam g₀ g hd]
    simp only [heckeOperator, add_mul, Finset.sum_mul, mul_assoc]
  simp only [hW]
  rw [← adeleAvg_const_mul k t hD, hpt, adeleAvg_add k hD₀ hD₁,
    adeleAvg_sum k Finset.univ (fun i => F (g i * x)) (fun i => hper (g i * x))]

/-- If `f(x' n(y)) = c f(x n(y))` for all `y`, then `W(x') = c W(x)`. -/
private theorem whittaker_eq_mul_of_forall [NeZero (ringChar k : Λ)]
    (hf : IsUnramifiedCuspForm f) (hψ : IsAdelicChar k K ψ) {x x' : GL (Fin 2) (AdeleRing K)}
    {c : Λ} (h : ∀ y, f (x' * GeneralLinearGroup.upperRightHom y) =
      c * f (x * GeneralLinearGroup.upperRightHom y)) :
    whittaker k K ψ f x' = c * whittaker k K ψ f x := by
  obtain ⟨D, hD⟩ := IsUnramifiedCuspForm.exists_isPeriodic_whittaker k hf hψ x (-1)
  simp only [whittaker, fourierCoeff]
  rw [← adeleAvg_const_mul k c hD]
  congr 1
  ext y
  rw [h, mul_assoc]

/-- `W` inherits `U_v f = u f`: `W(a x) = u W(x)`. -/
public theorem IsUnramifiedCuspForm.whittaker_central [NeZero (ringChar k : Λ)]
    (hf : IsUnramifiedCuspForm f) (hψ : IsAdelicChar k K ψ) {v : Place K} {u : Λ}
    (hu : IsCentralEigenvalueAt v f u) {a : GL (Fin 2) (AdeleRing K)} (ha : IsCentralDataAt v a)
    (x : GL (Fin 2) (AdeleRing K)) :
    whittaker k K ψ f (a * x) = u * whittaker k K ψ f x := by
  refine whittaker_eq_mul_of_forall k hf hψ fun y => ?_
  rw [mul_assoc]
  exact hu a ha _

end WhittakerProperties

section LocalIdentities

variable {v : Place K}

/-- For `c ∈ O_v` the matrix `(1, 0; c, 1)` of `lowerGL c` is integral. -/
public theorem isIntMat_lowerGL {c : v.completion} (hc : c ∈ v.integers) :
    IsIntMat v ((lowerGL c : GL (Fin 2) v.completion) : Matrix (Fin 2) (Fin 2) v.completion) := by
  rw [coe_lowerGL]
  exact isIntMat_of v.integers.one_mem v.integers.zero_mem hc v.integers.one_mem

/-- For `c ∈ O_v` the inverse `(1, 0; -c, 1)` of `lowerGL c` is integral. -/
public theorem isIntMat_lowerGL_inv {c : v.completion} (hc : c ∈ v.integers) :
    IsIntMat v (((lowerGL c)⁻¹ : GL (Fin 2) v.completion) :
      Matrix (Fin 2) (Fin 2) v.completion) := by
  rw [coe_lowerGL_inv]
  exact isIntMat_of v.integers.one_mem v.integers.zero_mem (neg_mem hc)
    v.integers.one_mem

/-- For `π, λ⁻¹ ∈ O_v` the matrix `(-π λ⁻², λ⁻¹; λ⁻¹, 0)` of `swapGL π hl` is integral. -/
public theorem isIntMat_swapGL {π l : v.completion} (hl : l ≠ 0) (hπ : π ∈ v.integers)
    (hl' : l⁻¹ ∈ v.integers) :
    IsIntMat v ((swapGL π hl : GL (Fin 2) v.completion) : Matrix (Fin 2) (Fin 2) v.completion) := by
  rw [coe_swapGL]
  exact isIntMat_of (neg_mem (mul_mem (mul_mem hπ hl') hl'))
    hl' hl' v.integers.zero_mem

/-- For `π, λ ∈ O_v` the inverse `(0, λ; λ, π)` of `swapGL π hl` is integral. -/
public theorem isIntMat_swapGL_inv {π l : v.completion} (hl : l ≠ 0) (hπ : π ∈ v.integers)
    (hl' : l ∈ v.integers) :
    IsIntMat v (((swapGL π hl)⁻¹ : GL (Fin 2) v.completion) :
      Matrix (Fin 2) (Fin 2) v.completion) := by
  rw [coe_swapGL_inv]
  exact isIntMat_of v.integers.zero_mem hl' hl' hπ

/-- `diag(π⁻¹, 1)` at `v` times `diag(y, 1)` is `diag(y', 1)` with `y'` equal to `π⁻¹ y` at `v`
and to `y` elsewhere. -/
public theorem mul_diagGL_of_isLocalMatrixAt_diagonal {π : v.completion} (hπ0 : π ≠ 0)
    {g₀ : GL (Fin 2) (AdeleRing K)} (h : IsLocalMatrixAt v (Matrix.diagonal ![π⁻¹, 1]) g₀)
    (y : (AdeleRing K)ˣ) :
    g₀ * diagGL y = diagGL (localIdele v (inv_ne_zero hπ0) * y) := by
  classical
  refine localMat_ext fun w => ?_
  rw [localMat_mul, localMat_diagGL, localMat_diagGL, idele_mul_apply]
  rcases eq_or_ne w v with rfl | hw
  · rw [localMat_of_isLocalMatrixAt_self h,
      localIdele_apply_self]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · rw [localMat_of_isLocalMatrixAt_ne h hw,
      localIdele_apply_ne hw, one_mul, one_mul]

/-- The coset matrix `(1, 0; -π⁻¹λ, π⁻¹)` times `diag(y, 1)` is
`(1, 0; -π⁻¹λ, 1) · π⁻¹ · diag(π y, 1)`, all factors local at `v`. -/
public theorem mul_diagGL_of_isLocalMatrixAt_coset {π l : v.completion} (hπ0 : π ≠ 0)
    {gi : GL (Fin 2) (AdeleRing K)} (h : IsLocalMatrixAt v !![1, 0; -(π⁻¹ * l), π⁻¹] gi)
    (y : (AdeleRing K)ˣ) :
    gi * diagGL y = localGL v (lowerGL (-(π⁻¹ * l))) *
      (scalarGL (localIdele v (inv_ne_zero hπ0)) * diagGL (localIdele v hπ0 * y)) := by
  classical
  refine localMat_ext fun w => ?_
  rw [localMat_mul, localMat_mul, localMat_mul, localMat_diagGL, localMat_diagGL,
    localMat_scalarGL, idele_mul_apply]
  rcases eq_or_ne w v with rfl | hw
  · rw [localMat_of_isLocalMatrixAt_self h,
      localMat_localGL_self, localIdele_apply_self, localIdele_apply_self, coe_lowerGL]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hπ0]
  · rw [localMat_of_isLocalMatrixAt_ne h hw,
      localMat_localGL_ne hw, localIdele_apply_ne hw, localIdele_apply_ne hw]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

open scoped Classical in
/-- For `λ ≠ 0`, the coset matrix `(1, 0; -π⁻¹λ, π⁻¹)` times `diag(y, 1)` is
`(-π λ⁻², λ⁻¹; λ⁻¹, 0) · diag(y', 1) · n(z)` with `y' = -π⁻¹λ² y` at `v` and `y` elsewhere, and
`z = -(λ y_v)⁻¹` at `v` and `0` elsewhere. -/
public theorem mul_diagGL_of_isLocalMatrixAt_coset_of_ne_zero {π l : v.completion} (hπ0 : π ≠ 0)
    (hl : l ≠ 0) {gi : GL (Fin 2) (AdeleRing K)}
    (h : IsLocalMatrixAt v !![1, 0; -(π⁻¹ * l), π⁻¹] gi) (y : (AdeleRing K)ˣ) :
    gi * diagGL y = localGL v (swapGL π hl) *
      (diagGL (localIdele v (neg_ne_zero.2 (mul_ne_zero (mul_ne_zero (inv_ne_zero hπ0) hl) hl)) *
        y) * GeneralLinearGroup.upperRightHom (singleAdele v (-(l * (y : AdeleRing K) v)⁻¹))) := by
  refine localMat_ext fun w => ?_
  rw [localMat_mul, localMat_mul, localMat_mul, localMat_diagGL, localMat_diagGL,
    localMat_upperRightHom, idele_mul_apply]
  rcases eq_or_ne w v with rfl | hw
  · have hy := idele_apply_ne_zero y w
    rw [localMat_of_isLocalMatrixAt_self h,
      localMat_localGL_self, localIdele_apply_self, singleAdele_apply_self, coe_swapGL]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp
    ring
  · rw [localMat_of_isLocalMatrixAt_ne h hw,
      localMat_localGL_ne hw, localIdele_apply_ne hw, singleAdele_apply_ne hw]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

include k in
/-- The scalar `π⁻¹` at `v` (and `1` elsewhere) is central data for `U_v`. -/
public theorem isCentralDataAt_scalarGL_localIdele {π : v.integers} (hπ : Place.IsUniformizer v π) :
    IsCentralDataAt v
      (scalarGL (localIdele v (inv_ne_zero (coe_ne_zero_of_isUniformizer k hπ)))) := by
  classical
  refine ⟨π, hπ, fun i j => ?_, fun w hw i j => ?_⟩
  · simp only [coe_scalarGL, Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs <;> simp [localIdele_apply_self]
  · simp only [coe_scalarGL, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs <;> simp [localIdele_apply_ne hw]

end LocalIdentities

section Recursion

variable {f : GL (Fin 2) (AdeleRing K) → Λ} {ψ : AddChar (AdeleRing K) Λ}

variable (K) in
/-- The Whittaker coefficient `c(D) = W(diag(y_D, 1))` at a divisor `D`, for the idele
`y_D = idelOfDiv D` of divisor `D`. -/
public def whittakerDiv (ψ : AddChar (AdeleRing K) Λ) (f : GL (Fin 2) (AdeleRing K) → Λ)
    (D : Place K →₀ ℤ) : Λ :=
  whittaker k K ψ f (diagGL (idelOfDiv k K D))

/-- `W(diag(y, 1))` depends only on the divisor of `y`. -/
public theorem IsUnramifiedCuspForm.whittaker_diagGL (hf : IsUnramifiedCuspForm f)
    (y : (AdeleRing K)ˣ) :
    whittaker k K ψ f (diagGL y) = whittakerDiv k K ψ f (idelDiv k K y) := by
  set y' := idelOfDiv k K (idelDiv k K y)
  have h0 : idelDiv k K (y * y'⁻¹) = 0 := by
    rw [idelDiv_mul, idelDiv_inv, idelDiv_idelOfDiv, add_neg_cancel]
  obtain ⟨o, ho⟩ := exists_integralUnit_of_idelDiv_eq_zero k h0
  have hmap : Units.map (integralAdeles K).subtype.toMonoidHom o = y * y'⁻¹ := Units.ext ho
  have hy : y = Units.map (integralAdeles K).subtype.toMonoidHom o * y' := by
    rw [hmap, inv_mul_cancel_right]
  rw [whittakerDiv]
  conv_lhs => rw [hy, diagGL_mul, ← map_diagGL]
  exact IsUnramifiedCuspForm.whittaker_mapO_mul k hf (diagGL o) _

/-- `c(D) = 0` unless `ψ` is trivial on `A(D)`: `diag(y, 1) n(z) ∈ GL₂(O) diag(y, 1)` for
`z ∈ A(div y)`, so `W(diag(y, 1)) = ψ(z) W(diag(y, 1))`. -/
public theorem IsUnramifiedCuspForm.whittakerDiv_eq_zero [NeZero (ringChar k : Λ)]
    (hf : IsUnramifiedCuspForm f) (hψ : IsAdelicChar k K ψ) {D : Place K →₀ ℤ} {z : AdeleRing K}
    (hz : z ∈ adeleLattice K D) (hne : ψ z ≠ 1) : whittakerDiv k K ψ f D = 0 := by
  set y := idelOfDiv k K D
  have hyD : idelDiv k K y = D := idelDiv_idelOfDiv k D
  have hint : (y : AdeleRing K) * z ∈ integralAdeles K := by
    rw [← mem_adeleLattice_zero_iff]
    have := (idele_mul_mem_adeleLattice_iff k y (E := D)).2 hz
    rwa [hyD, sub_self] at this
  have hmat : diagGL y * GeneralLinearGroup.upperRightHom z =
      mapO (GeneralLinearGroup.upperRightHom ⟨_, hint⟩) * diagGL y := by
    rw [mapO, mapO_upperRightHom, diagGL_eq_upperGL, upperGL_mul_upperRightHom, inv_one,
      Units.val_one, mul_one]
  have h1 := IsUnramifiedCuspForm.whittaker_mul_upperRightHom k hf hψ (diagGL y) z
  rw [hmat, IsUnramifiedCuspForm.whittaker_mapO_mul k hf] at h1
  have : (ψ z - 1) * whittaker k K ψ f (diagGL y) = 0 := by rw [sub_mul, ← h1, one_mul, sub_self]
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)

/-- **The Hecke recursion for the Whittaker coefficients of an eigenform.** If `ψ` is trivial on
`A(D)`, then `t_v c(D) = q_v c(D - v) + u_v c(D + v)`. -/
public theorem IsEigenform.whittakerDiv_recursion [NeZero (ringChar k : Λ)] {t u : Place K → Λ}
    (hf : IsEigenform f t u) (hψ : IsAdelicChar k K ψ) {D : Place K →₀ ℤ}
    (hD : ∀ a ∈ adeleLattice K D, ψ a = 1) (v : Place K) :
    t v * whittakerDiv k K ψ f D =
      (v.residueCard : Λ) * whittakerDiv k K ψ f (D - Finsupp.single v 1) +
        u v * whittakerDiv k K ψ f (D + Finsupp.single v 1) := by
  classical
  have hcusp := hf.isUnramifiedCuspForm
  have hv := isDiscrete k v
  obtain ⟨π, lam, g₀, g, hd⟩ := exists_isHeckeDataAt k v
  have hπ := hd.isUniformizer
  have hπ0 := coe_ne_zero_of_isUniformizer k hπ
  set y := idelOfDiv k K D
  have hyD : idelDiv k K y = D := idelDiv_idelOfDiv k D
  have hW : ∀ y' : (AdeleRing K)ˣ,
      whittaker k K ψ f (diagGL y') = whittakerDiv k K ψ f (idelDiv k K y') :=
    IsUnramifiedCuspForm.whittaker_diagGL k hcusp
  have hloc : ∀ (z : v.completion) (hz : z ≠ 0),
      whittaker k K ψ f (diagGL (localIdele v hz * y)) =
        whittakerDiv k K ψ f (D + Finsupp.single v (v.ordC z)) := fun z hz => by
    rw [hW, idelDiv_mul, idelDiv_localIdele k, hyD, add_comm]
  have hrel := IsUnramifiedCuspForm.whittaker_hecke k hcusp hψ (hf.hecke v) hd (diagGL y)
  -- the matrix `diag(π⁻¹, 1)`
  have h0 : whittaker k K ψ f (g₀ * diagGL y) =
      whittakerDiv k K ψ f (D - Finsupp.single v 1) := by
    rw [mul_diagGL_of_isLocalMatrixAt_diagonal hπ0 hd.diagonal, hloc,
      ordC_inv_of_isUniformizer hv hπ hπ0, Finsupp.single_neg, ← sub_eq_add_neg]
  -- the residue class of `0`
  obtain ⟨i₀, hi₀, huniq⟩ := hd.isResidueSystem 0
  have hmem₀ : lam i₀ ∈ Ideal.span {π} := by simpa using hi₀
  have hunit : ∀ i, i ≠ i₀ → IsUnit (lam i) := by
    intro i hi
    by_contra hnu
    apply hi
    refine huniq i ?_
    have : lam i ∈ IsLocalRing.maximalIdeal v.integers := (IsLocalRing.mem_maximalIdeal _).2 hnu
    rw [← hπ] at this
    simpa using this
  -- the coset with `λ ∈ (π)`
  have hc : (π : v.completion)⁻¹ * (lam i₀ : v.completion) ∈ v.integers := by
    rw [mul_comm]
    exact div_mem_integers_of_mem_span hmem₀ hπ0
  obtain ⟨κ₁, hκ₁⟩ :=
    exists_mapO_eq_localGL (lowerGL (-((π : v.completion)⁻¹ * (lam i₀ : v.completion))))
      (isIntMat_lowerGL (neg_mem hc)) (isIntMat_lowerGL_inv (neg_mem hc))
  have hi₀W : whittaker k K ψ f (g i₀ * diagGL y) =
      u v * whittakerDiv k K ψ f (D + Finsupp.single v 1) := by
    rw [mul_diagGL_of_isLocalMatrixAt_coset hπ0 (hd.coset i₀) y, ← hκ₁,
      IsUnramifiedCuspForm.whittaker_mapO_mul k hcusp,
      IsUnramifiedCuspForm.whittaker_central k hcusp hψ (hf.central v)
        (isCentralDataAt_scalarGL_localIdele k hπ),
      hloc, ordC_of_isUniformizer k hπ]
  -- the cosets with `λ` a unit
  have hiW : ∀ i ∈ Finset.univ.erase i₀, whittaker k K ψ f (g i * diagGL y) =
      whittakerDiv k K ψ f (D - Finsupp.single v 1) := by
    intro i hi
    have hu := hunit i (Finset.ne_of_mem_erase hi)
    have hval := valued_eq_one_of_isUnit k hu
    have hl0 : (lam i : v.completion) ≠ 0 := by exact_mod_cast hu.ne_zero
    have hlinv : (lam i : v.completion)⁻¹ ∈ v.integers := by
      show Valued.v ((lam i : v.completion)⁻¹) ≤ 1
      rw [map_inv₀, hval, inv_one]
    obtain ⟨κ, hκ⟩ := exists_mapO_eq_localGL (swapGL (π : v.completion) hl0)
      (isIntMat_swapGL hl0 π.2 hlinv) (isIntMat_swapGL_inv hl0 π.2 (lam i).2)
    have hz : singleAdele v (-((lam i : v.completion) * (y : AdeleRing K) v)⁻¹) ∈
        adeleLattice K D := by
      intro w
      rcases eq_or_ne w v with rfl | hw
      · rw [singleAdele_apply_self, Place.mem_ball, Valuation.map_neg, map_inv₀, map_mul, hval,
          one_mul, Place.valued_eq_unifVal_zpow_ordC hv (idele_apply_ne_zero y w),
          ← idelDiv_apply k y w, hyD, zpow_neg]
      · rw [singleAdele_apply_ne hw]
        exact (w.ball _).zero_mem
    rw [mul_diagGL_of_isLocalMatrixAt_coset_of_ne_zero hπ0 hl0 (hd.coset i) y, ← hκ,
      IsUnramifiedCuspForm.whittaker_mapO_mul k hcusp,
      IsUnramifiedCuspForm.whittaker_mul_upperRightHom k hcusp hψ, hD _ hz, one_mul, hloc,
      ordC_neg_inv_mul_mul k hπ hu, Finsupp.single_neg, ← sub_eq_add_neg]
  have hq : 1 ≤ v.residueCard := Fin.pos i₀
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀), hi₀W, Finset.sum_congr rfl hiW,
    Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin, h0, hW, hyD, nsmul_eq_mul, Nat.cast_sub hq, Nat.cast_one] at hrel
  linear_combination -hrel

end Recursion

section MultiplicityOne

/-- **Uniqueness for the Hecke recursion.** A function `c` on divisors which vanishes outside
`D ≤ W₀`, satisfies `t_v c(D) = q_v c(D - v) + u_v c(D + v)` for `D ≤ W₀`, and vanishes at
`W₀`, vanishes identically. -/
public theorem eq_zero_of_hecke_recursion [NeZero (ringChar k : Λ)] {W₀ : Place K →₀ ℤ}
    {t u : Place K → Λ} {c : (Place K →₀ ℤ) → Λ} (hsupp : ∀ D, ¬ D ≤ W₀ → c D = 0)
    (hrec : ∀ D, D ≤ W₀ → ∀ v : Place K, t v * c D =
      (v.residueCard : Λ) * c (D - Finsupp.single v 1) + u v * c (D + Finsupp.single v 1))
    (htop : c W₀ = 0) (D : Place K →₀ ℤ) : c D = 0 := by
  classical
  by_cases hD : D ≤ W₀
  swap
  · exact hsupp D hD
  have hq : ∀ v : Place K, IsUnit (v.residueCard : Λ) :=
    isUnit_residueCard k (Ne.isUnit (NeZero.ne (ringChar k : Λ)))
  have hsum_nonneg : ∀ E : Place K →₀ ℤ, 0 ≤ E → 0 ≤ E.sum fun _ m => m :=
    fun E hE => Finset.sum_nonneg fun v _ => hE v
  have hsum_sub : ∀ (E : Place K →₀ ℤ) (v : Place K),
      ((E - Finsupp.single v 1).sum fun _ m => m) = (E.sum fun _ m => m) - 1 := by
    intro E v
    rw [Finsupp.sum_sub_index (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
  suffices H : ∀ n : ℕ, ∀ E : Place K →₀ ℤ, 0 ≤ E → (E.sum fun _ m => m) = n →
      c (W₀ - E) = 0 by
    have h0 := hsum_nonneg (W₀ - D) (sub_nonneg.2 hD)
    have := H _ (W₀ - D) (sub_nonneg.2 hD) (Int.toNat_of_nonneg h0).symm
    rwa [sub_sub_cancel] at this
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro E hE hn
  by_cases hE0 : E = 0
  · rw [hE0, sub_zero]
    exact htop
  obtain ⟨v, hv⟩ : ∃ v, E v ≠ 0 := by
    by_contra h
    push Not at h
    exact hE0 (Finsupp.ext h)
  have hv1 : 1 ≤ E v := lt_of_le_of_ne (hE v) (Ne.symm hv)
  set E₁ := E - Finsupp.single v 1
  have hE₁ : 0 ≤ E₁ := fun w => by
    simp only [E₁, Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_apply]
    split_ifs with h
    · subst h; simpa using hv1
    · simpa using hE w
  have hsz₁ : (E₁.sum fun _ m => m) = (n : ℤ) - 1 := by rw [hsum_sub, hn]
  have hn1 : 1 ≤ n := by have := hsum_nonneg E₁ hE₁; omega
  have hc₁ : c (W₀ - E₁) = 0 := ih (n - 1) (by omega) E₁ hE₁ (by rw [hsz₁]; omega)
  have hc₂ : c (W₀ - E₁ + Finsupp.single v 1) = 0 := by
    by_cases h₁ : 1 ≤ E₁ v
    · set E₂ := E₁ - Finsupp.single v 1
      have hE₂ : 0 ≤ E₂ := fun w => by
        simp only [E₂, Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_apply]
        split_ifs with h
        · subst h; simpa using h₁
        · simpa using hE₁ w
      have hsz₂ : (E₂.sum fun _ m => m) = (n : ℤ) - 2 := by rw [hsum_sub, hsz₁]; ring
      have hn2 : 2 ≤ n := by have := hsum_nonneg E₂ hE₂; omega
      have := ih (n - 2) (by omega) E₂ hE₂ (by rw [hsz₂]; omega)
      rwa [show W₀ - E₂ = W₀ - E₁ + Finsupp.single v 1 by simp only [E₂]; abel] at this
    · apply hsupp
      intro hle
      have h' := hle v
      simp only [Finsupp.coe_add, Finsupp.coe_sub, Pi.add_apply, Pi.sub_apply,
        Finsupp.single_eq_same] at h'
      have := hE₁ v
      simp only [Finsupp.coe_zero, Pi.zero_apply] at this
      omega
  have hr := hrec (W₀ - E₁) (sub_le_self _ hE₁) v
  rw [hc₁, hc₂, mul_zero, mul_zero, add_zero,
    show W₀ - E₁ - Finsupp.single v 1 = W₀ - E by simp only [E₁]; abel] at hr
  exact ((hq v).mul_right_eq_zero).1 hr.symm

variable {f f' : GL (Fin 2) (AdeleRing K) → Λ} {ψ : AddChar (AdeleRing K) Λ}
  {t t' u : Place K → Λ}

include k in
/-- The ideles are generated by the units of `O` and the inverse uniformizers `ϖ_v⁻¹`: a subgroup
of `Aˣ` containing them is everything. -/
public theorem mem_of_mem_integralUnits_of_mem_unifInvIdele {Z : Subgroup (AdeleRing K)ˣ}
    (hO : ∀ o : (integralAdeles K)ˣ, Units.map (integralAdeles K).subtype.toMonoidHom o ∈ Z)
    (hU : ∀ v, unifInvIdele k v ∈ Z) (c : (AdeleRing K)ˣ) : c ∈ Z := by
  classical
  have hz : ∀ (a : Place K) (m : ℤ), idelDiv k K (unifInvIdele k a ^ m) = -Finsupp.single a m := by
    intro a m
    induction m using Int.induction_on with
    | zero => simp [idelDiv_one]
    | succ m ih' => rw [zpow_add_one, idelDiv_mul, ih', idelDiv_unifInvIdele,
        Finsupp.single_add]; abel
    | pred m ih' => rw [zpow_sub_one, idelDiv_mul, ih', idelDiv_inv, idelDiv_unifInvIdele,
        Finsupp.single_sub]; abel
  have hhom : ∀ (s : Finset (Place K)) (n : Place K → ℤ),
      idelDiv k K (∏ v ∈ s, unifInvIdele k v ^ n v) = -∑ v ∈ s, Finsupp.single v (n v) := by
    intro s n
    induction s using Finset.induction_on with
    | empty => simp [idelDiv_one]
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, idelDiv_mul, ih, Finset.sum_insert ha, neg_add, hz]
  have he : (∏ v ∈ (idelDiv k K c).support, unifInvIdele k v ^ (idelDiv k K c) v) ∈ Z :=
    Subgroup.prod_mem _ fun v _ => Subgroup.zpow_mem _ (hU v) _
  have hdiv : idelDiv k K
      (c * ∏ v ∈ (idelDiv k K c).support, unifInvIdele k v ^ (idelDiv k K c) v) = 0 := by
    rw [idelDiv_mul, hhom, ← Finsupp.sum, Finsupp.sum_single, add_neg_cancel]
  obtain ⟨o, ho⟩ := exists_integralUnit_of_idelDiv_eq_zero k hdiv
  have hce : c * ∏ v ∈ (idelDiv k K c).support, unifInvIdele k v ^ (idelDiv k K c) v ∈ Z := by
    rw [← (Units.ext ho : Units.map (integralAdeles K).subtype.toMonoidHom o = _)]
    exact hO o
  have := Z.mul_mem hce (Z.inv_mem he)
  rwa [mul_inv_cancel_right] at this

include k in
/-- The central eigenvalues of an eigenform are units. -/
public theorem IsEigenform.isUnit_central (hf : IsEigenform f t u) (v : Place K) :
    IsUnit (u v) := by
  obtain ⟨x, hx⟩ := hf.exists_isUnit
  have h := hf.central v _ (isCentralDataAt_scalarGL_unifInvIdele k v)
    (scalarGL (unifInvIdele k v)⁻¹ * x)
  simp only [centralOperator] at h
  rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul] at h
  rw [h] at hx
  exact isUnit_of_mul_isUnit_left hx

include k in
/-- **Central character.** Two eigenforms with the same central eigenvalues `u_v` are
multiplied by the same unit `ω(c)` under every scalar idele `c`. -/
public theorem IsEigenform.exists_centralChar (hf : IsEigenform f t u) (hf' : IsEigenform f' t' u)
    (c : (AdeleRing K)ˣ) : ∃ ω : Λˣ, ∀ x,
      f (scalarGL c * x) = ω * f x ∧ f' (scalarGL c * x) = ω * f' x := by
  classical
  let Z : Subgroup (AdeleRing K)ˣ :=
    { carrier := {c | ∃ ω : Λˣ, ∀ x,
        f (scalarGL c * x) = ω * f x ∧ f' (scalarGL c * x) = ω * f' x}
      one_mem' := ⟨1, fun x => by simp⟩
      mul_mem' := by
        rintro a b ⟨ω, hω⟩ ⟨ω', hω'⟩
        refine ⟨ω * ω', fun x => ?_⟩
        rw [map_mul, mul_assoc, (hω _).1, (hω' x).1, (hω _).2, (hω' x).2, Units.val_mul,
          mul_assoc, mul_assoc]
        exact ⟨rfl, rfl⟩
      inv_mem' := by
        rintro a ⟨ω, hω⟩
        refine ⟨ω⁻¹, fun x => ?_⟩
        have h := hω (scalarGL a⁻¹ * x)
        rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul] at h
        rw [h.1, h.2, ← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, one_mul]
        exact ⟨rfl, rfl⟩ }
  have hO : ∀ o : (integralAdeles K)ˣ, Units.map (integralAdeles K).subtype.toMonoidHom o ∈ Z := by
    intro o
    refine ⟨1, fun x => ?_⟩
    rw [← mapO_scalar o, Units.val_one, one_mul, one_mul]
    exact ⟨hf.isUnramifiedCuspForm.left_invariant x _,
      hf'.isUnramifiedCuspForm.left_invariant x _⟩
  have hU : ∀ v, unifInvIdele k v ∈ Z := by
    intro v
    refine ⟨(IsEigenform.isUnit_central k hf v).unit, fun x => ?_⟩
    exact ⟨hf.central v _ (isCentralDataAt_scalarGL_unifInvIdele k v) x,
      hf'.central v _ (isCentralDataAt_scalarGL_unifInvIdele k v) x⟩
  exact mem_of_mem_integralUnits_of_mem_unifInvIdele k hO hU c

/-- Scalars act on `W` as on `f`. -/
public theorem IsUnramifiedCuspForm.whittaker_scalarGL_mul [NeZero (ringChar k : Λ)]
    (hf : IsUnramifiedCuspForm f) (hψ : IsAdelicChar k K ψ) {c : (AdeleRing K)ˣ} {ω : Λ}
    (hω : ∀ x, f (scalarGL c * x) = ω * f x) (x : GL (Fin 2) (AdeleRing K)) :
    whittaker k K ψ f (scalarGL c * x) = ω * whittaker k K ψ f x := by
  refine whittaker_eq_mul_of_forall k hf hψ fun y => ?_
  rw [mul_assoc, hω]

/-- `(α, β; 0, δ) = δ · diag(α δ⁻¹, 1) · n(α⁻¹ β)`. -/
public theorem upperGL_eq_scalarGL_mul (α δ : (AdeleRing K)ˣ) (β : AdeleRing K) :
    upperGL α δ β = scalarGL δ * diagGL (α * δ⁻¹) *
      GeneralLinearGroup.upperRightHom (((α⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) * β) := by
  have h1 := Units.mul_inv δ
  have h2 := Units.mul_inv α
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, coe_scalarGL,
    coe_diagGL, upperRightHom_eq_upperGL, coe_upperGL, coe_upperGL]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply, Matrix.diagonal_apply]
  · linear_combination (-(α : AdeleRing K)) * h1
  · linear_combination (-(β * ((α : AdeleRing K) * ((α⁻¹ : (AdeleRing K)ˣ) : AdeleRing K)))) * h1
      - β * h2

/-- `W` on an upper triangular matrix: by the Iwasawa decomposition every value of `W` is
`W(κ (α, β; 0, δ)) = ψ(α⁻¹ β) ω(δ) c(div (α δ⁻¹))`. -/
public theorem IsUnramifiedCuspForm.whittaker_mapO_mul_upperGL [NeZero (ringChar k : Λ)]
    (hf : IsUnramifiedCuspForm f) (hψ : IsAdelicChar k K ψ) {δ : (AdeleRing K)ˣ} {ω : Λ}
    (hω : ∀ x, f (scalarGL δ * x) = ω * f x) (κ : GL (Fin 2) (integralAdeles K))
    (α : (AdeleRing K)ˣ) (β : AdeleRing K) :
    whittaker k K ψ f (mapO κ * upperGL α δ β) =
      ψ (((α⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) * β) *
        (ω * whittakerDiv k K ψ f (idelDiv k K (α * δ⁻¹))) := by
  rw [upperGL_eq_scalarGL_mul, IsUnramifiedCuspForm.whittaker_mapO_mul k hf,
    IsUnramifiedCuspForm.whittaker_mul_upperRightHom k hf hψ,
    IsUnramifiedCuspForm.whittaker_scalarGL_mul k hf hψ hω,
    IsUnramifiedCuspForm.whittaker_diagGL k hf]

/-- If all the coefficients `c(D)` of an eigenform vanish, so does its Whittaker function. -/
public theorem IsEigenform.whittaker_eq_zero [NeZero (ringChar k : Λ)] (hf : IsEigenform f t u)
    (hψ : IsAdelicChar k K ψ) (h0 : ∀ D, whittakerDiv k K ψ f D = 0)
    (x : GL (Fin 2) (AdeleRing K)) : whittaker k K ψ f x = 0 := by
  obtain ⟨κ, α, δ, β, rfl⟩ := exists_iwasawa x
  obtain ⟨ω, hω⟩ := IsEigenform.exists_centralChar k hf hf δ
  rw [show GeneralLinearGroup.map (integralAdeles K).subtype κ = mapO κ from rfl,
    IsUnramifiedCuspForm.whittaker_mapO_mul_upperGL k hf.isUnramifiedCuspForm hψ
      (fun x => (hω x).1), h0, mul_zero, mul_zero]

/-- The coefficients of an eigenform vanish outside `D ≤ W₀`, `A(W₀)` the greatest lattice on
which `ψ` is trivial. -/
public theorem IsUnramifiedCuspForm.whittakerDiv_eq_zero_of_not_le [NeZero (ringChar k : Λ)]
    (hf : IsUnramifiedCuspForm f) (hψ : IsAdelicChar k K ψ) {W₀ : Place K →₀ ℤ}
    (hW₀ : ∀ D, (∀ a ∈ adeleLattice K D, ψ a = 1) ↔ D ≤ W₀) {D : Place K →₀ ℤ}
    (hD : ¬ D ≤ W₀) : whittakerDiv k K ψ f D = 0 := by
  rw [← hW₀] at hD
  push Not at hD
  obtain ⟨a, ha, hne⟩ := hD
  exact IsUnramifiedCuspForm.whittakerDiv_eq_zero k hf hψ ha hne

/-- **The leading Whittaker coefficient of an eigenform is nonzero**: `c(W₀) ≠ 0`, for `A(W₀)`
the greatest lattice on which `ψ` is trivial. -/
public theorem IsEigenform.whittakerDiv_ne_zero [NeZero (ringChar k : Λ)]
    [HasEnoughRootsOfUnity Λ (ringChar k)] (hf : IsEigenform f t u) (hψ : IsAdelicChar k K ψ)
    (hψ1 : ψ ≠ 1) {W₀ : Place K →₀ ℤ}
    (hW₀ : ∀ D, (∀ a ∈ adeleLattice K D, ψ a = 1) ↔ D ≤ W₀) :
    whittakerDiv k K ψ f W₀ ≠ 0 := by
  intro htop
  have hc : ∀ D, whittakerDiv k K ψ f D = 0 :=
    eq_zero_of_hecke_recursion k (t := t) (u := u)
      (fun D hD => IsUnramifiedCuspForm.whittakerDiv_eq_zero_of_not_le k hf.isUnramifiedCuspForm
        hψ hW₀ hD)
      (fun D hD v => IsEigenform.whittakerDiv_recursion k hf hψ ((hW₀ D).2 hD) v) htop
  obtain ⟨x, hx⟩ := hf.exists_isUnit
  have hexp := (IsUnramifiedCuspForm.whittaker_expansion k hf.isUnramifiedCuspForm hψ hψ1 x).2
  simp only [IsEigenform.whittaker_eq_zero k hf hψ hc, finsum_zero] at hexp
  rw [hexp] at hx
  exact not_isUnit_zero hx

/-- **Multiplicity one.** Two eigenforms with the same eigenvalues `t_v` and `u_v` at every place
are proportional: `f' = a f`. The coefficients `c(D)` of both satisfy the same Hecke recursion
and vanish outside `D ≤ W₀`, so `c' - a c` vanishes for `a = c'(W₀) / c(W₀)`; hence `W' = a W`,
and `f' = a f` by the Fourier–Whittaker expansion. -/
public theorem IsEigenform.exists_eq_mul_of_eigenvalues_eq [NeZero (ringChar k : Λ)]
    [HasEnoughRootsOfUnity Λ (ringChar k)] (hf : IsEigenform f t u) (hf' : IsEigenform f' t u) :
    ∃ a : Λ, ∀ x, f' x = a * f x := by
  obtain ⟨ψ, hψ, hψ1⟩ := exists_isAdelicChar_ne_one k (K := K) (Λ := Λ)
  obtain ⟨W₀, hW₀⟩ := exists_forall_trivial_iff_le k hψ hψ1
  have hne := IsEigenform.whittakerDiv_ne_zero k hf hψ hψ1 hW₀
  set a := whittakerDiv k K ψ f' W₀ / whittakerDiv k K ψ f W₀
  have hsupp : ∀ D, ¬ D ≤ W₀ →
      whittakerDiv k K ψ f' D - a * whittakerDiv k K ψ f D = 0 := fun D hD => by
    rw [IsUnramifiedCuspForm.whittakerDiv_eq_zero_of_not_le k hf'.isUnramifiedCuspForm hψ hW₀ hD,
      IsUnramifiedCuspForm.whittakerDiv_eq_zero_of_not_le k hf.isUnramifiedCuspForm hψ hW₀ hD,
      mul_zero, sub_zero]
  have hrec : ∀ D, D ≤ W₀ → ∀ v : Place K,
      t v * (whittakerDiv k K ψ f' D - a * whittakerDiv k K ψ f D) =
        (v.residueCard : Λ) * (whittakerDiv k K ψ f' (D - Finsupp.single v 1) -
          a * whittakerDiv k K ψ f (D - Finsupp.single v 1)) +
        u v * (whittakerDiv k K ψ f' (D + Finsupp.single v 1) -
          a * whittakerDiv k K ψ f (D + Finsupp.single v 1)) := fun D hD v => by
    have h' := IsEigenform.whittakerDiv_recursion k hf' hψ ((hW₀ D).2 hD) v
    have h := IsEigenform.whittakerDiv_recursion k hf hψ ((hW₀ D).2 hD) v
    linear_combination h' - a * h
  have htop : whittakerDiv k K ψ f' W₀ - a * whittakerDiv k K ψ f W₀ = 0 := by
    rw [div_mul_cancel₀ _ hne, sub_self]
  have hc := eq_zero_of_hecke_recursion k (t := t) (u := u)
    (c := fun D => whittakerDiv k K ψ f' D - a * whittakerDiv k K ψ f D) hsupp hrec htop
  have hW : ∀ y, whittaker k K ψ f' y = a * whittaker k K ψ f y := by
    intro y
    obtain ⟨κ, α, δ, β, rfl⟩ := exists_iwasawa y
    obtain ⟨ω, hω⟩ := IsEigenform.exists_centralChar k hf hf' δ
    rw [show GeneralLinearGroup.map (integralAdeles K).subtype κ = mapO κ from rfl,
      IsUnramifiedCuspForm.whittaker_mapO_mul_upperGL k hf'.isUnramifiedCuspForm hψ
        (fun x => (hω x).2),
      IsUnramifiedCuspForm.whittaker_mapO_mul_upperGL k hf.isUnramifiedCuspForm hψ
        (fun x => (hω x).1)]
    have := hc (idelDiv k K (α * δ⁻¹))
    linear_combination (ψ (((α⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) * β) * (ω : Λ)) * this
  refine ⟨a, fun x => ?_⟩
  obtain ⟨-, hexp⟩ := IsUnramifiedCuspForm.whittaker_expansion k hf.isUnramifiedCuspForm hψ hψ1 x
  rw [(IsUnramifiedCuspForm.whittaker_expansion k hf'.isUnramifiedCuspForm hψ hψ1 x).2, hexp]
  simp_rw [hW]
  exact (mul_finsum _ a).symm

end MultiplicityOne

end Stacks.Adeles.GlobalFunctionField

end
