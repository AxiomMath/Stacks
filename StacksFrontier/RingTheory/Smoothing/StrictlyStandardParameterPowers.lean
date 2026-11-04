module

public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Smoothing.ParameterPowerAlgebra
public import StacksFrontier.RingTheory.Smoothing.SingularIdealFactorization
public import StacksFrontier.RingTheory.Smoothing.StablyFreeStrictlyStandardPowers

/-!
# Strictly standard powers of the parameters in the generic-element algebra

Let `A` be an algebra of finite type over a field `k`, let `a_1, …, a_t` generate the singular
ideal `H_{A/k}`, and let `B = A[x_1, …, x_d, z_{ij}]/(x_i^{2N} - Σ_j z_{ij} a_j)` be the algebra
of `Stacks.Smoothing.parameterPowerAlgebra`, viewed over `k[x_1, …, x_d]`. Inverting `a_j` makes
the defining relations solvable for `z_{i j}`, so `B_{a_j}` is a polynomial algebra over
`A_{a_j}[x_1, …, x_d]`; since `A_{a_j}` is smooth over `k`, that algebra is smooth over
`k[x_1, …, x_d]`. The relation `x_i^{2N} = Σ_j z_{ij} a_j` makes the `a_j` generate the unit
ideal of `B_{x_i}`, so `B_{x_i}` is smooth over `k[x_1, …, x_d]` by Zariski locality. Feeding
this into the two conclusions of Stacks 07FP shows that `C_{x_i}` is smooth over
`k[x_1, …, x_d]` with free module of differentials, and Stacks 07EZ then makes a common power
of every `x_i` strictly standard in `C` over `k[x_1, …, x_d]`.

## Main results

* `Stacks.Smoothing.smooth_parameterPowerAlgebra_of_isUnit`: `B` is smooth over
  `k[x_1, …, x_d]` once one of the coefficients `a_j` is invertible.
* `Stacks.Smoothing.smooth_parameterPowerAlgebra_localizationAway_coeff`: `B_{a_j}` is smooth
  over `k[x_1, …, x_d]` when `a_j` lies in the singular ideal of `A` over `k`.
* `Stacks.Smoothing.forall_algebraMap_mem_singularIdeal_parameterPowerAlgebra`: each `a_j` lies
  in the singular ideal of `B` over `k[x_1, …, x_d]`.
* `Stacks.Smoothing.smooth_parameterPowerAlgebra_localizationAway_X`: `B_{x_i}` is smooth over
  `k[x_1, …, x_d]`.
* `Stacks.Smoothing.exists_pos_isStrictlyStandard_X_pow`: **Stacks 07FQ**, a positive `c` with
  every `x_i^c` strictly standard in `C` over `k[x_1, …, x_d]`.
* `Stacks.Smoothing.resolutionTruncationOrder`, `Stacks.Smoothing.resolutionPowerExponent`:
  **Stacks 07FR**, the integers `n = N + dc` and `e = 8c`.

## Implementation notes

The variable elimination lives in `Stacks.Smoothing.ParameterPowerElim`: after
inverting `a_{j₀}` the relation for index `i` determines `z_{i j₀}`, and the remaining variables
are indexed by `Fin d × {j // j ≠ j₀} ⊕ Fin d`, the `z_{ij}` with `j ≠ j₀` first and the `x_i`
last, so that `MvPolynomial.sumAlgEquiv` presents the result as a polynomial algebra over
`A_{a_{j₀}}[x_1, …, x_d]`.

Statements about the algebra `C` of Stacks 07FP are made for an abstract `C` carrying exactly the
data and properties that `Stacks.Smoothing.exists_retraction_parameterPowerAlgebra` produces, so
that they compose with it without having to name its output.

## References

* [Stacks Project, Tag 07FQ](https://stacks.math.columbia.edu/tag/07FQ)
* [Stacks Project, Tag 07FR](https://stacks.math.columbia.edu/tag/07FR)
-/

@[expose] public section

open MvPolynomial
open scoped TensorProduct

namespace Stacks.Smoothing

universe u v

/-- Smoothness transports along a ring isomorphism commuting with the structure maps. -/
private lemma smooth_of_ringEquiv {R : Type*} [CommRing R] (A B : Type*) [CommRing A]
    [CommRing B] [Algebra R A] [Algebra R B] [Algebra.Smooth R A] (e : A ≃+* B)
    (he : ∀ r : R, e (algebraMap R A r) = algebraMap R B r) : Algebra.Smooth R B :=
  Algebra.Smooth.of_equiv (AlgEquiv.ofRingEquiv (f := e) he)

/-- Two localizations of `B` away from the same element are isomorphic over any base of `B`, so
smoothness over that base transfers between them. -/
private lemma smooth_of_isLocalization_away {R B : Type*} (T T' : Type*) [CommRing R]
    [CommRing B] [CommRing T] [CommRing T'] [Algebra R B] [Algebra B T] [Algebra B T']
    [Algebra R T] [Algebra R T'] [IsScalarTower R B T] [IsScalarTower R B T'] (x : B)
    [IsLocalization.Away x T] [IsLocalization.Away x T'] [Algebra.Smooth R T'] :
    Algebra.Smooth R T :=
  smooth_of_ringEquiv T' T
    (IsLocalization.algEquiv (Submonoid.powers x) T' T).toRingEquiv fun r => by
      rw [IsScalarTower.algebraMap_apply R B T', IsScalarTower.algebraMap_apply R B T]
      exact (IsLocalization.algEquiv (Submonoid.powers x) T' T).commutes _

/-- The generators of `parameterPowerIdeal`, spelled out. -/
private lemma parameterPowerIdeal_eq_span {A : Type*} [CommRing A] (d : ℕ) {t : ℕ} (N : ℕ)
    (a : Fin t → A) :
    parameterPowerIdeal d N a = Ideal.span (Set.range fun i : Fin d =>
      X (Sum.inl i) ^ (2 * N) - ∑ j, C (a j) * X (Sum.inr (i, j))) :=
  rfl

/-- The base map `k[x_1, …, x_d] → B` sends the variable `x_i` to the generator `x_i`. -/
private lemma parameterPowerBaseHom_X (k : Type*) {A : Type*} [CommRing k] [CommRing A]
    [Algebra k A] (d : ℕ) {t : ℕ} (N : ℕ) (a : Fin t → A) (i : Fin d) :
    parameterPowerBaseHom k d N a (X i) =
      Ideal.Quotient.mk (parameterPowerIdeal d N a) (X (Sum.inl i)) :=
  MvPolynomial.aeval_X _ _

/-- The base map `k[x_1, …, x_d] → B` is a `k`-algebra map. -/
private lemma parameterPowerBaseHom_C (k : Type*) {A : Type*} [CommRing k] [CommRing A]
    [Algebra k A] (d : ℕ) {t : ℕ} (N : ℕ) (a : Fin t → A) (r : k) :
    parameterPowerBaseHom k d N a (C r) = algebraMap k (parameterPowerAlgebra A d N a) r :=
  MvPolynomial.aeval_C _ _

/-- The base map `k[x_1, …, x_d] → B` sends a constant `r` to the class of the constant `r`. -/
private lemma algebraMap_mvPolynomial_C_parameterPowerAlgebra (k K : Type*) [CommRing k]
    [CommRing K] [Algebra k K] (d N : ℕ) {t : ℕ} (c : Fin t → K) (r : k) :
    algebraMap (MvPolynomial (Fin d) k) (parameterPowerAlgebra K d N c) (C r) =
      Ideal.Quotient.mk (parameterPowerIdeal d N c) (C (algebraMap k K r)) := by
  show parameterPowerBaseHom k d N c (C r) = _
  rw [parameterPowerBaseHom_C, IsScalarTower.algebraMap_apply k
    (MvPolynomial (Fin d ⊕ Fin d × Fin t) K) (parameterPowerAlgebra K d N c)]
  simp [MvPolynomial.algebraMap_eq, IsScalarTower.algebraMap_apply k K
    (MvPolynomial (Fin d ⊕ Fin d × Fin t) K)]

/-- Adjoining the same finite set of variables to the base and to the target of a smooth algebra
map keeps it smooth: `S[x_i]` is `k[x_i] ⊗_k S`. -/
theorem smooth_mvPolynomial_map (k K : Type*) [CommRing k] [CommRing K] [Algebra k K]
    [Algebra.Smooth k K] (ι : Type*) [Finite ι]
    [Algebra (MvPolynomial ι k) (MvPolynomial ι K)]
    (halg : ∀ p, algebraMap (MvPolynomial ι k) (MvPolynomial ι K) p =
      MvPolynomial.map (algebraMap k K) p) :
    Algebra.Smooth (MvPolynomial ι k) (MvPolynomial ι K) := by
  let e0 : (MvPolynomial ι k ⊗[k] K) ≃ₐ[k] MvPolynomial ι K :=
    (Algebra.TensorProduct.comm k (MvPolynomial ι k) K).trans
      ((MvPolynomial.algebraTensorAlgEquiv k K).restrictScalars k)
  have hcomm : ∀ p : MvPolynomial ι k,
      e0 (algebraMap (MvPolynomial ι k) (MvPolynomial ι k ⊗[k] K) p) =
        algebraMap (MvPolynomial ι k) (MvPolynomial ι K) p := by
    have key : (e0.toAlgHom.toRingHom.comp
        (algebraMap (MvPolynomial ι k) (MvPolynomial ι k ⊗[k] K))) =
        (MvPolynomial.map (algebraMap k K) : MvPolynomial ι k →+* MvPolynomial ι K) := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_) <;>
        simp [e0, Algebra.TensorProduct.algebraMap_apply]
    exact fun p => (RingHom.congr_fun key p).trans (halg p).symm
  exact Algebra.Smooth.of_equiv (AlgEquiv.ofRingEquiv (f := e0.toRingEquiv) hcomm)

/-! ### Eliminating the variables `z_{i j₀}` when `c j₀` is invertible -/

namespace ParameterPowerElim

variable {K : Type v} [CommRing K]

/-- The variables surviving the elimination of `z_{i j₀}`: the `z_{ij}` with `j ≠ j₀` first, then
the `x_i`. -/
abbrev Vars (d : ℕ) {t : ℕ} (j₀ : Fin t) := Fin d × {j : Fin t // j ≠ j₀} ⊕ Fin d

/-- The value `c_{j₀}^{-1}(x_i^{2N} - Σ_{j ≠ j₀} z_{ij} c_j)` substituted for `z_{i j₀}`. -/
noncomputable def zval (d N : ℕ) {t : ℕ} (c : Fin t → K) (j₀ : Fin t) (i : Fin d) :
    MvPolynomial (Vars d j₀) K :=
  Ring.inverse (c j₀) • (X (Sum.inr i) ^ (2 * N) -
    ∑ j : {j : Fin t // j ≠ j₀}, C (c j.1) * X (Sum.inl (i, j)))

/-- The substitution eliminating the variables `z_{i j₀}` and renaming the others. -/
noncomputable def subst (d N : ℕ) {t : ℕ} (c : Fin t → K) (j₀ : Fin t) :
    Fin d ⊕ Fin d × Fin t → MvPolynomial (Vars d j₀) K :=
  Sum.elim (fun i => X (Sum.inr i))
    (fun p => if h : p.2 = j₀ then zval d N c j₀ p.1 else X (Sum.inl (p.1, ⟨p.2, h⟩)))

/-- The substitution `subst` sends the variable `x_i` to `x_i`. -/
@[simp]
lemma subst_inl (d N : ℕ) {t : ℕ} (c : Fin t → K) (j₀ : Fin t) (i : Fin d) :
    subst d N c j₀ (Sum.inl i) = X (Sum.inr i) := rfl

/-- The substitution `subst` sends a variable `z_{ij}` with `j ≠ j₀` to the corresponding surviving
variable `z_{ij}`. -/
lemma subst_inr_of_ne (d N : ℕ) {t : ℕ} (c : Fin t → K) (j₀ : Fin t) (i : Fin d) {j : Fin t}
    (h : j ≠ j₀) : subst d N c j₀ (Sum.inr (i, j)) = X (Sum.inl (i, ⟨j, h⟩)) :=
  dite_eq_right h

/-- The substitution `subst` sends the variable `z_{i j₀}` to `zval`, that is, to
`c_{j₀}^{-1}(x_i^{2N} - Σ_{j ≠ j₀} z_{ij} c_j)`. -/
lemma subst_inr_self (d N : ℕ) {t : ℕ} (c : Fin t → K) (j₀ : Fin t) (i : Fin d) :
    subst d N c j₀ (Sum.inr (i, j₀)) = zval d N c j₀ i :=
  dite_eq_left rfl

/-- The algebra map `K[x_i, z_{ij}] → K[x_i, z_{ij} : j ≠ j₀]` given by `subst`. -/
noncomputable def fwdHom (d N : ℕ) {t : ℕ} (c : Fin t → K) (j₀ : Fin t) :
    MvPolynomial (Fin d ⊕ Fin d × Fin t) K →ₐ[K] MvPolynomial (Vars d j₀) K :=
  MvPolynomial.aeval (subst d N c j₀)

/-- `fwdHom` sends each variable `v` to `subst v`. -/
@[simp]
lemma fwdHom_X (d N : ℕ) {t : ℕ} (c : Fin t → K) (j₀ : Fin t) (v : Fin d ⊕ Fin d × Fin t) :
    fwdHom d N c j₀ (X v) = subst d N c j₀ v :=
  aeval_X _ _

/-- `fwdHom` fixes the constants. -/
@[simp]
lemma fwdHom_C (d N : ℕ) {t : ℕ} (c : Fin t → K) (j₀ : Fin t) (r : K) :
    fwdHom d N c j₀ (C r) = C r := by
  rw [fwdHom, aeval_C, algebraMap_eq]

/-- A sum over `Fin t` with `j₀` erased is the sum over the subtype `{j // j ≠ j₀}`. -/
lemma sum_erase_subtype {M : Type*} [AddCommMonoid M] {t : ℕ} (j₀ : Fin t) (f : Fin t → M) :
    ∑ j ∈ Finset.univ.erase j₀, f j = ∑ j : {j : Fin t // j ≠ j₀}, f j.1 :=
  Finset.sum_subtype (p := fun j => j ≠ j₀) _ (by simp) f

/-- A sum over `Fin t` splits as the term at `j₀` plus the sum over the indices `j ≠ j₀`. -/
lemma sum_split (M : Type*) [AddCommMonoid M] {t : ℕ} (j₀ : Fin t) (f : Fin t → M) :
    ∑ j, f j = f j₀ + ∑ j : {j : Fin t // j ≠ j₀}, f j.1 := by
  rw [← sum_erase_subtype j₀ f, ← Finset.add_sum_erase Finset.univ f (Finset.mem_univ j₀)]

/-- When `c_{j₀}` is invertible, `fwdHom` kills each generator `x_i^{2N} - Σ_j c_j z_{ij}` of
`parameterPowerIdeal`. -/
lemma fwdHom_gen (d N : ℕ) {t : ℕ} (c : Fin t → K) (j₀ : Fin t) (hj : IsUnit (c j₀))
    (i : Fin d) :
    fwdHom d N c j₀ (X (Sum.inl i) ^ (2 * N) - ∑ j, C (c j) * X (Sum.inr (i, j))) = 0 := by
  rw [map_sub, map_pow, map_sum, sub_eq_zero]
  simp only [map_mul, fwdHom_C, fwdHom_X, subst_inl]
  rw [sum_split _ j₀ (fun j => C (c j) * subst d N c j₀ (Sum.inr (i, j))), subst_inr_self]
  have hre : ∀ j : {j : Fin t // j ≠ j₀},
      C (c j.1) * subst d N c j₀ (Sum.inr (i, j.1)) = C (c j.1) * X (Sum.inl (i, j)) := by
    intro j
    rw [subst_inr_of_ne d N c j₀ i j.2]
  rw [Finset.sum_congr rfl fun j _ => hre j, zval, smul_eq_C_mul, ← mul_assoc,
    ← C_mul, show c j₀ * Ring.inverse (c j₀) = 1 from by rw [Ring.mul_inverse_cancel _ hj],
    C_1, one_mul]
  ring

/-- When `c_{j₀}` is invertible, `fwdHom` vanishes on `parameterPowerIdeal`. -/
lemma fwdHom_eq_zero_of_mem (d N : ℕ) {t : ℕ} (c : Fin t → K) (j₀ : Fin t) (hj : IsUnit (c j₀))
    {y : MvPolynomial (Fin d ⊕ Fin d × Fin t) K} (hy : y ∈ parameterPowerIdeal d N c) :
    fwdHom d N c j₀ y = 0 := by
  have hle : parameterPowerIdeal d N c ≤ RingHom.ker (fwdHom d N c j₀).toRingHom := by
    rw [parameterPowerIdeal_eq_span, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact RingHom.mem_ker.mpr (fwdHom_gen d N c j₀ hj i)
  exact RingHom.mem_ker.mp (hle hy)

/-- The elimination map on `B = K[x_i, z_{ij}]/(x_i^{2N} - Σ_j z_{ij} c_j)`. -/
noncomputable def fwd (d N : ℕ) {t : ℕ} (c : Fin t → K) (j₀ : Fin t) (hj : IsUnit (c j₀)) :
    parameterPowerAlgebra K d N c →ₐ[K] MvPolynomial (Vars d j₀) K :=
  Ideal.Quotient.liftₐ (parameterPowerIdeal d N c) (fwdHom d N c j₀)
    (fun _ hy => fwdHom_eq_zero_of_mem d N c j₀ hj hy)

/-- `fwd` on the class of a polynomial `y` is `fwdHom y`. -/
@[simp]
lemma fwd_mk (d N : ℕ) {t : ℕ} (c : Fin t → K) (j₀ : Fin t) (hj : IsUnit (c j₀))
    (y : MvPolynomial (Fin d ⊕ Fin d × Fin t) K) :
    fwd d N c j₀ hj (Ideal.Quotient.mk (parameterPowerIdeal d N c) y) = fwdHom d N c j₀ y :=
  rfl

/-- The inverse of the elimination map, adjoining back the variables `z_{i j₀}`. -/
noncomputable def bwd (d N : ℕ) {t : ℕ} (c : Fin t → K) (j₀ : Fin t) :
    MvPolynomial (Vars d j₀) K →ₐ[K] parameterPowerAlgebra K d N c :=
  MvPolynomial.aeval (Sum.elim
    (fun p : Fin d × {j : Fin t // j ≠ j₀} =>
      Ideal.Quotient.mk (parameterPowerIdeal d N c) (X (Sum.inr (p.1, p.2.1))))
    (fun i : Fin d => Ideal.Quotient.mk (parameterPowerIdeal d N c) (X (Sum.inl i))))

/-- `bwd` sends a constant `r` to its image in `B`. -/
@[simp]
lemma bwd_C (d N : ℕ) {t : ℕ} (c : Fin t → K) (j₀ : Fin t) (r : K) :
    bwd d N c j₀ (C r) = algebraMap K (parameterPowerAlgebra K d N c) r := by
  rw [bwd, aeval_C]

/-- `bwd` sends the surviving variable `z_{ij}`, `j ≠ j₀`, to the class of `z_{ij}` in `B`. -/
@[simp]
lemma bwd_X_inl (d N : ℕ) {t : ℕ} (c : Fin t → K) (j₀ : Fin t)
    (p : Fin d × {j : Fin t // j ≠ j₀}) :
    bwd d N c j₀ (X (Sum.inl p)) =
      Ideal.Quotient.mk (parameterPowerIdeal d N c) (X (Sum.inr (p.1, p.2.1))) :=
  aeval_X _ _

/-- `bwd` sends the variable `x_i` to the class of `x_i` in `B`. -/
@[simp]
lemma bwd_X_inr (d N : ℕ) {t : ℕ} (c : Fin t → K) (j₀ : Fin t) (i : Fin d) :
    bwd d N c j₀ (X (Sum.inr i)) =
      Ideal.Quotient.mk (parameterPowerIdeal d N c) (X (Sum.inl i)) :=
  aeval_X _ _

/-- `fwd` is a left inverse of `bwd`. -/
lemma fwd_bwd (d N : ℕ) {t : ℕ} (c : Fin t → K) (j₀ : Fin t) (hj : IsUnit (c j₀)) :
    (fwd d N c j₀ hj).comp (bwd d N c j₀) = AlgHom.id K (MvPolynomial (Vars d j₀) K) := by
  refine MvPolynomial.algHom_ext fun v => ?_
  obtain ⟨i, j⟩ | i := v
  · show fwd d N c j₀ hj (bwd d N c j₀ (X (Sum.inl (i, j)))) = X (Sum.inl (i, j))
    rw [bwd_X_inl, fwd_mk, fwdHom_X, subst_inr_of_ne d N c j₀ i j.2]
  · show fwd d N c j₀ hj (bwd d N c j₀ (X (Sum.inr i))) = X (Sum.inr i)
    rw [bwd_X_inr, fwd_mk, fwdHom_X, subst_inl]

/-- `bwd` is a left inverse of `fwd`. -/
lemma bwd_fwd (d N : ℕ) {t : ℕ} (c : Fin t → K) (j₀ : Fin t) (hj : IsUnit (c j₀)) :
    (bwd d N c j₀).comp (fwd d N c j₀ hj) = AlgHom.id K (parameterPowerAlgebra K d N c) := by
  refine Ideal.Quotient.algHom_ext _ (MvPolynomial.algHom_ext fun v => ?_)
  show bwd d N c j₀ (fwd d N c j₀ hj (Ideal.Quotient.mk _ (X v))) = Ideal.Quotient.mk _ (X v)
  rw [fwd_mk, fwdHom_X]
  obtain i | ⟨i, j⟩ := v
  · rw [subst_inl, bwd_X_inr]
  · by_cases h : j = j₀
    · rw [h, subst_inr_self, zval, map_smul, map_sub, map_pow, map_sum]
      simp only [map_mul, bwd_C, bwd_X_inl, bwd_X_inr]
      rw [parameterPowerAlgebra_X_pow N c i, sum_split _ j₀ (fun j =>
        algebraMap K (parameterPowerAlgebra K d N c) (c j) *
          Ideal.Quotient.mk (parameterPowerIdeal d N c) (X (Sum.inr (i, j))))]
      rw [add_sub_cancel_right]
      rw [Algebra.smul_def (R := K) (A := parameterPowerAlgebra K d N c)]
      rw [← mul_assoc, ← map_mul, Ring.inverse_mul_cancel _ hj, map_one, one_mul]
    · rw [subst_inr_of_ne d N c j₀ i h, bwd_X_inl]

/-- **Variable elimination.** Inverting `c_{j₀}` lets the defining relations of
`B = K[x_i, z_{ij}]/(x_i^{2N} - Σ_j z_{ij} c_j)` be solved for the `z_{i j₀}`, exhibiting `B` as
a polynomial algebra over `K` in the `x_i` and the remaining `z_{ij}`. -/
noncomputable def elimEquiv (d N : ℕ) {t : ℕ} (c : Fin t → K) (j₀ : Fin t) (hj : IsUnit (c j₀)) :
    parameterPowerAlgebra K d N c ≃ₐ[K] MvPolynomial (Vars d j₀) K :=
  AlgEquiv.ofAlgHom (fwd d N c j₀ hj) (bwd d N c j₀) (fwd_bwd d N c j₀ hj)
    (bwd_fwd d N c j₀ hj)

/-- The underlying map of `elimEquiv` is `fwd`. -/
@[simp]
lemma elimEquiv_apply (d N : ℕ) {t : ℕ} (c : Fin t → K) (j₀ : Fin t) (hj : IsUnit (c j₀))
    (x : parameterPowerAlgebra K d N c) :
    elimEquiv d N c j₀ hj x = fwd d N c j₀ hj x := rfl

end ParameterPowerElim

open ParameterPowerElim in
/-- If one coefficient `c_{j₀}` is invertible and `K` is smooth over `k`, then
`B = K[x_1, …, x_d, z_{ij}]/(x_i^{2N} - Σ_j z_{ij} c_j)` is smooth over `k[x_1, …, x_d]`: it is a
polynomial algebra over `K[x_1, …, x_d]`, which is the base change of `K` along
`k → k[x_1, …, x_d]`. -/
theorem smooth_parameterPowerAlgebra_of_isUnit (k : Type u) (K : Type v) [CommRing k]
    [CommRing K] [Algebra k K] [Algebra.Smooth k K] (d N : ℕ) {t : ℕ} (c : Fin t → K)
    (j₀ : Fin t) (hj : IsUnit (c j₀)) :
    Algebra.Smooth (MvPolynomial (Fin d) k) (parameterPowerAlgebra K d N c) := by
  let instRK : Algebra (MvPolynomial (Fin d) k) (MvPolynomial (Fin d) K) :=
    MvPolynomial.algebraMvPolynomial
  have halgRK : ∀ p, algebraMap (MvPolynomial (Fin d) k) (MvPolynomial (Fin d) K) p =
      MvPolynomial.map (algebraMap k K) p := fun _ => rfl
  have hsmRK : Algebra.Smooth (MvPolynomial (Fin d) k) (MvPolynomial (Fin d) K) :=
    smooth_mvPolynomial_map k K (Fin d) halgRK
  let instRT : Algebra (MvPolynomial (Fin d) k)
      (MvPolynomial (Fin d × {j : Fin t // j ≠ j₀}) (MvPolynomial (Fin d) K)) :=
    ((algebraMap (MvPolynomial (Fin d) K)
        (MvPolynomial (Fin d × {j : Fin t // j ≠ j₀}) (MvPolynomial (Fin d) K))).comp
      (algebraMap (MvPolynomial (Fin d) k) (MvPolynomial (Fin d) K))).toAlgebra
  have htowRT : IsScalarTower (MvPolynomial (Fin d) k) (MvPolynomial (Fin d) K)
      (MvPolynomial (Fin d × {j : Fin t // j ≠ j₀}) (MvPolynomial (Fin d) K)) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hsmT : Algebra.Smooth (MvPolynomial (Fin d) k)
      (MvPolynomial (Fin d × {j : Fin t // j ≠ j₀}) (MvPolynomial (Fin d) K)) :=
    have : Algebra.Smooth (MvPolynomial (Fin d) K)
        (MvPolynomial (Fin d × {j : Fin t // j ≠ j₀}) (MvPolynomial (Fin d) K)) :=
      ⟨inferInstance, Algebra.FinitePresentation.mvPolynomial _ _ _⟩
    Algebra.Smooth.comp (MvPolynomial (Fin d) k) (MvPolynomial (Fin d) K)
      (MvPolynomial (Fin d × {j : Fin t // j ≠ j₀}) (MvPolynomial (Fin d) K))
  have htowkT : IsScalarTower k (MvPolynomial (Fin d) k)
      (MvPolynomial (Fin d × {j : Fin t // j ≠ j₀}) (MvPolynomial (Fin d) K)) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      simp [MvPolynomial.algebraMap_eq, RingHom.algebraMap_toAlgebra]
  let E₀ : parameterPowerAlgebra K d N c ≃ₐ[K]
      MvPolynomial (Fin d × {j : Fin t // j ≠ j₀}) (MvPolynomial (Fin d) K) :=
    (elimEquiv d N c j₀ hj).trans
      (MvPolynomial.sumAlgEquiv K (Fin d × {j : Fin t // j ≠ j₀}) (Fin d))
  let E₁ : parameterPowerAlgebra K d N c ≃ₐ[k]
      MvPolynomial (Fin d × {j : Fin t // j ≠ j₀}) (MvPolynomial (Fin d) K) :=
    E₀.restrictScalars k
  have hcomm : ∀ p : MvPolynomial (Fin d) k,
      E₁ (algebraMap (MvPolynomial (Fin d) k) (parameterPowerAlgebra K d N c) p) =
        algebraMap (MvPolynomial (Fin d) k)
          (MvPolynomial (Fin d × {j : Fin t // j ≠ j₀}) (MvPolynomial (Fin d) K)) p := by
    have key : E₁.toAlgHom.comp (parameterPowerBaseHom k d N c) =
        (IsScalarTower.toAlgHom k (MvPolynomial (Fin d) K)
          (MvPolynomial (Fin d × {j : Fin t // j ≠ j₀}) (MvPolynomial (Fin d) K))).comp
          (MvPolynomial.mapAlgHom (σ := Fin d) (Algebra.ofId k K)) := by
      refine MvPolynomial.algHom_ext fun i => ?_
      show E₁ (parameterPowerBaseHom k d N c (MvPolynomial.X i)) = _
      rw [parameterPowerBaseHom_X]
      show E₀ (Ideal.Quotient.mk (parameterPowerIdeal d N c) (MvPolynomial.X (Sum.inl i))) = _
      show MvPolynomial.sumAlgEquiv K (Fin d × {j : Fin t // j ≠ j₀}) (Fin d)
        (elimEquiv d N c j₀ hj
          (Ideal.Quotient.mk (parameterPowerIdeal d N c) (MvPolynomial.X (Sum.inl i)))) = _
      rw [elimEquiv_apply, fwd_mk, fwdHom_X, subst_inl, MvPolynomial.sumAlgEquiv_X_inr]
      simp [MvPolynomial.algebraMap_eq]
    exact fun p => congrArg (fun f => f p) key
  exact Algebra.Smooth.of_equiv
    (AlgEquiv.ofRingEquiv (f := E₁.toRingEquiv) hcomm).symm

/-- **Step 2 of the proof of Stacks 07FQ.** If `a_{j₀}` lies in the singular ideal of `A` over
`k`, then `A_{a_{j₀}}` is smooth over `k`, and `B_{a_{j₀}}` — which is a polynomial algebra over
`A_{a_{j₀}}[x_1, …, x_d]` — is smooth over `k[x_1, …, x_d]`. -/
theorem smooth_parameterPowerAlgebra_localizationAway_coeff (k : Type u) (A : Type v)
    [CommRing k] [CommRing A] [Algebra k A] [Algebra.FinitePresentation k A] (d N : ℕ) {t : ℕ}
    (a : Fin t → A) (j₀ : Fin t) (hmem : a j₀ ∈ singularIdeal k A) :
    Algebra.Smooth (MvPolynomial (Fin d) k)
      (Localization.Away (algebraMap A (parameterPowerAlgebra A d N a) (a j₀))) := by
  classical
  have hsmK : Algebra.Smooth k (Localization.Away (a j₀)) :=
    smooth_localization_away_of_mem_singularIdeal k A hmem
  have hunit : IsUnit (algebraMap A (Localization.Away (a j₀)) (a j₀)) :=
    IsLocalization.Away.algebraMap_isUnit (a j₀)
  have hsm : Algebra.Smooth (MvPolynomial (Fin d) k)
      (parameterPowerAlgebra (Localization.Away (a j₀)) d N
        (fun j => algebraMap A (Localization.Away (a j₀)) (a j))) :=
    smooth_parameterPowerAlgebra_of_isUnit k (Localization.Away (a j₀)) d N _ j₀ hunit
  let algMvP : Algebra (MvPolynomial (Fin d ⊕ Fin d × Fin t) A)
      (MvPolynomial (Fin d ⊕ Fin d × Fin t) (Localization.Away (a j₀))) :=
    MvPolynomial.algebraMvPolynomial
  have hloc : IsLocalization
      (Submonoid.map (MvPolynomial.C : A →+* MvPolynomial (Fin d ⊕ Fin d × Fin t) A)
        (Submonoid.powers (a j₀)))
      (MvPolynomial (Fin d ⊕ Fin d × Fin t) (Localization.Away (a j₀))) :=
    MvPolynomial.isLocalization (Submonoid.powers (a j₀)) (Localization.Away (a j₀))
  have hsubeq : Algebra.algebraMapSubmonoid (parameterPowerAlgebra A d N a)
        (Submonoid.map (MvPolynomial.C : A →+* MvPolynomial (Fin d ⊕ Fin d × Fin t) A)
          (Submonoid.powers (a j₀)))
      = Submonoid.powers (algebraMap A (parameterPowerAlgebra A d N a) (a j₀)) := by
    unfold Algebra.algebraMapSubmonoid
    rw [Submonoid.map_powers, Submonoid.map_powers]
    congr 1
  have hquot : IsLocalization
      (Submonoid.powers (algebraMap A (parameterPowerAlgebra A d N a) (a j₀)))
      (MvPolynomial (Fin d ⊕ Fin d × Fin t) (Localization.Away (a j₀)) ⧸
        (parameterPowerIdeal d N a).map
          (algebraMap (MvPolynomial (Fin d ⊕ Fin d × Fin t) A)
            (MvPolynomial (Fin d ⊕ Fin d × Fin t) (Localization.Away (a j₀))))) := by
    rw [← hsubeq]; infer_instance
  have hgen : ∀ i : Fin d,
      (algebraMap (MvPolynomial (Fin d ⊕ Fin d × Fin t) A)
          (MvPolynomial (Fin d ⊕ Fin d × Fin t) (Localization.Away (a j₀))))
        (X (Sum.inl i) ^ (2 * N) - ∑ j, C (a j) * X (Sum.inr (i, j)))
      = X (Sum.inl i) ^ (2 * N) -
          ∑ j, C (algebraMap A (Localization.Away (a j₀)) (a j)) * X (Sum.inr (i, j)) := by
    intro i
    show MvPolynomial.map (algebraMap A (Localization.Away (a j₀))) _ = _
    simp
  have hidealeq : (parameterPowerIdeal d N a).map
        (algebraMap (MvPolynomial (Fin d ⊕ Fin d × Fin t) A)
          (MvPolynomial (Fin d ⊕ Fin d × Fin t) (Localization.Away (a j₀))))
      = parameterPowerIdeal d N (fun j => algebraMap A (Localization.Away (a j₀)) (a j)) := by
    rw [parameterPowerIdeal_eq_span, Ideal.map_span, ← Set.range_comp,
      parameterPowerIdeal_eq_span]
    exact congrArg Ideal.span (congrArg Set.range (funext hgen))
  let e1 := IsLocalization.algEquiv
    (Submonoid.powers (algebraMap A (parameterPowerAlgebra A d N a) (a j₀)))
    (Localization.Away (algebraMap A (parameterPowerAlgebra A d N a) (a j₀)))
    (MvPolynomial (Fin d ⊕ Fin d × Fin t) (Localization.Away (a j₀)) ⧸
      (parameterPowerIdeal d N a).map
        (algebraMap (MvPolynomial (Fin d ⊕ Fin d × Fin t) A)
          (MvPolynomial (Fin d ⊕ Fin d × Fin t) (Localization.Away (a j₀)))))
  let e2 := Ideal.quotEquivOfEq hidealeq
  have hcomm : ∀ p : MvPolynomial (Fin d) k,
      (e1.toRingEquiv.trans e2)
          (algebraMap (MvPolynomial (Fin d) k)
            (Localization.Away (algebraMap A (parameterPowerAlgebra A d N a) (a j₀))) p) =
        algebraMap (MvPolynomial (Fin d) k)
          (parameterPowerAlgebra (Localization.Away (a j₀)) d N
            (fun j => algebraMap A (Localization.Away (a j₀)) (a j))) p := by
    have hqmap : ∀ y : MvPolynomial (Fin d ⊕ Fin d × Fin t) A,
        algebraMap (parameterPowerAlgebra A d N a)
            (MvPolynomial (Fin d ⊕ Fin d × Fin t) (Localization.Away (a j₀)) ⧸
              (parameterPowerIdeal d N a).map
                (algebraMap (MvPolynomial (Fin d ⊕ Fin d × Fin t) A)
                  (MvPolynomial (Fin d ⊕ Fin d × Fin t) (Localization.Away (a j₀)))))
            (Ideal.Quotient.mk (parameterPowerIdeal d N a) y) =
          Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap A (Localization.Away (a j₀))) y) :=
      fun y => Ideal.Quotient.algebraMap_quotient_map_quotient y
    have key : ((e1.toRingEquiv.trans e2).toRingHom.comp
        (algebraMap (MvPolynomial (Fin d) k)
          (Localization.Away (algebraMap A (parameterPowerAlgebra A d N a) (a j₀)))))
        = algebraMap (MvPolynomial (Fin d) k)
          (parameterPowerAlgebra (Localization.Away (a j₀)) d N
            (fun j => algebraMap A (Localization.Away (a j₀)) (a j))) := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
      · show e2 (e1 (algebraMap (MvPolynomial (Fin d) k) _ (C r))) = _
        rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin d) k)
            (parameterPowerAlgebra A d N a)
            (Localization.Away (algebraMap A (parameterPowerAlgebra A d N a) (a j₀)))]
        rw [algebraMap_mvPolynomial_C_parameterPowerAlgebra k A d N a r]
        rw [e1.commutes, hqmap, MvPolynomial.map_C, Ideal.quotEquivOfEq_mk]
        show _ = algebraMap (MvPolynomial (Fin d) k) _ (C r)
        rw [algebraMap_mvPolynomial_C_parameterPowerAlgebra k (Localization.Away (a j₀)) d N _ r]
        rw [IsScalarTower.algebraMap_apply k A (Localization.Away (a j₀))]
      · show e2 (e1 (algebraMap (MvPolynomial (Fin d) k) _ (X i))) = _
        rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin d) k)
            (parameterPowerAlgebra A d N a)
            (Localization.Away (algebraMap A (parameterPowerAlgebra A d N a) (a j₀))),
          algebraMap_mvPolynomial_parameterPowerAlgebra_X, e1.commutes, hqmap,
          MvPolynomial.map_X, Ideal.quotEquivOfEq_mk]
        show _ = algebraMap (MvPolynomial (Fin d) k) _ (X i)
        rw [algebraMap_mvPolynomial_parameterPowerAlgebra_X]
    exact fun p => congrArg (fun f => f p) key
  refine smooth_of_ringEquiv (R := MvPolynomial (Fin d) k)
    (parameterPowerAlgebra (Localization.Away (a j₀)) d N
      (fun j => algebraMap A (Localization.Away (a j₀)) (a j)))
    (Localization.Away (algebraMap A (parameterPowerAlgebra A d N a) (a j₀)))
    (e1.toRingEquiv.trans e2).symm (fun p => ?_)
  exact (RingEquiv.symm_apply_eq _).mpr (hcomm p).symm

/-- The image in `B = A[x_i, z_{ij}]/(x_i^{2N} - Σ_j z_{ij} a_j)` of every generator `a_j` of
`H_{A/k}` lies in the singular ideal of `B` over `k[x_1, …, x_d]`: this is the first sentence of
the justification of Stacks 07FQ, in the form `B_{a_j}` is smooth over `k[x_1, …, x_d]` read
back through `Stacks.Smoothing.mem_singularIdeal_of_smooth_of_isLocalizationAway`. -/
theorem forall_algebraMap_mem_singularIdeal_parameterPowerAlgebra (k : Type u) (A : Type v)
    [CommRing k] [CommRing A] [Algebra k A] [Algebra.FinitePresentation k A] (d N : ℕ) {t : ℕ}
    (a : Fin t → A) (hmem : ∀ j, a j ∈ singularIdeal k A) :
    ∀ j, algebraMap A (parameterPowerAlgebra A d N a) (a j) ∈
      singularIdeal (MvPolynomial (Fin d) k) (parameterPowerAlgebra A d N a) := fun j =>
  mem_singularIdeal_of_smooth_of_isLocalizationAway (MvPolynomial (Fin d) k)
    (parameterPowerAlgebra A d N a)
    (Localization.Away (algebraMap A (parameterPowerAlgebra A d N a) (a j)))
    (smooth_parameterPowerAlgebra_localizationAway_coeff k A d N a j (hmem j))

/-- **Step 3 of the proof of Stacks 07FQ.** `B_{x_i}` is smooth over `k[x_1, …, x_d]`: the
relation `x_i^{2N} = Σ_j z_{ij} a_j` makes the `a_j` generate the unit ideal of `B_{x_i}`, and
each `B_{x_i a_j}` is a localization of the smooth algebra `B_{a_j}`. -/
theorem smooth_parameterPowerAlgebra_localizationAway_X (k : Type u) (A : Type v) [CommRing k]
    [CommRing A] [Algebra k A] [Algebra.FinitePresentation k A] (d N : ℕ) {t : ℕ}
    (a : Fin t → A) (hmem : ∀ j, a j ∈ singularIdeal k A) (i : Fin d) :
    Algebra.Smooth (MvPolynomial (Fin d) k)
      (Localization.Away (algebraMap (MvPolynomial (Fin d) k)
        (parameterPowerAlgebra A d N a) (MvPolynomial.X i))) := by
  classical
  have hXi : algebraMap (MvPolynomial (Fin d) k) (parameterPowerAlgebra A d N a)
      (MvPolynomial.X i) =
      Ideal.Quotient.mk (parameterPowerIdeal d N a) (X (Sum.inl i)) :=
    algebraMap_mvPolynomial_parameterPowerAlgebra_X k N a i
  -- `x_i` is invertible in `B_{x_i}` and `x_i^{2N}` is a combination of the `a_j` there.
  have hunit : IsUnit (algebraMap (parameterPowerAlgebra A d N a)
      (Localization.Away (algebraMap (MvPolynomial (Fin d) k)
        (parameterPowerAlgebra A d N a) (MvPolynomial.X i)))
      (algebraMap (MvPolynomial (Fin d) k) (parameterPowerAlgebra A d N a)
        (MvPolynomial.X i))) :=
    IsLocalization.Away.algebraMap_isUnit _
  have hpow : (algebraMap (parameterPowerAlgebra A d N a)
        (Localization.Away (algebraMap (MvPolynomial (Fin d) k)
          (parameterPowerAlgebra A d N a) (MvPolynomial.X i)))
        (algebraMap (MvPolynomial (Fin d) k) (parameterPowerAlgebra A d N a)
          (MvPolynomial.X i))) ^ (2 * N) =
      ∑ j, algebraMap (parameterPowerAlgebra A d N a) _
          (algebraMap A (parameterPowerAlgebra A d N a) (a j)) *
        algebraMap (parameterPowerAlgebra A d N a) _
          (Ideal.Quotient.mk (parameterPowerIdeal d N a) (X (Sum.inr (i, j)))) := by
    rw [hXi, ← map_pow, parameterPowerAlgebra_X_pow N a i, map_sum]
    exact Finset.sum_congr rfl fun j _ => map_mul _ _ _
  -- Hence the images of the `a_j` generate the unit ideal of `B_{x_i}`.
  have hspan : Ideal.span (Set.range fun j : Fin t =>
      algebraMap (parameterPowerAlgebra A d N a)
        (Localization.Away (algebraMap (MvPolynomial (Fin d) k)
          (parameterPowerAlgebra A d N a) (MvPolynomial.X i)))
        (algebraMap A (parameterPowerAlgebra A d N a) (a j))) = ⊤ := by
    obtain ⟨w, hw⟩ := (hunit.pow (2 * N)).exists_left_inv
    rw [Ideal.eq_top_iff_one, ← hw, hpow, Finset.mul_sum]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _
      (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨j, rfl⟩))
  refine smooth_of_span_eq_top_away _ _ _ hspan ?_
  rintro ⟨-, j, rfl⟩
  -- `B_{x_i a_j}` is a localization of `B_{a_j}` away from `x_i`, and `B_{a_j}` is smooth.
  have hsmc : Algebra.Smooth (MvPolynomial (Fin d) k)
      (Localization.Away (algebraMap A (parameterPowerAlgebra A d N a) (a j))) :=
    smooth_parameterPowerAlgebra_localizationAway_coeff k A d N a j (hmem j)
  have hsmT' : Algebra.Smooth (MvPolynomial (Fin d) k)
      (Localization.Away (algebraMap (parameterPowerAlgebra A d N a)
        (Localization.Away (algebraMap A (parameterPowerAlgebra A d N a) (a j)))
        (algebraMap (MvPolynomial (Fin d) k) (parameterPowerAlgebra A d N a)
          (MvPolynomial.X i)))) :=
    Algebra.Smooth.comp (MvPolynomial (Fin d) k)
      (Localization.Away (algebraMap A (parameterPowerAlgebra A d N a) (a j))) _
  have hawayT : IsLocalization.Away
      (algebraMap (MvPolynomial (Fin d) k) (parameterPowerAlgebra A d N a) (MvPolynomial.X i) *
        algebraMap A (parameterPowerAlgebra A d N a) (a j))
      (Localization.Away (algebraMap (parameterPowerAlgebra A d N a)
        (Localization.Away (algebraMap (MvPolynomial (Fin d) k)
          (parameterPowerAlgebra A d N a) (MvPolynomial.X i)))
        (algebraMap A (parameterPowerAlgebra A d N a) (a j)))) :=
    IsLocalization.Away.mul' (R := parameterPowerAlgebra A d N a)
      (S := Localization.Away (algebraMap (MvPolynomial (Fin d) k)
        (parameterPowerAlgebra A d N a) (MvPolynomial.X i))) _ _ _
  have hawayT' : IsLocalization.Away
      (algebraMap (MvPolynomial (Fin d) k) (parameterPowerAlgebra A d N a) (MvPolynomial.X i) *
        algebraMap A (parameterPowerAlgebra A d N a) (a j))
      (Localization.Away (algebraMap (parameterPowerAlgebra A d N a)
        (Localization.Away (algebraMap A (parameterPowerAlgebra A d N a) (a j)))
        (algebraMap (MvPolynomial (Fin d) k) (parameterPowerAlgebra A d N a)
          (MvPolynomial.X i)))) :=
    IsLocalization.Away.mul (R := parameterPowerAlgebra A d N a)
      (S := Localization.Away (algebraMap A (parameterPowerAlgebra A d N a) (a j))) _ _ _
  exact smooth_of_isLocalization_away
    (Localization.Away (algebraMap (parameterPowerAlgebra A d N a)
      (Localization.Away (algebraMap (MvPolynomial (Fin d) k)
        (parameterPowerAlgebra A d N a) (MvPolynomial.X i)))
      (algebraMap A (parameterPowerAlgebra A d N a) (a j))))
    (Localization.Away (algebraMap (parameterPowerAlgebra A d N a)
      (Localization.Away (algebraMap A (parameterPowerAlgebra A d N a) (a j)))
      (algebraMap (MvPolynomial (Fin d) k) (parameterPowerAlgebra A d N a)
        (MvPolynomial.X i))))
    (algebraMap (MvPolynomial (Fin d) k) (parameterPowerAlgebra A d N a) (MvPolynomial.X i) *
      algebraMap A (parameterPowerAlgebra A d N a) (a j))

/-- **Stacks 07FQ.** Let `A` be of finite type over a field `k`, let `a_1, …, a_t` generate the
singular ideal `H_{A/k}`, and let `C` be an algebra over `B = A[x_i, z_{ij}]/(x_i^{2N} - Σ_j
z_{ij} a_j)` with the two localization properties that Stacks 07FP supplies. Then some positive
power `x_i^c`, one `c` for all `i`, is strictly standard in `C` over `k[x_1, …, x_d]`. -/
@[stacks 07FQ]
theorem exists_pos_isStrictlyStandard_X_pow (k : Type u) (A : Type v) [Field k] [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] (d N : ℕ) {t : ℕ} (a : Fin t → A)
    (ha : Ideal.span (Set.range a) = singularIdeal k A) (C : Type v) [CommRing C]
    [Algebra (MvPolynomial (Fin d) k) C] [Algebra (parameterPowerAlgebra A d N a) C]
    [IsScalarTower (MvPolynomial (Fin d) k) (parameterPowerAlgebra A d N a) C]
    [Algebra.FinitePresentation (MvPolynomial (Fin d) k) C]
    (hC₁ : ∀ b : parameterPowerAlgebra A d N a,
      RingHom.IsLocalCompleteIntersection
          (algebraMap (MvPolynomial (Fin d) k) (Localization.Away b)) →
        (letI : Algebra (Localization.Away b)
            (Localization.Away (algebraMap (parameterPowerAlgebra A d N a) C b)) :=
          (Localization.awayMap (algebraMap (parameterPowerAlgebra A d N a) C) b).toAlgebra
        Algebra.Smooth (Localization.Away b)
            (Localization.Away (algebraMap (parameterPowerAlgebra A d N a) C b)) ∧
          HasFreeConormalPresentation (MvPolynomial (Fin d) k)
            (Localization.Away (algebraMap (parameterPowerAlgebra A d N a) C b))))
    (hC₂ : ∀ b : parameterPowerAlgebra A d N a,
      Algebra.Smooth (MvPolynomial (Fin d) k) (Localization.Away b) →
        Module.Free (Localization.Away (algebraMap (parameterPowerAlgebra A d N a) C b))
          (KaehlerDifferential (MvPolynomial (Fin d) k)
            (Localization.Away (algebraMap (parameterPowerAlgebra A d N a) C b)))) :
    ∃ c : ℕ, 0 < c ∧ ∀ i : Fin d, IsStrictlyStandard (R := MvPolynomial (Fin d) k)
      (algebraMap (MvPolynomial (Fin d) k) C (MvPolynomial.X i) ^ c) := by
  classical
  have : Algebra.FinitePresentation k A := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  have hmem : ∀ j, a j ∈ singularIdeal k A := fun j =>
    ha ▸ Ideal.subset_span ⟨j, rfl⟩
  -- For each `i`, the engine of Stacks 07EZ (e) applies to `C` at `x_i`.
  have hstd : ∀ i : Fin d, ∃ e₀ : ℕ, ∀ e : ℕ, e₀ ≤ e →
      IsStrictlyStandard (R := MvPolynomial (Fin d) k)
        (algebraMap (MvPolynomial (Fin d) k) C (MvPolynomial.X i) ^ e) := by
    intro i
    set b : parameterPowerAlgebra A d N a :=
      algebraMap (MvPolynomial (Fin d) k) (parameterPowerAlgebra A d N a) (MvPolynomial.X i)
      with hb
    have hbC : algebraMap (parameterPowerAlgebra A d N a) C b =
        algebraMap (MvPolynomial (Fin d) k) C (MvPolynomial.X i) := by
      rw [hb, ← IsScalarTower.algebraMap_apply]
    have hsmB : Algebra.Smooth (MvPolynomial (Fin d) k) (Localization.Away b) :=
      smooth_parameterPowerAlgebra_localizationAway_X k A d N a hmem i
    have hsmC : Algebra.Smooth (MvPolynomial (Fin d) k)
        (Localization.Away (algebraMap (parameterPowerAlgebra A d N a) C b)) :=
      smooth_localizationAway_awayMap_of_smooth b
        (hC₁ b isLocalCompleteIntersection_algebraMap_of_algebraSmooth).1
    have hfree : Module.Free (Localization.Away (algebraMap (parameterPowerAlgebra A d N a) C b))
        (KaehlerDifferential (MvPolynomial (Fin d) k)
          (Localization.Away (algebraMap (parameterPowerAlgebra A d N a) C b))) :=
      hC₂ b hsmB
    let S : SixStandardnessConditions.{u, v} :=
      { R := MvPolynomial (Fin d) k
        A := C
        a := algebraMap (parameterPowerAlgebra A d N a) C b }
    obtain ⟨e₀, he₀⟩ :=
      exists_eventually_isStrictlyStandard_pow S
        (free_of_differentials_implies_stably_free S ⟨hsmC, hfree⟩)
    exact ⟨e₀, fun e he => hbC ▸ he₀ e he⟩
  choose e₀ he₀ using hstd
  refine ⟨Finset.univ.sup e₀ + 1, Nat.succ_pos _, fun i => ?_⟩
  exact he₀ i _ (le_trans (Finset.le_sup (Finset.mem_univ i)) (Nat.le_succ _))

/-- **Stacks 07FR.** The order `n = N + dc` to which the local ring `Λ_q` is truncated in the
proof of Stacks 07FJ. -/
@[stacks 07FR]
def resolutionTruncationOrder (N d c : ℕ) : ℕ := N + d * c

/-- **Stacks 07FR.** The exponent `e = 8c` used in the proof of Stacks 07FJ: it is eight times
the exponent `c` making `x_i^c` strictly standard, so that `γ_i^e = (γ_i^c)^8` is the eighth
power required by Stacks 07F8. -/
@[stacks 07FR]
def resolutionPowerExponent (c : ℕ) : ℕ := 8 * c

end Stacks.Smoothing

end
