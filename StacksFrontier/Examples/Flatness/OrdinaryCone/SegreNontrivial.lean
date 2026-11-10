module

public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import StacksFrontier.Examples.Flatness.OrdinaryCone.FunctionField
public import StacksFrontier.Examples.Flatness.OrdinaryCone.Segre

/-!
# An Artin–Schreier obstruction on the Segre product

Let `k` be a field of characteristic two, `G` the cone over the ordinary elliptic curve `E` and
`Γ = ⊕_d G_d ⊗ k[s, t]_d` its Segre product with `k[s, t]`, the homogeneous coordinate ring of
`E × ℙ¹`. The function `(zs)² / (xs)² = (z / x)²` pulled back from `E` is not of the form `h² - h`
for any function `h` on `E × ℙ¹`, that is, for any quotient `h = α / β` of two homogeneous elements
of the same degree of `Γ`.

Clearing denominators gives `z² β² = x² (α² - α β)` in `G[s, t]`. Dehomogenizing the coefficients
at `x` turns this into `v² B² = A² - A B` over the function field `L = k(E)` of `E`, with `B ≠ 0`
because the dehomogenization is injective on each `G_d`. Then `A / B` is integral over the unique
factorization domain `L[s, t]`, hence a polynomial `P` with `P² - P = v²`, hence a constant, which
contradicts `Stacks.Examples.OrdinaryCone.CurveField.sq_add_self_ne_v_sq`.

## Main results

* `MvPolynomial.exists_eq_sq_sub_of_mul_sq_eq`: over a field `F`, if `γ B² = A² - A B` for
  polynomials `A`, `B ≠ 0` in finitely many variables, then `γ = u² - u` for some `u ∈ F`.
* `Stacks.Examples.OrdinaryCone.sq_zs_div_sq_xs_ne_sq_sub_self`: the obstruction above, in the
  fraction field of the Segre product (only the denominator needs to be homogeneous), and
  `Stacks.Examples.OrdinaryCone.forall_sq_sub_self_ne_sq_zs_div_sq_xs` for `α / β` with `α`, `β`
  homogeneous of the same degree.
-/

@[expose] public section

open MvPolynomial

/-- Over a field `F`, if `γ B² = A² - A B` for polynomials `A` and `B ≠ 0` in finitely many
variables, then `γ = u² - u` for some `u ∈ F`: the field `F` is closed under solutions of
`h² - h = γ` in the field of rational functions over it. -/
theorem MvPolynomial.exists_eq_sq_sub_of_mul_sq_eq {F σ : Type*} [Field F] [Finite σ] {γ : F}
    {A B : MvPolynomial σ F} (hB : B ≠ 0) (h : C γ * B ^ 2 = A ^ 2 - A * B) :
    ∃ u : F, γ = u ^ 2 - u := by
  set K := FractionRing (MvPolynomial σ F)
  have hB' : algebraMap (MvPolynomial σ F) K B ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ K)).2 hB
  have hmonic : (Polynomial.X ^ 2 - Polynomial.X - Polynomial.C (C γ) :
      Polynomial (MvPolynomial σ F)).Monic := by monicity!
  obtain ⟨P, hP⟩ := isInteger_of_is_root_of_monic hmonic
    (r := algebraMap (MvPolynomial σ F) K A / algebraMap (MvPolynomial σ F) K B) (by
      have := congrArg (algebraMap (MvPolynomial σ F) K) h
      simp only [map_mul, map_pow, map_sub] at this
      simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
      have hbinv := mul_inv_cancel₀ hB'
      rw [div_eq_mul_inv]
      linear_combination (-(algebraMap (MvPolynomial σ F) K B)⁻¹ ^ 2) * this +
        (algebraMap (MvPolynomial σ F) K A * (algebraMap (MvPolynomial σ F) K B)⁻¹ +
          algebraMap (MvPolynomial σ F) K (C γ) * (algebraMap (MvPolynomial σ F) K B *
            (algebraMap (MvPolynomial σ F) K B)⁻¹ + 1)) * hbinv)
  have hAP : A = P * B := IsFractionRing.injective _ K (by
    rw [map_mul, hP, div_mul_cancel₀ _ hB'])
  have hγ : C γ = P ^ 2 - P := by
    rw [hAP] at h
    exact mul_right_cancel₀ (pow_ne_zero 2 hB) (by linear_combination h)
  -- `P` is constant, by comparing total degrees.
  have hdeg : P.totalDegree = 0 := by
    by_contra hne
    have hP0 : P ≠ 0 := by rintro rfl; simp at hne
    have h2 : (P ^ 2).totalDegree = 2 * P.totalDegree := by
      rw [pow_two, totalDegree_mul_of_isDomain hP0 hP0, two_mul]
    have h3 : (P ^ 2 - P).totalDegree = 2 * P.totalDegree := by
      rw [sub_eq_add_neg, totalDegree_add_eq_left_of_totalDegree_lt (by
        rw [totalDegree_neg, h2]; omega), h2]
    rw [← hγ, totalDegree_C] at h3
    omega
  have hPc := totalDegree_eq_zero_iff_eq_C.1 hdeg
  exact ⟨P.coeff 0, C_injective σ F (by rw [hγ, map_sub, map_pow, ← hPc])⟩

namespace Stacks.Examples.OrdinaryCone

variable (k : Type*) [Field k]

/-- The `k`-subspace of `G[s, t]` of the polynomials all of whose coefficients have degree `d`. -/
private noncomputable def coeffComponent (d : ℕ) : Submodule k (MvPolynomial (Fin 2) (Cone k)) where
  carrier := {A | ∀ m, A.coeff m ∈ Cone.component k d}
  add_mem' ha hb m := by
    rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]; exact add_mem (ha m) (hb m)
  zero_mem' m := by rw [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]; exact zero_mem _
  smul_mem' c A hA m := by rw [coeff_smul]; exact Submodule.smul_mem _ c (hA m)

/-- The coefficients of an element of `G_d ⊗ k[s, t]_d` lie in `G_d`. -/
private theorem segreComponent_le_coeffComponent (d : ℕ) :
    segreComponent k d ≤ coeffComponent k d := by
  classical
  induction d with
  | zero =>
    rw [segreComponent, pow_zero, Submodule.one_le]
    intro m
    rw [coeff_one]
    split_ifs
    · exact Cone.one_mem_component_zero
    · exact zero_mem _
  | succ d ih =>
    rw [segreComponent, pow_succ, Submodule.mul_le]
    intro a ha b hb
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨⟨i, j⟩, rfl⟩ := hb
      dsimp only
      intro m
      have hg : (Ideal.Quotient.mk (Ideal.span {equation k}) (X i) : Cone k) ∈
          Cone.component k 1 := Cone.mem_component.2 ⟨X i, isHomogeneous_X _ _, rfl⟩
      rw [segreGen, ← mul_assoc, coeff_mul_X', mul_comm a, coeff_C_mul]
      split_ifs
      · rw [mul_comm]
        exact Cone.mul_mem_component (ih ha _) hg
      · exact zero_mem _
    | zero => rw [mul_zero]; exact zero_mem _
    | add b c _ _ hb hc => rw [mul_add]; exact add_mem hb hc
    | smul r b _ hb => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hb

/-- The dehomogenization at `x` is injective on each graded piece `G_d` of the cone. -/
theorem Cone.dehomogenize_injOn {d : ℕ} {g : Cone k} (hg : g ∈ component k d)
    (h0 : dehomogenize k g = 0) : g = 0 := by
  have := toFractionRing_dehomogenize k hg
  rw [h0, map_zero, eq_comm, div_eq_zero_iff] at this
  exact (map_eq_zero_iff _ (IsFractionRing.injective (Cone k) (FractionRing (Cone k)))).1
    (this.resolve_right (pow_ne_zero _ (algebraMap_x_ne_zero k)))

/-- **`(zs)² / (xs)²` is not an Artin–Schreier value on `E × ℙ¹`.** Let `k` be a field of
characteristic two. For elements `α` and `β ≠ 0` of the Segre product `Γ` with `β` homogeneous,
`(zs)² / (xs)² ≠ (α / β)² - α / β` in the fraction field of `Γ`. In particular this holds for
every function `α / β` on `E × ℙ¹`, with `α` and `β` homogeneous of the same degree. -/
theorem sq_zs_div_sq_xs_ne_sq_sub_self [CharP k 2] {d : ℕ} {α β : segre k}
    (hβ : β ∈ segreGrading k d) (hβ0 : β ≠ 0) :
    algebraMap (segre k) (FractionRing (segre k)) (segreElem k 2 0 ^ 2) /
        algebraMap (segre k) (FractionRing (segre k)) (segreElem k 0 0 ^ 2) ≠
      (algebraMap (segre k) (FractionRing (segre k)) α /
          algebraMap (segre k) (FractionRing (segre k)) β) ^ 2 -
        algebraMap (segre k) (FractionRing (segre k)) α /
          algebraMap (segre k) (FractionRing (segre k)) β := by
  intro heq
  set Ω := FractionRing (segre k)
  have hinj := IsFractionRing.injective (segre k) Ω
  have hxs : segreElem k 0 0 ≠ 0 := fun h => by
    have := congrArg Subtype.val h
    simp only [coe_segreElem, segreGen, ZeroMemClass.coe_zero, mul_eq_zero, C_eq_zero,
      X_ne_zero, or_false] at this
    exact Cone.x_ne_zero k this
  have hne : ∀ {a : segre k}, a ≠ 0 → algebraMap (segre k) Ω a ≠ 0 :=
    fun ha => (map_ne_zero_iff _ hinj).2 ha
  have hxs' := hne hxs
  have hβ' := hne hβ0
  -- Clear denominators in `Γ`, then in `G[s, t]`.
  have hΓ : segreElem k 2 0 ^ 2 * β ^ 2 = segreElem k 0 0 ^ 2 * (α ^ 2 - α * β) := by
    apply hinj
    rw [div_pow, div_sub_div _ _ (pow_ne_zero 2 hβ') hβ', map_pow, map_pow,
      div_eq_div_iff (pow_ne_zero 2 hxs') (mul_ne_zero (pow_ne_zero 2 hβ') hβ')] at heq
    simp only [map_mul, map_pow, map_sub]
    exact mul_left_cancel₀ hβ' (by linear_combination heq)
  have hG := congrArg Subtype.val hΓ
  simp only [Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_sub, coe_segreElem,
    segreGen] at hG
  set A := (α : MvPolynomial (Fin 2) (Cone k)) with hA
  set B := (β : MvPolynomial (Fin 2) (Cone k)) with hB
  have hG' : C (Cone.z k) ^ 2 * B ^ 2 = C (Cone.x k) ^ 2 * (A ^ 2 - A * B) := by
    refine mul_left_cancel₀ (pow_ne_zero 2 (X_ne_zero (0 : Fin 2))) ?_
    simp only [Cone.x, Cone.z]
    linear_combination hG
  -- Dehomogenize the coefficients at `x`.
  have hL := congrArg (MvPolynomial.map (Cone.dehomogenize k).toRingHom) hG'
  simp only [map_mul, map_pow, map_sub, map_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Cone.dehomogenize_x, Cone.dehomogenize_z, map_one, one_pow, one_mul] at hL
  have hB0 : MvPolynomial.map (Cone.dehomogenize k : Cone k →+* CurveField k) B ≠ 0 := by
    intro h0
    apply hβ0
    apply Subtype.ext
    ext m
    have hm := congrArg (fun p => p.coeff m) h0
    rw [coeff_map, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hm
    exact Cone.dehomogenize_injOn k (segreComponent_le_coeffComponent k d hβ m) hm
  obtain ⟨u, hu⟩ := MvPolynomial.exists_eq_sq_sub_of_mul_sq_eq (γ := CurveField.v k ^ 2) hB0
    (by rw [map_pow]; exact hL)
  refine CurveField.sq_add_self_ne_v_sq k u ?_
  have h2 : (2 : CurveField k) = 0 := by
    have : CharP (CurveField k) 2 :=
      charP_of_injective_algebraMap (algebraMap k (CurveField k)).injective 2
    exact CharTwo.two_eq_zero
  linear_combination -hu + u * h2

/-- `(zs)² / (xs)²` is not of the form `h² - h` for any function `h = α / β` on `E × ℙ¹`, with `α`
and `β ≠ 0` homogeneous of the same degree of the Segre product: the form of
`sq_zs_div_sq_xs_ne_sq_sub_self` consumed by the graded completion argument. -/
theorem forall_sq_sub_self_ne_sq_zs_div_sq_xs [CharP k 2] :
    ∀ (d : ℕ) (α β : segre k), α ∈ segreGrading k d → β ∈ segreGrading k d → β ≠ 0 →
      (algebraMap (segre k) (FractionRing (segre k)) α /
          algebraMap (segre k) (FractionRing (segre k)) β) ^ 2 -
        algebraMap (segre k) (FractionRing (segre k)) α /
          algebraMap (segre k) (FractionRing (segre k)) β ≠
      algebraMap (segre k) (FractionRing (segre k)) (segreElem k 2 0 ^ 2) /
        algebraMap (segre k) (FractionRing (segre k)) (segreElem k 0 0 ^ 2) :=
  fun _ _ _ _ hβ hβ0 => (sq_zs_div_sq_xs_ne_sq_sub_self k hβ hβ0).symm

end Stacks.Examples.OrdinaryCone
