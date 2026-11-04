module

public import StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.HeckeStability

/-!
# Unramified twists of eigenforms

Let `K` be a function field over a finite field `k`, and let `χ` be a character of the divisor
group of `K` with values in `Λˣ` which is trivial on principal divisors, that is, a character of
the divisor class group `Pic(X)` of the curve. Through the divisor `div (det x)` of the
determinant, `χ` gives a function on `GL₂(A)` which is invariant under `GL₂(K)` and under
`GL₂(O)`, and the twist of an unramified cusp form `f` by `χ` is `x ↦ χ(div (det x)) f(x)`.

The twist of an eigenform is an eigenform: the matrices of the formula for `T_v` have
determinant `π_v⁻¹` at `v` and `1` elsewhere, and the matrix of `U_v` has determinant `π_v⁻²`,
so if `T_v f = t_v f` and `U_v f = u_v f`, then the twist satisfies
`T_v = χ(v)⁻¹ t_v` and `U_v = χ(v)⁻² u_v`, where `χ(v)` is the value of `χ` at the prime
divisor `v`.

On the Galois side this corresponds to twisting `ρ` by the unramified character with
`F_v ↦ χ(v)⁻¹`; it is the reduction used to normalize the determinant of `ρ` in the proof of
the converse direction of the Langlands correspondence for `GL₂` (Stacks Tag 03VU).

## Main definitions

* `Stacks.Adeles.GlobalFunctionField.detCharacter` — `x ↦ χ(div (det x))` on `GL₂(A)`.
* `Stacks.Adeles.GlobalFunctionField.unramifiedTwist` — the twist `x ↦ χ(div (det x)) f(x)`.

## Main results

* `Stacks.Adeles.GlobalFunctionField.IsUnramifiedCuspForm.unramifiedTwist` — the twist of an
  unramified cusp form is an unramified cusp form.
* `Stacks.Adeles.GlobalFunctionField.IsEigenform.unramifiedTwist` — the twist of an eigenform
  with eigenvalues `t_v, u_v` is an eigenform with eigenvalues `χ(v)⁻¹ t_v, χ(v)⁻² u_v`.
-/

@[expose] public noncomputable section

open Matrix

universe u w

namespace Stacks.Adeles.GlobalFunctionField

section KFree

variable {K : Type u} [Field K]

/-- The determinant of an adelic matrix, at a place, is the determinant of its component
there. -/
public theorem val_det_apply (x : GL (Fin 2) (AdeleRing K)) (w : Place K) :
    ((GeneralLinearGroup.det x : (AdeleRing K)ˣ) : AdeleRing K) w =
      ((evalAt K w).mapMatrix (x : Matrix (Fin 2) (Fin 2) (AdeleRing K))).det := by
  show (evalAt K w) (x : Matrix (Fin 2) (Fin 2) (AdeleRing K)).det = _
  exact RingHom.map_det (evalAt K w) _

/-- At its own place `v`, a local matrix at `v` with component `m` evaluates to `m`. -/
public theorem mapMatrix_evalAt_self_of_isLocalMatrixAt {v : Place K}
    {m : Matrix (Fin 2) (Fin 2) v.completion} {x : GL (Fin 2) (AdeleRing K)}
    (h : IsLocalMatrixAt v m x) :
    (evalAt K v).mapMatrix (x : Matrix (Fin 2) (Fin 2) (AdeleRing K)) = m := by
  ext i j
  exact h.1 i j

/-- At a place `w ≠ v`, a local matrix at `v` evaluates to the identity matrix. -/
public theorem mapMatrix_evalAt_ne_of_isLocalMatrixAt {v w : Place K}
    {m : Matrix (Fin 2) (Fin 2) v.completion} {x : GL (Fin 2) (AdeleRing K)}
    (h : IsLocalMatrixAt v m x) (hw : w ≠ v) :
    (evalAt K w).mapMatrix (x : Matrix (Fin 2) (Fin 2) (AdeleRing K)) = 1 := by
  ext i j
  exact h.2 w hw i j

/-- `ord_v y = n` as soon as `v(y) = v(ϖ)ⁿ`. -/
public theorem ordC_eq_of_valued_eq {v : Place K} (hv : v.IsDiscrete) {y : v.completion}
    (hy : y ≠ 0) {n : ℤ} (h : Valued.v y = v.unifVal ^ n) : v.ordC y = n :=
  zpow_right_injective₀ (zero_lt_iff.2 (Place.unifVal_ne_zero hv)) (Place.unifVal_lt_one hv).ne
    ((Place.valued_eq_unifVal_zpow_ordC hv hy).symm.trans h)

/-- A uniformizer of `O_v` has the valuation of the uniformizer `ϖ ∈ K`. -/
public theorem valued_eq_unifVal_of_isUniformizer {v : Place K} (hv : v.IsDiscrete)
    {π : v.integers} (hπ : Place.IsUniformizer v π) :
    Valued.v (π : v.completion) = v.unifVal := by
  have h := hπ.trans (Place.isUniformizer_unif hv).symm
  obtain ⟨c, hc⟩ := (Ideal.span_singleton_eq_span_singleton.1 h)
  have hc1 : Valued.v ((c : v.integers) : v.completion) = 1 :=
    (Place.integers_valuation_eq_one_iff (c : v.integers)).1 (v.integers.valuation_unit c)
  have := congrArg (fun z : v.integers => Valued.v (z : v.completion)) hc
  simp only [MulMemClass.coe_mul, map_mul, hc1, mul_one] at this
  rw [this, Place.valued_coeRingHom]
  rfl

/-- A uniformizer has order `1`. -/
public theorem ordC_inv_of_isUniformizer {v : Place K} (hv : v.IsDiscrete)
    {π : v.integers} (hπ : Place.IsUniformizer v π) (hπ0 : (π : v.completion) ≠ 0) :
    v.ordC ((π : v.completion)⁻¹) = -1 :=
  ordC_eq_of_valued_eq hv (inv_ne_zero hπ0) (by
    rw [map_inv₀, valued_eq_unifVal_of_isUniformizer hv hπ, zpow_neg, zpow_one])

/-- The square of the inverse of a uniformizer has order `-2`. -/
public theorem ordC_inv_mul_inv_of_isUniformizer {v : Place K} (hv : v.IsDiscrete)
    {π : v.integers} (hπ : Place.IsUniformizer v π) (hπ0 : (π : v.completion) ≠ 0) :
    v.ordC ((π : v.completion)⁻¹ * (π : v.completion)⁻¹) = -2 := by
  rw [Place.ordC_mul hv (inv_ne_zero hπ0) (inv_ne_zero hπ0),
    ordC_inv_of_isUniformizer hv hπ hπ0]
  norm_num

/-- The value `χ(v)` of a character of the divisor group at the prime divisor `v`. -/
public abbrev primeValue {Λ : Type w} [CommRing Λ] (χ : Multiplicative (Place K →₀ ℤ) →* Λˣ)
    (v : Place K) : Λˣ :=
  χ (Multiplicative.ofAdd (Finsupp.single v 1))

/-- A character takes the divisor `-v` to `χ(v)⁻¹`. -/
public theorem map_ofAdd_single_neg_one {Λ : Type w} [CommRing Λ]
    (χ : Multiplicative (Place K →₀ ℤ) →* Λˣ) (v : Place K) :
    χ (Multiplicative.ofAdd (Finsupp.single v (-1))) = (primeValue χ v)⁻¹ := by
  rw [← map_inv, ← ofAdd_neg, Finsupp.single_neg]

/-- A character takes the divisor `-2v` to `χ(v)⁻²`. -/
public theorem map_ofAdd_single_neg_two {Λ : Type w} [CommRing Λ]
    (χ : Multiplicative (Place K →₀ ℤ) →* Λˣ) (v : Place K) :
    χ (Multiplicative.ofAdd (Finsupp.single v (-2))) = (primeValue χ v)⁻¹ ^ 2 := by
  have : Finsupp.single v (-2 : ℤ) = Finsupp.single v (-1) + Finsupp.single v (-1) := by
    rw [← Finsupp.single_add]; norm_num
  rw [this, ofAdd_add, map_mul, map_ofAdd_single_neg_one, sq]

end KFree

variable (k : Type u) [Field k] [Finite k] {K : Type u} [Field K] [Algebra k K]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]

include k

/-- The divisor of the determinant of an adelic matrix which is `m` at `v` and the identity
elsewhere is `ord_v (det m)` times the prime divisor `v`. -/
public theorem idelDiv_det_of_isLocalMatrixAt {v : Place K}
    {m : Matrix (Fin 2) (Fin 2) v.completion} {x : GL (Fin 2) (AdeleRing K)}
    (h : IsLocalMatrixAt v m x) :
    idelDiv k K (GeneralLinearGroup.det x) = Finsupp.single v (v.ordC m.det) := by
  classical
  ext w
  rw [idelDiv_apply, val_det_apply, Finsupp.single_apply]
  by_cases hw : w = v
  · subst hw
    rw [mapMatrix_evalAt_self_of_isLocalMatrixAt h, if_pos rfl]
  · rw [mapMatrix_evalAt_ne_of_isLocalMatrixAt h hw, det_one, if_neg (Ne.symm hw), ordC_one k]

/-- An idele which is a unit of the integral adeles has divisor `0`. -/
public theorem idelDiv_units_map_integralAdeles (o : (integralAdeles K)ˣ) :
    idelDiv k K (Units.map (integralAdeles K).subtype.toMonoidHom o) = 0 := by
  ext v
  rw [idelDiv_apply, Finsupp.coe_zero, Pi.zero_apply]
  set c : (AdeleRing K)ˣ := Units.map (integralAdeles K).subtype.toMonoidHom o
  have h1 : (c : AdeleRing K) v ∈ v.integers := (o : integralAdeles K).2 v
  have h2 : ((c⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) v ∈ v.integers :=
    ((o⁻¹ : (integralAdeles K)ˣ) : integralAdeles K).2 v
  rw [← Place.mem_ball_zero_iff, Place.mem_ball_iff_ordC (isDiscrete k v)] at h1 h2
  have h3 := ordC_inv_idele k c v
  rcases h1 with h1 | h1
  · exact absurd h1 (idele_apply_ne_zero c v)
  rcases h2 with h2 | h2
  · exact absurd h2 (idele_apply_ne_zero c⁻¹ v)
  omega

/-- An idele which is a unit of the principal adeles is the idele of an element of `Kˣ`. -/
public theorem exists_eq_diagUnit (c : (principalAdeles K)ˣ) :
    ∃ (κ : K) (hκ : κ ≠ 0),
      Units.map (principalAdeles K).subtype.toMonoidHom c = diagUnit k hκ := by
  obtain ⟨κ, hκ⟩ : ∃ κ : K, diag k K κ = ((c : principalAdeles K) : AdeleRing K) := by
    have h : ((c : principalAdeles K) : AdeleRing K) ∈ (diag k K).range := by
      rw [range_diag k]
      exact (c : principalAdeles K).2
    exact RingHom.mem_range.1 h
  have hκ0 : κ ≠ 0 := by
    rintro rfl
    obtain ⟨v⟩ := nonempty_place k (K := K)
    have h := congrArg (fun z : principalAdeles K => (z : AdeleRing K) v) c.mul_inv
    simp only [Subring.coe_mul, Subring.coe_one] at h
    rw [RestrictedProduct.mul_apply, ← hκ, map_zero, RestrictedProduct.zero_apply, zero_mul,
      RestrictedProduct.one_apply] at h
    exact zero_ne_one h
  exact ⟨κ, hκ0, Units.ext hκ.symm⟩

variable {k}

variable {Λ : Type w} [CommRing Λ]

variable (k) in
/-- The function `x ↦ χ(div (det x))` on `GL₂(A)` attached to a character `χ` of the divisor
group of `K`. -/
public def detCharacter (χ : Multiplicative (Place K →₀ ℤ) →* Λˣ) :
    GL (Fin 2) (AdeleRing K) →* Λˣ where
  toFun x := χ (Multiplicative.ofAdd (idelDiv k K (GeneralLinearGroup.det x)))
  map_one' := by rw [map_one, idelDiv_one k, ofAdd_zero, map_one]
  map_mul' x y := by rw [map_mul, idelDiv_mul k, ofAdd_add, map_mul]

/-- `detCharacter k χ x` is `χ` of the divisor of `det x`. -/
public theorem detCharacter_apply (χ : Multiplicative (Place K →₀ ℤ) →* Λˣ)
    (x : GL (Fin 2) (AdeleRing K)) :
    detCharacter k χ x = χ (Multiplicative.ofAdd (idelDiv k K (GeneralLinearGroup.det x))) :=
  rfl

/-- `χ(div (det x))` on the image of a matrix over a subring is `χ` of the divisor of its
determinant, as an idele. -/
private theorem detCharacter_map_subtype (χ : Multiplicative (Place K →₀ ℤ) →* Λˣ)
    (S : Subring (AdeleRing K)) (γ : GL (Fin 2) S) :
    detCharacter k χ (GeneralLinearGroup.map S.subtype γ) = χ (Multiplicative.ofAdd
      (idelDiv k K (Units.map S.subtype.toMonoidHom (GeneralLinearGroup.det γ)))) := by
  rw [detCharacter_apply, GeneralLinearGroup.map_det]
  rfl

/-- `χ(div (det x))` is trivial on `GL₂(K)` when `χ` is trivial on principal divisors. -/
public theorem detCharacter_principal {χ : Multiplicative (Place K →₀ ℤ) →* Λˣ}
    (hχ : ∀ (κ : K), κ ≠ 0 → χ (Multiplicative.ofAdd (principalDivisor k K κ)) = 1)
    (γ : GL (Fin 2) (principalAdeles K)) :
    detCharacter k χ (GeneralLinearGroup.map (principalAdeles K).subtype γ) = 1 := by
  obtain ⟨κ, hκ, he⟩ := exists_eq_diagUnit k (GeneralLinearGroup.det γ)
  rw [detCharacter_map_subtype, he, idelDiv_diagUnit]
  exact hχ κ hκ

/-- `χ(div (det x))` is trivial on `GL₂(O)`. -/
public theorem detCharacter_integral (χ : Multiplicative (Place K →₀ ℤ) →* Λˣ)
    (o : GL (Fin 2) (integralAdeles K)) :
    detCharacter k χ (GeneralLinearGroup.map (integralAdeles K).subtype o) = 1 := by
  rw [detCharacter_map_subtype, idelDiv_units_map_integralAdeles, ofAdd_zero, map_one]

/-- `χ(div (det x))` is invariant under the unipotent matrices `(1, z; 0, 1)`. -/
public theorem detCharacter_upperRightHom (χ : Multiplicative (Place K →₀ ℤ) →* Λˣ)
    (z : AdeleRing K) : detCharacter k χ (GeneralLinearGroup.upperRightHom z) = 1 := by
  have : GeneralLinearGroup.det (GeneralLinearGroup.upperRightHom z) = 1 :=
    Units.ext (by simp [Matrix.det_fin_two])
  rw [detCharacter_apply, this, idelDiv_one k, ofAdd_zero, map_one]

/-- The value of `χ(div (det x))` on an adelic matrix which is `m` at `v` and the identity
elsewhere. -/
public theorem detCharacter_of_isLocalMatrixAt (χ : Multiplicative (Place K →₀ ℤ) →* Λˣ)
    {v : Place K} {m : Matrix (Fin 2) (Fin 2) v.completion} {x : GL (Fin 2) (AdeleRing K)}
    (h : IsLocalMatrixAt v m x) :
    detCharacter k χ x = χ (Multiplicative.ofAdd (Finsupp.single v (v.ordC m.det))) := by
  rw [detCharacter_apply, idelDiv_det_of_isLocalMatrixAt k h]

variable (k) in
/-- The unramified twist `x ↦ χ(div (det x)) f(x)` of a function on `GL₂(A)` by a character `χ`
of the divisor group. -/
public def unramifiedTwist (χ : Multiplicative (Place K →₀ ℤ) →* Λˣ)
    (f : GL (Fin 2) (AdeleRing K) → Λ) : GL (Fin 2) (AdeleRing K) → Λ :=
  fun x => (detCharacter k χ x : Λ) * f x

/-- The unramified twist `x ↦ χ(div (det x)) f(x)`, pointwise. -/
public theorem unramifiedTwist_apply (χ : Multiplicative (Place K →₀ ℤ) →* Λˣ)
    (f : GL (Fin 2) (AdeleRing K) → Λ) (x : GL (Fin 2) (AdeleRing K)) :
    unramifiedTwist k χ f x = (detCharacter k χ x : Λ) * f x := rfl

/-- The twist of an unramified cusp form by a character of the divisor class group is an
unramified cusp form. -/
public theorem IsUnramifiedCuspForm.unramifiedTwist {χ : Multiplicative (Place K →₀ ℤ) →* Λˣ}
    (hχ : ∀ (κ : K), κ ≠ 0 → χ (Multiplicative.ofAdd (principalDivisor k K κ)) = 1)
    {f : GL (Fin 2) (AdeleRing K) → Λ} (hf : IsUnramifiedCuspForm f) :
    IsUnramifiedCuspForm (GlobalFunctionField.unramifiedTwist k χ f) where
  right_invariant x γ := by
    rw [unramifiedTwist_apply, unramifiedTwist_apply, map_mul, detCharacter_principal hχ,
      mul_one, hf.right_invariant]
  left_invariant x o := by
    rw [unramifiedTwist_apply, unramifiedTwist_apply, map_mul, detCharacter_integral, one_mul,
      hf.left_invariant]
  vanishing_constant_term x U hU hinv s hs := by
    have hdet : ∀ z, (detCharacter k χ (x * GeneralLinearGroup.upperRightHom z) : Λ) =
        detCharacter k χ x := fun z => by
      rw [map_mul, detCharacter_upperRightHom, mul_one]
    have hinv' : ∀ z : AdeleRing K, ∀ y ∈ U,
        f (x * GeneralLinearGroup.upperRightHom (z + y)) =
          f (x * GeneralLinearGroup.upperRightHom z) := fun z y hy => by
      have h := hinv z y hy
      rw [unramifiedTwist_apply, unramifiedTwist_apply, hdet, hdet] at h
      exact (Units.isUnit _).mul_right_injective h
    simp only [unramifiedTwist_apply, hdet, ← Finset.mul_sum,
      hf.vanishing_constant_term x U hU hinv' s hs, mul_zero]

/-- The Hecke sum of a twist, when the twisting function takes one value `c` on all the
matrices of the sum. -/
public theorem heckeOperator_unramifiedTwist {χ : Multiplicative (Place K →₀ ℤ) →* Λˣ} {q : ℕ}
    {g₀ : GL (Fin 2) (AdeleRing K)} {g : Fin q → GL (Fin 2) (AdeleRing K)} {c : Λˣ}
    (h0 : detCharacter k χ g₀ = c) (hi : ∀ i, detCharacter k χ (g i) = c)
    {f : GL (Fin 2) (AdeleRing K) → Λ} (x : GL (Fin 2) (AdeleRing K)) :
    heckeOperator g₀ g (GlobalFunctionField.unramifiedTwist k χ f) x =
      (c : Λ) * detCharacter k χ x * heckeOperator g₀ g f x := by
  simp only [heckeOperator, unramifiedTwist_apply, map_mul, h0, hi, Units.val_mul, mul_add,
    Finset.mul_sum]

/-- **The unramified twist of an eigenform.** If `f` is an eigenform with eigenvalues
`T_v f = t_v f` and `U_v f = u_v f`, and `χ` is a character of the divisor group of `K` trivial
on principal divisors, then `x ↦ χ(div (det x)) f(x)` is an eigenform with eigenvalues
`χ(v)⁻¹ t_v` and `χ(v)⁻² u_v`. -/
public theorem IsEigenform.unramifiedTwist {χ : Multiplicative (Place K →₀ ℤ) →* Λˣ}
    (hχ : ∀ (κ : K), κ ≠ 0 → χ (Multiplicative.ofAdd (principalDivisor k K κ)) = 1)
    {f : GL (Fin 2) (AdeleRing K) → Λ} {t u : Place K → Λ} (hf : IsEigenform f t u) :
    IsEigenform (GlobalFunctionField.unramifiedTwist k χ f)
      (fun v => ((primeValue χ v)⁻¹ : Λˣ) * t v)
      (fun v => (((primeValue χ v)⁻¹ ^ 2 : Λˣ) : Λ) * u v) where
  isUnramifiedCuspForm := IsUnramifiedCuspForm.unramifiedTwist hχ hf.isUnramifiedCuspForm
  exists_isUnit := by
    obtain ⟨x, hx⟩ := hf.exists_isUnit
    exact ⟨x, (Units.isUnit _).mul hx⟩
  hecke v := by
    intro q π lam g₀ g hd x
    have hv := isDiscrete k v
    have hπ0 := coe_ne_zero_of_isUniformizer k hd.isUniformizer
    have h0 : detCharacter k χ g₀ = (primeValue χ v)⁻¹ := by
      rw [detCharacter_of_isLocalMatrixAt χ hd.diagonal, det_diagonal, Fin.prod_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_one]
      rw [ordC_inv_of_isUniformizer hv hd.isUniformizer hπ0, map_ofAdd_single_neg_one]
    have hi : ∀ i, detCharacter k χ (g i) = (primeValue χ v)⁻¹ := fun i => by
      rw [detCharacter_of_isLocalMatrixAt χ (hd.coset i), det_fin_two_of]
      simp only [one_mul, zero_mul, sub_zero]
      rw [ordC_inv_of_isUniformizer hv hd.isUniformizer hπ0, map_ofAdd_single_neg_one]
    rw [heckeOperator_unramifiedTwist h0 hi, hf.hecke v π lam g₀ g hd x, unramifiedTwist_apply]
    ring
  central v := by
    intro a ha x
    obtain ⟨π, hπ, hloc⟩ := ha
    have hv := isDiscrete k v
    have hπ0 := coe_ne_zero_of_isUniformizer k hπ
    have h0 : detCharacter k χ a = (primeValue χ v)⁻¹ ^ 2 := by
      rw [detCharacter_of_isLocalMatrixAt χ hloc, det_diagonal, Fin.prod_univ_two,
        ordC_inv_mul_inv_of_isUniformizer hv hπ hπ0, map_ofAdd_single_neg_two]
    have hU := hf.central v a ⟨π, hπ, hloc⟩ x
    simp only [centralOperator, unramifiedTwist_apply, map_mul, h0, Units.val_mul] at hU ⊢
    rw [hU]
    ring

end Stacks.Adeles.GlobalFunctionField
