module

public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import StacksFrontier.NumberTheory.Adeles.GeneralLinear.AlgebraicEigenvaluesCentral

/-!
# Algebraicity of twisted Hecke eigenvalues on `GL_n`

Let `K` be a function field over a finite field `k` and `Λ` an algebraically closed field, with
prime subfield `F ⊂ Λ` (the bottom subfield `⊥`). From Harder's finiteness theorem
(`Stacks.Adeles.GeneralLinear.FiniteSupportModCenter`) for `GL_n`, we deduce that the Hecke
eigenvalues `t_{v,i}` of an unramified cusp form `f` on `GL_n(A)` become algebraic over `F` after
a twist by the degree: there is `γ ≠ 0` with `t_{v,i} γ ^ {i deg v}` algebraic over `F` for all
places `v` and all `1 ≤ i ≤ n`.

The argument:
1. `T_{v,n}` is translation by `ϖ_v⁻¹`, so `f(ϖ_v⁻¹ x) = t_{v,n} f(x)` and `t_{v,n} ≠ 0`.
2. Fix a place `w₀` and `c` with `c ^ {n deg w₀} = t_{w₀,n}`. The twist
   `g(x) = c ^ {deg x} f(x)` is an eigenform with eigenvalues `t'_{v,i} = t_{v,i} c ^ {-i deg v}`
   and `t'_{w₀,n} = 1`.
3. Every idele `z` acts on `g` by a scalar: `g(z x) = μ_z g(x)`, with `μ_z` determined by the
   class of `div z` modulo principal divisors and `w₀`. These classes are finite in number
   (finiteness of the class number), so the `μ_z` take finitely many values.
4. With the finite set `S` of Harder's theorem, every value of `g` lies in the `F`-span of the
   finitely many `μ_z g(s)`, `s ∈ S`. That span is finite-dimensional and stable under each
   `t'_{v,i}`, which is therefore integral, hence algebraic, over `F`.

## Main results

* `Stacks.Adeles.GeneralLinear.exists_isCentralMultiplier` — every idele acts on a nonzero
  eigenform by a nonzero scalar.
* `Stacks.Adeles.GeneralLinear.exists_isAlgebraic_mul_pow` — the algebraicity of the twisted
  eigenvalues.
-/

@[expose] public noncomputable section

open Matrix

universe u w

namespace Stacks.Adeles.GeneralLinear

open Stacks.Adeles.GlobalFunctionField Stacks.Drinfeld.Lattice

variable (k : Type u) [Field k] [Finite k] {K : Type u} [Field K] [Algebra k K]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K] {n : ℕ}

section Divisor

variable (K) in
/-- The divisor of ideles, as a homomorphism to the multiplicative group of divisors. -/
public def idelDivHom : (AdeleRing K)ˣ →* Multiplicative (Place K →₀ ℤ) where
  toFun c := Multiplicative.ofAdd (idelDiv k K c)
  map_one' := by rw [idelDiv_one]; rfl
  map_mul' a b := by rw [idelDiv_mul]; rfl

/-- The divisor of `c ^ m` is `m • div c`. -/
public theorem idelDiv_zpow (c : (AdeleRing K)ˣ) (m : ℤ) :
    idelDiv k K (c ^ m) = m • idelDiv k K c := by
  change Multiplicative.toAdd (idelDivHom k K (c ^ m)) = _
  rw [map_zpow, toAdd_zpow]
  rfl

/-- The divisor of a finite product of ideles is the sum of their divisors. -/
public theorem idelDiv_prod {ι : Type*} (s : Finset ι) (c : ι → (AdeleRing K)ˣ) :
    idelDiv k K (∏ i ∈ s, c i) = ∑ i ∈ s, idelDiv k K (c i) := by
  change Multiplicative.toAdd (idelDivHom k K (∏ i ∈ s, c i)) = _
  rw [map_prod, toAdd_prod]
  rfl

/-- The degree of the divisor `v` is `deg v`. -/
public theorem divisorDegree_single (v : Place K) (m : ℤ) :
    Stacks.Drinfeld.divisorDegree k K (Finsupp.single v m) =
      m * (Stacks.Drinfeld.placeDegree k K v : ℤ) := by
  rw [Stacks.Drinfeld.divisorDegree, Finsupp.linearCombination_single, smul_eq_mul]

end Divisor

section Central

variable {Λ : Type w} [Field Λ]

variable (n) in
/-- The idele `z` acts on `F` by the scalar `μ`: `F(z x) = μ F(x)` for all `x`. -/
public def IsCentralMultiplier (F : GL (Fin n) (AdeleRing K) → Λ) (z : (AdeleRing K)ˣ) (μ : Λ) :
    Prop :=
  ∀ y, F (scalarGL n z * y) = μ * F y

variable {F : GL (Fin n) (AdeleRing K) → Λ}

/-- The unit idele acts by `1`. -/
public theorem isCentralMultiplier_one : IsCentralMultiplier n F 1 1 := fun y => by
  rw [map_one, one_mul, one_mul]

/-- Multipliers multiply. -/
public theorem IsCentralMultiplier.mul {z z' : (AdeleRing K)ˣ} {μ μ' : Λ}
    (h : IsCentralMultiplier n F z μ) (h' : IsCentralMultiplier n F z' μ') :
    IsCentralMultiplier n F (z * z') (μ * μ') := fun y => by
  rw [map_mul, mul_assoc, h, h', mul_assoc]

/-- A multiplier of a nonzero function is nonzero. -/
public theorem IsCentralMultiplier.ne_zero (hF : F ≠ 0) {z : (AdeleRing K)ˣ} {μ : Λ}
    (h : IsCentralMultiplier n F z μ) : μ ≠ 0 := by
  rintro rfl
  apply hF
  funext y
  have := h (scalarGL n z⁻¹ * y)
  rwa [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul, zero_mul] at this

/-- The inverse idele acts by the inverse multiplier. -/
public theorem IsCentralMultiplier.inv {z : (AdeleRing K)ˣ} {μ : Λ} (hμ : μ ≠ 0)
    (h : IsCentralMultiplier n F z μ) : IsCentralMultiplier n F z⁻¹ μ⁻¹ := fun y => by
  have := h (scalarGL n z⁻¹ * y)
  rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul] at this
  rw [this, inv_mul_cancel_left₀ hμ]

/-- Powers of an idele act by the powers of the multiplier. -/
public theorem IsCentralMultiplier.zpow {z : (AdeleRing K)ˣ} {μ : Λ} (hμ : μ ≠ 0)
    (h : IsCentralMultiplier n F z μ) (m : ℤ) : IsCentralMultiplier n F (z ^ m) (μ ^ m) := by
  induction m using Int.induction_on with
  | zero => rw [zpow_zero, zpow_zero]; exact isCentralMultiplier_one
  | succ i ih => rw [zpow_add_one, zpow_add_one₀ hμ]; exact ih.mul h
  | pred i ih => rw [zpow_sub_one, zpow_sub_one₀ hμ]; exact ih.mul (h.inv hμ)

/-- Finite products of ideles act by the products of the multipliers. -/
public theorem isCentralMultiplier_prod {ι : Type*} (s : Finset ι) {z : ι → (AdeleRing K)ˣ}
    {μ : ι → Λ} (h : ∀ i, IsCentralMultiplier n F (z i) (μ i)) :
    IsCentralMultiplier n F (∏ i ∈ s, z i) (∏ i ∈ s, μ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty]; exact isCentralMultiplier_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (h a).mul ih

/-- A unit of the integral adeles acts trivially on a left `GL_n(O)`-invariant function. -/
public theorem isCentralMultiplier_of_integral (hL : ∀ κ x, F (mapO K n κ * x) = F x)
    (o : (integralAdeles K)ˣ) :
    IsCentralMultiplier n F (Units.map (integralAdeles K).subtype.toMonoidHom o) 1 := fun y => by
  have : scalarGL n (Units.map (integralAdeles K).subtype.toMonoidHom o) =
      mapO K n (Units.map (algebraMap (integralAdeles K)
        (Matrix (Fin n) (Fin n) (integralAdeles K))).toMonoidHom o) := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    change algebraMap (AdeleRing K) (Matrix (Fin n) (Fin n) (AdeleRing K))
      ((o : integralAdeles K) : AdeleRing K) i j =
      (algebraMap (integralAdeles K) (Matrix (Fin n) (Fin n) (integralAdeles K))
        (o : integralAdeles K) i j : AdeleRing K)
    rw [Matrix.algebraMap_matrix_apply, Matrix.algebraMap_matrix_apply]
    split_ifs <;> rfl
  rw [this, hL, one_mul]

/-- An idele of divisor `0` acts trivially on a left `GL_n(O)`-invariant function. -/
public theorem isCentralMultiplier_of_idelDiv_eq_zero (hL : ∀ κ x, F (mapO K n κ * x) = F x)
    {z : (AdeleRing K)ˣ} (hz : idelDiv k K z = 0) : IsCentralMultiplier n F z 1 := by
  obtain ⟨o, ho⟩ := exists_integralUnit_of_idelDiv_eq_zero k hz
  have : Units.map (integralAdeles K).subtype.toMonoidHom o = z := Units.ext ho
  rw [← this]
  exact isCentralMultiplier_of_integral hL o

/-- Two ideles with the same divisor act by the same scalar on a left `GL_n(O)`-invariant
function. -/
public theorem IsCentralMultiplier.of_idelDiv_eq (hL : ∀ κ x, F (mapO K n κ * x) = F x)
    {z z' : (AdeleRing K)ˣ} {μ : Λ} (h : IsCentralMultiplier n F z μ)
    (hzz' : idelDiv k K z = idelDiv k K z') : IsCentralMultiplier n F z' μ := by
  have h0 : idelDiv k K (z⁻¹ * z') = 0 := by rw [idelDiv_mul, idelDiv_inv, hzz', neg_add_cancel]
  have := h.mul (isCentralMultiplier_of_idelDiv_eq_zero k hL h0)
  rwa [mul_inv_cancel_left, mul_one] at this

/-- A principal idele acts trivially on a right `GL_n(K)`-invariant function. -/
public theorem isCentralMultiplier_diagUnit (hR : ∀ x γ, F (x * mapK K n γ) = F x) {κ : K}
    (hκ : κ ≠ 0) : IsCentralMultiplier n F (diagUnit k hκ) 1 := fun y => by
  let u : (principalAdeles K)ˣ :=
    { val := ⟨diag k K κ, κ, fun v => rfl⟩
      inv := ⟨diag k K κ⁻¹, κ⁻¹, fun v => rfl⟩
      val_inv := Subtype.ext (by
        rw [Subring.coe_mul, ← map_mul, mul_inv_cancel₀ hκ, map_one]; rfl)
      inv_val := Subtype.ext (by
        rw [Subring.coe_mul, ← map_mul, inv_mul_cancel₀ hκ, map_one]; rfl) }
  have : scalarGL n (diagUnit k hκ) =
      mapK K n (Units.map (algebraMap (principalAdeles K)
        (Matrix (Fin n) (Fin n) (principalAdeles K))).toMonoidHom u) := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    change algebraMap (AdeleRing K) (Matrix (Fin n) (Fin n) (AdeleRing K)) (diag k K κ) i j =
      (algebraMap (principalAdeles K) (Matrix (Fin n) (Fin n) (principalAdeles K))
        (u : principalAdeles K) i j : AdeleRing K)
    rw [Matrix.algebraMap_matrix_apply, Matrix.algebraMap_matrix_apply]
    split_ifs <;> rfl
  rw [scalarGL_mul_comm, this, hR, one_mul]

/-- **Every idele acts by a scalar**: on a nonzero left `GL_n(O)`-invariant function on which
each `ϖ_v⁻¹` acts by a scalar `τ_v`, every idele acts by a nonzero scalar. -/
public theorem exists_isCentralMultiplier (hF : F ≠ 0) (hL : ∀ κ x, F (mapO K n κ * x) = F x)
    {τ : Place K → Λ} (hτ : ∀ v, IsCentralMultiplier n F (unifInvIdele k v) (τ v))
    (z : (AdeleRing K)ˣ) : ∃ μ, μ ≠ 0 ∧ IsCentralMultiplier n F z μ := by
  classical
  obtain ⟨D, hD⟩ : ∃ D, idelDiv k K z = D := ⟨_, rfl⟩
  have hτ0 : ∀ v, τ v ≠ 0 := fun v => (hτ v).ne_zero hF
  have hP := isCentralMultiplier_prod D.support (z := fun v => unifInvIdele k v ^ (-D v))
    (μ := fun v => τ v ^ (-D v)) fun v => (hτ v).zpow (hτ0 v) _
  refine ⟨_, Finset.prod_ne_zero_iff.2 fun v _ => zpow_ne_zero _ (hτ0 v),
    hP.of_idelDiv_eq k hL ?_⟩
  rw [idelDiv_prod, hD]
  simp only [idelDiv_zpow, idelDiv_unifInvIdele, smul_neg, neg_smul, neg_neg]
  conv_rhs => rw [← Finsupp.sum_single D]
  rw [Finsupp.sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finsupp.smul_single, smul_eq_mul, mul_one]

end Central

section Algebraic

variable {Λ : Type w} [Field Λ]

/-- A finsum of elements of a submodule lies in the submodule. -/
public theorem finsum_mem_submodule {R : Type*} [Semiring R] [Module R Λ] (V : Submodule R Λ)
    {α : Type*} {h : α → Λ} (hh : ∀ a, h a ∈ V) : ∑ᶠ a, h a ∈ V :=
  finsum_induction (· ∈ V) V.zero_mem (fun _ _ => V.add_mem) hh

/-- On an eigenform, `ϖ_v⁻¹` acts by the eigenvalue `t_{v,n}` of `T_{v,n}`. -/
public theorem isCentralMultiplier_of_isHeckeEigenformGL (hn : 0 < n)
    {F : GL (Fin n) (AdeleRing K) → Λ} (hL : ∀ κ x, F (mapO K n κ * x) = F x)
    {t : Place K → ℕ → Λ} (ht : IsHeckeEigenformGL F t) (v : Place K) :
    IsCentralMultiplier n F (unifInvIdele k v) (t v n) := fun y => by
  rw [← heckeOperatorGL_top k F hL v y, ht.hecke v n hn le_rfl y]

/-- **Finitely many central multipliers**: if `ϖ_{w₀}⁻¹` acts trivially on a nonzero function `F`
invariant on the left under `GL_n(O)` and on the right under `GL_n(K)`, on which every idele `z`
acts by `μ z`, then there is a finite set `F₀` of divisors such that every idele acts by some
`μ (idelOfDiv D')`, `D' ∈ F₀`. -/
public theorem exists_finset_isCentralMultiplier {F : GL (Fin n) (AdeleRing K) → Λ}
    (hL : ∀ κ x, F (mapO K n κ * x) = F x) (hR : ∀ x γ, F (x * mapK K n γ) = F x)
    {w₀ : Place K} (hd₀ : 0 < Stacks.Drinfeld.placeDegree k K w₀)
    (hw₀ : IsCentralMultiplier n F (unifInvIdele k w₀) 1) (μ : (AdeleRing K)ˣ → Λ)
    (hμ : ∀ z, IsCentralMultiplier n F z (μ z)) :
    ∃ F₀ : Finset (Place K →₀ ℤ), ∀ z, ∃ D' ∈ F₀,
      IsCentralMultiplier n F z (μ (idelOfDiv k K D')) := by
  set d₀ : ℤ := (Stacks.Drinfeld.placeDegree k K w₀ : ℤ)
  have hd₀' : 0 < d₀ := by
    change (0 : ℤ) < (Stacks.Drinfeld.placeDegree k K w₀ : ℤ)
    exact_mod_cast hd₀
  set q : ℚ := (Nat.card k : ℚ)
  have hq : 1 ≤ q := by
    have := Fintype.ofFinite k
    change (1 : ℚ) ≤ (Nat.card k : ℚ)
    exact_mod_cast (Nat.card_pos : 0 < Nat.card k)
  obtain ⟨F₀, hF₀⟩ := exists_finset_divisor_classes k (K := K) (q ^ d₀)
  refine ⟨F₀, fun z => ?_⟩
  set D := idelDiv k K z
  set m := Stacks.Drinfeld.divisorDegree k K D / d₀
  set D₁ := D - m • Finsupp.single w₀ 1
  have hdeg : Stacks.Drinfeld.divisorDegree k K D₁ = Stacks.Drinfeld.divisorDegree k K D % d₀ := by
    rw [map_sub, map_zsmul, divisorDegree_single, one_mul, smul_eq_mul, Int.emod_def, mul_comm]
  have h0 : 0 ≤ Stacks.Drinfeld.divisorDegree k K D₁ := hdeg ▸ Int.emod_nonneg _ hd₀'.ne'
  have hlt : Stacks.Drinfeld.divisorDegree k K D₁ ≤ d₀ :=
    (hdeg ▸ Int.emod_lt_of_pos _ hd₀').le
  have hnorm := Stacks.Drinfeld.divNorm_eq_zpow_divisorDegree k D₁
  have hl : (q ^ d₀)⁻¹ ≤ divNorm K D₁ := by
    rw [hnorm]
    calc (q ^ d₀)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_zpow₀ hq hd₀'.le)
      _ ≤ q ^ Stacks.Drinfeld.divisorDegree k K D₁ := one_le_zpow₀ hq h0
  have hu : divNorm K D₁ ≤ q ^ d₀ := by
    rw [hnorm]
    exact zpow_le_zpow_right₀ hq hlt
  obtain ⟨D', hD', κ, hκ, hD₁⟩ := hF₀ D₁ hl hu
  refine ⟨D', hD', ?_⟩
  have hZ := (((hμ (idelOfDiv k K D')).mul
    ((isCentralMultiplier_diagUnit k hR hκ).inv one_ne_zero)).mul
    (hw₀.zpow one_ne_zero (-m)))
  rw [inv_one, mul_one, one_zpow, mul_one] at hZ
  refine hZ.of_idelDiv_eq k hL ?_
  rw [idelDiv_mul, idelDiv_mul, idelDiv_inv, idelDiv_idelOfDiv, idelDiv_diagUnit, idelDiv_zpow,
    idelDiv_unifInvIdele]
  have hD : idelDiv k K z = D₁ + m • Finsupp.single w₀ 1 := (sub_add_cancel _ _).symm
  rw [hD, hD₁, smul_neg, neg_smul, neg_neg, sub_eq_add_neg]

/-- **Algebraicity of the twisted Hecke eigenvalues on `GL_n`.** Let `K` be a function field over
a finite field `k`, `Λ` an algebraically closed field with prime subfield `F = ⊥`, and assume
Harder's finiteness theorem `FiniteSupportModCenter` for `GL_n`. If `f` is an unramified cusp
form on `GL_n(A)` which is a Hecke eigenform with eigenvalues `t`, then there is `γ ≠ 0` such
that `t_{v,i} γ ^ {i deg v}` is algebraic over `F` for every place `v` and every `1 ≤ i ≤ n`. -/
public theorem exists_isAlgebraic_mul_pow (hS : FiniteSupportModCenter.{u, w} K n)
    [IsAlgClosed Λ] (hn : 0 < n) {f : GL (Fin n) (AdeleRing K) → Λ}
    (hf : IsUnramifiedCuspFormGL n f) {t : Place K → ℕ → Λ} (ht : IsHeckeEigenformGL f t) :
    ∃ γ : Λ, γ ≠ 0 ∧ ∀ v i, 1 ≤ i → i ≤ n →
      IsAlgebraic (⊥ : Subfield Λ) (t v i * γ ^ (i * Stacks.Drinfeld.placeDegree k K v)) := by
  classical
  obtain ⟨S, hSS⟩ := hS
  obtain ⟨w₀⟩ := nonempty_place k (K := K)
  set d₀ := Stacks.Drinfeld.placeDegree k K w₀
  have hd₀ : 0 < d₀ := by
    have h1 := one_lt_resCard k w₀
    rw [Stacks.Drinfeld.resCard_eq_pow_placeDegree k w₀] at h1
    rcases Nat.eq_zero_or_pos d₀ with h | h
    · rw [show Stacks.Drinfeld.placeDegree k K w₀ = 0 from h, pow_zero] at h1
      exact absurd h1 (lt_irrefl 1)
    · exact h
  have ht0 : t w₀ n ≠ 0 :=
    (isCentralMultiplier_of_isHeckeEigenformGL k hn (fun κ x => hf.left_invariant x κ) ht
      w₀).ne_zero ht.ne_zero
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (t w₀ n) (Nat.mul_pos hn hd₀)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow (Nat.mul_pos hn hd₀).ne'] at hc
    exact ht0 hc.symm
  set g := twistGL k K c f
  have hg := ht.twistGL k hc0
  set t' : Place K → ℕ → Λ :=
    fun v i => t v i * c ^ (-((i : ℤ) * (Stacks.Drinfeld.placeDegree k K v : ℤ)))
  have hgL : ∀ κ x, g (mapO K n κ * x) = g x := twistGL_mapO_mul k c hf
  have hgR : ∀ x γ, g (x * mapK K n γ) = g x := twistGL_mul_mapK k c hf
  have hZ := isCentralMultiplier_of_isHeckeEigenformGL k hn hgL hg
  have ht'w₀ : t' w₀ n = 1 := by
    change t w₀ n * c ^ (-((n : ℤ) * (d₀ : ℤ))) = 1
    rw [← hc, zpow_neg, show (n : ℤ) * (d₀ : ℤ) = ((n * d₀ : ℕ) : ℤ) by push_cast; ring,
      zpow_natCast, mul_inv_cancel₀ (pow_ne_zero _ hc0)]
  have hw₀ : IsCentralMultiplier n g (unifInvIdele k w₀) 1 := ht'w₀ ▸ hZ w₀
  choose μ hμ0 hμ using exists_isCentralMultiplier k hg.ne_zero hgL hZ
  obtain ⟨F₀, hF₀⟩ := exists_finset_isCentralMultiplier k hgL hgR hd₀ hw₀ μ hμ
  set T : Finset Λ := (F₀ ×ˢ S).image fun p => μ (idelOfDiv k K p.1) * g p.2
  set W := Submodule.span (⊥ : Subfield Λ) (T : Set Λ)
  have hval : ∀ x, g x ∈ W := by
    intro x
    by_cases hx : f x = 0
    · rw [show g x = 0 by simp only [g, twistGL, hx, mul_zero]]
      exact W.zero_mem
    obtain ⟨s, hs, κ, z, γ, rfl⟩ := hSS Λ f hf x hx
    rw [hgR, mul_assoc, hgL]
    obtain ⟨D', hD', hDz⟩ := hF₀ z
    rw [hDz s]
    exact Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image.2
      ⟨(D', s), Finset.mem_product.2 ⟨hD', hs⟩, rfl⟩))
  set V := Submodule.span (⊥ : Subfield Λ) (Set.range g)
  have hle : V ≤ W := Submodule.span_le.2 (by rintro _ ⟨x, rfl⟩; exact hval x)
  have hfg : V.FG := by
    have : FiniteDimensional (⊥ : Subfield Λ) W := Module.Finite.span_of_finite _ T.finite_toSet
    have := Submodule.finiteDimensional_of_le hle
    exact (Submodule.fg_iff_finiteDimensional _).2 this
  have hne : V ≠ ⊥ := by
    obtain ⟨x, hx⟩ := Function.ne_iff.1 hg.ne_zero
    intro hbot
    have hmem : g x ∈ V := Submodule.subset_span ⟨x, rfl⟩
    rw [hbot, Submodule.mem_bot] at hmem
    exact hx hmem
  refine ⟨c⁻¹, inv_ne_zero hc0, fun v i hi hin => ?_⟩
  have hmul : ∀ y ∈ V, t' v i * y ∈ V := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, rfl⟩ := hy
      rw [← hg.hecke v i hi hin x]
      exact finsum_mem_submodule V fun L' => Submodule.subset_span ⟨_, rfl⟩
    | zero => simp
    | add y y' _ _ hy hy' => rw [mul_add]; exact V.add_mem hy hy'
    | smul a y _ hy =>
      have hcomm : t' v i * (a • y) = a • (t' v i * y) := by
        simp only [Algebra.smul_def]
        ring
      rw [hcomm]
      exact V.smul_mem a hy
  have halg := (isIntegral_of_smul_mem_submodule V hne hfg (t' v i)
    fun y hy => by simpa only [smul_eq_mul] using hmul y hy).isAlgebraic
  have heq : t v i * c⁻¹ ^ (i * Stacks.Drinfeld.placeDegree k K v) = t' v i := by
    change t v i * c⁻¹ ^ (i * Stacks.Drinfeld.placeDegree k K v) =
      t v i * c ^ (-((i : ℤ) * (Stacks.Drinfeld.placeDegree k K v : ℤ)))
    rw [zpow_neg, inv_pow, ← zpow_natCast, Nat.cast_mul]
  rw [heq]
  exact halg

end Algebraic

end Stacks.Adeles.GeneralLinear

end
