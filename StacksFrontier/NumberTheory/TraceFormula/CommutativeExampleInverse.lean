module

public import StacksFrontier.NumberTheory.TraceFormula.CommutativeExampleExistence
public import StacksFrontier.NumberTheory.TraceFormula.NecklaceSum
public import StacksFrontier.NumberTheory.TraceFormula.ProfinitePowers
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The commutative example with `a = qu = 1` has an abstract trace formula

Let `q ≥ 2` and `Γ = Ẑ^{(q)} ⋊ Ẑ` with `F x F⁻¹ = q⁻¹ x` (that is, `u = q⁻¹`, `a = qu = 1`; the
action of `z ∈ Ẑ` is multiplication by `q^{-z}`, `Stacks.TraceFormula.profinitePowers`). Then `Γ`
has an abstract trace formula with integer `q`, with `S_d` the orbits of exact size `d` of
multiplication by `q` on `ℤ/(q^d - 1)` (`Stacks.TraceFormula.Necklace.Orbits`), and with `F_x` the
class of `σ^k F^d` for `k ∈ x`, where `σ ∈ Ẑ^{(q)}` is `1`. In particular `#S_1 = q - 1` and
`#S_2 = ((q² - 1) - (q - 1)) / 2`, as for the closed points of `𝐆_m` over a field with `q`
elements.

## Proof

Write `T(x) = Tr(σ^x F^n | M)`. It is invariant under `x ↦ q⁻¹ x` (conjugation by `F`), under
`x ↦ x + (1 - q^{-n}) y` (conjugation by `σ^y`) and under the open subgroup acting trivially, so on
the integers it is periodic with period `G = gcd(N₀, q^n - 1)`, `N₀` the order of `σ` modulo that
subgroup. By `Stacks.TraceFormula.Necklace.sum_eq_sum_divisors_orbits` the left hand side of the
trace formula is `Σ_{t < q^n - 1} T(t) = ((q^n - 1)/G) S`, `S = Σ_{t < G} T(t)`. By
`Stacks.GroupHomology.Procyclic.perfectDerivedTrace_derivedCoinvariantsAction`,
`Tr(Φ^n | LH₀) = T(b) - Σ_{j < v} T(b - j)` with `v ≡ q^{-n}` modulo a deep level; then
`v = 1 + G w` and `q^n Tr(Φ^n | LH₀) = -q^n w S`, and the difference `((q^n v - 1)/G) S` vanishes
because the characteristic of `Λ` divides `(q^n v - 1)/G`.

## References

* [Stacks Project, Tag 03VQ](https://stacks.math.columbia.edu/tag/03VQ)
* [Stacks Project, Section 03VO](https://stacks.math.columbia.edu/tag/03VO)
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.GroupHomology Stacks.GroupHomology.Procyclic
  CategoryTheory.FilteredDerived

universe u

namespace Stacks.TraceFormula

/-! ### The semidirect product -/

section Gamma

variable {q : ℕ} (χ : Multiplicative ProfiniteIntegers →* (RestrictedProfiniteIntegers q)ˣ)

/-- The element `σ^x = x ∈ Ẑ^{(q)}` of `Γ`. -/
public abbrev elt (x : RestrictedProfiniteIntegers q) : Gamma χ := incl χ (Multiplicative.ofAdd x)

/-- `σ^{x + y} = σ^x σ^y`. -/
public theorem elt_add (x y : RestrictedProfiniteIntegers q) :
    elt χ (x + y) = elt χ x * elt χ y := by
  rw [elt, ofAdd_add, map_mul]

/-- `σ^{-x} = (σ^x)⁻¹`. -/
public theorem elt_neg (x : RestrictedProfiniteIntegers q) : elt χ (-x) = (elt χ x)⁻¹ := by
  rw [elt, ofAdd_neg, map_inv]

/-- The degree of `F^s` is `s`. -/
public theorem degree_frobenius_pow (s : ℕ) :
    degree χ (frobenius χ ^ s) = Multiplicative.ofAdd (s : ProfiniteIntegers) := by
  rw [map_pow, degree_frobenius, ← ofAdd_nsmul, nsmul_one]

/-- Left multiplication by `σ^x` does not change the degree. -/
public theorem degree_elt_mul (x : RestrictedProfiniteIntegers q) (g : Gamma χ) :
    degree χ (elt χ x * g) = degree χ g := by
  rw [map_mul, elt, SemidirectProduct.rightHom_inl, one_mul]

/-- `χ(s) = χ(1)^s`. -/
public theorem character_natCast (s : ℕ) :
    χ (Multiplicative.ofAdd (s : ProfiniteIntegers)) = χ (Multiplicative.ofAdd 1) ^ s := by
  rw [← map_pow, ← ofAdd_nsmul, nsmul_one]

/-- `F^s σ^x F^{-s} = σ^{u^s x}`. -/
public theorem frobenius_pow_conj (s : ℕ) (x : RestrictedProfiniteIntegers q) :
    frobenius χ ^ s * elt χ x * (frobenius χ ^ s)⁻¹ =
      elt χ (((χ (Multiplicative.ofAdd 1) ^ s : (RestrictedProfiniteIntegers q)ˣ) :
        RestrictedProfiniteIntegers q) * x) := by
  rw [elt, conj_incl, degree_frobenius_pow, character_natCast]

/-- An element of degree `n` is `σ^b F^n`. -/
public theorem eq_elt_mul_frobenius_pow {n : ℕ} (g : Gamma χ)
    (hg : degree χ g = Multiplicative.ofAdd (n : ProfiniteIntegers)) :
    g = elt χ (Multiplicative.toAdd (g * (frobenius χ ^ n)⁻¹).left) * frobenius χ ^ n := by
  have hk : degree χ (g * (frobenius χ ^ n)⁻¹) = 1 := by
    rw [map_mul, map_inv, hg, degree_frobenius_pow, mul_inv_cancel]
  have : g * (frobenius χ ^ n)⁻¹ = elt χ (Multiplicative.toAdd (g * (frobenius χ ^ n)⁻¹).left) :=
    SemidirectProduct.ext rfl hk
  rw [← this, inv_mul_cancel_right]

/-- `(σ^k F^d)^m = σ^{k Σ_{i < m} u^{d i}} F^{d m}`. -/
public theorem elt_mul_frobenius_pow_pow (k : RestrictedProfiniteIntegers q) (d m : ℕ) :
    (elt χ k * frobenius χ ^ d) ^ m =
      elt χ (k * ∑ i ∈ Finset.range m, ((χ (Multiplicative.ofAdd 1) ^ (d * i) :
        (RestrictedProfiniteIntegers q)ˣ) : RestrictedProfiniteIntegers q)) *
        frobenius χ ^ (d * m) := by
  induction m with
  | zero => simp [elt]
  | succ m ih =>
    rw [pow_succ, ih, Finset.sum_range_succ, mul_add, elt_add]
    have h := frobenius_pow_conj χ (d * m) k
    rw [mul_comm _ k] at h
    rw [← h, Nat.mul_succ]
    simp only [mul_assoc, pow_add, inv_mul_cancel_left]

end Gamma

/-! ### Traces on a module -/

section Traces

variable {Γ : Type u} [Group Γ] (Λ : Type u) [Ring Λ] (M : Type u) [AddCommGroup M] [Module Λ M]
  [Module.Finite Λ M] [Module.Projective Λ M] [DistribMulAction Γ M] [SMulCommClass Γ Λ M]

/-- The trace of `g ∈ Γ` on `M`. -/
public abbrev actionTrace (g : Γ) : AdditiveCommutatorQuotient Λ :=
  Stacks.Trace.projectiveModuleTrace Λ M (DistribMulAction.toModuleEnd Λ M g)

/-- Traces are invariant under conjugation. -/
@[sga "5 X 3.1" "partial"]
public theorem actionTrace_conj (h g : Γ) :
    actionTrace Λ M (h * g * h⁻¹) = actionTrace Λ M g := by
  dsimp only [actionTrace]
  conv_rhs => rw [← projectiveModuleTrace_conj Λ (DistribMulAction.toLinearEquiv Λ M h)]
  congr 1
  refine LinearMap.ext fun m => ?_
  simp [mul_smul]

/-- Traces only see the action. -/
public theorem actionTrace_mul_of_forall {a : Γ} (ha : ∀ m : M, a • m = m) (g : Γ) :
    actionTrace Λ M (a * g) = actionTrace Λ M g := by
  dsimp only [actionTrace]
  congr 1
  refine LinearMap.ext fun m => ?_
  simp [mul_smul, ha]

end Traces

/-! ### Periodic sums -/

section Periodic

variable {A : Type*} [AddCommMonoid A]

/-- A sum of a `P`-periodic function over `P` consecutive integers does not depend on the start. -/
public theorem sum_range_add_of_periodic (f : ℕ → A) (P : ℕ) (hf : ∀ t, f (t + P) = f t) (s : ℕ) :
    ∑ i ∈ Finset.range P, f (s + i) = ∑ i ∈ Finset.range P, f i := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [← ih]
    rcases Nat.eq_zero_or_pos P with rfl | hP
    · simp
    · obtain ⟨P', rfl⟩ : ∃ P', P = P' + 1 := ⟨P - 1, by omega⟩
      rw [Finset.sum_range_succ, Finset.sum_range_succ']
      have : f (s + 1 + P') = f (s + 0) := by
        rw [show s + 1 + P' = s + (P' + 1) by ring, hf]
        rfl
      rw [this]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by rw [show s + 1 + i = s + (i + 1) by ring]

end Periodic

/-! ### The character `z ↦ q^{-z}` -/

section Inverse

variable (q : ℕ)

/-- `q⁻¹`, a unit of `Ẑ^{(q)}`. -/
public def qInv : (RestrictedProfiniteIntegers q)ˣ :=
  (isUnit_natCast_restrictedProfiniteIntegers q).unit⁻¹

/-- `q · q⁻¹ = 1` in `Ẑ^{(q)}`. -/
public theorem natCast_mul_qInv :
    (q : RestrictedProfiniteIntegers q) * (qInv q : RestrictedProfiniteIntegers q) = 1 :=
  (isUnit_natCast_restrictedProfiniteIntegers q).mul_val_inv

/-- **The character `z ↦ q^{-z}`**: `u = q⁻¹`. -/
public abbrev inverseCharacter :
    Multiplicative ProfiniteIntegers →* (RestrictedProfiniteIntegers q)ˣ :=
  profinitePowers (qInv q)

/-- The character `z ↦ q^{-z}` sends `1` to `q⁻¹`. -/
public theorem inverseCharacter_ofAdd_one :
    inverseCharacter q (Multiplicative.ofAdd 1) = qInv q :=
  profinitePowers_ofAdd_one _

/-- For the character `z ↦ q^{-z}`, `Γ = Ẑ^{(q)} ⋊ Ẑ` is a topological group. -/
public instance : IsTopologicalGroup (Gamma (inverseCharacter q)) :=
  isTopologicalGroup_gamma _ (continuous_profinitePowers _)

/-- The class `σ^k F^d` attached to an orbit `x ∈ S_d`, `k ∈ x`. -/
public def orbitElement (d : ℕ) (x : Necklace.Orbits q d) : Gamma (inverseCharacter q) :=
  elt _ (((Quotient.out x).1.val : ℕ) : RestrictedProfiniteIntegers q) * frobenius _ ^ d

end Inverse

/-! ### The abstract trace formula for `u = q⁻¹` -/

section InverseFormula

variable {q : ℕ} [hq : Fact (2 ≤ q)]

attribute [local instance] compactSpace_gamma totallyDisconnectedSpace_gamma

/-- `ℓ`-primary torsion and quotients: the characteristic of `Λ^♮` kills it. -/
public theorem ringChar_nsmul_additiveCommutatorQuotient (Λ : Type u) [Ring Λ]
    (S : AdditiveCommutatorQuotient Λ) : ringChar Λ • S = 0 := by
  induction S using QuotientAddGroup.induction_on with
  | H a =>
    rw [← QuotientAddGroup.mk_nsmul, nsmul_eq_mul, ringChar.Nat.cast_ringChar, zero_mul]
    rfl

/-- **Stacks Project, Tag 03VQ: the case `a = qu = 1`.** For `q ≥ 2` the extension
`Γ = Ẑ^{(q)} ⋊ Ẑ` with `F x F⁻¹ = q⁻¹ x` has an abstract trace formula with integer `q`, with
`S_d` the orbits of exact size `d` of multiplication by `q` on `ℤ/(q^d - 1)` and `F_x` the class
of `σ^k F^d`, `k ∈ x`. -/
public def commutativeExample_abstractTraceFormula_inverse :
    AbstractTraceFormula (Gamma (inverseCharacter q)) (degree _) (continuous_degree _)
      (degree_surjective _) where
  q := q
  one_le_q := one_le_two.trans hq.out
  S d := Necklace.Orbits q d
  F d x := ConjClasses.mk (orbitElement q d x)
  deg_F d _ x g hg := by
    obtain ⟨c, hc⟩ := isConj_iff.1 (ConjClasses.mk_eq_mk_iff_isConj.1 hg)
    have h : degree _ (c * g * c⁻¹) = degree _ g := by
      rw [map_mul, map_mul, map_inv, mul_comm (degree _ c) (degree _ g), mul_inv_cancel_right]
    rw [← h, hc, orbitElement, degree_elt_mul, degree_frobenius_pow]
  finite_cohomologicalDimension ℓ hℓ _ := by
    have := compactSpace_ker (degree (inverseCharacter q)) (continuous_degree _)
    exact hasFiniteCohomologicalDimensionAt_of_continuousMulEquiv (kerEquiv _) ℓ hℓ
  trace_formula Λ _ _ hqΛ M _ _ _ _ _ _ hM n hn := by
    classical
    have := compactSpace_ker (degree (inverseCharacter q)) (continuous_degree _)
    have : Finite M := Module.finite_of_finite Λ
    set e := kerEquiv (inverseCharacter q)
    set σ := generatorOf e
    have hgen := generatesQuotients_of_continuousMulEquiv e
    have hc0 : ringChar Λ ≠ 0 := CharP.char_ne_zero_of_finite Λ (ringChar Λ)
    have hcΛ := ringChar_nsmul_eq_zero Λ
    have hpow : ∀ p : ℕ, p.Prime → p ∣ ringChar Λ → HasPrimePowerQuotients σ p :=
      fun p hp hpc => hasPrimePowerQuotients_of_continuousMulEquiv e
        ⟨p, hp, not_dvd_of_dvd_ringChar Λ hqΛ hp hpc⟩
    set hV := isSmoothFor_ker (degree (inverseCharacter q)) (continuous_degree _) M hM
    have hperf := isPerfect_derivedCoinvariants (Λ := Λ) hgen hc0 hpow hcΛ hV
    refine ⟨hperf, fun g hg Φ hΦ => ?_⟩
    -- notation
    set u : RestrictedProfiniteIntegers q := (qInv q : RestrictedProfiniteIntegers q) with hu
    have hqu : (q : RestrictedProfiniteIntegers q) * u = 1 := natCast_mul_qInv q
    have hχpow : ∀ s : ℕ, (((inverseCharacter q) (Multiplicative.ofAdd 1) ^ s :
        (RestrictedProfiniteIntegers q)ˣ) : RestrictedProfiniteIntegers q) = u ^ s := by
      intro s
      rw [Units.val_pow_eq_pow_val, inverseCharacter_ofAdd_one]
    have hσpow : ∀ j : ℕ, (((σ ^ j : (degree (inverseCharacter q)).ker)) :
        Gamma (inverseCharacter q)) = elt (inverseCharacter q) (j : _) := by
      intro j
      rw [generatorOf_pow]
      rfl
    set V' := hV.choose
    have hV' : ∀ g ∈ V', ∀ m : M, g • m = m := hV.choose_spec
    set N₀ := orderOf (σ : (degree (inverseCharacter q)).ker ⧸
      (V' : Subgroup (degree (inverseCharacter q)).ker))
    have hN₀pos : 0 < N₀ := orderOf_pos _
    have hσN₀ : σ ^ N₀ ∈ (V' : Subgroup (degree (inverseCharacter q)).ker) := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, pow_orderOf_eq_one]
    -- the traces `T(x) = Tr(σ^x F^n)`
    set T : RestrictedProfiniteIntegers q → AdditiveCommutatorQuotient Λ :=
      fun x => actionTrace Λ M
        (elt (inverseCharacter q) x * frobenius (inverseCharacter q) ^ n) with hT
    have hTloc : ∀ x x', e (Multiplicative.ofAdd (x - x')) ∈
        (V' : Subgroup (degree (inverseCharacter q)).ker) → T x = T x' := by
      intro x x' hx
      have : elt (inverseCharacter q) x * frobenius (inverseCharacter q) ^ n =
          elt (inverseCharacter q) (x - x') *
            (elt (inverseCharacter q) x' * frobenius (inverseCharacter q) ^ n) := by
        rw [← mul_assoc, ← elt_add, sub_add_cancel]
      have ha : ∀ m : M, elt (inverseCharacter q) (x - x') • m = m := by
        intro m
        have := hV' _ hx m
        rwa [Subgroup.smul_def, kerEquiv_apply_coe] at this
      simp only [hT]
      rw [this]
      exact actionTrace_mul_of_forall Λ M ha _
    have hTu : ∀ x, T (u * x) = T x := by
      intro x
      have h3 := frobenius_pow_conj (inverseCharacter q) 1 x
      rw [hχpow, pow_one, pow_one] at h3
      have h2 : frobenius (inverseCharacter q) *
          (elt (inverseCharacter q) x * frobenius (inverseCharacter q) ^ n) *
            (frobenius (inverseCharacter q))⁻¹ =
          elt (inverseCharacter q) (u * x) * frobenius (inverseCharacter q) ^ n := by
        rw [← h3]
        generalize elt (inverseCharacter q) x = a
        group
      simp only [hT]
      rw [← h2, actionTrace_conj]
    have hTq : ∀ s x, T ((q : RestrictedProfiniteIntegers q) ^ s * x) = T x := by
      intro s
      induction s with
      | zero => simp
      | succ s ih =>
        intro x
        rw [← ih x, ← hTu, pow_succ', mul_assoc, ← mul_assoc u, mul_comm u, hqu, one_mul]
    have hTshift : ∀ x y, T (x + (1 - u ^ n) * y) = T x := by
      intro x y
      have h3 := frobenius_pow_conj (inverseCharacter q) n (-y)
      rw [hχpow] at h3
      have h2 : elt (inverseCharacter q) y *
          (elt (inverseCharacter q) x * frobenius (inverseCharacter q) ^ n) *
            (elt (inverseCharacter q) y)⁻¹ =
          elt (inverseCharacter q) (x + (1 - u ^ n) * y) * frobenius (inverseCharacter q) ^ n := by
        have h4 : elt (inverseCharacter q) (x + (1 - u ^ n) * y) =
            elt (inverseCharacter q) y * elt (inverseCharacter q) x *
              elt (inverseCharacter q) (u ^ n * -y) := by
          rw [← elt_add, ← elt_add]
          congr 1
          ring
        rw [h4, ← h3, elt_neg]
        generalize elt (inverseCharacter q) x = a
        generalize elt (inverseCharacter q) y = b
        group
      simp only [hT]
      rw [← h2, actionTrace_conj]
    -- on the naturals
    set H₀ : ℕ → AdditiveCommutatorQuotient Λ := fun t => T t with hH₀
    have hH₀N : ∀ t k, H₀ (t + k * N₀) = H₀ t := by
      intro t k
      simp only [hH₀]
      apply hTloc
      push_cast
      rw [add_sub_cancel_left, ← nsmul_eq_mul, ofAdd_nsmul, map_pow, ← generatorOf_pow]
      exact Subgroup.pow_mem _ hσN₀ k
    have hq1 : 1 ≤ q ^ n := Nat.one_le_pow _ _ (by have := hq.out; omega)
    have hH₀R : ∀ t k, H₀ (t + k * Necklace.R q n) = H₀ t := by
      intro t k
      simp only [hH₀]
      have : ((t + k * Necklace.R q n : ℕ) : RestrictedProfiniteIntegers q) =
          t + (1 - u ^ n) * (k * (q : RestrictedProfiniteIntegers q) ^ n) := by
        rw [Necklace.R, Nat.cast_add, Nat.cast_mul, Nat.cast_sub hq1, Nat.cast_pow, Nat.cast_one]
        have : u ^ n * (q : RestrictedProfiniteIntegers q) ^ n = 1 := by
          rw [← mul_pow, mul_comm, hqu, one_pow]
        linear_combination (k : RestrictedProfiniteIntegers q) * this
      rw [this, hTshift]
    have hH₀mod : ∀ t, H₀ (t % Necklace.R q n) = H₀ t := by
      intro t
      conv_rhs => rw [← Nat.mod_add_div t (Necklace.R q n), mul_comm]
      rw [hH₀R]
    have hH₀q : ∀ t, H₀ (q * t) = H₀ t := by
      intro t
      simp only [hH₀]
      rw [Nat.cast_mul, ← pow_one (q : RestrictedProfiniteIntegers q), hTq]
    have hRpos : 0 < Necklace.R q n := Necklace.R_pos hn
    set G := Nat.gcd N₀ (Necklace.R q n) with hGdef
    have hGpos : 0 < G := Nat.gcd_pos_of_pos_right _ hRpos
    have hGR : G ∣ Necklace.R q n := Nat.gcd_dvd_right _ _
    have hGN : G ∣ N₀ := Nat.gcd_dvd_left _ _
    have hH₀G : ∀ t, H₀ (t + G) = H₀ t := by
      intro t
      rcases lt_or_eq_of_le (Nat.le_of_dvd hRpos hGR) with hlt | heq
      · obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_gcd hlt
        have hdecomp : N₀ * m = (N₀ * m / Necklace.R q n) * Necklace.R q n + G := by
          rw [hGdef, ← hm]
          exact (Nat.div_add_mod' _ _).symm
        calc H₀ (t + G) = H₀ (t + G + (N₀ * m / Necklace.R q n) * Necklace.R q n) :=
              (hH₀R _ _).symm
          _ = H₀ (t + m * N₀) := by
              congr 1
              rw [mul_comm m N₀]
              linarith
          _ = H₀ t := hH₀N t m
      · rw [heq, show t + Necklace.R q n = t + 1 * Necklace.R q n by ring, hH₀R]
    set S := ∑ a ∈ Finset.range G, H₀ a with hS
    -- the left hand side
    have : NeZero (Necklace.R q n) := ⟨hRpos.ne'⟩
    set H : ZMod (Necklace.R q n) → AdditiveCommutatorQuotient Λ := fun t => H₀ t.val with hHdef
    have hHq : ∀ t, H ((q : ZMod (Necklace.R q n)) * t) = H t := by
      intro t
      simp only [hHdef]
      rw [ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod, hH₀mod, hH₀q]
    have hterm : ∀ d (hd : d ∈ n.divisors) (x : Necklace.Orbits q d),
        actionTrace Λ M (g d x ^ (n / d)) =
          H (Necklace.iota (Nat.dvd_of_mem_divisors hd) (Quotient.out x).1) := by
      intro d hd x
      have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
      have hdn := Nat.dvd_of_mem_divisors hd
      have : NeZero (Necklace.R q d) := ⟨(Necklace.R_pos hdpos).ne'⟩
      obtain ⟨c, hc⟩ := isConj_iff.1 (ConjClasses.mk_eq_mk_iff_isConj.1 (hg d x))
      set k := (Quotient.out x).1.val
      set m := n / d
      have hdm : d * m = n := Nat.mul_div_cancel' hdn
      have h1 : actionTrace Λ M (g d x ^ m) = actionTrace Λ M (orbitElement q d x ^ m) := by
        rw [← hc, conj_pow, actionTrace_conj]
      rw [h1, orbitElement, elt_mul_frobenius_pow_pow, hdm]
      simp only [hχpow]
      change T _ = _
      have hgeom : ∑ i ∈ Finset.range m, (q : RestrictedProfiniteIntegers q) ^ (d * (m - 1)) *
          u ^ (d * i) =
            ((Necklace.R q n / Necklace.R q d : ℕ) : RestrictedProfiniteIntegers q) := by
        have hnat : ∑ j ∈ Finset.range m, (q ^ d) ^ j = Necklace.R q n / Necklace.R q d := by
          rw [Nat.geomSum_eq (le_trans hq.out (Nat.le_self_pow hdpos.ne' q)), ← pow_mul, hdm]
        rw [← hnat, Nat.cast_sum, ← Finset.sum_range_reflect]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hi' := Finset.mem_range.1 hi
        rw [Nat.cast_pow, Nat.cast_pow, ← pow_mul]
        have : d * (m - 1) = d * (m - 1 - i) + d * i := by rw [← mul_add]; congr 1; omega
        rw [this, pow_add, mul_assoc, mul_left_comm, ← mul_pow, hqu, one_pow, mul_one]
      rw [← hTq (d * (m - 1)), ← mul_assoc, mul_comm _ ((k : ℕ) : RestrictedProfiniteIntegers q),
        mul_assoc, Finset.mul_sum, hgeom]
      simp only [hHdef]
      rw [← ZMod.natCast_zmod_val (Quotient.out x).1, Necklace.iota_natCast, ZMod.val_natCast,
        hH₀mod]
      simp only [hH₀]
      push_cast
      rfl
    have hsumZ : ∑ t : ZMod (Necklace.R q n), H t = ∑ a ∈ Finset.range (Necklace.R q n), H₀ a :=
      Finset.sum_bij' (fun t _ => t.val) (fun a _ => (a : ZMod (Necklace.R q n)))
        (fun t _ => Finset.mem_range.2 (ZMod.val_lt t)) (fun a _ => Finset.mem_univ _)
        (fun t _ => ZMod.natCast_zmod_val t)
        (fun a ha => ZMod.val_cast_of_lt (Finset.mem_range.1 ha)) (fun t _ => rfl)
    have hLHS : ∑ d ∈ n.divisors, d • ∑ x : Necklace.Orbits q d,
        actionTrace Λ M (g d x ^ (n / d)) = (Necklace.R q n / G) • S := by
      rw [← Finset.sum_attach n.divisors]
      have hnk := Necklace.sum_eq_sum_divisors_orbits hn H hHq
      rw [hsumZ] at hnk
      have : ∑ d ∈ n.divisors.attach, d.1 • ∑ x : Necklace.Orbits q d.1,
          actionTrace Λ M (g d.1 x ^ (n / d.1)) = ∑ d ∈ n.divisors.attach, d.1 •
            ∑ x : Necklace.Orbits q d.1, H (Necklace.iota (Nat.dvd_of_mem_divisors d.2)
              (Quotient.out x).1) :=
        Finset.sum_congr rfl fun d _ => by
          rw [Finset.sum_congr rfl fun x _ => hterm d.1 d.2 x]
      rw [this, ← hnk, hS]
      conv_lhs => rw [← Nat.div_mul_cancel hGR]
      exact sum_range_mul_of_periodic H₀ G _ hH₀G
    -- the right hand side
    have hΦn :
        degree (inverseCharacter q) (Φ ^ n) = Multiplicative.ofAdd (n : ProfiniteIntegers) := by
      rw [map_pow, hΦ, ← ofAdd_nsmul, nsmul_one]
    set b := Multiplicative.toAdd ((Φ ^ n) * (frobenius (inverseCharacter q) ^ n)⁻¹).left
    have hb : Φ ^ n = elt (inverseCharacter q) b * frobenius (inverseCharacter q) ^ n :=
      eq_elt_mul_frobenius_pow (inverseCharacter q) _ hΦn
    obtain ⟨b₀, hb₀⟩ := hgen V' (e (Multiplicative.ofAdd b))
    obtain ⟨W, hW⟩ := exists_isDeep (σ := σ) hc0 hpow hcΛ V'
    set τ := conjContinuousMulEquiv _ (Φ ^ n) σ
    obtain ⟨v₀, hv₀⟩ := hgen W τ
    set v := v₀ + orderOf (σ : (degree (inverseCharacter q)).ker ⧸
      (W : Subgroup (degree (inverseCharacter q)).ker))
    have hv : (τ : (degree (inverseCharacter q)).ker ⧸
        (W : Subgroup (degree (inverseCharacter q)).ker)) =
          (σ : (degree (inverseCharacter q)).ker ⧸
            (W : Subgroup (degree (inverseCharacter q)).ker)) ^ v := by
      rw [pow_add, pow_orderOf_eq_one, mul_one]
      exact hv₀
    have hvpos : 0 < v := Nat.add_pos_right _ (orderOf_pos _)
    rw [perfectDerivedTrace_derivedCoinvariantsAction (Φ ^ n) hgen hc0 hpow hcΛ hV hperf V' W hV'
      hW hv]
    have hemul : ∀ x y : RestrictedProfiniteIntegers q,
        e (Multiplicative.ofAdd (x + y)) =
          e (Multiplicative.ofAdd x) * e (Multiplicative.ofAdd y) :=
      fun x y => by rw [ofAdd_add, map_mul]
    have heneg : ∀ x : RestrictedProfiniteIntegers q,
        e (Multiplicative.ofAdd (-x)) = (e (Multiplicative.ofAdd x))⁻¹ :=
      fun x => by rw [ofAdd_neg, map_inv]
    set b₁ := b₀ + v * N₀ with hb₁def
    have hb₁ :
        e (Multiplicative.ofAdd (b - b₁)) ∈ (V' : Subgroup (degree (inverseCharacter q)).ker) := by
      have h1 : (σ ^ b₀)⁻¹ * e (Multiplicative.ofAdd b) ∈
          (V' : Subgroup (degree (inverseCharacter q)).ker) := by
        rw [← QuotientGroup.eq, QuotientGroup.mk_pow]
        exact hb₀.symm
      have h2 : e (Multiplicative.ofAdd (b - b₁)) =
          (σ ^ b₀)⁻¹ * e (Multiplicative.ofAdd b) * ((σ ^ N₀) ^ v)⁻¹ := by
        rw [generatorOf_pow, ← pow_mul, generatorOf_pow, ← heneg, ← heneg, ← hemul, ← hemul,
          hb₁def]
        congr 2
        push_cast
        ring
      rw [h2]
      exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ (Subgroup.pow_mem _ hσN₀ v))
    have hTb : ∀ j, j ≤ b₁ → T (b - j) = H₀ (b₁ - j) := by
      intro j hj
      simp only [hH₀]
      apply hTloc
      rw [Nat.cast_sub hj, show b - (j : RestrictedProfiniteIntegers q) -
        ((b₁ : RestrictedProfiniteIntegers q) - j) = b - b₁ by ring]
      exact hb₁
    have hR1 : actionTrace Λ M (Φ ^ n) = H₀ b₁ := by
      have := hTb 0 (Nat.zero_le _)
      rw [Nat.cast_zero, sub_zero, Nat.sub_zero] at this
      rw [hb]
      exact this
    have hR2 : ∀ j ∈ Finset.range v,
        actionTrace Λ M ((((σ ^ j : (degree (inverseCharacter q)).ker)) :
          Gamma (inverseCharacter q))⁻¹ * Φ ^ n) = H₀ (b₁ - j) := by
      intro j hj
      rw [hσpow, hb, ← mul_assoc, ← elt_neg, ← elt_add, neg_add_eq_sub]
      refine hTb j ?_
      have := Finset.mem_range.1 hj
      have : v ≤ v * N₀ := Nat.le_mul_of_pos_right v hN₀pos
      omega
    change _ = q ^ n • (actionTrace Λ M (Φ ^ n) - ∑ j ∈ Finset.range v,
      actionTrace Λ M ((((σ ^ j : (degree (inverseCharacter q)).ker)) :
        Gamma (inverseCharacter q))⁻¹ * Φ ^ n))
    rw [hR1, Finset.sum_congr rfl hR2]
    change ∑ d ∈ n.divisors, d • ∑ x : Necklace.Orbits q d,
      actionTrace Λ M (g d x ^ (n / d)) = _
    rw [hLHS]
    -- the order of `σ` at `W`
    have hτ : ((τ : (degree (inverseCharacter q)).ker) : Gamma (inverseCharacter q)) =
        elt (inverseCharacter q) (u ^ n) := by
      rw [conjContinuousMulEquiv_apply]
      change Φ ^ n * elt (inverseCharacter q) 1 * (Φ ^ n)⁻¹ = _
      rw [elt, conj_incl, hΦn, character_natCast, hχpow, mul_one]
    have hq1v : 1 ≤ q ^ n * v := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero
      (Nat.one_le_iff_ne_zero.1 hq1) hvpos.ne')
    have hNW : orderOf (σ : (degree (inverseCharacter q)).ker ⧸
        (W : Subgroup (degree (inverseCharacter q)).ker)) ∣ q ^ n * v - 1 := by
      have h1 : (σ ^ v)⁻¹ * τ ∈ (W : Subgroup (degree (inverseCharacter q)).ker) := by
        rw [← QuotientGroup.eq, QuotientGroup.mk_pow]
        exact hv.symm
      have h2 : (σ ^ v)⁻¹ * τ = e (Multiplicative.ofAdd (u ^ n - v)) := by
        refine Subtype.ext ?_
        rw [Subgroup.coe_mul, Subgroup.coe_inv, hσpow, hτ, kerEquiv_apply_coe, ← elt_neg,
          ← elt_add, neg_add_eq_sub]
      have h3 : (e (Multiplicative.ofAdd (u ^ n - v))) ^ (q ^ n) = (σ ^ (q ^ n * v - 1))⁻¹ := by
        rw [← map_pow, ← ofAdd_nsmul, generatorOf_pow, ← heneg]
        congr 2
        rw [nsmul_eq_mul, Nat.cast_sub hq1v, Nat.cast_mul, Nat.cast_pow, Nat.cast_one, mul_sub,
          ← mul_pow, hqu, one_pow]
        ring
      have h4 : σ ^ (q ^ n * v - 1) ∈ (W : Subgroup (degree (inverseCharacter q)).ker) := by
        rw [← inv_inv (σ ^ _), ← h3]
        exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (h2 ▸ h1) _)
      rw [orderOf_dvd_iff_pow_eq_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact h4
    obtain ⟨-, c', hc', hc'Λ⟩ := hW
    have hcc' : ringChar Λ ∣ c' := (ringChar.spec Λ c').1 (by
      have := hc'Λ 1
      rwa [nsmul_eq_mul, mul_one] at this)
    have hcG : ringChar Λ * G ∣ q ^ n * v - 1 :=
      (show ringChar Λ * G ∣ orderOf (σ : (degree (inverseCharacter q)).ker ⧸
          (W : Subgroup (degree (inverseCharacter q)).ker)) by
        rw [hc']
        exact mul_dvd_mul hcc' hGN).trans hNW
    have hGv : G ∣ v - 1 := by
      have h1 : G ∣ q ^ n * v - 1 := (dvd_mul_left G _).trans hcG
      have h2 : G ∣ (q ^ n - 1) * v := hGR.mul_right v
      have h3 : q ^ n * v - 1 = (q ^ n - 1) * v + (v - 1) := by
        zify [hq1, hvpos, hq1v]
        ring
      rw [h3] at h1
      exact (Nat.dvd_add_right h2).1 h1
    obtain ⟨w, hw⟩ := hGv
    have hsplit : ∑ j ∈ Finset.range v, H₀ (b₁ - j) = w • S + H₀ b₁ := by
      have hv' : v = G * w + 1 := by omega
      have hL : G * w ≤ b₁ := by
        have : v ≤ v * N₀ := Nat.le_mul_of_pos_right v hN₀pos
        omega
      rw [hv', Finset.sum_range_succ', Nat.sub_zero]
      congr 1
      have hre : ∀ j ∈ Finset.range (G * w), H₀ (b₁ - (j + 1)) =
          (fun i => H₀ ((b₁ - G * w) + i)) (G * w - 1 - j) := by
        intro j hj
        have := Finset.mem_range.1 hj
        simp only
        congr 1
        omega
      rw [Finset.sum_congr rfl hre, Finset.sum_range_reflect (fun i => H₀ ((b₁ - G * w) + i))]
      generalize b₁ - G * w = s₀
      rw [mul_comm G w, sum_range_mul_of_periodic (fun i => H₀ (s₀ + i)) G w
          (fun j => by show H₀ (s₀ + (j + G)) = H₀ (s₀ + j); rw [← add_assoc, hH₀G]),
        sum_range_add_of_periodic H₀ G hH₀G]
    rw [hsplit]
    have hkey : ringChar Λ ∣ Necklace.R q n / G + q ^ n * w := by
      have : G * (Necklace.R q n / G + q ^ n * w) = q ^ n * v - 1 := by
        rw [mul_add, Nat.mul_div_cancel' hGR, mul_left_comm, ← hw]
        simp only [Necklace.R]
        zify [hq1, hvpos, hq1v]
        ring
      rw [← this, mul_comm (ringChar Λ) G] at hcG
      exact Nat.dvd_of_mul_dvd_mul_left hGpos hcG
    obtain ⟨t, ht⟩ := hkey
    have hzero : (Necklace.R q n / G) • S + (q ^ n * w) • S = 0 := by
      rw [← add_nsmul, ht, mul_nsmul', ringChar_nsmul_additiveCommutatorQuotient]
    rw [show H₀ b₁ - (w • S + H₀ b₁) = -(w • S) by abel, smul_neg, ← mul_nsmul']
    exact eq_neg_of_add_eq_zero_left hzero

end InverseFormula

section InverseRegistered

variable (q : ℕ) [hq : Fact (2 ≤ q)]

attribute [local instance] compactSpace_gamma totallyDisconnectedSpace_gamma

/-- **Stacks Project, Tag 03VQ: the special case `a = 1` occurs.** For every `q ≥ 2` the
extension `1 → Ẑ^{(q)} → Γ → Ẑ → 1` with `F x F⁻¹ = q⁻¹ x` (so `u = q⁻¹` and `qu = a = 1`) has an
abstract trace formula with integer `q`; its sets `S_d` are the orbits of exact size `d` of
multiplication by `q` on `ℤ/(q^d - 1)`, and `#S_1 = q - 1`, `#S_2 = ((q² - 1) - (q - 1))/2`. -/
@[stacks 03VQ "the special case a = 1 does occur: Γ = Ẑ^(q) ⋊ Ẑ with F x F⁻¹ = q⁻¹ x has an \
abstract trace formula with integer q, with #S₁ = q - 1 and \
#S₂ = ((q² - 1) - (q - 1))/2"]
public theorem commutativeExample_hasAbstractTraceFormula_inverse :
    ∃ T : AbstractTraceFormula (Gamma (inverseCharacter q)) (degree _) (continuous_degree _)
        (degree_surjective _),
      T.q = q ∧
        (∀ x : RestrictedProfiniteIntegers q,
          frobenius (inverseCharacter q) * incl _ (Multiplicative.ofAdd x) *
              (frobenius (inverseCharacter q))⁻¹ =
            incl _ (Multiplicative.ofAdd ((qInv q : RestrictedProfiniteIntegers q) * x))) ∧
        (q : RestrictedProfiniteIntegers q) * (qInv q : RestrictedProfiniteIntegers q) = 1 ∧
        (∀ d, T.S d = Necklace.Orbits q d) ∧
        Fintype.card (T.S 1) = q - 1 ∧ Fintype.card (T.S 2) = ((q ^ 2 - 1) - (q - 1)) / 2 := by
  set T := commutativeExample_abstractTraceFormula_inverse (q := q)
  have hconj : ∀ x : RestrictedProfiniteIntegers q,
      frobenius (inverseCharacter q) * incl _ (Multiplicative.ofAdd x) *
          (frobenius (inverseCharacter q))⁻¹ =
        incl _ (Multiplicative.ofAdd ((qInv q : RestrictedProfiniteIntegers q) * x)) := fun x => by
    rw [frobenius_conj, inverseCharacter_ofAdd_one]
  have hcard := commutativeExample_card_eq_of_eq_one (kerEquiv (inverseCharacter q))
    (degree_frobenius _) (qInv q) (fun x => by simpa only [kerEquiv_apply_coe] using hconj x) T rfl
    (natCast_mul_qInv q)
  exact ⟨T, rfl, hconj, natCast_mul_qInv q, fun _ => rfl, hcard⟩

end InverseRegistered

end Stacks.TraceFormula

end
