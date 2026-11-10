module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ExceptionalFiltration

/-!
# Independence of monomials from a principal chart

This file contains the commutative algebra behind the `monomials_indep` input of
[Stacks, Tag 0C2K]. Let `A` be a ring with a decreasing filtration `I₀ ⊇ I₁ ⊇ ⋯`, and suppose the
filtration is detected on a *principal chart*: there are a ring `B`, a nonzerodivisor `t ∈ B`
generating an ideal `J = (t)`, and ring maps `ψₙ : A ⟶ B / Jⁿ⁺¹`, compatible with the projections
`B / Jⁿ⁺² ⟶ B / Jⁿ⁺¹`, such that `Iₙ₊₁ = ker ψₙ`. Geometrically `A` is the ring of compatible
functions on the thickenings of an effective Cartier divisor `E`, `B` is the coordinate ring of an
affine open on which `E` is cut out by `t`, and `ψₙ` restricts a function on the `n`-th thickening
to that open.

For `a ∈ I_d` the value `ψ_d(a)` is the class of `t^d h` for some `h ∈ B`, and the class of `h` in
`B / J` is the *leading coefficient* of `a`. Unlike the symbol valued in binary forms, it is
multiplicative for free, because the `ψₙ` are ring maps. If `B / J` embeds, by `π : B ⟶ K`, into
a field `K` in which the residue field `k = A / I₁` is algebraically closed, then for two
elements `x, y ∈ I₁` that are independent modulo `I₂` the degree-`d` monomials `x^{d-j} y^j` are
independent over `A / I₁` modulo `I_{d+1}`:
`AlgebraicGeometry.SemistableReduction.coeff_mem_of_sum_genMonomial_mem_of_chart`.

The argument: a relation `∑ cⱼ x^{d-j} y^j ∈ I_{d+1}` becomes, after dividing by `t^d` in `B`,
the relation `∑ c̄ⱼ α^{d-j} β^j = 0` in `K` between the leading coefficients `α, β` of `x, y`.
Here `α ≠ 0` since `x ∉ I₂`, so if some `c̄ⱼ` is nonzero then `β / α` is algebraic over `k`, hence
equal to some `λ ∈ k`; lifting `λ` to `ℓ ∈ A`, the element `y - ℓ x` has leading coefficient
`β - λ α = 0`, so it lies in `I₂`, contradicting the independence of `x` and `y` modulo `I₂`.

## References

* [Stacks Project, Tag 0C2K](https://stacks.math.columbia.edu/tag/0C2K)
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.SemistableReduction

open Polynomial

variable {A B K k : Type*} [CommRing A] [CommRing B] [Field K] [Field k]

/-- **Cancelling a unit modulo a principal prime.** Let `t` be a nonzerodivisor generating a
prime ideal. If `b ∈ (t)^d` and `μ b ∈ (t)^{d+1}` for some `μ ∉ (t)`, then `b ∈ (t)^{d+1}`. -/
public theorem mem_span_singleton_pow_succ_of_mul_mem {t μ b : B} (ht : t ∈ nonZeroDivisors B)
    (hp : (Ideal.span {t}).IsPrime) (hμ : μ ∉ Ideal.span {t}) {d : ℕ}
    (hb : b ∈ Ideal.span {t} ^ d) (hμb : μ * b ∈ Ideal.span {t} ^ (d + 1)) :
    b ∈ Ideal.span {t} ^ (d + 1) := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hb hμb ⊢
  obtain ⟨h, rfl⟩ := hb
  obtain ⟨r, hr⟩ := hμb
  have hzero : (μ * h - r * t) * t ^ d = 0 := by linear_combination -hr
  have hmem : μ * h ∈ Ideal.span {t} := by
    rw [sub_eq_zero.1 ((mul_right_mem_nonZeroDivisors_eq_zero_iff (pow_mem ht d)).1 hzero)]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self t)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 ((hp.mem_or_mem hmem).resolve_left hμ)
  exact ⟨c, by linear_combination t ^ d * hc⟩

/-- For a compatible family `ψₙ : A ⟶ B / Jⁿ⁺¹`, a lift of `ψₙ(a)` is a lift of `ψₘ(a)` for
`m ≤ n`. -/
private theorem map_eq_mk_of_le {J : Ideal B} (ψ : ∀ n : ℕ, A →+* B ⧸ J ^ (n + 1))
    (hcomp : ∀ n a b, ψ (n + 1) a = Ideal.Quotient.mk _ b → ψ n a = Ideal.Quotient.mk _ b)
    {m n : ℕ} (hmn : m ≤ n) {a : A} {b : B} (hab : ψ n a = Ideal.Quotient.mk _ b) :
    ψ m a = Ideal.Quotient.mk _ b := by
  induction n, hmn using Nat.le_induction with
  | base => exact hab
  | succ n _ ih => exact ih (hcomp n a b hab)

/-- If `ψ₀(a) = 0` for a compatible family `ψₙ : A ⟶ B / (t)ⁿ⁺¹`, then `ψₙ(a)` is the class of a
multiple of `t`. -/
private theorem exists_eq_mk_mul_of_map_zero_eq_zero (t : B)
    (ψ : ∀ n : ℕ, A →+* B ⧸ Ideal.span {t} ^ (n + 1))
    (hcomp : ∀ n a b, ψ (n + 1) a = Ideal.Quotient.mk _ b → ψ n a = Ideal.Quotient.mk _ b)
    {a : A} (ha : ψ 0 a = 0) (n : ℕ) : ∃ X, ψ n a = Ideal.Quotient.mk _ (t * X) := by
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (ψ n a)
  have h0 := map_eq_mk_of_le ψ hcomp (Nat.zero_le n) hb.symm
  rw [ha, eq_comm, Ideal.Quotient.eq_zero_iff_mem, zero_add, pow_one,
    Ideal.mem_span_singleton'] at h0
  obtain ⟨X, hX⟩ := h0
  exact ⟨X, by rw [← hb, ← hX, mul_comm]⟩

/-- The leading coefficient of an element modulo `(t)` does not depend on the level `n ≥ 1` at
which it is read off. -/
private theorem map_eq_map_of_eq_mk_mul {t : B} (ht : t ∈ nonZeroDivisors B)
    (ψ : ∀ n : ℕ, A →+* B ⧸ Ideal.span {t} ^ (n + 1))
    (hcomp : ∀ n a b, ψ (n + 1) a = Ideal.Quotient.mk _ b → ψ n a = Ideal.Quotient.mk _ b)
    (π : B →+* K) (hπ : RingHom.ker π = Ideal.span {t}) {n : ℕ} (hn : 1 ≤ n) {a : A}
    {X X' : B} (hX : ψ n a = Ideal.Quotient.mk _ (t * X))
    (hX' : ψ 1 a = Ideal.Quotient.mk _ (t * X')) : π X = π X' := by
  have h1 := (map_eq_mk_of_le ψ hcomp hn hX).symm.trans hX'
  rw [Ideal.Quotient.eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h1
  obtain ⟨r, hr⟩ := h1
  have hzero : (X - X' - r * t) * t = 0 := by linear_combination -hr
  have h2 := (mul_right_mem_nonZeroDivisors_eq_zero_iff ht).1 hzero
  rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, hπ, Ideal.mem_span_singleton']
  exact ⟨r, by linear_combination -h2⟩

/-- A relation `∑ cᵢ x^{d-i} y^i` killed by `ψ_d` yields, after dividing by `t^d`, the relation
`∑ c̄ᵢ α^{d-i} β^i = 0` between the leading coefficients `α, β` of `x, y`. -/
private theorem sum_mul_pow_eq_zero_of_map_sum_genMonomial_eq_zero {t : B}
    (ht : t ∈ nonZeroDivisors B) (ψ : ∀ n : ℕ, A →+* B ⧸ Ideal.span {t} ^ (n + 1))
    (π : B →+* K) (hπt : π t = 0) (ρ : A →+* k) (f : k →+* K) {d : ℕ}
    (hres : ∀ a b, ψ d a = Ideal.Quotient.mk _ b → π b = f (ρ a))
    {x y : A} {X Y : B} (hX : ψ d x = Ideal.Quotient.mk _ (t * X))
    (hY : ψ d y = Ideal.Quotient.mk _ (t * Y)) (c : ℕ → A)
    (h : ψ d (∑ j ∈ Finset.range (d + 1), c j * genMonomial x y d j) = 0) :
    ∑ i ∈ Finset.range (d + 1), f (ρ (c i)) * π X ^ (d - i) * π Y ^ i = 0 := by
  choose C hC using fun i => Ideal.Quotient.mk_surjective (ψ d (c i))
  have hterm : ∀ i ∈ Finset.range (d + 1), ψ d (c i * genMonomial x y d i) =
      Ideal.Quotient.mk _ (t ^ d * (C i * X ^ (d - i) * Y ^ i)) := by
    intro i hi
    rw [genMonomial, map_mul, map_mul, map_pow, map_pow, hX, hY, ← hC i, ← map_pow, ← map_pow,
      ← map_mul, ← map_mul]
    congr 1
    calc C i * ((t * X) ^ (d - i) * (t * Y) ^ i)
        = t ^ (d - i + i) * (C i * X ^ (d - i) * Y ^ i) := by ring
      _ = _ := by rw [Nat.sub_add_cancel (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))]
  rw [map_sum, Finset.sum_congr rfl hterm, ← map_sum, ← Finset.mul_sum,
    Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h
  obtain ⟨r, hr⟩ := h
  have hzero : (∑ i ∈ Finset.range (d + 1), C i * X ^ (d - i) * Y ^ i - r * t) * t ^ d = 0 := by
    linear_combination -hr
  have hmem := sub_eq_zero.1 ((mul_right_mem_nonZeroDivisors_eq_zero_iff (pow_mem ht d)).1 hzero)
  have hπ0 : π (∑ i ∈ Finset.range (d + 1), C i * X ^ (d - i) * Y ^ i) = 0 := by
    rw [hmem, map_mul, hπt, mul_zero]
  rw [map_sum] at hπ0
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hπ0
  rw [map_mul, map_mul, map_pow, map_pow, hres (c i) (C i) (hC i).symm]

/-- The polynomial `∑_{i ≤ d} aᵢ Xⁱ` is nonzero as soon as one `aⱼ` with `j ≤ d` is. -/
private theorem sum_C_mul_X_pow_ne_zero {R : Type*} [Semiring R] {a : ℕ → R} {d j : ℕ}
    (hj : j ≤ d) (ha : a j ≠ 0) : ∑ i ∈ Finset.range (d + 1), C (a i) * X ^ i ≠ 0 := by
  intro hp0
  have hcoeff := congrArg (fun q : R[X] => q.coeff j) hp0
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
    Finset.sum_ite_eq, Finset.mem_range, Polynomial.coeff_zero] at hcoeff
  rw [ite_eq_left (Nat.lt_succ_of_le hj)] at hcoeff
  exact ha hcoeff

/-- **Dehomogenization.** For `u ≠ 0`, `∑ aᵢ (v / u)ⁱ = (∑ aᵢ u^{d-i} vⁱ) / u^d`. -/
private theorem sum_mul_div_pow_eq {F : Type*} [Field F] (a : ℕ → F) {u : F} (v : F) (d : ℕ)
    (hu : u ≠ 0) : ∑ i ∈ Finset.range (d + 1), a i * (v / u) ^ i =
      (∑ i ∈ Finset.range (d + 1), a i * u ^ (d - i) * v ^ i) / u ^ d := by
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hid : u ^ d = u ^ (d - i) * u ^ i := by
    rw [← pow_add, Nat.sub_add_cancel (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))]
  rw [hid, div_pow]
  field_simp

/-- **The degree-`d` monomials in two elements independent modulo `I₂` are independent over
`A / I₁` modulo `I_{d+1}`**, for a filtration detected on a principal chart.

The hypotheses: `J = (t)` with `t` a nonzerodivisor of `B`; ring maps `ψₙ : A ⟶ B / Jⁿ⁺¹`
compatible with the projections (`hcomp`), with `Iₙ₊₁ ⊆ ker ψₙ` (`hI`) and `I₁ ∩ ker ψ₁ ⊆ I₂`
(`hI₂`); a ring map `π : B ⟶ K` to a field with kernel `J`; a surjection `ρ : A ⟶ k` onto a field
with kernel `I₁` (`hρI`) and a ring map `f : k ⟶ K` such
that `π` of a lift of `ψ₀(a)` is `f (ρ a)` (`hπρ`); and the algebraic closedness of `k` in `K`
along `f` (`halg`). The two elements `x, y ∈ I₁` are independent modulo `I₂` over `A / I₁`
(`hxy`). -/
public theorem coeff_mem_of_sum_genMonomial_mem_of_chart
    (I : ℕ → Ideal A) (J : Ideal B) (t : B) (hJ : J = Ideal.span {t})
    (ht : t ∈ nonZeroDivisors B)
    (ψ : ∀ n : ℕ, A →+* B ⧸ J ^ (n + 1))
    (hcomp : ∀ n a b, ψ (n + 1) a = Ideal.Quotient.mk _ b → ψ n a = Ideal.Quotient.mk _ b)
    (hI : ∀ n a, a ∈ I (n + 1) → ψ n a = 0)
    (hI₂ : ∀ a, a ∈ I 1 → ψ 1 a = 0 → a ∈ I 2)
    (π : B →+* K) (hπ : RingHom.ker π = J)
    (ρ : A →+* k) (hρ : Function.Surjective ρ) (hρI : ∀ a, a ∈ I 1 ↔ ρ a = 0) (f : k →+* K)
    (hπρ : ∀ a b, ψ 0 a = Ideal.Quotient.mk _ b → π b = f (ρ a))
    (halg : ∀ (u : K) (p : k[X]), p ≠ 0 → p.eval₂ f u = 0 → ∃ c, f c = u)
    {x y : A} (hx : x ∈ I 1) (hy : y ∈ I 1)
    (hxy : ∀ a b, a * x + b * y ∈ I 2 → a ∈ I 1 ∧ b ∈ I 1)
    (d : ℕ) (c : ℕ → A)
    (h : (∑ j ∈ Finset.range (d + 1), c j * genMonomial x y d j) ∈ I (d + 1))
    (j : ℕ) (hj : j ≤ d) : c j ∈ I 1 := by
  subst hJ
  have hπt : ∀ b, π b = 0 ↔ b ∈ Ideal.span {t} := fun b => by rw [← RingHom.mem_ker, hπ]
  have hlift : ∀ n a, a ∈ I 1 → ∃ X, ψ n a = Ideal.Quotient.mk _ (t * X) :=
    fun n a ha => exists_eq_mk_mul_of_map_zero_eq_zero t ψ hcomp (hI 0 a ha) n
  have hres : ∀ n a b, ψ n a = Ideal.Quotient.mk _ b → π b = f (ρ a) :=
    fun n a b hab => hπρ a b (map_eq_mk_of_le ψ hcomp (Nat.zero_le n) hab)
  have h1I : (1 : A) ∉ I 1 := by simp [hρI]
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · obtain rfl : j = 0 := Nat.le_zero.1 hj
    simpa [genMonomial] using h
  obtain ⟨X₁, hX₁⟩ := hlift 1 x hx
  obtain ⟨Y₁, hY₁⟩ := hlift 1 y hy
  have hα : π X₁ ≠ 0 := by
    intro h0
    rw [hπt, Ideal.mem_span_singleton'] at h0
    obtain ⟨r, hr⟩ := h0
    have hx2 : x ∈ I 2 := by
      refine hI₂ x hx ?_
      rw [hX₁, Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton']
      exact ⟨r, by linear_combination t * hr⟩
    exact h1I (hxy 1 0 (by simpa using hx2)).1
  obtain ⟨X, hX⟩ := hlift d x hx
  obtain ⟨Y, hY⟩ := hlift d y hy
  have hrel := sum_mul_pow_eq_zero_of_map_sum_genMonomial_eq_zero ht ψ π
    ((hπt t).2 (Ideal.mem_span_singleton_self t)) ρ f (hres d) hX hY c (hI d _ h)
  rw [map_eq_map_of_eq_mk_mul ht ψ hcomp π hπ hd hX hX₁,
    map_eq_map_of_eq_mk_mul ht ψ hcomp π hπ hd hY hY₁] at hrel
  by_contra hcj
  rw [hρI] at hcj
  let p : k[X] := ∑ i ∈ Finset.range (d + 1), Polynomial.C (ρ (c i)) * Polynomial.X ^ i
  have hpu : p.eval₂ f (π Y₁ / π X₁) = 0 := by
    simp only [p, Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_X_pow]
    rw [sum_mul_div_pow_eq _ _ _ hα, hrel, zero_div]
  obtain ⟨l, hl⟩ := halg _ p (sum_C_mul_X_pow_ne_zero (a := fun i => ρ (c i)) hj hcj) hpu
  obtain ⟨ℓ, hℓ⟩ := hρ l
  obtain ⟨L, hL⟩ := Ideal.Quotient.mk_surjective (ψ 1 ℓ)
  have hz : (-ℓ) * x + 1 * y ∈ I 2 := by
    have hmem : Y₁ - L * X₁ ∈ Ideal.span {t} := by
      rw [← hπt, map_sub, map_mul, hres 1 ℓ L hL.symm, hℓ, hl, div_mul_cancel₀ _ hα, sub_self]
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hmem
    refine hI₂ _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ hx) (Ideal.mul_mem_left _ _ hy)) ?_
    rw [map_add, map_mul, map_mul, map_neg, map_one, one_mul, hX₁, hY₁, ← hL, ← map_neg,
      ← map_mul, ← map_add, Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton']
    exact ⟨r, by linear_combination t * hr⟩
  exact h1I (hxy (-ℓ) 1 hz).2

end AlgebraicGeometry.SemistableReduction
