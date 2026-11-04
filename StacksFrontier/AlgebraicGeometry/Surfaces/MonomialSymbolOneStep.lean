module

public import StacksFrontier.AlgebraicGeometry.Surfaces.FormalNeighborhoodSymbol
public import StacksFrontier.AlgebraicGeometry.Surfaces.FormalNeighborhoodSymbolAdditive

/-!
# A monomial symbol system from the one-step multiplicativity alone

`AlgebraicGeometry.SemistableReduction.MonomialSymbol` asks for its symbol to be multiplicative
across *every* pair of degrees,

`σ_{m+n}(ab) = σₘ(a) σₙ(b)`  for `a ∈ Iₘ`, `b ∈ Iₙ`.

This file proves that the general bidegree is a *consequence* of two much weaker laws:

* the **one-step law**, the same equation in the single bidegree `(d, 1)`, and
* the **degree-zero law** `σₙ(ca) = σ₀(c) σₙ(a)` for an arbitrary ring element `c`, which is
  semilinearity of the symbol over the residue map.

`AlgebraicGeometry.SemistableReduction.OneStepSymbol` bundles those two in place of
`symbol_mul`, and `AlgebraicGeometry.SemistableReduction.OneStepSymbol.toMonomialSymbol` turns
such a bundle into a monomial symbol system with nothing else supplied.

## Why this is the reduction that matters

For the formal neighbourhood of an exceptional curve of the first kind both weak laws are on a
different footing from the general one. The degree-zero law is **already proved**, and
unconditionally:
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.gradedPieceComparison_smul`
says that multiplying a graded piece by the component of a compatible function is multiplying by
its residue in `k`. The one-step law is exactly the bidegree in which the sheaf-level
multiplicativity of the sequence of [Stacks, Tag 0C4T] is proved,
`Stacks.Divisors.idealTensorMul_comp_unit_comp_thickeningKernelMap`, and the bidegree in which
the coherent family of twists carries its cross-degree law,
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
`.curveTwistIso_tensorHom_comp_succIso`. So after this file the whole of the monomial symbol
system rests on **one** equation about the degreewise comparison, in **one** bidegree, and not on
a graded identification in all bidegrees at once.

## The proof, and what it does not use

The general bidegree is an induction on the second degree `n`.

* `n = 0` is the degree-zero law and commutativity.
* For `n + 1`, the spanning statement at degree `n + 1` writes `b ∈ Iₙ₊₁` as a combination
  `∑ⱼ cⱼ x^{n+1-j} y^j` of the degree-`(n+1)` monomials in the two chosen elements, plus an error
  in `Iₙ₊₂`. The error contributes nothing, because `a` times it lies in `I_{m+n+2}`. Each
  monomial term loses one factor of a *single* generator by the one-step law, which is where the
  induction hypothesis at `n` applies, and the degree-zero law moves `cⱼ` out of the way.

The spanning statement is not a hypothesis: it is itself derived from the one-step law here
(`AlgebraicGeometry.SemistableReduction.OneStepSymbol.ideal_le_span_pow_sup_oneStep`), by the
argument of `AlgebraicGeometry.SemistableReduction.MonomialSymbol.ideal_le_span_pow_sup` — the
symbol of an element of `Iₙ` is a binary form of degree `n`, those are spanned by the `n + 1`
monomials, and the coefficients lift to `A` because `σ₀` is onto.

**Completeness of the filtration is not used, and neither is separatedness.** Neither is any
surjectivity of the symbol beyond degree zero. An earlier note on this chain, in the module
docstring of
`StacksFrontier/AlgebraicGeometry/Surfaces/ExceptionalCurveFormalNeighborhood.lean`, said that the
general bidegree "follows from the one-step law together with the spanning statement
`le_span_pow_sup` and the completeness of the filtration"; the completeness half of that is
unnecessary, and the spanning half is not an extra hypothesis but a consequence.

One axiom does have to be added that `AlgebraicGeometry.SemistableReduction.MonomialSymbol` does
not state: that the filtration **decreases**, `ideal_succ_le`. It is used once, to know that
`a` times the error term of the spanning statement lies in the step whose symbol the
`symbol_eq_zero_iff` axiom is guarded by. It is not derivable from the other axioms, and it costs
nothing where it is wanted: for the projection-kernel filtration it is
`AlgebraicGeometry.Scheme.IdealSheafData.formalNeighborhoodFiltration_succ_le`, which holds for
every ideal sheaf on every scheme, and for the leading-form filtration of `k[T₀, T₁]` it is
monotonicity of the powers of an ideal.

Nothing here carries a `@[stacks]` attribute: this is one step of the proof of
[Stacks, Tag 0C2K].

## Main definitions

* `AlgebraicGeometry.SemistableReduction.OneStepSymbol` — a symbol system asked only for the
  one-step and degree-zero multiplicativity laws.
* `AlgebraicGeometry.SemistableReduction.OneStepSymbol.toMonomialSymbol` — **the monomial symbol
  system it determines.**

## Main results

* `AlgebraicGeometry.SemistableReduction.OneStepSymbol.symbol_genMonomial_eq` — the symbol of a
  degree-`n` monomial in the two chosen elements is the corresponding binary monomial, from the
  one-step law alone.
* `AlgebraicGeometry.SemistableReduction.OneStepSymbol.ideal_le_span_pow_sup_oneStep` — the
  spanning statement, from the one-step law alone.
* `AlgebraicGeometry.SemistableReduction.OneStepSymbol.symbol_mul_of_oneStep` — **the general
  bidegree multiplicativity.**

## References

* [Stacks Project, Tag 0C2K](https://stacks.math.columbia.edu/tag/0C2K)
* [Stacks Project, Tag 0C4T](https://stacks.math.columbia.edu/tag/0C4T)
-/

@[expose] public noncomputable section

universe u

namespace MvPolynomial

/-- Multiplying a degree-`n` binary monomial by the first coordinate raises its degree, keeping
the exponent of the second coordinate. -/
theorem binaryMonomial_mul_X_zero (R : Type u) [CommRing R] {n j : ℕ} (hj : j ≤ n) :
    binaryMonomial R n j * X 0 = binaryMonomial R (n + 1) j := by
  have h : n + 1 - j = (n - j) + 1 := by omega
  simp only [binaryMonomial, h, pow_succ]
  ring

/-- Multiplying a degree-`n` binary monomial by the second coordinate raises its degree and the
exponent of the second coordinate. -/
theorem binaryMonomial_mul_X_one (R : Type u) [CommRing R] (n j : ℕ) :
    binaryMonomial R n j * X 1 = binaryMonomial R (n + 1) (j + 1) := by
  have h : n + 1 - (j + 1) = n - j := by omega
  simp only [binaryMonomial, h, pow_succ]
  ring

end MvPolynomial

namespace AlgebraicGeometry.SemistableReduction

/-- A *one-step symbol system* on a commutative ring `A`, with values in a commutative ring `k`.

Every axiom of `AlgebraicGeometry.SemistableReduction.MonomialSymbol` is asked for except
`symbol_mul`, the multiplicativity of the symbol across an arbitrary pair of degrees. In its
place two weaker laws are asked for: `symbol_smul`, multiplicativity against degree zero, and
`symbol_mul_one`, multiplicativity in the single bidegree `(d, 1)`. The decrease of the
filtration, `ideal_succ_le`, is asked for as well; see the module docstring for both points.

`AlgebraicGeometry.SemistableReduction.OneStepSymbol.toMonomialSymbol` shows that nothing is lost:
the general bidegree follows. -/
structure OneStepSymbol (A : Type u) [CommRing A] (k : Type u) [CommRing k] where
  /-- The filtering ideals `Iₙ`. -/
  ideal : ℕ → Ideal A
  /-- The symbol, or leading form, of an element of `Iₙ`. -/
  symbol : ℕ → A → MvPolynomial (Fin 2) k
  /-- The filtration starts at the whole ring. -/
  ideal_zero : ideal 0 = ⊤
  /-- The filtration decreases. -/
  ideal_succ_le : ∀ n, ideal (n + 1) ≤ ideal n
  /-- The filtration is multiplicative. -/
  mul_le : ∀ m n, ideal m * ideal n ≤ ideal (m + n)
  /-- The symbol of an element of `Iₙ` is a binary form of degree `n`. -/
  symbol_mem : ∀ (n : ℕ) {a : A}, a ∈ ideal n →
    symbol n a ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k n
  /-- The symbol is additive on `Iₙ`. -/
  symbol_add : ∀ (n : ℕ) {a b : A}, a ∈ ideal n → b ∈ ideal n →
    symbol n (a + b) = symbol n a + symbol n b
  /-- The symbol of an element of `Iₙ` vanishes exactly when the element lies in `Iₙ₊₁`. -/
  symbol_eq_zero_iff : ∀ (n : ℕ) {a : A}, a ∈ ideal n → (symbol n a = 0 ↔ a ∈ ideal (n + 1))
  /-- **Multiplicativity against degree zero**: the symbol is semilinear over `σ₀`. -/
  symbol_smul : ∀ (n : ℕ) (c : A) {a : A}, a ∈ ideal n →
    symbol n (c * a) = symbol 0 c * symbol n a
  /-- **The one-step law**: the symbol is multiplicative in the bidegree `(d, 1)`. -/
  symbol_mul_one : ∀ (d : ℕ) {a b : A}, a ∈ ideal d → b ∈ ideal 1 →
    symbol (d + 1) (a * b) = symbol d a * symbol 1 b
  /-- The symbol of `1` in degree `0` is `1`. -/
  symbol_one : symbol 0 1 = 1
  /-- Every constant is the degree-zero symbol of some element: `A ⟶ A / I₁ = k` is onto. -/
  surjective_symbol_zero : ∀ c : k, ∃ a : A, symbol 0 a = MvPolynomial.C c
  /-- Both coordinates are degree-one symbols: `I₁ ⟶ H⁰(𝐏¹_k, 𝒪(1))` is onto. -/
  exists_symbol_one_eq_X : ∃ x y : A, x ∈ ideal 1 ∧ y ∈ ideal 1 ∧
    symbol 1 x = MvPolynomial.X 0 ∧ symbol 1 y = MvPolynomial.X 1

namespace OneStepSymbol

variable {A : Type u} [CommRing A] {k : Type u} [CommRing k] (S : OneStepSymbol A k)

/-! ### Routine consequences of additivity and of the filtration axioms

Vanishing at `0`, additivity on differences and additivity on finite sums are not restated here:
they hold for any additive symbol map, and
`AlgebraicGeometry.SemistableReduction.symbol_zero_of_add`,
`AlgebraicGeometry.SemistableReduction.symbol_sub_of_add` and
`AlgebraicGeometry.SemistableReduction.symbol_sum_range_of_add` are applied to the `symbol_add`
field directly. -/

private theorem mem_ideal_top (a : A) : a ∈ S.ideal 0 := by
  rw [S.ideal_zero]; trivial

private theorem mul_mem_ideal_of_add_eq {m n p : ℕ} (h : m + n = p) {a b : A}
    (ha : a ∈ S.ideal m) (hb : b ∈ S.ideal n) : a * b ∈ S.ideal p :=
  h ▸ S.mul_le m n (Ideal.mul_mem_mul ha hb)

private theorem pow_mem_ideal_of_mem_one {x : A} (hx : x ∈ S.ideal 1) :
    ∀ p : ℕ, x ^ p ∈ S.ideal p := by
  intro p
  induction p with
  | zero => simpa using S.mem_ideal_top 1
  | succ p ih =>
    rw [pow_succ]
    exact S.mul_mem_ideal_of_add_eq rfl ih hx

private theorem genMonomial_mem_ideal_of_mem_one {x y : A} (hx : x ∈ S.ideal 1)
    (hy : y ∈ S.ideal 1) {n j : ℕ} (hj : j ≤ n) : genMonomial x y n j ∈ S.ideal n := by
  exact S.mul_mem_ideal_of_add_eq (Nat.sub_add_cancel hj) (S.pow_mem_ideal_of_mem_one hx (n - j))
    (S.pow_mem_ideal_of_mem_one hy j)

private theorem coeff_genMonomial_mem_ideal {x y : A} (hx : x ∈ S.ideal 1) (hy : y ∈ S.ideal 1)
    {n j : ℕ} (hj : j ≤ n) (c : A) : c * genMonomial x y n j ∈ S.ideal n :=
  Ideal.mul_mem_left _ _ (S.genMonomial_mem_ideal_of_mem_one hx hy hj)

/-! ### The symbols of the monomials, from the one-step law -/

variable {x y : A} (hx : x ∈ S.ideal 1) (hy : y ∈ S.ideal 1)
  (hsx : S.symbol 1 x = MvPolynomial.X 0) (hsy : S.symbol 1 y = MvPolynomial.X 1)

include hx hy hsx hsy in
/-- **The symbol of a degree-`n` monomial in the two chosen elements is the corresponding binary
monomial**, from the one-step law alone.

The general bidegree law is not used: a degree-`(n+1)` monomial is a degree-`n` monomial times a
*single* generator, so the one-step law peels one factor off at a time. -/
theorem symbol_genMonomial_eq : ∀ (n j : ℕ), j ≤ n →
    S.symbol n (genMonomial x y n j) = MvPolynomial.binaryMonomial k n j := by
  intro n
  induction n with
  | zero =>
    intro j hj
    obtain rfl : j = 0 := Nat.le_zero.1 hj
    rw [genMonomial_zero_zero, S.symbol_one, MvPolynomial.binaryMonomial]
    simp
  | succ n ih =>
    intro j hj
    rcases Nat.lt_or_ge j (n + 1) with hjn | hjn
    · have hjn' : j ≤ n := Nat.lt_succ_iff.1 hjn
      rw [← genMonomial_mul_gen₁ x y hjn',
        S.symbol_mul_one n (S.genMonomial_mem_ideal_of_mem_one hx hy hjn') hx, ih j hjn', hsx]
      exact MvPolynomial.binaryMonomial_mul_X_zero k hjn'
    · obtain rfl : j = n + 1 := le_antisymm hj hjn
      rw [← genMonomial_mul_gen₂ x y n n,
        S.symbol_mul_one n (S.genMonomial_mem_ideal_of_mem_one hx hy (le_refl n)) hy,
        ih n (le_refl n), hsy]
      exact MvPolynomial.binaryMonomial_mul_X_one k n n

include hx hy hsx hsy in
private theorem symbol_coeff_genMonomial_eq {n j : ℕ} (hj : j ≤ n) (c : A) :
    S.symbol n (c * genMonomial x y n j) =
      S.symbol 0 c * MvPolynomial.binaryMonomial k n j := by
  rw [S.symbol_smul n c (S.genMonomial_mem_ideal_of_mem_one hx hy hj),
    S.symbol_genMonomial_eq hx hy hsx hsy n j hj]

/-! ### The spanning statement, from the one-step law -/

include hx hy hsx hsy in
/-- **`Iₙ` is spanned by the degree-`n` monomials in the two chosen elements modulo `Iₙ₊₁`**, from
the one-step law alone.

This is the argument of `AlgebraicGeometry.SemistableReduction.MonomialSymbol`
`.ideal_le_span_pow_sup`, which consumes the general bidegree law only through the symbol of a
monomial: the symbol of an element of `Iₙ` is a binary form of degree `n`, those are spanned by
the `n + 1` monomials of that degree, and the coefficients lift to `A` because `σ₀` is onto. -/
theorem ideal_le_span_pow_sup_oneStep (n : ℕ) :
    S.ideal n ≤ Ideal.span {x, y} ^ n ⊔ S.ideal (n + 1) := by
  intro a ha
  obtain ⟨lam, hlam⟩ :=
    MvPolynomial.exists_eq_sum_binaryMonomial n (S.symbol n a) (S.symbol_mem n ha)
  choose c hc using fun j : ℕ => S.surjective_symbol_zero (lam j)
  have hterm : ∀ j ∈ Finset.range (n + 1), c j * genMonomial x y n j ∈ S.ideal n := fun j hj =>
    S.coeff_genMonomial_mem_ideal hx hy (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) (c j)
  have hwmem : (∑ j ∈ Finset.range (n + 1), c j * genMonomial x y n j) ∈ S.ideal n :=
    Submodule.sum_mem _ hterm
  have hsymw : S.symbol n (∑ j ∈ Finset.range (n + 1), c j * genMonomial x y n j) =
      S.symbol n a := by
    rw [symbol_sum_range_of_add S.symbol_add n (n + 1) _ hterm, hlam]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [S.symbol_coeff_genMonomial_eq hx hy hsx hsy
      (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) (c j), hc j, MvPolynomial.smul_eq_C_mul]
  have hrem : a - ∑ j ∈ Finset.range (n + 1), c j * genMonomial x y n j ∈ S.ideal (n + 1) :=
    (S.symbol_eq_zero_iff n (sub_mem ha hwmem)).1
      (by rw [symbol_sub_of_add S.symbol_add n ha hwmem, hsymw, sub_self])
  exact Submodule.mem_sup.2 ⟨_, sum_genMonomial_mem_span_pow x y n c, _, hrem, by ring⟩

/-! ### The general bidegree -/

include hx hy hsx hsy in
private theorem symbol_mul_step (n : ℕ)
    (ih : ∀ (m : ℕ) {a b : A}, a ∈ S.ideal m → b ∈ S.ideal n →
      S.symbol (m + n) (a * b) = S.symbol m a * S.symbol n b)
    (m : ℕ) {a b : A} (ha : a ∈ S.ideal m) (hb : b ∈ S.ideal (n + 1)) :
    S.symbol (m + n + 1) (a * b) = S.symbol m a * S.symbol (n + 1) b := by
  obtain ⟨w, hw, b', hb', hbw⟩ :=
    Submodule.mem_sup.1 (S.ideal_le_span_pow_sup_oneStep hx hy hsx hsy (n + 1) hb)
  obtain ⟨c, hc⟩ := exists_repr_of_mem_span_pow x y hw
  -- the degree-`(n+1)` monomial terms of `w`, and their membership
  have hmono : ∀ j ∈ Finset.range (n + 1 + 1),
      c j * genMonomial x y (n + 1) j ∈ S.ideal (n + 1) := fun j hj =>
    S.coeff_genMonomial_mem_ideal hx hy (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) (c j)
  have hwmem : w ∈ S.ideal (n + 1) := by
    rw [hc]; exact Submodule.sum_mem _ hmono
  -- the key computation on a single monomial term
  have hkey : ∀ j ∈ Finset.range (n + 1 + 1),
      S.symbol (m + n + 1) (a * (c j * genMonomial x y (n + 1) j)) =
        S.symbol m a * S.symbol (n + 1) (c j * genMonomial x y (n + 1) j) := by
    intro j hj
    have hjle : j ≤ n + 1 := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    rw [S.symbol_coeff_genMonomial_eq hx hy hsx hsy hjle (c j)]
    rcases Nat.lt_or_ge j (n + 1) with hjn | hjn
    · have hjn' : j ≤ n := Nat.lt_succ_iff.1 hjn
      have hsplit : a * (c j * genMonomial x y (n + 1) j) =
          a * (c j * genMonomial x y n j) * x := by
        rw [← genMonomial_mul_gen₁ x y hjn']; ring
      have hcg := S.coeff_genMonomial_mem_ideal hx hy hjn' (c j)
      rw [hsplit, S.symbol_mul_one (m + n) (S.mul_mem_ideal_of_add_eq rfl ha hcg) hx, ih m ha hcg,
        S.symbol_coeff_genMonomial_eq hx hy hsx hsy hjn' (c j), hsx,
        ← MvPolynomial.binaryMonomial_mul_X_zero k hjn']
      ring
    · obtain rfl : j = n + 1 := le_antisymm hjle hjn
      have hsplit : a * (c (n + 1) * genMonomial x y (n + 1) (n + 1)) =
          a * (c (n + 1) * genMonomial x y n n) * y := by
        rw [← genMonomial_mul_gen₂ x y n n]; ring
      have hcg := S.coeff_genMonomial_mem_ideal hx hy (le_refl n) (c (n + 1))
      rw [hsplit, S.symbol_mul_one (m + n) (S.mul_mem_ideal_of_add_eq rfl ha hcg) hy, ih m ha hcg,
        S.symbol_coeff_genMonomial_eq hx hy hsx hsy (le_refl n) (c (n + 1)), hsy,
        ← MvPolynomial.binaryMonomial_mul_X_one k n n]
      ring
  -- the error term of the spanning statement contributes nothing
  have hb'n : b' ∈ S.ideal (n + 1) := S.ideal_succ_le (n + 1) hb'
  have herrmem : a * b' ∈ S.ideal (m + n + 1 + 1) :=
    S.mul_mem_ideal_of_add_eq (by omega) ha hb'
  have herrmem' : a * b' ∈ S.ideal (m + n + 1) := S.ideal_succ_le (m + n + 1) herrmem
  have herr : S.symbol (m + n + 1) (a * b') = 0 :=
    (S.symbol_eq_zero_iff (m + n + 1) herrmem').2 herrmem
  -- the monomial part carries the product
  have hamem : ∀ j ∈ Finset.range (n + 1 + 1),
      a * (c j * genMonomial x y (n + 1) j) ∈ S.ideal (m + n + 1) := fun j hj =>
    S.mul_mem_ideal_of_add_eq (by omega) ha (hmono j hj)
  have hawmem : a * w ∈ S.ideal (m + n + 1) := S.mul_mem_ideal_of_add_eq (by omega) ha hwmem
  have haw : S.symbol (m + n + 1) (a * w) = S.symbol m a * S.symbol (n + 1) w := by
    have hexp : a * w = ∑ j ∈ Finset.range (n + 1 + 1), a * (c j * genMonomial x y (n + 1) j) := by
      rw [hc, Finset.mul_sum]
    rw [hexp, symbol_sum_range_of_add S.symbol_add (m + n + 1) (n + 1 + 1) _ hamem,
      Finset.sum_congr rfl hkey, ← Finset.mul_sum, hc,
      symbol_sum_range_of_add S.symbol_add (n + 1) (n + 1 + 1) _ hmono]
  -- the symbol of `b` is the symbol of its monomial part
  have hsymb : S.symbol (n + 1) b = S.symbol (n + 1) w := by
    rw [← hbw, S.symbol_add (n + 1) hwmem hb'n,
      (S.symbol_eq_zero_iff (n + 1) hb'n).2 hb', add_zero]
  rw [hsymb, ← hbw, mul_add, S.symbol_add (m + n + 1) hawmem herrmem', haw, herr, add_zero]

include hx hy hsx hsy in
/-- **The symbol of a one-step symbol system is multiplicative across every pair of degrees.**

An induction on the second degree. The spanning statement writes an element of `Iₙ₊₁` as a
combination of the degree-`(n+1)` monomials in the two chosen elements modulo `Iₙ₊₂`; each
monomial loses a factor of a single generator by the one-step law, which is where the induction
hypothesis applies, and the coefficients move out of the way by the degree-zero law. Neither
completeness nor separatedness of the filtration is used; see the module docstring. -/
theorem symbol_mul_of_oneStep : ∀ (n m : ℕ) {a b : A}, a ∈ S.ideal m → b ∈ S.ideal n →
    S.symbol (m + n) (a * b) = S.symbol m a * S.symbol n b := by
  intro n
  induction n with
  | zero =>
    intro m a b ha _
    rw [Nat.add_zero, mul_comm a b, S.symbol_smul m b ha, mul_comm]
  | succ n ih =>
    intro m a b ha hb
    rw [show m + (n + 1) = m + n + 1 from by omega]
    exact S.symbol_mul_step hx hy hsx hsy n ih m ha hb

end OneStepSymbol

/-- **A one-step symbol system is a monomial symbol system.** The multiplicativity of the symbol
across an arbitrary pair of degrees, which
`AlgebraicGeometry.SemistableReduction.MonomialSymbol` asks for as an axiom, is a consequence of
the one-step and degree-zero laws;
`AlgebraicGeometry.SemistableReduction.OneStepSymbol.symbol_mul_of_oneStep` proves it.

For the formal neighbourhood of an exceptional curve of the first kind the degree-zero law is
already proved and the one-step law is the single remaining geometric input; see the module
docstring. -/
def OneStepSymbol.toMonomialSymbol {A : Type u} [CommRing A] {k : Type u} [CommRing k]
    (S : OneStepSymbol A k) : MonomialSymbol A k where
  ideal := S.ideal
  symbol := S.symbol
  ideal_zero := S.ideal_zero
  mul_le := S.mul_le
  symbol_mem := S.symbol_mem
  symbol_add := S.symbol_add
  symbol_eq_zero_iff := S.symbol_eq_zero_iff
  symbol_mul := by
    intro m n a b ha hb
    exact S.symbol_mul_of_oneStep S.exists_symbol_one_eq_X.choose_spec.choose_spec.1
      S.exists_symbol_one_eq_X.choose_spec.choose_spec.2.1
      S.exists_symbol_one_eq_X.choose_spec.choose_spec.2.2.1
      S.exists_symbol_one_eq_X.choose_spec.choose_spec.2.2.2 n m ha hb
  symbol_one := S.symbol_one
  surjective_symbol_zero := S.surjective_symbol_zero
  exists_symbol_one_eq_X := S.exists_symbol_one_eq_X

/-- The ideal filtration of `S.toMonomialSymbol` is that of `S`. -/
@[simp]
theorem OneStepSymbol.toMonomialSymbol_ideal {A : Type u} [CommRing A] {k : Type u} [CommRing k]
    (S : OneStepSymbol A k) : S.toMonomialSymbol.ideal = S.ideal := rfl

/-- The symbol map of `S.toMonomialSymbol` is that of `S`. -/
@[simp]
theorem OneStepSymbol.toMonomialSymbol_symbol {A : Type u} [CommRing A] {k : Type u} [CommRing k]
    (S : OneStepSymbol A k) : S.toMonomialSymbol.symbol = S.symbol := rfl

end AlgebraicGeometry.SemistableReduction

end
