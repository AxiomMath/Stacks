module

public import StacksFrontier.AlgebraicGeometry.Surfaces.FormalNeighborhoodFiltration
public import StacksFrontier.RingTheory.MvPolynomial.BinaryFormBasis

/-!
# The symbol of a function and the monomial structure of the formal neighbourhood

Let `A` be a commutative ring with a filtration `A = I₀ ⊇ I₁ ⊇ ⋯` by ideals.  A *monomial symbol
system* on it, with values in a commutative ring `k`, is a family of maps

`σₙ : Iₙ ⟶ (k[T₀, T₁])ₙ`

— the *symbol*, or leading form, of a function vanishing to order `n` — which is additive, has
kernel exactly `Iₙ₊₁`, is multiplicative in the sense `σ_{m+n}(ab) = σₘ(a) σₙ(b)`, is surjective
onto the constants in degree `0` and hits both coordinates in degree `1`.

This is precisely the structure the Stacks proof of [Stacks, Tag 0C2K] extracts from the formal
neighbourhood of an exceptional curve of the first kind `E ⊆ X`, with `A` the ring of compatible
functions on the infinitesimal thickenings and `Iₙ` the projection kernels: the graded piece
`Iₙ / Iₙ₊₁` is `H⁰(E, ℐⁿ/ℐⁿ⁺¹) = H⁰(𝐏¹_k, 𝒪(n))`, which is the module of binary forms of degree
`n`, and multiplication of functions induces multiplication of forms.

Given such a system, this file produces three of the five geometric inputs that
`AlgebraicGeometry.Scheme.IdealSheafData.formalNeighborhoodMonomialFiltration` asks for: two
elements `x, y ∈ I₁` (`hgen`), the fact that `Iₙ` is spanned by the degree-`n` monomials in them
modulo `Iₙ₊₁` (`hspanPow`), and the linear independence of those monomials over `A / I₁`
(`hindep`).  All three come from one statement about the projective line: the binary forms of
degree `n` are free on the `n + 1` monomials `T₀^{n-j} T₁^j`
(`MvPolynomial.homogeneousBinaryBasis`).

**What is proved here and what is not.**  The construction of a monomial symbol system from
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind` is *not* in this file,
and is the remaining geometric content of 0C2K for these three inputs: it needs the
identification of `Iₙ / Iₙ₊₁` with `H⁰(E, 𝒪_X(-nE)|_E)` from the short exact sequence of
[Stacks, Tag 0C4T], the identification of the latter with `H⁰(𝐏¹_k, 𝒪(n))` compatibly with
multiplication across all `n`, and the surjectivity of `A ⟶ Γ(E₂, 𝒪)` which
`AlgebraicGeometry.Scheme.IdealSheafData.surjective_formalNeighborhoodProjection` supplies from
the vanishing of `H¹(𝐏¹_k, 𝒪(n))`.  Nothing here carries a `@[stacks]` attribute.

## Main definitions

* `AlgebraicGeometry.SemistableReduction.MonomialSymbol` — the symbol system.

## Main results

* `AlgebraicGeometry.SemistableReduction.MonomialSymbol.exists_gen_spanPow_indep` — a monomial
  symbol system produces the generators, the spanning statement and the independence statement.
* `AlgebraicGeometry.Scheme.IdealSheafData.exists_gen_spanPow_indep_of_monomialSymbol` — the same
  for the projection-kernel filtration of a formal neighbourhood, in the exact shape of the
  `hgen`, `hspanPow` and `hindep` arguments of
  `AlgebraicGeometry.Scheme.IdealSheafData.formalNeighborhoodMonomialFiltration`.

## References

* [Stacks Project, Tag 0C2K](https://stacks.math.columbia.edu/tag/0C2K)
* [Stacks Project, Tag 0C4T](https://stacks.math.columbia.edu/tag/0C4T)
-/

@[expose] public noncomputable section

open MvPolynomial

universe u

namespace AlgebraicGeometry.SemistableReduction

/-- A *monomial symbol system* on a commutative ring `A`, with values in a commutative ring `k`:
a filtration `I` by ideals together with symbol maps `σₙ : Iₙ ⟶ (k[T₀, T₁])ₙ` which are additive,
kill exactly `Iₙ₊₁`, multiply as `σ_{m+n}(ab) = σₘ(a) σₙ(b)`, reach every constant in degree `0`
and reach both coordinates in degree `1`.

The symbol is carried as a bare function `ℕ → A → k[T₀, T₁]`; every axiom is guarded by the
hypothesis that its arguments lie in the relevant step of the filtration, so the value of
`symbol n a` for `a ∉ ideal n` is unconstrained.

For the formal neighbourhood of an exceptional curve of the first kind this is the symbol, or
leading form, of a function vanishing to order `n`, with values in
`H⁰(𝐏¹_k, 𝒪(n)) = (k[T₀, T₁])ₙ`; see the module docstring. -/
structure MonomialSymbol (A : Type u) [CommRing A] (k : Type u) [CommRing k] where
  /-- The filtering ideals `Iₙ`. -/
  ideal : ℕ → Ideal A
  /-- The symbol, or leading form, of an element of `Iₙ`. -/
  symbol : ℕ → A → MvPolynomial (Fin 2) k
  /-- The filtration starts at the whole ring. -/
  ideal_zero : ideal 0 = ⊤
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
  /-- The symbol is multiplicative across degrees. -/
  symbol_mul : ∀ (m n : ℕ) {a b : A}, a ∈ ideal m → b ∈ ideal n →
    symbol (m + n) (a * b) = symbol m a * symbol n b
  /-- The symbol of `1` in degree `0` is `1`. -/
  symbol_one : symbol 0 1 = 1
  /-- Every constant is the degree-zero symbol of some element: `A ⟶ A / I₁ = k` is onto. -/
  surjective_symbol_zero : ∀ c : k, ∃ a : A, symbol 0 a = MvPolynomial.C c
  /-- Both coordinates are degree-one symbols: `I₁ ⟶ H⁰(𝐏¹_k, 𝒪(1))` is onto. -/
  exists_symbol_one_eq_X : ∃ x y : A, x ∈ ideal 1 ∧ y ∈ ideal 1 ∧
    symbol 1 x = MvPolynomial.X 0 ∧ symbol 1 y = MvPolynomial.X 1

namespace MonomialSymbol

variable {A : Type u} [CommRing A] {k : Type u} [CommRing k] (S : MonomialSymbol A k)

/-! ### Elementary consequences of the axioms -/

/-- Every element of `A` lies in the zeroth step of the filtration. -/
theorem mem_ideal_zero (a : A) : a ∈ S.ideal 0 := by
  rw [S.ideal_zero]; trivial

/-- The symbol of `0` vanishes. -/
theorem symbol_zero (n : ℕ) : S.symbol n 0 = 0 := by
  have h := S.symbol_add n (zero_mem (S.ideal n)) (zero_mem (S.ideal n))
  rw [add_zero] at h
  linear_combination -h

/-- The symbol is additive on differences inside `Iₙ`. -/
theorem symbol_sub (n : ℕ) {a b : A} (ha : a ∈ S.ideal n) (hb : b ∈ S.ideal n) :
    S.symbol n (a - b) = S.symbol n a - S.symbol n b := by
  have h := S.symbol_add n (sub_mem ha hb) hb
  rw [sub_add_cancel] at h
  rw [h]
  ring

/-- The symbol is additive on finite sums inside `Iₙ`. -/
theorem symbol_sum_range (n : ℕ) : ∀ (N : ℕ) (f : ℕ → A),
    (∀ j ∈ Finset.range N, f j ∈ S.ideal n) →
    S.symbol n (∑ j ∈ Finset.range N, f j) = ∑ j ∈ Finset.range N, S.symbol n (f j) := by
  intro N
  induction N with
  | zero => intro f _; simpa using S.symbol_zero n
  | succ N ih =>
    intro f hf
    have hsub : ∀ j ∈ Finset.range N, f j ∈ S.ideal n := fun j hj =>
      hf j (Finset.mem_range.2 ((Finset.mem_range.1 hj).trans (Nat.lt_succ_self N)))
    rw [Finset.sum_range_succ, Finset.sum_range_succ,
      S.symbol_add n (Submodule.sum_mem _ hsub) (hf N (Finset.mem_range.2 (Nat.lt_succ_self N))),
      ih f hsub]

/-- An element lies in `I₁` exactly when its degree-zero symbol vanishes: `I₁` is the kernel of
`A ⟶ A / I₁ = k`. -/
theorem mem_ideal_one_iff (a : A) : a ∈ S.ideal 1 ↔ S.symbol 0 a = 0 := by
  have h := S.symbol_eq_zero_iff 0 (S.mem_ideal_zero a)
  rw [zero_add] at h
  exact h.symm

/-- The degree-zero symbol of any element is a constant. -/
theorem exists_symbol_zero_eq_C (a : A) : ∃ c : k, S.symbol 0 a = MvPolynomial.C c := by
  obtain ⟨c, hc⟩ :=
    exists_eq_sum_binaryMonomial 0 (S.symbol 0 a) (S.symbol_mem 0 (S.mem_ideal_zero a))
  refine ⟨c 0, ?_⟩
  rw [hc]
  simp [binaryMonomial, MvPolynomial.smul_eq_C_mul]

/-- The powers of `I₁` sit inside the filtration. -/
theorem ideal_one_pow_le : ∀ n : ℕ, S.ideal 1 ^ n ≤ S.ideal n := by
  intro n
  induction n with
  | zero => simp [S.ideal_zero]
  | succ n ih =>
    rw [pow_succ]
    exact (Ideal.mul_mono ih le_rfl).trans (S.mul_le n 1)

/-- A power of an element of `I₁` lies in the corresponding step of the filtration, and its
symbol is the corresponding power. -/
theorem pow_mem_and_symbol_pow {x : A} (hx : x ∈ S.ideal 1) :
    ∀ p : ℕ, x ^ p ∈ S.ideal p ∧ S.symbol p (x ^ p) = (S.symbol 1 x) ^ p := by
  intro p
  induction p with
  | zero => exact ⟨by simpa using S.mem_ideal_zero 1, by simpa using S.symbol_one⟩
  | succ p ih =>
    refine ⟨?_, ?_⟩
    · rw [pow_succ]
      exact S.mul_le p 1 (Ideal.mul_mem_mul ih.1 hx)
    · rw [pow_succ, S.symbol_mul p 1 ih.1 hx, ih.2, ← pow_succ]

/-! ### The symbols of the monomials in two chosen generators -/

variable {x y : A} (hx : x ∈ S.ideal 1) (hy : y ∈ S.ideal 1)

include hx hy in
/-- A degree-`n` monomial in two elements of `I₁` lies in `Iₙ`. -/
theorem genMonomial_mem_ideal {n j : ℕ} (hj : j ≤ n) : genMonomial x y n j ∈ S.ideal n := by
  have h := S.mul_le (n - j) j
    (Ideal.mul_mem_mul (S.pow_mem_and_symbol_pow hx (n - j)).1 (S.pow_mem_and_symbol_pow hy j).1)
  rwa [Nat.sub_add_cancel hj] at h

include hx hy in
/-- **The symbol of a degree-`n` monomial is the corresponding binary monomial.** -/
theorem symbol_genMonomial (hsx : S.symbol 1 x = MvPolynomial.X 0)
    (hsy : S.symbol 1 y = MvPolynomial.X 1) {n j : ℕ} (hj : j ≤ n) :
    S.symbol n (genMonomial x y n j) = binaryMonomial k n j := by
  have h := S.symbol_mul (n - j) j (S.pow_mem_and_symbol_pow hx (n - j)).1
    (S.pow_mem_and_symbol_pow hy j).1
  rw [Nat.sub_add_cancel hj, (S.pow_mem_and_symbol_pow hx (n - j)).2,
    (S.pow_mem_and_symbol_pow hy j).2, hsx, hsy] at h
  exact h

include hx hy in
/-- The symbol of a coefficient times a degree-`n` monomial. -/
theorem symbol_mul_genMonomial (hsx : S.symbol 1 x = MvPolynomial.X 0)
    (hsy : S.symbol 1 y = MvPolynomial.X 1) {n j : ℕ} (hj : j ≤ n) (c : A) :
    S.symbol n (c * genMonomial x y n j) = S.symbol 0 c * binaryMonomial k n j := by
  have h := S.symbol_mul 0 n (S.mem_ideal_zero c) (S.genMonomial_mem_ideal hx hy hj)
  rw [zero_add, S.symbol_genMonomial hx hy hsx hsy hj] at h
  exact h

/-! ### The three geometric inputs of Stacks 0C2K -/

/-- A combination of the degree-`d` monomials lies in `I_d`, with symbol the combination of binary
monomials whose coefficients are the degree-zero symbols of the coefficients. -/
private theorem sum_mul_genMonomial_mem_and_symbol (hx : x ∈ S.ideal 1) (hy : y ∈ S.ideal 1)
    (hsx : S.symbol 1 x = MvPolynomial.X 0)
    (hsy : S.symbol 1 y = MvPolynomial.X 1) (d : ℕ) (c : ℕ → A) (lam : ℕ → k)
    (hlam : ∀ i, S.symbol 0 (c i) = MvPolynomial.C (lam i)) :
    (∑ j ∈ Finset.range (d + 1), c j * genMonomial x y d j) ∈ S.ideal d ∧
      S.symbol d (∑ j ∈ Finset.range (d + 1), c j * genMonomial x y d j) =
        ∑ j ∈ Finset.range (d + 1), lam j • binaryMonomial k d j := by
  have hterm : ∀ j ∈ Finset.range (d + 1), c j * genMonomial x y d j ∈ S.ideal d := fun j hj =>
    Ideal.mul_mem_left _ _
      (S.genMonomial_mem_ideal hx hy (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)))
  refine ⟨Submodule.sum_mem _ hterm, ?_⟩
  rw [S.symbol_sum_range d (d + 1) _ hterm]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [S.symbol_mul_genMonomial hx hy hsx hsy (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) (c j),
    hlam j, MvPolynomial.smul_eq_C_mul]

include hx hy in
/-- **`Iₙ` is spanned by the degree-`n` monomials modulo `Iₙ₊₁`.**  This is the `hspanPow`
hypothesis of
`AlgebraicGeometry.Scheme.IdealSheafData.formalNeighborhoodMonomialFiltration`: a function
vanishing to order `n` agrees, modulo order `n + 1`, with a degree-`n` form in the two
generators, because its symbol is a binary form of degree `n` and those are spanned by the
`n + 1` monomials. -/
theorem ideal_le_span_pow_sup (hsx : S.symbol 1 x = MvPolynomial.X 0)
    (hsy : S.symbol 1 y = MvPolynomial.X 1) (n : ℕ) :
    S.ideal n ≤ Ideal.span {x, y} ^ n ⊔ S.ideal (n + 1) := by
  intro a ha
  obtain ⟨lam, hlam⟩ :=
    exists_eq_sum_binaryMonomial n (S.symbol n a) (S.symbol_mem n ha)
  choose c hc using fun j : ℕ => S.surjective_symbol_zero (lam j)
  obtain ⟨hwmem, hsymw⟩ := S.sum_mul_genMonomial_mem_and_symbol hx hy hsx hsy n c lam hc
  set w : A := ∑ j ∈ Finset.range (n + 1), c j * genMonomial x y n j with hw
  rw [← hlam] at hsymw
  have hrem : a - w ∈ S.ideal (n + 1) :=
    (S.symbol_eq_zero_iff n (sub_mem ha hwmem)).1
      (by rw [S.symbol_sub n ha hwmem, hsymw, sub_self])
  exact Submodule.mem_sup.2 ⟨w, sum_genMonomial_mem_span_pow x y n c, a - w, hrem, by ring⟩

include hx hy in
/-- **The degree-`d` monomials in the two generators are linearly independent over `A / I₁`.**
This is the `hindep` hypothesis of
`AlgebraicGeometry.Scheme.IdealSheafData.formalNeighborhoodMonomialFiltration`: a combination of
the degree-`d` monomials that vanishes to order `d + 1` has symbol zero, hence has all its
coefficients in `I₁`, because the `d + 1` binary monomials of degree `d` are independent. -/
theorem coeff_mem_ideal_one (hsx : S.symbol 1 x = MvPolynomial.X 0)
    (hsy : S.symbol 1 y = MvPolynomial.X 1) (d : ℕ) (c : ℕ → A)
    (h : (∑ j ∈ Finset.range (d + 1), c j * genMonomial x y d j) ∈ S.ideal (d + 1))
    (j : ℕ) (hj : j ≤ d) : c j ∈ S.ideal 1 := by
  choose lam hlam using fun i : ℕ => S.exists_symbol_zero_eq_C (c i)
  obtain ⟨hmem, hsym⟩ := S.sum_mul_genMonomial_mem_and_symbol hx hy hsx hsy d c lam hlam
  have hzero : ∑ i ∈ Finset.range (d + 1), lam i • binaryMonomial k d i = 0 := by
    rw [← hsym, (S.symbol_eq_zero_iff d hmem).2 h]
  have hlamj : lam j = 0 := eq_zero_of_sum_binaryMonomial_eq_zero d lam hzero hj
  rw [S.mem_ideal_one_iff, hlam j, hlamj, map_zero]

/-! ### The two chosen generators -/

/-- The first of the two generators a monomial symbol system provides: an element of `I₁` whose
symbol is the first coordinate of `𝐏¹`. -/
def gen₁ : A := S.exists_symbol_one_eq_X.choose

/-- The second of the two generators a monomial symbol system provides: an element of `I₁` whose
symbol is the second coordinate of `𝐏¹`. -/
def gen₂ : A := S.exists_symbol_one_eq_X.choose_spec.choose

/-- The generator `gen₁` lies in `I₁`. -/
theorem gen₁_mem : S.gen₁ ∈ S.ideal 1 :=
  S.exists_symbol_one_eq_X.choose_spec.choose_spec.1

/-- The generator `gen₂` lies in `I₁`. -/
theorem gen₂_mem : S.gen₂ ∈ S.ideal 1 :=
  S.exists_symbol_one_eq_X.choose_spec.choose_spec.2.1

/-- The degree-one symbol of `gen₁` is the first coordinate `X 0`. -/
@[simp]
theorem symbol_gen₁ : S.symbol 1 S.gen₁ = MvPolynomial.X 0 :=
  S.exists_symbol_one_eq_X.choose_spec.choose_spec.2.2.1

/-- The degree-one symbol of `gen₂` is the second coordinate `X 1`. -/
@[simp]
theorem symbol_gen₂ : S.symbol 1 S.gen₂ = MvPolynomial.X 1 :=
  S.exists_symbol_one_eq_X.choose_spec.choose_spec.2.2.2

/-- **Both generators lie in `I₁`.**  This is the `hgen` hypothesis of
`AlgebraicGeometry.Scheme.IdealSheafData.formalNeighborhoodMonomialFiltration`. -/
theorem span_gen_le_ideal_one : Ideal.span {S.gen₁, S.gen₂} ≤ S.ideal 1 := by
  rw [Ideal.span_le]
  rintro a (rfl | rfl)
  · exact S.gen₁_mem
  · exact S.gen₂_mem

/-- **`Iₙ` is spanned by the degree-`n` monomials in the two generators modulo `Iₙ₊₁`.**  This is
the `hspanPow` hypothesis of
`AlgebraicGeometry.Scheme.IdealSheafData.formalNeighborhoodMonomialFiltration`. -/
theorem ideal_le_span_gen_pow_sup (n : ℕ) :
    S.ideal n ≤ Ideal.span {S.gen₁, S.gen₂} ^ n ⊔ S.ideal (n + 1) :=
  S.ideal_le_span_pow_sup S.gen₁_mem S.gen₂_mem S.symbol_gen₁ S.symbol_gen₂ n

/-- **The degree-`d` monomials in the two generators are independent over `A / I₁`.**  This is
the `hindep` hypothesis of
`AlgebraicGeometry.Scheme.IdealSheafData.formalNeighborhoodMonomialFiltration`. -/
theorem gen_monomials_indep (d : ℕ) (c : ℕ → A)
    (h : (∑ j ∈ Finset.range (d + 1), c j * genMonomial S.gen₁ S.gen₂ d j) ∈ S.ideal (d + 1))
    (j : ℕ) (hj : j ≤ d) : c j ∈ S.ideal 1 :=
  S.coeff_mem_ideal_one S.gen₁_mem S.gen₂_mem S.symbol_gen₁ S.symbol_gen₂ d c h j hj

/-- **A monomial symbol system produces the three geometric inputs of Stacks 0C2K**: two
generators lying in `I₁`, the spanning of `Iₙ` by the degree-`n` monomials modulo `Iₙ₊₁`, and the
linear independence of those monomials over `A / I₁`.  These are the `hgen`, `hspanPow` and
`hindep` arguments of
`AlgebraicGeometry.Scheme.IdealSheafData.formalNeighborhoodMonomialFiltration`. -/
theorem exists_gen_spanPow_indep :
    ∃ x y : A, Ideal.span {x, y} ≤ S.ideal 1 ∧
      (∀ n, S.ideal n ≤ Ideal.span {x, y} ^ n ⊔ S.ideal (n + 1)) ∧
      ∀ (d : ℕ) (c : ℕ → A),
        (∑ j ∈ Finset.range (d + 1), c j * genMonomial x y d j) ∈ S.ideal (d + 1) →
        ∀ j ≤ d, c j ∈ S.ideal 1 :=
  ⟨S.gen₁, S.gen₂, S.span_gen_le_ideal_one, S.ideal_le_span_gen_pow_sup,
    S.gen_monomials_indep⟩

end MonomialSymbol

end AlgebraicGeometry.SemistableReduction

namespace AlgebraicGeometry.Scheme.IdealSheafData

open AlgebraicGeometry.SemistableReduction

variable {X : Scheme.{u}} (D : X.IdealSheafData)

section Symbol

variable {k : Type u} [CommRing k] (S : MonomialSymbol (formalNeighborhoodRing D) k)
  (hS : S.ideal = formalNeighborhoodFiltration D)

include hS

/-- The `hgen` input, for the two generators a monomial symbol system chooses. -/
theorem span_gen_le_formalNeighborhoodFiltration_one :
    Ideal.span {S.gen₁, S.gen₂} ≤ formalNeighborhoodFiltration D 1 := by
  rw [← hS]; exact S.span_gen_le_ideal_one

/-- The `hspanPow` input, for the two generators a monomial symbol system chooses. -/
theorem formalNeighborhoodFiltration_le_span_gen_pow_sup (n : ℕ) :
    formalNeighborhoodFiltration D n ≤
      Ideal.span {S.gen₁, S.gen₂} ^ n ⊔ formalNeighborhoodFiltration D (n + 1) := by
  rw [← hS]; exact S.ideal_le_span_gen_pow_sup n

/-- The `hindep` input, for the two generators a monomial symbol system chooses. -/
theorem gen_monomials_indep_formalNeighborhoodFiltration (d : ℕ)
    (c : ℕ → formalNeighborhoodRing D)
    (h : (∑ j ∈ Finset.range (d + 1), c j * genMonomial S.gen₁ S.gen₂ d j) ∈
      formalNeighborhoodFiltration D (d + 1)) (j : ℕ) (hj : j ≤ d) :
    c j ∈ formalNeighborhoodFiltration D 1 := by
  rw [← hS] at h ⊢
  exact S.gen_monomials_indep d c h j hj

end Symbol

/-- **The three geometric inputs of Stacks 0C2K for a formal neighbourhood, from a monomial
symbol system on it.**  Given a symbol system whose filtration is the projection-kernel
filtration, this is exactly the `hgen`, `hspanPow` and `hindep` triple that
`AlgebraicGeometry.Scheme.IdealSheafData.formalNeighborhoodMonomialFiltration` consumes.

What is still missing for Stacks 0C2K is the *construction* of the symbol system from
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`; see the module
docstring. -/
theorem exists_gen_spanPow_indep_of_monomialSymbol (k : Type u) [CommRing k]
    (S : MonomialSymbol (formalNeighborhoodRing D) k)
    (hS : S.ideal = formalNeighborhoodFiltration D) :
    ∃ x y : formalNeighborhoodRing D,
      Ideal.span {x, y} ≤ formalNeighborhoodFiltration D 1 ∧
      (∀ n, formalNeighborhoodFiltration D n ≤
        Ideal.span {x, y} ^ n ⊔ formalNeighborhoodFiltration D (n + 1)) ∧
      ∀ (d : ℕ) (c : ℕ → formalNeighborhoodRing D),
        (∑ j ∈ Finset.range (d + 1), c j * genMonomial x y d j) ∈
          formalNeighborhoodFiltration D (d + 1) →
        ∀ j ≤ d, c j ∈ formalNeighborhoodFiltration D 1 := by
  rw [← hS]
  exact S.exists_gen_spanPow_indep

end AlgebraicGeometry.Scheme.IdealSheafData
