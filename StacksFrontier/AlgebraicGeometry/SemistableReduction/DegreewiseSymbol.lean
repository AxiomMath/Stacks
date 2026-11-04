module

public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ExceptionalFiltration
public import StacksFrontier.RingTheory.MvPolynomial.BinaryFormBasis

/-!
# Degreewise symbols and the monomial structure of a filtration

Let `A` be a commutative ring with a multiplicative filtration `A = I₀ ⊇ I₁ ⊇ ⋯` by ideals and
let `k` be a field.  A *degreewise symbol system* on `A` with values in `k` is a residue
homomorphism `A ⟶ k` with kernel `I₁` together with maps

`σₙ : Iₙ ⟶ (k[T₀, T₁])ₙ`

which are additive, semilinear over the residue map, have kernel exactly `Iₙ₊₁`, and are
**onto** the binary forms of degree `n`.  Equivalently: a presentation of each graded piece
`Iₙ / Iₙ₊₁` as the space of binary forms of degree `n`, one degree at a time.

The point of the structure is what it does **not** ask: nothing relates `σₘ` and `σₙ` to
`σₘ₊ₙ`.  `AlgebraicGeometry.SemistableReduction.MonomialSymbol` asks for exactly that
compatibility, `σ_{m+n}(ab) = σₘ(a) σₙ(b)`, and it is the one hypothesis of the Stacks proof of
[Stacks, Tag 0C2K] that a non-canonical identification of the graded pieces cannot supply.  What
replaces it here is one statement about the filtration alone,

`Iₙ₊₁ ⊆ I₁ · Iₙ + Iₙ₊₂`,

that the associated graded ring is generated in degree one.  That statement is invariant under
changing each identification `Iₙ / Iₙ₊₁ ≅ (k[T₀, T₁])ₙ` by an arbitrary automorphism, so it can
be read off a family of isomorphisms that is not canonical.

## The argument

Pick `x, y ∈ I₁` whose symbols are the two coordinates; surjectivity of `σ₁` provides them, and
nothing is claimed about the symbols of their higher powers.  Because the degree-one forms are
spanned by the two coordinates, `I₁ ⊆ (x, y) + I₂`.  Feeding that and degree-one generation into
each other gives `Iₙ ⊆ (x, y)ⁿ + Iₙ₊₁` for every `n`, by induction on `n`: a product `ab` with
`a ∈ I₁` and `b ∈ Iₙ` splits into four terms, of which one lies in `(x, y)ⁿ⁺¹` and the other
three in `Iₙ₊₂`.

With that in hand the `n + 1` symbols of the degree-`n` monomials in `x` and `y` span the
degree-`n` forms, a space of dimension `n + 1`
(`MvPolynomial.homogeneousBinaryBasis`), so they are a basis
(`linearIndependent_of_top_le_span_of_card_eq_finrank`) — and that is the independence of the
monomials over `A / I₁`.  Multiplicativity of the symbol would have identified those `n + 1`
symbols with the `n + 1` monomial forms outright; the dimension count reaches the same
conclusion without knowing which forms they are.

## Main definitions

* `AlgebraicGeometry.SemistableReduction.DegreewiseSymbol` — the symbol system.

## Main results

* `AlgebraicGeometry.SemistableReduction.DegreewiseSymbol.ideal_le_span_gen_pow_sup` — `Iₙ` is
  spanned by the degree-`n` monomials in the two generators modulo `Iₙ₊₁`.
* `AlgebraicGeometry.SemistableReduction.DegreewiseSymbol.coeff_mem_ideal_one` — those monomials
  are linearly independent over `A / I₁`.
* `AlgebraicGeometry.SemistableReduction.DegreewiseSymbol.exists_gen_spanPow_indep` — the two
  together, with the generators, in the shape the monomial filtration of 0C2K consumes.

## References

* [Stacks Project, Tag 0C2K](https://stacks.math.columbia.edu/tag/0C2K)
-/

@[expose] public noncomputable section

open MvPolynomial

universe u

namespace AlgebraicGeometry.SemistableReduction

/-- A *degreewise symbol system* on a commutative ring `A` with values in a field `k`: a
filtration `I` by ideals, a residue homomorphism `A ⟶ k` with kernel `I₁`, and symbol maps
`σₙ : Iₙ ⟶ (k[T₀, T₁])ₙ` which are additive, semilinear over the residue map, kill exactly
`Iₙ₊₁`, and reach every binary form of degree `n`.

The symbol is carried as a bare function `ℕ → A → k[T₀, T₁]`; every condition is guarded by the
hypothesis that its argument lies in the relevant step of the filtration, so the value of
`symbol n a` for `a ∉ ideal n` is unconstrained.

Nothing relates the symbols in different degrees to one another.  Such a system is therefore
exactly a degreewise presentation of `Iₙ / Iₙ₊₁` as the binary forms of degree `n`, with no
compatibility with multiplication; see the module docstring. -/
structure DegreewiseSymbol (A : Type u) [CommRing A] (k : Type u) [Field k] where
  /-- The filtering ideals `Iₙ`. -/
  ideal : ℕ → Ideal A
  /-- The residue homomorphism `A ⟶ A / I₁ = k`. -/
  scalar : A →+* k
  /-- The symbol, or leading form, of an element of `Iₙ`. -/
  symbol : ℕ → A → MvPolynomial (Fin 2) k
  /-- The filtration starts at the whole ring. -/
  ideal_zero : ideal 0 = ⊤
  /-- The filtration decreases. -/
  ideal_succ_le : ∀ n, ideal (n + 1) ≤ ideal n
  /-- The filtration is multiplicative. -/
  mul_le : ∀ m n, ideal m * ideal n ≤ ideal (m + n)
  /-- The residue homomorphism has kernel the first step of the filtration. -/
  ker_scalar : RingHom.ker scalar = ideal 1
  /-- The residue homomorphism is onto. -/
  surjective_scalar : Function.Surjective scalar
  /-- The symbol of an element of `Iₙ` is a binary form of degree `n`. -/
  symbol_mem : ∀ (n : ℕ) {a : A}, a ∈ ideal n →
    symbol n a ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k n
  /-- The symbol is additive on `Iₙ`. -/
  symbol_add : ∀ (n : ℕ) {a b : A}, a ∈ ideal n → b ∈ ideal n →
    symbol n (a + b) = symbol n a + symbol n b
  /-- The symbol is semilinear over the residue homomorphism. -/
  symbol_smul : ∀ (n : ℕ) (c : A) {a : A}, a ∈ ideal n →
    symbol n (c * a) = scalar c • symbol n a
  /-- The symbol of an element of `Iₙ` vanishes exactly when the element lies in `Iₙ₊₁`. -/
  symbol_eq_zero_iff : ∀ (n : ℕ) {a : A}, a ∈ ideal n → (symbol n a = 0 ↔ a ∈ ideal (n + 1))
  /-- Every binary form of degree `n` is the symbol of an element of `Iₙ`. -/
  surjective_symbol : ∀ (n : ℕ) (v : MvPolynomial (Fin 2) k),
    v ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k n → ∃ a ∈ ideal n, symbol n a = v

namespace DegreewiseSymbol

variable {A : Type u} [CommRing A] {k : Type u} [Field k] (S : DegreewiseSymbol A k)

/-! ### Elementary consequences of the axioms -/

/-- Every element of `A` lies in the zeroth step of the filtration. -/
theorem mem_ideal_zero (a : A) : a ∈ S.ideal 0 := by
  rw [S.ideal_zero]; trivial

/-- The filtration is antitone. -/
theorem antitone_ideal : Antitone S.ideal :=
  antitone_nat_of_succ_le S.ideal_succ_le

/-- The symbol of `0` vanishes. -/
theorem symbol_zero (n : ℕ) : S.symbol n 0 = 0 := by
  have h := S.symbol_add n (zero_mem (S.ideal n)) (zero_mem (S.ideal n))
  rw [add_zero] at h
  linear_combination -h

/-- An element whose residue vanishes lies in the first step of the filtration. -/
theorem mem_ideal_one_of_scalar_eq_zero {a : A} (ha : S.scalar a = 0) : a ∈ S.ideal 1 := by
  rw [← S.ker_scalar]
  exact ha

/-- The powers of `I₁` sit inside the filtration. -/
theorem ideal_one_pow_le (n : ℕ) : S.ideal 1 ^ n ≤ S.ideal n := by
  induction n with
  | zero => simp [S.ideal_zero]
  | succ n ih =>
    rw [pow_succ]
    exact (Ideal.mul_mono ih le_rfl).trans (S.mul_le n 1)

/-! ### The two generators -/

/-- The first of the two generators: an element of `I₁` whose symbol is the first coordinate. -/
def gen₁ : A :=
  (S.surjective_symbol 1 (binaryMonomial k 1 0) (binaryMonomial_mem (Nat.zero_le 1))).choose

/-- The second of the two generators: an element of `I₁` whose symbol is the second
coordinate. -/
def gen₂ : A :=
  (S.surjective_symbol 1 (binaryMonomial k 1 1) (binaryMonomial_mem (le_refl 1))).choose

/-- The first generator lies in the first step of the filtration. -/
theorem gen₁_mem : S.gen₁ ∈ S.ideal 1 :=
  (S.surjective_symbol 1 (binaryMonomial k 1 0)
    (binaryMonomial_mem (Nat.zero_le 1))).choose_spec.1

/-- The second generator lies in the first step of the filtration. -/
theorem gen₂_mem : S.gen₂ ∈ S.ideal 1 :=
  (S.surjective_symbol 1 (binaryMonomial k 1 1)
    (binaryMonomial_mem (le_refl 1))).choose_spec.1

/-- The symbol of the first generator is the first coordinate `T₀`. -/
@[simp]
theorem symbol_gen₁ : S.symbol 1 S.gen₁ = binaryMonomial k 1 0 :=
  (S.surjective_symbol 1 (binaryMonomial k 1 0)
    (binaryMonomial_mem (Nat.zero_le 1))).choose_spec.2

/-- The symbol of the second generator is the second coordinate `T₁`. -/
@[simp]
theorem symbol_gen₂ : S.symbol 1 S.gen₂ = binaryMonomial k 1 1 :=
  (S.surjective_symbol 1 (binaryMonomial k 1 1)
    (binaryMonomial_mem (le_refl 1))).choose_spec.2

/-- The first generator lies in the ideal generated by the two generators. -/
theorem gen₁_mem_span : S.gen₁ ∈ Ideal.span ({S.gen₁, S.gen₂} : Set A) :=
  Ideal.subset_span (by simp)

/-- The second generator lies in the ideal generated by the two generators. -/
theorem gen₂_mem_span : S.gen₂ ∈ Ideal.span ({S.gen₁, S.gen₂} : Set A) :=
  Ideal.subset_span (by simp)

/-- The ideal generated by the two generators lies in `I₁`. -/
private theorem span_gen_le_ideal_one : Ideal.span ({S.gen₁, S.gen₂} : Set A) ≤ S.ideal 1 := by
  rw [Ideal.span_le]
  rintro a (rfl | rfl)
  · exact S.gen₁_mem
  · exact S.gen₂_mem

/-- **The powers of the ideal generated by the two generators sit inside the filtration.** For
`n = 1` this says that both generators lie in `I₁`. -/
theorem span_gen_pow_le (n : ℕ) : Ideal.span ({S.gen₁, S.gen₂} : Set A) ^ n ≤ S.ideal n :=
  (Ideal.pow_right_mono S.span_gen_le_ideal_one n).trans (S.ideal_one_pow_le n)

/-- A degree-`n` monomial in the two generators lies in `Iₙ`. -/
theorem genMonomial_mem_ideal {n j : ℕ} (hj : j ≤ n) :
    genMonomial S.gen₁ S.gen₂ n j ∈ S.ideal n :=
  S.span_gen_pow_le n (genMonomial_mem_span_pow S.gen₁ S.gen₂ hj)

/-! ### The first step of the filtration -/

/-- **`I₁` is generated by the two chosen elements modulo `I₂`.**  The degree-one binary forms
are spanned by the two coordinates, which are the symbols of the two generators. -/
theorem ideal_one_le_span_gen_sup :
    S.ideal 1 ≤ Ideal.span ({S.gen₁, S.gen₂} : Set A) ⊔ S.ideal 2 := by
  intro a ha
  obtain ⟨lam, hlam⟩ := exists_eq_sum_binaryMonomial 1 (S.symbol 1 a) (S.symbol_mem 1 ha)
  choose c hc using fun j : ℕ => S.surjective_scalar (lam j)
  have hx : c 0 * S.gen₁ ∈ S.ideal 1 := Ideal.mul_mem_left _ _ S.gen₁_mem
  have hy : c 1 * S.gen₂ ∈ S.ideal 1 := Ideal.mul_mem_left _ _ S.gen₂_mem
  set w : A := c 0 * S.gen₁ + c 1 * S.gen₂ with hw
  have hwmem : w ∈ S.ideal 1 := add_mem hx hy
  have hsym : S.symbol 1 w = S.symbol 1 a := by
    rw [hw, S.symbol_add 1 hx hy, S.symbol_smul 1 (c 0) S.gen₁_mem,
      S.symbol_smul 1 (c 1) S.gen₂_mem, S.symbol_gen₁, S.symbol_gen₂, hc 0, hc 1, hlam,
      Finset.sum_range_succ, Finset.sum_range_one]
  have hrem : a - w ∈ S.ideal 2 := by
    have h : a - w ∈ S.ideal (1 + 1) :=
      (S.symbol_eq_zero_iff 1 (sub_mem ha hwmem)).1 (by
        have h := S.symbol_add 1 (sub_mem ha hwmem) hwmem
        rw [sub_add_cancel] at h
        linear_combination -h - hsym)
    rwa [show 1 + 1 = 2 from rfl] at h
  refine Submodule.mem_sup.2 ⟨w, ?_, a - w, hrem, by ring⟩
  exact add_mem (Ideal.mul_mem_left _ _ S.gen₁_mem_span)
    (Ideal.mul_mem_left _ _ S.gen₂_mem_span)

/-! ### The spanning of each step by the monomials -/

/-- **`Iₙ` is spanned by the degree-`n` monomials in the two generators modulo `Iₙ₊₁`**, as soon
as the associated graded ring is generated in degree one.

This is the `hspanPow` hypothesis of
`AlgebraicGeometry.Scheme.IdealSheafData.formalNeighborhoodMonomialFiltration`.  The induction
splits a product `a b` with `a ∈ I₁` and `b ∈ Iₙ` along `I₁ ⊆ (x, y) + I₂` and
`Iₙ ⊆ (x, y)ⁿ + Iₙ₊₁`: of the four terms one lies in `(x, y)ⁿ⁺¹`, and the other three lie in
`Iₙ₊₂` because `(x, y)ⁿ ⊆ Iₙ` and the filtration is multiplicative and decreasing. -/
theorem ideal_le_span_gen_pow_sup
    (hgen : ∀ n, S.ideal (n + 1) ≤ S.ideal 1 * S.ideal n ⊔ S.ideal (n + 2)) (n : ℕ) :
    S.ideal n ≤ Ideal.span ({S.gen₁, S.gen₂} : Set A) ^ n ⊔ S.ideal (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    refine (hgen n).trans (sup_le ?_ le_sup_right)
    refine Ideal.mul_le.2 fun a ha b hb => ?_
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := Submodule.mem_sup.1 (S.ideal_one_le_span_gen_sup ha)
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := Submodule.mem_sup.1 (ih hb)
    have h₁ : a₁ * b₁ ∈ Ideal.span ({S.gen₁, S.gen₂} : Set A) ^ (n + 1) := by
      rw [pow_succ, mul_comm a₁ b₁]
      exact Ideal.mul_mem_mul hb₁ ha₁
    have key : ∀ i j, n + 2 ≤ i + j → ∀ a ∈ S.ideal i, ∀ b ∈ S.ideal j,
        a * b ∈ S.ideal (n + 2) := fun i j hij a ha b hb =>
      S.antitone_ideal hij (S.mul_le i j (Ideal.mul_mem_mul ha hb))
    have h₂ : a₁ * b₂ ∈ S.ideal (n + 2) :=
      key 1 (n + 1) (by omega) _ (S.span_gen_le_ideal_one ha₁) _ hb₂
    have h₃ : a₂ * b₁ ∈ S.ideal (n + 2) :=
      key 2 n (by omega) _ ha₂ _ (S.span_gen_pow_le n hb₁)
    have h₄ : a₂ * b₂ ∈ S.ideal (n + 2) := key 2 (n + 1) (by omega) _ ha₂ _ hb₂
    have hexp : (a₁ + a₂) * (b₁ + b₂) = a₁ * b₁ + (a₁ * b₂ + (a₂ * b₁ + a₂ * b₂)) := by ring
    rw [hexp]
    exact add_mem (Submodule.mem_sup_left h₁)
      (add_mem (Submodule.mem_sup_right h₂)
        (add_mem (Submodule.mem_sup_right h₃) (Submodule.mem_sup_right h₄)))

/-! ### The monomial basis of each graded piece -/

/-- The symbols of the degree-`n` monomials in the two generators, as a family of binary forms
of degree `n`. -/
def symbolFamily (n : ℕ) (j : Fin (n + 1)) : homogeneousSubmodule (Fin 2) k n :=
  ⟨S.symbol n (genMonomial S.gen₁ S.gen₂ n j),
    S.symbol_mem n (S.genMonomial_mem_ideal (Nat.lt_succ_iff.1 j.2))⟩

/-- The binary form underlying `symbolFamily n j` is the symbol of the `j`-th degree-`n`
monomial in the two generators. -/
@[simp]
theorem coe_symbolFamily (n : ℕ) (j : Fin (n + 1)) :
    (S.symbolFamily n j : MvPolynomial (Fin 2) k) =
      S.symbol n (genMonomial S.gen₁ S.gen₂ n j) := rfl

/-- A multiple of a degree-`n` monomial in the two generators lies in `Iₙ`. -/
private theorem mul_genMonomial_mem_ideal (c : A) {n j : ℕ} (hj : j ∈ Finset.range (n + 1)) :
    c * genMonomial S.gen₁ S.gen₂ n j ∈ S.ideal n :=
  Ideal.mul_mem_left _ _ (S.genMonomial_mem_ideal (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)))

/-- The symbol of a combination of the degree-`n` monomials is the corresponding combination of
their symbols, with the residues of the coefficients as scalars. -/
theorem symbol_sum_mul_genMonomial (n : ℕ) (c : ℕ → A) :
    S.symbol n (∑ j ∈ Finset.range (n + 1), c j * genMonomial S.gen₁ S.gen₂ n j) =
      ∑ j ∈ Finset.range (n + 1),
        S.scalar (c j) • S.symbol n (genMonomial S.gen₁ S.gen₂ n j) := by
  have hsum : ∀ (N : ℕ) (f : ℕ → A), (∀ j ∈ Finset.range N, f j ∈ S.ideal n) →
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
  rw [hsum (n + 1) _ fun j hj => S.mul_genMonomial_mem_ideal (c j) hj]
  exact Finset.sum_congr rfl fun j hj =>
    S.symbol_smul n (c j) (S.genMonomial_mem_ideal (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)))

/-- A combination of the symbols of the degree-`n` monomials, with scalars the residues of
coefficients in `A`, is the symbol of the corresponding combination of the monomials. -/
theorem coe_sum_smul_symbolFamily (n : ℕ) (c : ℕ → A) :
    ((∑ j : Fin (n + 1), S.scalar (c (j : ℕ)) • S.symbolFamily n j :
        homogeneousSubmodule (Fin 2) k n) : MvPolynomial (Fin 2) k) =
      S.symbol n (∑ j ∈ Finset.range (n + 1), c j * genMonomial S.gen₁ S.gen₂ n j) := by
  rw [S.symbol_sum_mul_genMonomial n c]
  push_cast
  simp only [coe_symbolFamily]
  exact Fin.sum_univ_eq_sum_range
    (fun j : ℕ => S.scalar (c j) • S.symbol n (genMonomial S.gen₁ S.gen₂ n j)) (n + 1)

/-- **The symbols of the degree-`n` monomials span the binary forms of degree `n`.** -/
theorem top_le_span_symbolFamily
    (hgen : ∀ n, S.ideal (n + 1) ≤ S.ideal 1 * S.ideal n ⊔ S.ideal (n + 2)) (n : ℕ) :
    ⊤ ≤ Submodule.span k (Set.range (S.symbolFamily n)) := by
  intro v _
  obtain ⟨a, ha, hav⟩ :=
    S.surjective_symbol n (v : MvPolynomial (Fin 2) k) v.2
  obtain ⟨u, hu, r, hr, rfl⟩ :=
    Submodule.mem_sup.1 (S.ideal_le_span_gen_pow_sup hgen n ha)
  obtain ⟨c, hc⟩ := exists_repr_of_mem_span_pow S.gen₁ S.gen₂ hu
  have humem : u ∈ S.ideal n := S.span_gen_pow_le n hu
  have hrmem : r ∈ S.ideal n := S.ideal_succ_le n hr
  have hrzero : S.symbol n r = 0 := (S.symbol_eq_zero_iff n hrmem).2 hr
  refine (Submodule.mem_span_range_iff_exists_fun k).2
    ⟨fun j : Fin (n + 1) => S.scalar (c (j : ℕ)), Subtype.ext ?_⟩
  rw [S.coe_sum_smul_symbolFamily n c, ← hc, ← hav, S.symbol_add n humem hrmem, hrzero,
    add_zero]

/-- **The symbols of the degree-`n` monomials are a basis of the binary forms of degree `n`.**
They span a space of dimension `n + 1` and there are `n + 1` of them. -/
theorem linearIndependent_symbolFamily
    (hgen : ∀ n, S.ideal (n + 1) ≤ S.ideal 1 * S.ideal n ⊔ S.ideal (n + 2)) (n : ℕ) :
    LinearIndependent k (S.symbolFamily n) :=
  linearIndependent_of_top_le_span_of_card_eq_finrank (S.top_le_span_symbolFamily hgen n)
    (by rw [Fintype.card_fin, Module.finrank_eq_card_basis (homogeneousBinaryBasis k n),
      Fintype.card_fin])

/-- **The degree-`d` monomials in the two generators are linearly independent over `A / I₁`.**

This is the `hindep` hypothesis of
`AlgebraicGeometry.Scheme.IdealSheafData.formalNeighborhoodMonomialFiltration`: a combination of
the degree-`d` monomials that vanishes to order `d + 1` has symbol zero, and the symbols of the
monomials are a basis of the degree-`d` forms, so every coefficient has vanishing residue. -/
theorem coeff_mem_ideal_one
    (hgen : ∀ n, S.ideal (n + 1) ≤ S.ideal 1 * S.ideal n ⊔ S.ideal (n + 2)) (d : ℕ) (c : ℕ → A)
    (h : (∑ j ∈ Finset.range (d + 1), c j * genMonomial S.gen₁ S.gen₂ d j) ∈ S.ideal (d + 1))
    (j : ℕ) (hj : j ≤ d) : c j ∈ S.ideal 1 := by
  classical
  have hmem : (∑ i ∈ Finset.range (d + 1), c i * genMonomial S.gen₁ S.gen₂ d i) ∈ S.ideal d :=
    Submodule.sum_mem _ fun i hi => S.mul_genMonomial_mem_ideal (c i) hi
  have hzero : ∑ i : Fin (d + 1), S.scalar (c (i : ℕ)) • S.symbolFamily d i = 0 :=
    Submodule.coe_eq_zero.1 (by
      rw [S.coe_sum_smul_symbolFamily d c]
      exact (S.symbol_eq_zero_iff d hmem).2 h)
  have hcoeff := Fintype.linearIndependent_iff.1 (S.linearIndependent_symbolFamily hgen d)
    (fun i : Fin (d + 1) => S.scalar (c (i : ℕ))) hzero ⟨j, Nat.lt_succ_of_le hj⟩
  exact S.mem_ideal_one_of_scalar_eq_zero hcoeff

/-- **A degreewise symbol system whose associated graded ring is generated in degree one
produces the three monomial inputs of Stacks 0C2K**: two generators lying in `I₁`, the spanning
of `Iₙ` by the degree-`n` monomials modulo `Iₙ₊₁`, and the linear independence of those
monomials over `A / I₁`.  These are the `hgen`, `hspanPow` and `hindep` arguments of
`AlgebraicGeometry.Scheme.IdealSheafData.formalNeighborhoodMonomialFiltration`. -/
theorem exists_gen_spanPow_indep
    (hgen : ∀ n, S.ideal (n + 1) ≤ S.ideal 1 * S.ideal n ⊔ S.ideal (n + 2)) :
    ∃ x y : A, Ideal.span {x, y} ≤ S.ideal 1 ∧
      (∀ n, S.ideal n ≤ Ideal.span {x, y} ^ n ⊔ S.ideal (n + 1)) ∧
      ∀ (d : ℕ) (c : ℕ → A),
        (∑ j ∈ Finset.range (d + 1), c j * genMonomial x y d j) ∈ S.ideal (d + 1) →
        ∀ j ≤ d, c j ∈ S.ideal 1 :=
  ⟨S.gen₁, S.gen₂, (pow_one _).symm.trans_le (S.span_gen_pow_le 1),
    S.ideal_le_span_gen_pow_sup hgen,
    fun d c h j hj => S.coeff_mem_ideal_one hgen d c h j hj⟩

end DegreewiseSymbol

end AlgebraicGeometry.SemistableReduction

end
