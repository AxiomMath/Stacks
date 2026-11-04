module

public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveMonomialSymbol
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveFormalNeighborhoodOfExceptional
public import StacksFrontier.AlgebraicGeometry.Surfaces.FormalNeighborhoodResidueMap
public import StacksFrontier.AlgebraicGeometry.Surfaces.FormalNeighborhoodSymbolAdditive

/-!
# The five geometric inputs of an exceptional curve from the monomial values of its symbol

Let `X` be a scheme and `E ⊂ X` an exceptional curve of the first kind, cut out by an ideal sheaf
`D` and presented as the projective line by `e : 𝐏¹_k ≅ E`. Write `A` for the ring of compatible
global functions on the infinitesimal thickenings of `D`, `Iₙ` for the projection kernels and
`σₙ : Iₙ ⟶ k[T₀, T₁]ₙ` for the symbol
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.formalNeighborhoodSymbol`.

`AlgebraicGeometry.Scheme.IdealSheafData.ExceptionalMonomialData` bundles the five inputs from
which [Stacks, Tag 0C2K] follows, and
`AlgebraicGeometry.Scheme.IdealSheafData.ExceptionalMonomialData.ofMonomialInputsOfExceptional`
builds the bundle from three statements about two chosen elements `x, y ∈ I₁`. This file replaces
those three by the single statement

`σₙ(x^{n-j} y^j) = T₀^{n-j} T₁^j`  for `j ≤ n`,

the *values of the symbol on the monomials in the two chosen elements*, carried here as
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.MonomialValueLaw`.

## Why this is weaker than the one-step law

`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.OneStepLaw` asks for
`σ_{d+1}(ab) = σ_d(a) σ₁(b)` for *every* `a ∈ I_d` and `b ∈ I₁`. The law here is that equation's
consequence along one chain of elements only: the `d + 1` monomials of each degree in two fixed
elements. That it is a consequence is
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
`.monomialValueLaw_of_oneStepLaw`, which goes through
`AlgebraicGeometry.SemistableReduction.MonomialSymbol.symbol_genMonomial`; the implication is
strict in shape, since the hypothesis no longer quantifies over the ring at all, only over two
natural numbers.

Nothing beyond it is needed, for two reasons, and neither is about multiplication.

* **Independence is a one-line consequence of the values.** A combination
  `∑ⱼ cⱼ x^{d-j} y^j` lying in `I_{d+1}` has vanishing symbol, by
  `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
  `.formalNeighborhoodSymbol_eq_zero_iff`; the symbol of the sum is the sum of the symbols, by
  `formalNeighborhoodSymbol_add`; and each term's symbol is `σ₀(cⱼ)` times the corresponding
  binary monomial, by the *degree-zero* law `formalNeighborhoodSymbol_smul` together with the
  hypothesis. So `∑ⱼ φ(cⱼ) T₀^{d-j} T₁^j = 0` with `φ` the residue map, and the `d + 1` binary
  monomials of degree `d` are independent, `MvPolynomial.eq_zero_of_sum_binaryMonomial_eq_zero`.
  Every lemma used here holds with no hypothesis beyond the exceptional curve.
* **Spanning is then free.** It is interderivable with independence degree by degree,
  `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
  `.le_span_pow_sup_iff_coeff_mem_one`, which carries no hypothesis beyond `x, y ∈ I₁`. The
  degree-zero case is not covered by that equivalence and does not need it: `I₀` is the whole ring
  and so is the empty power of any ideal.

So the remaining content of [Stacks, Tag 0C2K] is the displayed equation, in which no element of
`A` is quantified over. The two chosen elements themselves need no choice beyond
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
`.exists_formalNeighborhoodSymbol_one_eq_X`, which is proved outright from the surjectivity of the
graded-piece comparison in degree one.

Nothing here carries a `@[stacks]` attribute: this is one step of the proof of
[Stacks, Tag 0C2K].

## Main definitions

* `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.MonomialValueLaw` — the
  values of the symbol on the monomials in two chosen elements.
* `AlgebraicGeometry.Scheme.IdealSheafData.ExceptionalMonomialData.ofMonomialValueLaw` — **the
  five geometric inputs of [Stacks, Tag 0C2K] from those values alone.**

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
  `.monomials_indep_of_monomialValueLaw` — the `monomials_indep` input.
* `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
  `.le_span_pow_sup_of_monomialValueLaw` — the `le_span_pow_sup` input.
* `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
  `.monomialValueLaw_of_oneStepLaw` — the law is implied by the one-step law.

## References

* [Stacks Project, Tag 0C2K](https://stacks.math.columbia.edu/tag/0C2K)
-/

@[expose] public noncomputable section

open AlgebraicGeometry.SemistableReduction Stacks.Divisors

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} {D : X.IdealSheafData} {k : Type u} [Field k]
  {e : projectiveLineProj k ≅ D.subscheme}

namespace IsExceptionalCurveOfFirstKind

variable [IsEffectiveCartierDivisor D] (hE : IsExceptionalCurveOfFirstKind D k e)

/-- **The monomial values of the symbol**: the symbol of a degree-`n` monomial in the two chosen
elements is the corresponding binary monomial.

This is the only part of multiplicativity the five geometric inputs of [Stacks, Tag 0C2K] need.
It is implied by
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.OneStepLaw`
(`monomialValueLaw_of_oneStepLaw`) and quantifies over no element of the ring. -/
public def MonomialValueLaw (x y : formalNeighborhoodRing D) : Prop :=
  ∀ n j : ℕ, j ≤ n →
    hE.formalNeighborhoodSymbol n (genMonomial x y n j) = MvPolynomial.binaryMonomial k n j

variable {x y : formalNeighborhoodRing D} (hx : x ∈ formalNeighborhoodFiltration D 1)
  (hy : y ∈ formalNeighborhoodFiltration D 1)

include hx hy in
/-- **The degree-`d` monomials in the two chosen elements are independent over `A / I₁`**, given
the values of the symbol on them.

This is the `monomials_indep` field of
`AlgebraicGeometry.Scheme.IdealSheafData.ExceptionalMonomialData`. A combination of the degree-`d`
monomials lying in `I_{d+1}` has vanishing symbol, so the residues of its coefficients are the
coefficients of a vanishing combination of the `d + 1` binary monomials of degree `d`, which are
independent. Only the degree-zero multiplicativity of the symbol is used, and that is proved
outright. -/
public theorem monomials_indep_of_monomialValueLaw (hmono : hE.MonomialValueLaw x y)
    (d : ℕ) (c : ℕ → formalNeighborhoodRing D)
    (h : (∑ j ∈ Finset.range (d + 1), c j * genMonomial x y d j) ∈
      formalNeighborhoodFiltration D (d + 1)) (j : ℕ) (hj : j ≤ d) :
    c j ∈ formalNeighborhoodFiltration D 1 := by
  have hmono' : ∀ i ∈ Finset.range (d + 1),
      genMonomial x y d i ∈ formalNeighborhoodFiltration D d := fun i hi =>
    genMonomial_mem_of_mem_ideal_one (formalNeighborhoodFiltration D)
      (formalNeighborhoodFiltration_zero D) (formalNeighborhoodFiltration_mul_le D) hx hy
      (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
  have hterm : ∀ i ∈ Finset.range (d + 1),
      c i * genMonomial x y d i ∈ formalNeighborhoodFiltration D d := fun i hi =>
    Ideal.mul_mem_left _ _ (hmono' i hi)
  have hmem : (∑ i ∈ Finset.range (d + 1), c i * genMonomial x y d i) ∈
      formalNeighborhoodFiltration D d := Submodule.sum_mem _ hterm
  have hvanish : ∑ i ∈ Finset.range (d + 1),
      formalNeighborhoodResidue D k e (c i) • MvPolynomial.binaryMonomial k d i = 0 := by
    rw [← (hE.formalNeighborhoodSymbol_eq_zero_iff d hmem).2 h,
      symbol_sum_range_of_add hE.formalNeighborhoodSymbol_add d (d + 1) _ hterm]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hE.formalNeighborhoodSymbol_smul d (c i) (hmono' i hi),
      hmono d i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)),
      hE.formalNeighborhoodSymbol_zero, MvPolynomial.smul_eq_C_mul]
  have hres := MvPolynomial.eq_zero_of_sum_binaryMonomial_eq_zero d
    (fun i => formalNeighborhoodResidue D k e (c i)) hvanish hj
  rwa [← RingHom.mem_ker, ker_formalNeighborhoodResidue] at hres

include hx hy in
/-- **Each step of the filtration is spanned modulo the next by the degree-`n` monomials in the
two chosen elements**, given the values of the symbol on them.

This is the `le_span_pow_sup` field of
`AlgebraicGeometry.Scheme.IdealSheafData.ExceptionalMonomialData`. In a positive degree it is the
independence just proved, read through the equivalence
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
`.le_span_pow_sup_iff_coeff_mem_one`; in degree zero both sides are the whole ring. -/
public theorem le_span_pow_sup_of_monomialValueLaw (hmono : hE.MonomialValueLaw x y) (n : ℕ) :
    formalNeighborhoodFiltration D n ≤
      Ideal.span {x, y} ^ n ⊔ formalNeighborhoodFiltration D (n + 1) := by
  cases n with
  | zero => rw [pow_zero, Ideal.one_eq_top]; exact le_top.trans le_sup_left
  | succ m =>
    exact (hE.le_span_pow_sup_iff_coeff_mem_one hx hy m).2
      fun c hc j hj => hE.monomials_indep_of_monomialValueLaw hx hy hmono (m + 1) c hc j hj

include hx hy in
/-- **The one-step law implies the monomial values.** The symbol of a degree-`n` monomial is the
corresponding binary monomial for the monomial symbol system the one-step law builds,
`AlgebraicGeometry.SemistableReduction.MonomialSymbol.symbol_genMonomial`, and that system's
filtration and symbol are the projection-kernel filtration and the symbol of this development. -/
public theorem monomialValueLaw_of_oneStepLaw (hmul : hE.OneStepLaw)
    (hsx : hE.formalNeighborhoodSymbol 1 x = MvPolynomial.X 0)
    (hsy : hE.formalNeighborhoodSymbol 1 y = MvPolynomial.X 1) :
    hE.MonomialValueLaw x y :=
  fun _ _ hj => (hE.monomialSymbol hmul).symbol_genMonomial hx hy hsx hsy hj

end IsExceptionalCurveOfFirstKind

namespace ExceptionalMonomialData

/-- **The five geometric inputs of [Stacks, Tag 0C2K] from the monomial values of the symbol.**

Every hypothesis is a hypothesis of the tag except `hmono`, and `hmono` is the equation
`σₙ(x^{n-j} y^j) = T₀^{n-j} T₁^j`, which quantifies over no element of the ring: the two chosen
elements come from
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
`.exists_formalNeighborhoodSymbol_one_eq_X`, and the remaining four inputs are proved outright.
This is a weaker carried hypothesis than that of
`AlgebraicGeometry.Scheme.IdealSheafData.ExceptionalMonomialData.ofOneStepLaw`; see
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
`.monomialValueLaw_of_oneStepLaw`. -/
public def ofMonomialValueLaw [IsEffectiveCartierDivisor D]
    (hE : IsExceptionalCurveOfFirstKind D k e) {x y : formalNeighborhoodRing D}
    (hx : x ∈ formalNeighborhoodFiltration D 1)
    (hy : y ∈ formalNeighborhoodFiltration D 1) (hmono : hE.MonomialValueLaw x y) :
    ExceptionalMonomialData D :=
  ofMonomialInputsOfExceptional (D := D) k hE x y
    (Ideal.span_le.2 (Set.insert_subset_iff.2 ⟨hx, Set.singleton_subset_iff.2 hy⟩))
    (hE.le_span_pow_sup_of_monomialValueLaw hx hy hmono)
    fun d c h j hj => hE.monomials_indep_of_monomialValueLaw hx hy hmono d c h j hj

end ExceptionalMonomialData

end AlgebraicGeometry.Scheme.IdealSheafData

end
