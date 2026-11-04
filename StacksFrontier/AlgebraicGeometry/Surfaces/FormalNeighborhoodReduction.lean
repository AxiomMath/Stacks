module

public import StacksFrontier.AlgebraicGeometry.Surfaces.FormalNeighborhoodFiltration

/-!
# Reducing the structure of the formal neighbourhood to five geometric inputs

Let `D` be an ideal sheaf on a scheme `X` and let
`A = AlgebraicGeometry.Scheme.IdealSheafData.formalNeighborhoodRing D` be the ring of
compatible global functions on the infinitesimal thickenings of `D`. Stacks 0C2K asserts, for
`D` an exceptional curve of the first kind on a Noetherian scheme, that `A` is a
two-dimensional regular complete local Noetherian ring whose `(n + 1)`-st projection kernel is
the `(n + 1)`-st power of the maximal ideal.

`AlgebraicGeometry.SemistableReduction.MonomialFiltration` is the purely algebraic hypothesis
bundle from which all four of those conclusions follow, and
`AlgebraicGeometry.Scheme.IdealSheafData.formalNeighborhoodFiltration` is the filtration of `A`
that the Stacks argument puts on it. Four of the eleven axioms of a monomial filtration hold
for that filtration with no hypothesis at all on `D`, and are proved in
`StacksDraft.AlgebraicGeometry.Surfaces.Ch54Rank.FormalNeighborhoodFiltration`: the filtration
starts at `⊤`, it decreases, it is separated, and it is complete.

This file assembles the remainder. It packages the five axioms that do carry geometric content
into `formalNeighborhoodMonomialFiltration`, and then reads the four conclusions of 0C2K off any
monomial filtration whose underlying filtration is the projection-kernel one. So the geometric
part of 0C2K is reduced to exactly five statements about `A`, each with an explicit Lean type:

* the filtration is multiplicative, `Iₘ · Iₙ ⊆ Iₘ₊ₙ`;
* two chosen elements lie in `I₁`;
* `Iₙ` is spanned modulo `Iₙ₊₁` by the degree-`n` monomials in them;
* those monomials are linearly independent over `A / I₁` in each degree;
* `A / I₁` is a field.

The first three are statements about vanishing orders of functions on the thickenings; the last
two are `H⁰(𝐏¹_k, 𝒪(d))` and `H⁰(𝐏¹_k, 𝒪) = k`. None of the five is proved *in this file*, where
all five are hypotheses, and nothing here carries a `@[stacks 0C2K]` attribute. Two of them are
proved for an exceptional curve of the first kind elsewhere — multiplicativity in
`StacksFrontier.AlgebraicGeometry.Surfaces.FormalNeighborhoodMultiplicative` and the residue field
in `StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveResidueField` — and the three
monomial statements are not proved anywhere: 0C2K is not formalized until they are.

## Main definitions

* `AlgebraicGeometry.Scheme.IdealSheafData.formalNeighborhoodMonomialFiltration` — the monomial
  filtration on `A` built from the five geometric inputs.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.formalNeighborhoodRing_isNoetherianCompleteLocalRing`,
  `formalNeighborhoodRing_isRegularLocalRing`, `formalNeighborhoodRing_ringKrullDim` and
  `ker_formalNeighborhoodProjection_eq_maximalIdeal_pow` — the four conclusions of 0C2K, from a
  monomial filtration whose ideals are the projection kernels.

## References

* [Stacks Project, Tag 0C2K](https://stacks.math.columbia.edu/tag/0C2K)
-/

@[expose] public noncomputable section

open AlgebraicGeometry.SemistableReduction

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (D : X.IdealSheafData)

/-- The monomial filtration on the ring of compatible functions, assembled from the four
unconditional axioms of the projection-kernel filtration and the five that carry geometric
content.

The five hypotheses are exactly what the Stacks proof of 0C2K extracts from the geometry of an
exceptional curve of the first kind: `hmul` and `hspanPow` are statements about vanishing orders
of functions on the thickenings, `hgen` chooses two generators, `hindep` is the monomial basis
of `H⁰(𝐏¹_k, 𝒪(d))`, and `hfield` is `H⁰(𝐏¹_k, 𝒪) = k`. -/
public def formalNeighborhoodMonomialFiltration (x y : formalNeighborhoodRing D)
    (hmul : ∀ m n, formalNeighborhoodFiltration D m * formalNeighborhoodFiltration D n ≤
      formalNeighborhoodFiltration D (m + n))
    (hgen : Ideal.span {x, y} ≤ formalNeighborhoodFiltration D 1)
    (hspanPow : ∀ n, formalNeighborhoodFiltration D n ≤
      Ideal.span {x, y} ^ n ⊔ formalNeighborhoodFiltration D (n + 1))
    (hindep : ∀ (d : ℕ) (c : ℕ → formalNeighborhoodRing D),
      (∑ j ∈ Finset.range (d + 1), c j * genMonomial x y d j) ∈
        formalNeighborhoodFiltration D (d + 1) →
      ∀ j ≤ d, c j ∈ formalNeighborhoodFiltration D 1)
    (hfield : IsField (formalNeighborhoodRing D ⧸ formalNeighborhoodFiltration D 1)) :
    MonomialFiltration (formalNeighborhoodRing D) where
  ideal := formalNeighborhoodFiltration D
  gen₁ := x
  gen₂ := y
  ideal_zero := rfl
  ideal_succ_le := formalNeighborhoodFiltration_succ_le D
  mul_le := hmul
  span_le_ideal_one := hgen
  le_span_pow_sup := hspanPow
  iInf_eq_bot := iInf_formalNeighborhoodFiltration D
  exists_sum := exists_sum_formalNeighborhoodFiltration D
  monomials_indep := hindep
  quotient_isField := hfield

/-- The ideals of `formalNeighborhoodMonomialFiltration` are the projection kernels
`formalNeighborhoodFiltration D`. -/
@[simp]
public theorem formalNeighborhoodMonomialFiltration_ideal (x y : formalNeighborhoodRing D)
    (hmul hgen hspanPow hindep hfield) :
    (formalNeighborhoodMonomialFiltration D x y hmul hgen hspanPow hindep hfield).ideal =
      formalNeighborhoodFiltration D := rfl

section Conclusions

variable (F : MonomialFiltration (formalNeighborhoodRing D))
  (hF : F.ideal = formalNeighborhoodFiltration D)

include F

/-- **Stacks 0C2K, the complete-Noetherian-local clause.** -/
public theorem formalNeighborhoodRing_isNoetherianCompleteLocalRing :
    IsNoetherianCompleteLocalRing (formalNeighborhoodRing D) :=
  F.isNoetherianCompleteLocalRing

/-- **Stacks 0C2K, the regularity clause.** -/
public theorem formalNeighborhoodRing_isRegularLocalRing :
    IsRegularLocalRing (formalNeighborhoodRing D) :=
  F.isRegularLocalRing

/-- **Stacks 0C2K, the dimension clause.** -/
public theorem formalNeighborhoodRing_ringKrullDim :
    ringKrullDim (formalNeighborhoodRing D) = 2 :=
  F.ringKrullDim_eq_two

include hF

/-- **Stacks 0C2K, the projection-kernel clause.** The kernel of the projection to the
`(n + 1)`-st thickening is the `(n + 1)`-st power of the maximal ideal. -/
public theorem ker_formalNeighborhoodProjection_eq_maximalIdeal_pow (n : ℕ) :
    letI : IsLocalRing (formalNeighborhoodRing D) := F.isLocalRing
    RingHom.ker (formalNeighborhoodProjection D n) =
      IsLocalRing.maximalIdeal (formalNeighborhoodRing D) ^ (n + 1) := by
  let _ : IsLocalRing (formalNeighborhoodRing D) := F.isLocalRing
  rw [← formalNeighborhoodFiltration_succ D n, ← hF, F.ideal_eq_maximalIdeal_pow]

end Conclusions

end AlgebraicGeometry.Scheme.IdealSheafData
