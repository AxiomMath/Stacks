module

public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveFormalNeighborhood
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurve
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveResidueField
public import StacksFrontier.AlgebraicGeometry.Surfaces.FormalNeighborhoodMultiplicative
public import StacksFrontier.AlgebraicGeometry.Surfaces.FormalNeighborhoodReduction
public import StacksFrontier.AlgebraicGeometry.Surfaces.FormalNeighborhoodSymbol
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveResidueFieldSupplement
public import StacksFrontier.AlgebraicGeometry.Surfaces.FormalNeighborhoodSymbolSupplement

/-!
# Further results on `ExceptionalCurveFormalNeighborhood`

Constructions of `AlgebraicGeometry.Scheme.IdealSheafData.ExceptionalMonomialData` for an
exceptional curve of the first kind, from two elements of the formal neighbourhood ring and the
statements about their monomials, from a `AlgebraicGeometry.SemistableReduction.MonomialSymbol`,
or from a `AlgebraicGeometry.SemistableReduction.DegreewiseSymbol` whose associated graded ring
is generated in degree one.

## Main definitions

* `AlgebraicGeometry.Scheme.IdealSheafData.ExceptionalMonomialData.ofMonomialInputs_unconditional`:
  the data from two elements and the three statements about their monomials.
* `AlgebraicGeometry.Scheme.IdealSheafData.ExceptionalMonomialData.ofMonomialSymbol_unconditional`:
  the data from a monomial symbol whose filtration is the formal neighbourhood filtration.
* `AlgebraicGeometry.Scheme.IdealSheafData.ExceptionalMonomialData.ofDegreewiseSymbol`: the data
  from a degreewise symbol generated in degree one.
-/

@[expose] public noncomputable section

open AlgebraicGeometry.SemistableReduction

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (D : X.IdealSheafData)

namespace ExceptionalMonomialData

variable {D}

/-- The `ExceptionalMonomialData` of an exceptional curve of the first kind with generators `x`
and `y`, given that `x` and `y` lie in the first step of the formal neighbourhood filtration, that
each step `Iₙ` lies in `(x, y) ^ n ⊔ Iₙ₊₁`, and that the coefficients of a combination of the
degree-`d` monomials lying in `I_{d+1}` lie in `I₁`. Multiplicativity of the filtration is
`formalNeighborhoodFiltration_mul_le` and the residue field is
`isField_quotient_of_isExceptionalCurveOfFirstKind_unconditional`. -/
public def ofMonomialInputs_unconditional (k : Type u) [Field k]
    {e : projectiveLineProj k ≅ D.subscheme} (hE : IsExceptionalCurveOfFirstKind D k e)
    (x y : formalNeighborhoodRing D)
    (hgen : Ideal.span {x, y} ≤ formalNeighborhoodFiltration D 1)
    (hspanPow : ∀ n, formalNeighborhoodFiltration D n ≤
      Ideal.span {x, y} ^ n ⊔ formalNeighborhoodFiltration D (n + 1))
    (hindep : ∀ (d : ℕ) (c : ℕ → formalNeighborhoodRing D),
      (∑ j ∈ Finset.range (d + 1), c j * genMonomial x y d j) ∈
        formalNeighborhoodFiltration D (d + 1) →
      ∀ j ≤ d, c j ∈ formalNeighborhoodFiltration D 1) :
    ExceptionalMonomialData D where
  gen₁ := x
  gen₂ := y
  mul_le := formalNeighborhoodFiltration_mul_le D
  span_le_ideal_one := hgen
  le_span_pow_sup := hspanPow
  monomials_indep := hindep
  quotient_isField := isField_quotient_of_isExceptionalCurveOfFirstKind_unconditional D k hE

/-- The `ExceptionalMonomialData` of an exceptional curve of the first kind given by a
`AlgebraicGeometry.SemistableReduction.MonomialSymbol` on the formal neighbourhood ring whose
filtration is the formal neighbourhood filtration, with generators the two generators of the
symbol. -/
public def ofMonomialSymbol_unconditional (k : Type u) [Field k]
    {e : projectiveLineProj k ≅ D.subscheme} (hE : IsExceptionalCurveOfFirstKind D k e)
    (S : MonomialSymbol (formalNeighborhoodRing D) k)
    (hS : S.ideal = formalNeighborhoodFiltration D) :
    ExceptionalMonomialData D :=
  ofMonomialInputs_unconditional (D := D) k hE S.gen₁ S.gen₂
    (span_gen_le_formalNeighborhoodFiltration_one D S hS)
    (formalNeighborhoodFiltration_le_span_gen_pow_sup D S hS)
    (gen_monomials_indep_formalNeighborhoodFiltration D S hS)

/-- The `ExceptionalMonomialData` of an exceptional curve of the first kind given by a
`AlgebraicGeometry.SemistableReduction.DegreewiseSymbol` on the formal neighbourhood ring, which
identifies each graded piece `Iₙ / Iₙ₊₁` of the formal neighbourhood filtration with the binary
forms of degree `n`, provided the associated graded ring is generated in degree one: `Iₙ₊₁` lies
in `I₁ * Iₙ ⊔ Iₙ₊₂` for every `n`. -/
public def ofDegreewiseSymbol (k : Type u) [Field k]
    {e : projectiveLineProj k ≅ D.subscheme} (hE : IsExceptionalCurveOfFirstKind D k e)
    (S : DegreewiseSymbol (formalNeighborhoodRing D) k)
    (hS : S.ideal = formalNeighborhoodFiltration D)
    (hgen : ∀ n, S.ideal (n + 1) ≤ S.ideal 1 * S.ideal n ⊔ S.ideal (n + 2)) :
    ExceptionalMonomialData D :=
  ofMonomialInputs_unconditional (D := D) k hE S.gen₁ S.gen₂
    (by rw [← hS, ← pow_one (Ideal.span _)]; exact S.span_gen_pow_le 1)
    (fun n => by rw [← hS]; exact S.ideal_le_span_gen_pow_sup hgen n)
    (fun d c h j hj => by
      rw [← hS] at h ⊢
      exact S.coeff_mem_ideal_one hgen d c h j hj)

end ExceptionalMonomialData

variable (k : Type u) [Field k] {e : projectiveLineProj k ≅ D.subscheme}

end AlgebraicGeometry.Scheme.IdealSheafData

end
