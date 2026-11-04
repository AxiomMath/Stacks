module

public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveFormalNeighborhood
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveThickeningSurjective

/-!
# The formal-neighbourhood inputs of an exceptional curve from a monomial symbol system

For an exceptional curve of the first kind the restrictions between the thickenings are surjective
(`StacksFrontier/AlgebraicGeometry/Surfaces/ExceptionalCurveThickeningSurjective.lean`), so the
surjectivity hypothesis of the constructors of
`AlgebraicGeometry.Scheme.IdealSheafData.ExceptionalMonomialData` can be dropped.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.ExceptionalMonomialData.ofMonomialInputsOfExceptional`:
  the three monomial inputs suffice.
* `AlgebraicGeometry.Scheme.IdealSheafData.ExceptionalMonomialData.ofMonomialSymbolOfExceptional`:
  all five inputs from a monomial symbol system alone.

## References

* [Stacks Project, Tag 0C2K](https://stacks.math.columbia.edu/tag/0C2K)
-/

@[expose] public noncomputable section

open AlgebraicGeometry.SemistableReduction

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (D : X.IdealSheafData)

namespace ExceptionalMonomialData

variable {D}

/-- **The three monomial inputs suffice: the surjectivity of the thickening restrictions is not
a hypothesis.** `AlgebraicGeometry.Scheme.IdealSheafData.ExceptionalMonomialData.ofMonomialInputs`
asks for the restrictions `Γ(Eₘ₊₂, 𝒪) ⟶ Γ(Eₘ₊₁, 𝒪)` to be surjective, which it needs only to
know that the residue quotient is a field. For an exceptional curve of the first kind that
surjectivity is proved,
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
`.surjective_thickeningRestriction`, so the bundle may be built from the three statements about
the monomials in the two chosen elements alone. -/
public def ofMonomialInputsOfExceptional (k : Type u) [Field k]
    {e : projectiveLineProj k ≅ D.subscheme} (hE : IsExceptionalCurveOfFirstKind D k e)
    (x y : formalNeighborhoodRing D)
    (hgen : Ideal.span {x, y} ≤ formalNeighborhoodFiltration D 1)
    (hspanPow : ∀ n, formalNeighborhoodFiltration D n ≤
      Ideal.span {x, y} ^ n ⊔ formalNeighborhoodFiltration D (n + 1))
    (hindep : ∀ (d : ℕ) (c : ℕ → formalNeighborhoodRing D),
      (∑ j ∈ Finset.range (d + 1), c j * genMonomial x y d j) ∈
        formalNeighborhoodFiltration D (d + 1) →
      ∀ j ≤ d, c j ∈ formalNeighborhoodFiltration D 1) :
    ExceptionalMonomialData D :=
  ofMonomialInputs (D := D) k hE hE.surjective_thickeningRestriction x y hgen hspanPow hindep

/-- **All five inputs from a monomial symbol system alone.** For an exceptional curve of the
first kind the surjectivity hypothesis of
`AlgebraicGeometry.Scheme.IdealSheafData.ExceptionalMonomialData.ofMonomialSymbol` is proved,
so the whole of Stacks 0C2K rests on producing a single
`AlgebraicGeometry.SemistableReduction.MonomialSymbol` on `A` whose filtration is the
projection-kernel one, and on nothing else. -/
public def ofMonomialSymbolOfExceptional (k : Type u) [Field k]
    {e : projectiveLineProj k ≅ D.subscheme} (hE : IsExceptionalCurveOfFirstKind D k e)
    (S : MonomialSymbol (formalNeighborhoodRing D) k)
    (hS : S.ideal = formalNeighborhoodFiltration D) :
    ExceptionalMonomialData D :=
  ofMonomialSymbol (D := D) k hE hE.surjective_thickeningRestriction S hS

end ExceptionalMonomialData

variable (k : Type u) [Field k] {e : projectiveLineProj k ≅ D.subscheme}

end AlgebraicGeometry.Scheme.IdealSheafData

end
