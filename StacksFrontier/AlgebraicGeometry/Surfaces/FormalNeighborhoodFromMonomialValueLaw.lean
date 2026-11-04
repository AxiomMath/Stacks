module

public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveMonomialValues
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveFormalNeighborhood

/-!
# Stacks 0C2K from a single equation

The four [Stacks, Tag 0C2K] carriers in
`StacksFrontier/AlgebraicGeometry/Surfaces/ExceptionalCurveFormalNeighborhood.lean` each take an
`AlgebraicGeometry.Scheme.IdealSheafData.ExceptionalMonomialData` as a hypothesis, and several
modules of this development have asserted in prose that nothing constructs that bundle. **That
is false**, and this file is the machine-checked retraction: the bundle is constructed by
`AlgebraicGeometry.Scheme.IdealSheafData.ExceptionalMonomialData.ofMonomialValueLaw`, and the
two elements it wants come from
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
`.exists_formalNeighborhoodSymbol_one_eq_X`, which is proved outright.

So the whole of 0C2K rests on one carried hypothesis: the *monomial value law*

`σₙ(xⁿ⁻ʲ yʲ) = T₀ⁿ⁻ʲ T₁ʲ`,

which quantifies over no element of the ring. Everything else — multiplicativity of the
filtration, the span bound, the monomial independence, surjectivity of the thickening
restrictions, and the residue quotient being a field — is proved. The result below composes the
constructor with the three carriers so that this reduction is a theorem rather than a remark.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData`
  `.isNoetherianCompleteLocalRing_and_isRegular_and_dim_formalNeighborhoodRing_of_monomialValueLaw`
  — the complete-Noetherian-local, regularity and dimension-two clauses of [Stacks, Tag 0C2K]
  for the ring of compatible functions on the thickenings of an exceptional curve of the first
  kind, granted only the monomial value law for some pair of elements of the first step of the
  filtration.

## What this does and does not do

It does **not** earn the tag, and no attribute is placed here: `hmono` is a hypothesis
[Stacks, Tag 0C2K] does not have. The four existing `@[stacks 0C2K]` carriers are left exactly
as they are — `ExceptionalMonomialData` has been *reduced*, not discharged.

It also does **not** discharge the binders `hreg` and `hdim` of the [Stacks, Tag 0C2L] chain, and
a note in
`StacksFrontier/AlgebraicGeometry/F6Rank136/ExceptionalCurveContractionBirational.lean` which
implied otherwise has been corrected. Those binders are about the local ring `𝒪_{Y, y}` of the
**base**, whereas everything here is about
`AlgebraicGeometry.Scheme.IdealSheafData.formalNeighborhoodRing`, a ring built on the
**source**. What joins them is the transport `A ≅ 𝒪_{Y, y}^∧` of the source's proof — the
comparison of [Stacks, Tag 02OD] together with the cofinality `Eₙ ⊆ X ×_Y Spec(𝒪/𝔪ⁿ) ⊆ E_{nm}`.
That transport is therefore the real root of `hreg` and `hdim`, and an earlier claim of this
development that it was pointless because the bundle was unconstructible rested on the false
premise retracted above.

## References

* [Stacks Project, Tag 0C2K](https://stacks.math.columbia.edu/tag/0C2K)
* [Stacks Project, Tag 02OD](https://stacks.math.columbia.edu/tag/02OD)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry.SemistableReduction Stacks.Divisors

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} {D : X.IdealSheafData} {k : Type u} [Field k]
  {e : projectiveLineProj k ≅ D.subscheme}

/-- **Three clauses of [Stacks, Tag 0C2K] from the monomial value law alone.** For an exceptional
curve of the first kind on a Noetherian scheme, the ring `A` of compatible global functions on
the infinitesimal thickenings is a complete Noetherian local ring, is regular, and has Krull
dimension two — granted only that the symbol takes the expected values on the monomials in
*some* pair of elements of the first step of the filtration.

Such a pair exists unconditionally
(`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
`.exists_formalNeighborhoodSymbol_one_eq_X`), so the hypothesis `hmono` is the only thing
between this development and the tag. It is not a hypothesis of the tag, so no attribute is
placed here. -/
public theorem
    isNoetherianCompleteLocalRing_and_isRegular_and_dim_formalNeighborhoodRing_of_monomialValueLaw
    [IsNoetherian X] [IsEffectiveCartierDivisor D]
    (hE : IsExceptionalCurveOfFirstKind D k e)
    (hmono : ∃ x y : formalNeighborhoodRing D,
      x ∈ formalNeighborhoodFiltration D 1 ∧ y ∈ formalNeighborhoodFiltration D 1 ∧
        hE.MonomialValueLaw x y) :
    IsNoetherianCompleteLocalRing (formalNeighborhoodRing D) ∧
      IsRegularLocalRing (formalNeighborhoodRing D) ∧
      ringKrullDim (formalNeighborhoodRing D) = 2 := by
  obtain ⟨x, y, hx, hy, hlaw⟩ := hmono
  have M : ExceptionalMonomialData D :=
    ExceptionalMonomialData.ofMonomialValueLaw hE hx hy hlaw
  exact ⟨isNoetherianCompleteLocalRing_formalNeighborhoodRing (D := D) (k := k) hE M,
    isRegularLocalRing_formalNeighborhoodRing (D := D) (k := k) hE M,
    ringKrullDim_formalNeighborhoodRing_eq_two (D := D) (k := k) hE M⟩

end AlgebraicGeometry.Scheme.IdealSheafData

end
