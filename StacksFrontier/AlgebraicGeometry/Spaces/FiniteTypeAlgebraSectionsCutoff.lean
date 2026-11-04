module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.BoundedAffineAlgebraAntiEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraChartSectionsBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeOnSiteAffineCharts
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.SetTheory.Cardinal.SizeBound

/-!
# Algebra sheaves of finite type satisfy the size condition of the bounded Stacks 081V

An algebra sheaf `𝒜` of finite type on an algebraic space `X` has fewer sections than the cutoff
of the big fppf site at every étale chart of `X`.  This is the size condition
`AlgebraicGeometry.Space.AlgebraSheaf.SectionsBelowCutoff` of the bounded form of Stacks 081V,
so a quasi-coherent algebra of finite type, in particular one of finite presentation, has a
relative spectrum in the site itself (`AlgebraicGeometry.Space.boundedRelativeSpec`).

## Main results

* `AlgebraicGeometry.Space.AlgebraSheaf.sectionsBelowCutoff_of_isFiniteType`.

## Implementation notes

Let `V` be an étale chart of `X` and `T` its scheme.  The charts cut out by the affine opens `O`
of `T` cover `V`, so the sections of `𝒜` over `V` inject into the product of its sections over
them.  Over such an `O` the sections are a finite type algebra over `Γ(T, O)`, which has at most
`size T` elements, so each factor has at most `size T` elements, and there are at most `size T`
factors.  Hence `#𝒜(V) ≤ size T ^ size T ≤ 2 ^ size T`, which is below the cutoff because `T`
is an object of the site and the cutoff is a strong limit.

## References

* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
-/

@[expose] public section

open CategoryTheory Opposite Cardinal

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A finite type algebra over a commutative ring `R` has at most `max #R ℵ₀` elements. -/
theorem mk_le_max_of_finiteType {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
    (hf : f.FiniteType) : #A ≤ max #R ℵ₀ := by
  let := f.toAlgebra
  obtain ⟨ι, _, g, hg⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial'.1 hf
  refine (mk_le_of_surjective hg).trans (MvPolynomial.cardinalMk_le_max.trans ?_)
  exact max_le (max_le (le_max_left _ _) ((lt_aleph0_of_finite ι).le.trans (le_max_right _ _)))
    (le_max_right _ _)

/-- **An algebra sheaf of finite presentation satisfies the size condition of the bounded
Stacks 081V**: it is of finite type. -/
theorem AlgebraSheaf.sectionsBelowCutoff_of_isFinitePresentation {X : AlgebraicSpaces B S hS}
    (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) (hA : A.IsFinitePresentation) :
    AlgebraSheaf.SectionsBelowCutoff B S hS A :=
  AlgebraSheaf.sectionsBelowCutoff_of_isFiniteType B S hS A fun U hU =>
    RingHom.FiniteType.of_finitePresentation (hA U hU)

end AlgebraicGeometry.Space

end
