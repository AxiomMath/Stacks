module

public import StacksFrontier.AlgebraicGeometry.ProjF1DegreeOneChart.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Assembled

/-!
# Morphisms into relative Proj out of chart data

The residue of the label `01O4 "represents_f1"` is a single bijection: between the morphisms
`T ⟶ Proj A` over the base and the strict-equivalence classes of invertible degree-one quotients
of `f⁎A`. Both directions of it were recorded in
`Stacks.AlgebraicGeometry.ProjF1Normalisation` as needing *a construction of a morphism into
relative Proj out of such a quotient*, with the note that no equivalence of that shape exists in
the pinned Mathlib or in this repository.

The claim about the equivalence holds; the claim about the morphism is narrower than recorded.
`AlgebraicGeometry.Proj.fromOfGlobalSections` takes a *plain* ring homomorphism to global
sections, which is what a quotient becomes after dehomogenization at a section that trivializes
its invertible sheaf — so it is the local model of the construction rather than only the case of
the trivial sheaf, and by
`Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.map_irrelevant_eq_top_of_isUnit` the hypothesis it
asks for is free once one positive-degree section is inverted. This file therefore builds
morphisms into relative Proj out of exactly the data Tag 01NA produces, by composing the chart
bijection of `Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.chartHomEquiv` with the affine charts
of `Stacks.AlgebraicGeometry.RelativeProj.relativeProj`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.toRelativeProj`: the morphism into relative Proj
  determined by a homomorphism out of the `Away` ring of a positive-degree homogeneous section
  over an affine open of the base.
* `Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.toRelativeProjOfIsUnit`: the same from a ring map
  to global sections that inverts one positive-degree homogeneous section.

## Main results

* `Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.toRelativeProj_comp_toBase` and
  `Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.toRelativeProjOfIsUnit_comp_toBase`: these
  morphisms lie over the affine open they were built on, which is what makes them points of the
  functor over the base.

## Implementation notes

**What this does not do, and why Tag 01O4 is not yet proved.** These are morphisms into relative
Proj
built from data over *one* affine open of the base and from *one* homogeneous section inverted on
all of the test scheme. Tag 01O4's bijection needs, in addition: the dehomogenization that turns
an invertible degree-one quotient into such a ring map (which is where the hypothesis that `A` is
generated in degree one is used, to make the degree-one basic opens cover), the glueing of the
resulting local morphisms over a cover of the test scheme, and the injectivity and surjectivity
of the assembled map on strict-equivalence classes. None of those is done here.

## References

* [Stacks Project, Tag 01NA](https://stacks.math.columbia.edu/tag/01NA)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj

namespace Stacks.AlgebraicGeometry.ProjF1DegreeOneChart

universe u

variable {S : Scheme.{u}} (A : SheafGradedAlgebra.{u} S) (U : S.Opens) (hU : IsAffineOpen U)
  {X : Scheme.{u}} {r : A.sectionRing U} {d : ℕ}

/-- **A morphism into relative Proj out of chart data.** A homomorphism from the degree-zero part
of the localization at a positive-degree homogeneous section over an affine open `U` of the base
classifies a morphism to the chart of relative Proj over `U`, hence one into relative Proj. -/
public def toRelativeProj (hr : r ∈ A.grading U d) (hd : 0 < d)
    (ρ : CommRingCat.of (HomogeneousLocalization.Away (A.grading U) r) ⟶ Γ(X, ⊤)) :
    X ⟶ (relativeProj A).scheme :=
  ((chartHomEquiv (A.grading U) hr hd X).symm ρ).1 ≫ (relativeProj A).chart U hU

/-- The morphism of `toRelativeProj` lies over the affine open it was built on. -/
public theorem toRelativeProj_comp_toBase (hr : r ∈ A.grading U d) (hd : 0 < d)
    (ρ : CommRingCat.of (HomogeneousLocalization.Away (A.grading U) r) ⟶ Γ(X, ⊤)) :
    toRelativeProj A U hU hr hd ρ ≫ (relativeProj A).toBase =
      ((chartHomEquiv (A.grading U) hr hd X).symm ρ).1 ≫
        projInclusionToOpen A U hU ≫ U.ι := by
  rw [toRelativeProj, Category.assoc, ((relativeProj A).chart_isPullback U hU).w]

/-- **A morphism into relative Proj from a ring map inverting one homogeneous section.** This is
the shape Tag 01NA's pairs take after dehomogenization at a generating degree-one section. -/
public def toRelativeProjOfIsUnit (φ : A.sectionRing U →+* Γ(X, ⊤)) (hd : 0 < d)
    (hr : r ∈ A.grading U d) (hu : IsUnit (φ r)) :
    X ⟶ (relativeProj A).scheme :=
  fromOfIsUnit (A.grading U) φ hd hr hu ≫ (relativeProj A).chart U hU

/-- The morphism of `toRelativeProjOfIsUnit` lies over the affine open it was built on. -/
public theorem toRelativeProjOfIsUnit_comp_toBase (φ : A.sectionRing U →+* Γ(X, ⊤)) (hd : 0 < d)
    (hr : r ∈ A.grading U d) (hu : IsUnit (φ r)) :
    toRelativeProjOfIsUnit A U hU φ hd hr hu ≫ (relativeProj A).toBase =
      fromOfIsUnit (A.grading U) φ hd hr hu ≫ projInclusionToOpen A U hU ≫ U.ι := by
  rw [toRelativeProjOfIsUnit, Category.assoc, ((relativeProj A).chart_isPullback U hU).w]

end Stacks.AlgebraicGeometry.ProjF1DegreeOneChart

end
