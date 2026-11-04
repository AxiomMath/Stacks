module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartFdRepresentation

/-!
# The chart-wise morphism of the class a morphism into the absolute `U_d` induces

`...RelativeProjQcohSheaf.Fd.chartHom` of
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartFdRepresentation` attaches to a
chart-wise class of `F_d(T)` — a class of quadruples for the restriction `𝒜|_U` to an affine open
`U` of the base — a morphism `T ⟶ X` into a relative homogeneous spectrum, through the absolute
representation of [Stacks, Tag 01NU] and the chart of `U`.

`...AffineTripleSections.fdOfHom` sends a morphism `φ : T ⟶ U_d(Γ(U, 𝒜))` into the absolute
degree-`d` open to the class of the quadruple obtained by pulling the universal family of
[Stacks, Tag 01N9] back along `φ`. This file computes `Fd.chartHom` on those classes.

## Main results

* `...RelativeProjQcohSheaf.Fd.chartEquiv_fdOfHom`: the absolute representation sends the class
  of `φ` back to `φ`, read through the grading identification
  `...SheafGradedAlgebra.restrictDegreeOpenHomEquiv`.
* `...RelativeProjQcohSheaf.Fd.chartHom_fdOfHom`: the chart-wise morphism of the class of `φ` is
  `φ ≫ U_d(Γ(U, 𝒜)).ι ≫ (chart of U)`.
* `...RelativeProjQcohSheaf.Fd.chartHom_fdOfHom_eq_degreeOpenChartIso`: the same morphism,
  factored through the open `U_d ⊓ f⁻¹(U)` of the relative `Proj`.

## References

* [Stacks Project, Tag 01NU](https://stacks.math.columbia.edu/tag/01NU)
* [Stacks Project, Tag 01N9](https://stacks.math.columbia.edu/tag/01N9)
* [Stacks Project, Tag 01NY](https://stacks.math.columbia.edu/tag/01NY)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S) (U : S.Opens) {k : ℕ}

/-! ### The absolute representation on the class of a morphism -/

/-- **The chart-wise representation sends the class of a morphism back to that morphism.** For an
affine open `U` of the base, `...AffineTripleSections.fdOfHom` sends a morphism
`φ : T ⟶ U_d(Γ(U, 𝒜))` to the class of the quadruple obtained by pulling the universal family of
[Stacks, Tag 01N9] back along it, and `...RelativeProjQcohSheaf.Fd.chartEquiv` is the absolute
representation of [Stacks, Tag 01NU] for `𝒜|_U`; the composite is `φ`, read through the
identification `...SheafGradedAlgebra.restrictDegreeOpenHomEquiv` of the degree-`d` open of
`Γ(U, 𝒜|_U)` with that of `𝒜` over `U`. -/
public theorem Fd.chartEquiv_fdOfHom (hU : IsAffineOpen U) (hk : 0 < k) (T : Scheme.{u})
    (φ : T ⟶ (AlgebraicGeometry.Proj.degreeOpen
      ((A.restrict U.ι).grading (⊤ : U.toScheme.Opens)) k).toScheme) :
    letI : IsAffine U.toScheme := hU
    Fd.chartEquiv A U hU hk T (AffineTripleSections.fdOfHom (A.restrict U.ι) φ hk)
      = SheafGradedAlgebra.restrictDegreeOpenHomEquiv A U k T φ :=
  let : IsAffine U.toScheme := hU
  congrArg (SheafGradedAlgebra.restrictDegreeOpenHomEquiv A U k T)
    (Quadruple.classifyingHomOfClass_fdOfHom (B := A.restrict U.ι) hk
      (fun n => (A.restrict U.ι).isQuasicoherent n) φ)

/-! ### The chart-wise morphism of the class of a morphism -/

variable (P : RelativeProjData A)

/-- **The chart-wise morphism attached to the class of `φ : T ⟶ U_d(Γ(U, 𝒜))` is `φ` followed by
the chart of `U`.** Over an affine open `U` of the base, the morphism
`...RelativeProjQcohSheaf.Fd.chartHom` attaches to the class of the pullback along `φ` of the
universal family of [Stacks, Tag 01N9] is

`φ ≫ U_d(Γ(U, 𝒜)).ι ≫ (chart of U)` ,

the grading identification `...SheafGradedAlgebra.restrictDegreeOpenHomEquiv` mediating between
the two spellings of the absolute degree-`d` open. -/
public theorem Fd.chartHom_fdOfHom (hU : IsAffineOpen U) (hk : 0 < k) (T : Scheme.{u})
    (φ : T ⟶ (AlgebraicGeometry.Proj.degreeOpen
      ((A.restrict U.ι).grading (⊤ : U.toScheme.Opens)) k).toScheme) :
    letI : IsAffine U.toScheme := hU
    Fd.chartHom A U P hU hk T (AffineTripleSections.fdOfHom (A.restrict U.ι) φ hk)
      = SheafGradedAlgebra.restrictDegreeOpenHomEquiv A U k T φ
          ≫ (AlgebraicGeometry.Proj.degreeOpen (A.grading U) k).ι ≫ P.chart U hU := by
  let : IsAffine U.toScheme := hU
  rw [Fd.chartHom_eq_comp A U P hU hk T (AffineTripleSections.fdOfHom (A.restrict U.ι) φ hk),
    Fd.chartEquiv_fdOfHom A U hU hk T φ]

/-- **The chart-wise morphism of the class of `φ`, read through the comparison of the chart with
`U_d ⊓ f⁻¹(U)`.** The chart-wise morphism attached to the class of `φ` factors through the open
`U_d ⊓ f⁻¹(U)` of the relative `Proj`, and the factor is `φ` followed by the comparison
`...RelativeProjData.degreeOpenChartIso`. -/
public theorem Fd.chartHom_fdOfHom_eq_degreeOpenChartIso (hU : IsAffineOpen U) (hk : 0 < k)
    (T : Scheme.{u})
    (φ : T ⟶ (AlgebraicGeometry.Proj.degreeOpen
      ((A.restrict U.ι).grading (⊤ : U.toScheme.Opens)) k).toScheme) :
    letI : IsAffine U.toScheme := hU
    Fd.chartHom A U P hU hk T (AffineTripleSections.fdOfHom (A.restrict U.ι) φ hk)
      = (SheafGradedAlgebra.restrictDegreeOpenHomEquiv A U k T φ
            ≫ (P.degreeOpenChartIso U hU k).hom)
          ≫ (P.toBase ⁻¹ᵁ U ⊓ P.degreeOpen k).ι := by
  let : IsAffine U.toScheme := hU
  rw [Category.assoc, P.degreeOpenChartIso_hom_fac U hU k,
    Fd.chartHom_fdOfHom A U P hU hk T φ]

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
