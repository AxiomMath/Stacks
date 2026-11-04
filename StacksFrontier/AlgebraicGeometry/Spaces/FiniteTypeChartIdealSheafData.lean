module

public import StacksFrontier.AlgebraicGeometry.Sheaves.SectionsWithSupport.QuasiCompactOpenIdealSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSheafDataFromCartesian

/-!
# The chartwise sheaf of ideals of a finite type sheaf of ideals is of finite type

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, and let
`ℐ ⊆ 𝒪_X` be a quasi-coherent sheaf of ideals on its small étale site which is of finite type.
`AlgebraicGeometry.Space.idealSheafDataOfChart` turns `ℐ` into a Zariski sheaf of ideals on the
scheme of an étale chart of `X`.  That sheaf of ideals is of finite type in the sense of
`AlgebraicGeometry.Scheme.IdealSheafData.IsFiniteType`: its ideal over every affine open of the
chart is finitely generated.

## Main results

* `AlgebraicGeometry.Space.fg_chartIdeal_of_isFiniteTypeOnSite`: the ideal of sections of `ℐ`
  over an affine étale chart is finitely generated.
* `AlgebraicGeometry.Space.isFiniteType_idealSheafDataOfChart`: the chartwise Zariski sheaf of
  ideals is of finite type.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)

/-- The ideal of sections of a finite type quasi-coherent sheaf of ideals over an affine étale
chart is finitely generated. -/
theorem fg_chartIdeal_of_isFiniteTypeOnSite
    (hIq : I.toSheafOfModules.IsQuasicoherentOnSite)
    (hIft : SheafOfModules.IsFiniteTypeOnSite I.toSheafOfModules)
    (P : SmallEtale B S hS X.1)
    (hP : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj P)) :
    (chartIdeal B S hS X I P).FG :=
  Module.Finite.iff_fg.1 (module_finite_sections_of_isFiniteTypeOnSite
    (B := B) (S := S) (hS := hS) (F := X.1) (hF := X.2) I.toSheafOfModules hIq hIft P hP)

/-- The chartwise Zariski sheaf of ideals attached to a finite type quasi-coherent sheaf of
ideals is of finite type. -/
theorem isFiniteType_idealSheafDataOfChart
    (hIq : I.toSheafOfModules.IsQuasicoherentOnSite)
    (hIft : SheafOfModules.IsFiniteTypeOnSite I.toSheafOfModules)
    (hcart : IsCartesianOnAffineCharts I.toSheafOfModules)
    (A : SmallEtale B S hS X.1) :
    (idealSheafDataOfChart B S hS X I hcart A).IsFiniteType :=
  fun V => Ideal.FG.map (fg_chartIdeal_of_isFiniteTypeOnSite B S hS X I hIq hIft
    (openChart B S hS X.1 A V.1) V.2) _

end AlgebraicGeometry.Space

end
