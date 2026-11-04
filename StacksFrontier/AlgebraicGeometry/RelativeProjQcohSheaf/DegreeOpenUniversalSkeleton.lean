module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartDegreeOpenEquiv

/-!
# The universal element of `F_d` on the relative degree-`d` locus

`Fd.homDegreeOpen` is a bijection `F_d(W) ≃ Mor(W, U_d)`, where `U_d` is the relative degree-`d`
locus. A class of `F_d(U_d)` whose chart-wise morphisms are the chart inclusions is sent to
`𝟙 U_d`, and every class of `F_d(W)` is the pullback of such a class along the morphism it
classifies.

## Main results

* `Fd.homDegreeOpen_eq_id_of_chartHom`: a class of `F_d(U_d)` over the structure morphism whose
  chart-wise morphisms are the chart inclusions is sent by `Fd.homDegreeOpen` to `𝟙 U_d`.
* `Fd.pullback_eq_of_homDegreeOpen_eq_id`: if `Fd.homDegreeOpen` sends `ξ` to `𝟙 U_d`, then every
  class is the pullback of `ξ` along the morphism it classifies.

## References

* [Stacks Project, Tag 01O1](https://stacks.math.columbia.edu/tag/01O1)
* [Stacks Project, Tag 01NY](https://stacks.math.columbia.edu/tag/01NY)
* [Stacks Project, Tag 01N9](https://stacks.math.columbia.edu/tag/01N9)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S) (P : RelativeProjData A) {k : ℕ}

/-! ### The class whose charts are the chart inclusions is the universal element -/

/-- A class `ξ` of `F_d(U_d)` whose chart-wise morphisms are the chart inclusions is sent by
`Fd.homDegreeOpen` to the identity of `U_d`.

The hypothesis is that for every affine open `U` of the base and every chart-wise class `η` whose
`Fd.chartClassInv` is the restriction of `ξ` to `ξ.1 ⁻¹ᵁ U`, the chart-wise morphism `Fd.chartHom`
of `η` is the inclusion of `ξ.1 ⁻¹ᵁ U` into the relative `Proj` through `U_d`. -/
public theorem Fd.homDegreeOpen_eq_id_of_chartHom (hk : 0 < k)
    (ξ : Fd (situationAlgebra A) (k : ℤ) (P.degreeOpen k).toScheme)
    (hchart : ∀ (U : S.Opens) (hU : IsAffineOpen U)
      (η : Fd (situationAlgebra (A.restrict U.ι)) (k : ℤ) (ξ.1 ⁻¹ᵁ U).toScheme),
      Fd.chartClassInv A U η = Fd.pullback (ξ.1 ⁻¹ᵁ U).ι ξ →
      Fd.chartHom A U P hU hk _ η = (ξ.1 ⁻¹ᵁ U).ι ≫ (P.degreeOpen k).ι) :
    Fd.homDegreeOpen A P hk ξ = CategoryStruct.id (P.degreeOpen k).toScheme :=
  (Fd.eq_homDegreeOpen A P hk ξ (CategoryStruct.id _) fun U hU η hη =>
    Eq.trans
      (congrArg ((ξ.1 ⁻¹ᵁ U).ι ≫ ·) (Category.id_comp ((P.degreeOpen k).ι)))
      (hchart U hU η hη).symm).symm

/-! ### Every class is then the pullback of the universal one -/

/-- If `Fd.homDegreeOpen` sends `ξ` to the identity of `U_d`, then every class `ζ` of `F_d(W)` is
the pullback of `ξ` along the morphism `Fd.homDegreeOpen ζ` that `ζ` classifies. -/
public theorem Fd.pullback_eq_of_homDegreeOpen_eq_id (hk : 0 < k) {W : Scheme.{u}}
    (ξ : Fd (situationAlgebra A) (k : ℤ) (P.degreeOpen k).toScheme)
    (hξ : Fd.homDegreeOpen A P hk ξ = CategoryStruct.id (P.degreeOpen k).toScheme)
    (ζ : Fd (situationAlgebra A) (k : ℤ) W) :
    Fd.pullback (Fd.homDegreeOpen A P hk ζ) ξ = ζ :=
  Fd.homDegreeOpen_injective A P hk W
    (Eq.trans (Fd.homDegreeOpen_pullback' A P hk (Fd.homDegreeOpen A P hk ζ) ξ)
      (Eq.trans (congrArg (Fd.homDegreeOpen A P hk ζ ≫ ·) hξ)
        (Category.comp_id _)))

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
