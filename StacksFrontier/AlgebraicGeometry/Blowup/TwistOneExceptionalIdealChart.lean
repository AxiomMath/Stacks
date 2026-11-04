module

public import StacksFrontier.AlgebraicGeometry.Blowup.TwistOneExceptionalIdeal

/-!
# The isomorphism `𝒪_{X'}(1) ≅ ℐ·𝒪_{X'}` on the standard affine charts

Let `X` be a scheme, `ℐ` a quasi-coherent sheaf of ideals and `b : X' ⟶ X` its blowup.
`AlgebraicGeometry.twistOneIsoExceptionalIdealModule` is part (3) of Stacks 02OS, glued from the
chartwise comparisons `AlgebraicGeometry.chartEquiv`.  This file records what the glued
isomorphism *is* on each standard affine chart `D₊(a⁽¹⁾)`, `a ∈ ℐ(U)`: a section `t` of
`𝒪_{X'}(1)` is sent to the function `(t / a⁽¹⁾) · b^♯(a)`, that is, it is divided by the
trivializing degree-one section `a⁽¹⁾` and multiplied by the pullback of `a`.  Nothing in this
formula refers to the exceptional divisor: it is the canonical map `𝒪_{X'}(1) ⟶ 𝒪_{X'}` that
sends the degree-one section `x⁽¹⁾` of `x ∈ ℐ` to `b^♯(x)`, so the isomorphism of Stacks 02OS (3)
is that canonical map, corestricted to its image.

## Main results

* `AlgebraicGeometry.twistOneIsoExceptionalIdealModule_hom_app_of_le`: over an open of the chart
  at `a`, the glued isomorphism is the chartwise comparison at `a`.
* `AlgebraicGeometry.incl_app_twistOneIsoExceptionalIdealModule_hom`: **the formula** — the image
  in `𝒪_{X'}` of the section attached to `t` is `(t / a⁽¹⁾) · b^♯(a)`.

## References

* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Stacks.SheafOfModules

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens) (a : I.ideal U)

/-- **On the chart at `a`, the isomorphism of Stacks 02OS (3) is the chartwise comparison at
`a`.**  The isomorphism is glued from the chartwise comparisons, and a glued comparison agrees
with each member of the family over the member's open
(`Stacks.SheafOfModules.OModuleLocalPresheaf.LocalEquiv.glueLinearEquiv_eq`). -/
theorem twistOneIsoExceptionalIdealModule_hom_app_of_le {V : (blowUp I).Opens}
    (hV : V ≤ (Stacks.BlowUpChartCover.chartOpen I U a).1)
    (t : ToType ((blowUpTwist I 1).val.obj (op V))) :
    ((twistOneIsoExceptionalIdealModule I).hom.val.app (op V)).hom t = chartEquiv I U a hV t :=
  (twistOneLocalEquiv I).glueLinearEquiv_eq
    (OModuleLocalPresheaf.isSheaf_ofSheafOfModules (blowUpTwist I 1) ⊤)
    (OModuleLocalPresheaf.isSheaf_ofSheafOfModules (exceptionalIdealModule I) ⊤) ⟨U, a⟩ hV t

/-- **The isomorphism `𝒪_{X'}(1) ≅ ℐ·𝒪_{X'}` of Stacks 02OS (3), on the chart at `a ∈ ℐ(U)`.**
The image in the structure sheaf of the section of the exceptional ideal sheaf attached to a
section `t` of `𝒪_{X'}(1)` is `t` divided by the trivializing section of the degree-one generator
`a⁽¹⁾`, times the pullback `b^♯(a)` of `a`
(`AlgebraicGeometry.chartGeneratorRes_eq_appLE`).  This is the description that makes the
isomorphism canonical: it is the map `𝒪_{X'}(1) ⟶ 𝒪_{X'}` induced by the shift `A(1) ⟶ A` of the
Rees algebra `A = ⨁ ℐⁿ`, and does not depend on `a`
(`AlgebraicGeometry.chartEquiv_agree`). -/
theorem incl_app_twistOneIsoExceptionalIdealModule_hom {V : (blowUp I).Opens}
    (hV : V ≤ (Stacks.BlowUpChartCover.chartOpen I U a).1)
    (t : ToType ((blowUpTwist I 1).val.obj (op V))) :
    ((Stacks.CartierAffineLocal.incl (exceptionalIdeal I)).val.app (op V)).hom
        (((twistOneIsoExceptionalIdealModule I).hom.val.app (op V)).hom t)
      = chartTwistCoeff I U a hV t * chartGeneratorRes I U a hV := by
  rw [twistOneIsoExceptionalIdealModule_hom_app_of_le I U a hV t]
  exact incl_app_chartEquiv I U a hV t

end AlgebraicGeometry

end
