module

public import StacksFrontier.Cotangent.AtiyahClassBigSiteCoefficientChange
public import StacksFrontier.Cotangent.DerivedLowerShriekRestrictedCoefficients
import StacksCore.Tactic.StacksAttribute

/-!
# The third displayed endpoint of the Atiyah triangle, at the site `C_{B/A}` itself

The triangle of [Stacks, Tag 09DD] is displayed with its first and third terms identified:

`L_{B/A} ⊗^𝐋_B M → Lπ_!(P¹_{𝒪/A}(M)) → M → L_{B/A} ⊗^𝐋_B M[1]`.

This file identifies the third term at the site `C_{B/A}` of [Stacks, Tag 08PR] itself, read on
its `CategoryTheory.AsSmall` model `CommAlgCat.atiyahSite`, which is where
`StacksFrontier/Cotangent/AtiyahClass.lean` forms the triangle:

`Lπ_!(M̲) = M`.

The `Lπ_!` of the triangle is the functor `D(𝒪) ⟶ D(B)` of [Stacks, Tag 09CZ], so the
identification is *not* [Stacks, Tag 08QE] directly: 08QE computes `Lπ_! : D(B̲) ⟶ D(B)`. The
passage between the two at a sheaf which is a `B̲`-module is
`Stacks.ChaoticSite.derivedColimitWithCoefficientsRestrictScalarsIso`, which rests on the change
of coefficients of [Stacks, Tag 08QJ] and asks for two inputs: a point resolution of the site,
which is `CommAlgCat.isPointResolution_atiyahStandardCosimplicialObject`, and that `L_nπ_!`
invert the augmentation `𝒪 ⟶ B̲`, which is
`CommAlgCat.coefficientInverted_atiyahCoefficientHom`.

The same statement on the small model of the footnote-restricted site is
`CommAlgCat.smallPolynomialAtiyahTriangleObj₃Iso`
(`StacksFrontier/Cotangent/AtiyahClassSmallSiteEndpoints.lean`). That is a statement about
different coefficients twice over: the restriction to a full subcategory of bounded-cardinality
augmentations changes both `Mod(B̲)` and `Lπ_!`, and its module `M` ranges over
`ModuleCat.{u} B` rather than over `ModuleCat.{u + 1} (ULift B)`, the coefficients of the site's
own ringed point `CommAlgCat.polynomialRingedPoint`. So neither statement implies the other, and
this one is proved rather than transported.

## Main results

* `CommAlgCat.polynomialAtiyahTriangleObj₃Iso`: **`Lπ_!(M̲) = M` in `D(B)`** -- the third term of
  the Atiyah triangle at the site `C_{B/A}` itself is `M`.

## References

* [Stacks Project, Tag 09DD](https://stacks.math.columbia.edu/tag/09DD)
* [Stacks Project, Tag 08QE](https://stacks.math.columbia.edu/tag/08QE)
* [Stacks Project, Tag 08QJ](https://stacks.math.columbia.edu/tag/08QJ)
* [Stacks Project, Tag 09CZ](https://stacks.math.columbia.edu/tag/09CZ)
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.SheafOfModules (moduleSheaves)

universe u

attribute [local instance 2000] HasDerivedCategory.standard

namespace CommAlgCat

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A)
  (M : ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u)))

/-- **`Lπ_!(M̲) = M` in `D(B)`: the third term of the Atiyah triangle at the site `C_{B/A}`
itself is `M`.** The `Lπ_!` here is the functor `D(𝒪) ⟶ D(B)` of [Stacks, Tag 09CZ];
`Stacks.ChaoticSite.derivedColimitWithCoefficientsRestrictScalarsIso` replaces it by
`Lπ_! : D(B̲) ⟶ D(B)` at the `𝒪`-module underlying the constant `B̲`-module `M`, and
[Stacks, Tag 08QE] -- `CommAlgCat.atiyahModuleDerivedInverseImageCompLowerShriekIso` -- computes
that to be `M`. -/
def polynomialAtiyahTriangleObj₃Iso :
    (polynomialAtiyahTriangle A B M).obj₃ ≅
      (DerivedCategory.singleFunctor
        (ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u))) 0).obj M :=
  (Stacks.Atiyah.lowerShriek (O₂ := atiyahStructureSheaf A B)
        (ULift.{u + 1} (B : Type u)) (atiyahCoefficientHom A B)).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ
        (PresheafOfModules.{u + 1} (atiyahRingSheaf A B).obj) 0).app _) ≪≫
    Stacks.ChaoticSite.derivedColimitWithCoefficientsRestrictScalarsIso
      (atiyahCoefficientHom A B)
      (atiyahStandardCosimplicialObject A B)
      (isPointResolution_atiyahStandardCosimplicialObject A B)
      (coefficientInverted_atiyahCoefficientHom A B)
      ((Stacks.ChaoticSite.constantModulePresheafEquivalence
        (ULift.{u + 1} (B : Type u))).inverse.obj ((Functor.const _).obj M)) ≪≫
    (Stacks.CategoryHomology.totalDerivedColimit _
        (ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u)))).mapIso
      (DerivedCategory.Q.mapIso ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).mapIso
        ((Stacks.ChaoticSite.constantModulePresheafEquivalence
          (ULift.{u + 1} (B : Type u))).counitIso.app ((Functor.const _).obj M)))) ≪≫
    (Stacks.CategoryHomology.totalDerivedColimit _
        (ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u)))).mapIso
      (DerivedCategory.Q.mapIso ((HomologicalComplex.singleMapHomologicalComplex
        (Functor.const (atiyahSite A B)ᵒᵖ :
            ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u)) ⥤ _)
          (ComplexShape.up ℤ) 0).app M).symm) ≪≫
    (Stacks.CategoryHomology.totalDerivedColimit _
        (ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u)))).mapIso
      (((Functor.const (atiyahSite A B)ᵒᵖ :
          ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u)) ⥤ _).mapDerivedCategoryFactors.app
            ((HomologicalComplex.single (ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u)))
              (ComplexShape.up ℤ) 0).obj M)).symm) ≪≫
    (atiyahModuleDerivedInverseImageCompLowerShriekIso A B).app
      (DerivedCategory.Q.obj
        ((HomologicalComplex.single (ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u)))
          (ComplexShape.up ℤ) 0).obj M)) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ
      (ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u))) 0).app M).symm

end CommAlgCat

end
