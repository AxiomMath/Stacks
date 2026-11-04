module

public import StacksFrontier.Cotangent.AtiyahClassBigSiteEndpoints
public import StacksFrontier.Cotangent.AtiyahClassBigSiteFirstVertex

/-!
# The first vertex of the Atiyah triangle at `C_{B/A}` is an extended Moore complex

At the site `C_{B/A}` of [Stacks, Tag 08PR] itself -- read on its `CategoryTheory.AsSmall` model
`CommAlgCat.atiyahSite`, where `StacksFrontier/Cotangent/AtiyahClass.lean` forms the triangle of
[Stacks, Tag 09DD] -- the first vertex of that triangle is computed here as an extended Moore
complex on the standard resolution:

`Lπ_!(Ω_{𝒪/A} ⊗_𝒪 M̲) ≅ Q(Moore((M ⊗_{B̲} (B̲ ⊗_𝒪 Ω_{𝒪/A}))(P_•, ε)))` in `D(B)`.

The isomorphism is the composite of four steps:

1. the vertex as the plain objectwise tensor product,
   `CommAlgCat.atiyahFirstVertexTensorIso`, which undoes the sheafification and the
   corepresenting-object spelling;
2. that tensor product as the `𝒪`-module underlying a `B̲`-module,
   `CommAlgCat.atiyahFirstVertexRestrictionIso`, which is the projection formula;
3. the replacement of `Lπ_! : D(𝒪) ⟶ D(B)` of [Stacks, Tag 09CZ] by `Lπ_! : D(B̲) ⟶ D(B)` at a
   module of that form, `Stacks.ChaoticSite.derivedColimitWithCoefficientsRestrictScalarsIso`,
   which rests on the change of coefficients of [Stacks, Tag 08QJ] -- its two inputs at this site
   being `CommAlgCat.isPointResolution_atiyahStandardCosimplicialObject` and
   `CommAlgCat.coefficientInverted_atiyahCoefficientHom`;
4. the computation of the latter as an extended Moore complex on a point resolution,
   `Stacks.ChaoticSite.ModuleValued.mooreCochainQIsoDerivedColimit`, the derived form of
   [Stacks, Tag 08PT].

The analogous statement on the small model of the footnote-restricted site is
`CommAlgCat.smallAtiyahFirstVertexMooreIso`
(`StacksFrontier/Cotangent/AtiyahClassSmallSiteFirstVertexDerived.lean`); it is a statement about
different coefficients, the restriction to a full subcategory changing both `Mod(B̲)` and `Lπ_!`,
and its module `M` ranging over `ModuleCat.{u} B` rather than over the
`ModuleCat.{u + 1} (ULift B)` of the site's own ringed point. Neither implies the other.

## Main definitions

* `CommAlgCat.atiyahFirstVertexConstantModule`: the `B̲`-module `M ⊗_{B̲} (B̲ ⊗_𝒪 Ω_{𝒪/A})`,
  whose `𝒪`-module of restricted scalars is the first vertex before `Lπ_!`.

## Main results

* `CommAlgCat.atiyahFirstVertexMooreIso`: **the first vertex of the Atiyah triangle at
  `C_{B/A}` is the extended Moore complex of `M ⊗_{B̲} (B̲ ⊗_𝒪 Ω_{𝒪/A})` evaluated on the
  standard resolution.**

## References

* [Stacks Project, Tag 09DD](https://stacks.math.columbia.edu/tag/09DD)
* [Stacks Project, Tag 08PT](https://stacks.math.columbia.edu/tag/08PT)
* [Stacks Project, Tag 08PU](https://stacks.math.columbia.edu/tag/08PU)
* [Stacks Project, Tag 08QJ](https://stacks.math.columbia.edu/tag/08QJ)
* [Stacks Project, Tag 09CZ](https://stacks.math.columbia.edu/tag/09CZ)
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.SheafOfModules (moduleSheaves)
open Stacks.ChaoticSite.ModuleValued

universe u

attribute [local instance 2000] HasDerivedCategory.standard

namespace CommAlgCat

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A)
  (M : ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u)))

/-- **The `B̲`-module `M ⊗_{B̲} (B̲ ⊗_𝒪 Ω_{𝒪/A})`** on `CommAlgCat.atiyahSite`, whose
`𝒪`-module of restricted scalars is the first vertex of the Atiyah triangle before `Lπ_!`. Its
sections over `(P, α)` are `M ⊗_{ULift B} (ULift B ⊗_{ULift P} Ω[ULift P ⁄ ULift A])`. -/
abbrev atiyahFirstVertexConstantModule :
    PresheafOfModules.{u + 1} ((Functor.const (atiyahSite A B)ᵒᵖ).obj
      (RingCat.of (ULift.{u + 1} (B : Type u)))) :=
  (Stacks.tensorRight (O := (atiyahConstantSheaf A B).obj)
      ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings
        (atiyahAugmentationComm A B).hom).obj
          (atiyahRelativeDifferentialsPresheaf A B))).obj
    (atiyahModuleOverConstant A B M)

/-- **The first vertex of the Atiyah triangle at the site `C_{B/A}` itself is the extended Moore
complex of `M ⊗_{B̲} (B̲ ⊗_𝒪 Ω_{𝒪/A})` evaluated on the standard resolution.**

`Lπ_!(Ω_{𝒪/A} ⊗_𝒪 M̲) ≅ Q(Moore((M ⊗_{B̲} (B̲ ⊗_𝒪 Ω_{𝒪/A}))(P_•, ε)))` in `D(B)`.

The four steps are listed in the module documentation: the vertex is first stripped of the
sheafification and of the corepresenting-object spelling of its tensor factor
(`CommAlgCat.atiyahFirstVertexTensorIso`), then recognised as the `𝒪`-module underlying a
`B̲`-module by the projection formula (`CommAlgCat.atiyahFirstVertexRestrictionIso`), after which
`Lπ_!` of [Stacks, Tag 09CZ] is replaced by `Lπ_! : D(B̲) ⟶ D(B)`
(`Stacks.ChaoticSite.derivedColimitWithCoefficientsRestrictScalarsIso`) and the latter computed
by the derived form of [Stacks, Tag 08PT] on the standard resolution
(`Stacks.ChaoticSite.ModuleValued.mooreCochainQIsoDerivedColimit`). -/
def atiyahFirstVertexMooreIso :
    (polynomialAtiyahTriangle A B M).obj₁ ≅
      DerivedCategory.Q.obj
        ((mooreCochainComplex (atiyahStandardCosimplicialObject A B)).obj
          ((Stacks.ChaoticSite.constantModulePresheafEquivalence
              (ULift.{u + 1} (B : Type u))).functor.obj
            (atiyahFirstVertexConstantModule A B M))) :=
  (Stacks.Atiyah.lowerShriek (O₂ := atiyahStructureSheaf A B)
        (ULift.{u + 1} (B : Type u)) (atiyahCoefficientHom A B)).mapIso
      ((DerivedCategory.singleFunctor
            (PresheafOfModules.{u + 1} (atiyahRingSheaf A B).obj) 0).mapIso
        (atiyahFirstVertexTensorIso A B M ≪≫ atiyahFirstVertexRestrictionIso A B M)) ≪≫
    (Stacks.Atiyah.lowerShriek (O₂ := atiyahStructureSheaf A B)
        (ULift.{u + 1} (B : Type u)) (atiyahCoefficientHom A B)).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ
        (PresheafOfModules.{u + 1} (atiyahRingSheaf A B).obj) 0).app _) ≪≫
    Stacks.ChaoticSite.derivedColimitWithCoefficientsRestrictScalarsIso
      (atiyahCoefficientHom A B)
      (atiyahStandardCosimplicialObject A B)
      (isPointResolution_atiyahStandardCosimplicialObject A B)
      (coefficientInverted_atiyahCoefficientHom A B)
      (atiyahFirstVertexConstantModule A B M) ≪≫
    (mooreCochainQIsoDerivedColimit (atiyahStandardCosimplicialObject A B)
      ((Stacks.ChaoticSite.constantModulePresheafEquivalence
          (ULift.{u + 1} (B : Type u))).functor.obj
        (atiyahFirstVertexConstantModule A B M))
      (isPointResolution_atiyahStandardCosimplicialObject A B)).symm

end CommAlgCat

end
