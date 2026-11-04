module

public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportDerivedHomPushforward
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportPushforwardInternalHom

/-!
# Derived internal Hom out of a derived pushforward

Let `i : Z ⟶ X` be a closed quotient morphism of ringed spaces, so that pushforward
`i_* : Mod(𝒪_Z) ⥤ Mod(𝒪_X)` is exact and left adjoint to sheaf Hom with exact support
`ℰom(𝒪_Z, -) : Mod(𝒪_X) ⥤ Mod(𝒪_Z)`. For `M` in `D(𝒪_Z)` and `K` in `D(𝒪_X)`,

`R ℋom_{𝒪_X}(Ri_* M, K) ≅ Ri_* R ℋom_{𝒪_Z}(M, R ℰom(𝒪_Z, K))` in `D(𝒪_X)`.

## Main definitions

* `pushforwardSheafHomComplexIsoSite`: the isomorphism of complexes
  `i_* ℋom^•_{𝒪_Z}(ℳ, ℰom^•(𝒪_Z, 𝒦)) ≅ ℋom^•_{𝒪_X}(i_* ℳ, 𝒦)`, with both internal Hom complexes
  those of the ringed sites of `Z` and `X`.
* `derivedSheafHomDerivedModulePushforwardIso'`: the isomorphism
  `R ℋom_{𝒪_X}(Ri_* M, K) ≅ Ri_* R ℋom_{𝒪_Z}(M, R ℰom(𝒪_Z, K))` in `D(𝒪_X)`.

## References

* [Stacks Project, Tag 0E2I](https://stacks.math.columbia.edu/tag/0E2I)
* [Stacks Project, Tag 0A75](https://stacks.math.columbia.edu/tag/0A75)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open RingedSpaceModuleAdjunction

attribute [local instance] HasDerivedCategory.standard

universe u

namespace RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

variable (S : ClosedQuotientMorphismOfRingedSpaces.{u})

/-- The isomorphism of complexes `i_* ℋom^•_{𝒪_Z}(N, ℰom^•(𝒪_Z, I)) ≅ ℋom^•_{𝒪_X}(i_* N, I)`,
with both internal Hom complexes those of the ringed sites of `Z` and of `X`. -/
noncomputable def pushforwardSheafHomComplexIsoSite
    (N : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.closedSite.O)) ℤ)
    (I : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.ambientSite.O)) ℤ) :
    (S.siteModulePushforward.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (RingedSite.sheafHomComplex S.closedSite N
          ((S.siteSheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)).obj ≅
      (RingedSite.sheafHomComplex S.ambientSite
        ((S.siteModulePushforward.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) I).obj :=
  pushforwardSheafHomComplexIso S.pushforwardInternalHom
    (Stacks.SheafOfModules.sheafHomComplexComparison S.X.sheaf) N I

/-- For `M` in `D(𝒪_Z)` and `K` in `D(𝒪_X)`, the isomorphism

`R ℋom_{𝒪_X}(Ri_* M, K) ≅ Ri_* R ℋom_{𝒪_Z}(M, R ℰom(𝒪_Z, K))` in `D(𝒪_X)`. -/
noncomputable def derivedSheafHomDerivedModulePushforwardIso'
    (M : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.closedSite.O)))
    (K : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.ambientSite.O))) :
    ((RingedSite.derivedSheafHomBifunctor S.ambientSite).obj
          (op (S.siteModulePushforward.mapDerivedCategory.obj M))).obj K ≅
      S.siteModulePushforward.mapDerivedCategory.obj
        (((RingedSite.derivedSheafHomBifunctor S.closedSite).obj (op M)).obj
          (S.siteDerivedSheafHomExactSupport.obj K)) :=
  S.derivedSheafHomDerivedModulePushforwardIso S.pushforwardSheafHomComplexIsoSite M K

end RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

end
