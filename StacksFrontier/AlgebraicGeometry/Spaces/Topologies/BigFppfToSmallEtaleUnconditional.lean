module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfToSmallEtaleSchemeVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfToSmallEtaleSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfToSmallEtaleDerived
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfToSmallEtaleCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfToSmallEtaleFinitePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfToSmallEtaleProperDerivedPushforward

/-!
# Comparing the big fppf and the small étale topoi of an algebraic space

Let `S` be a scheme, `X` an algebraic space over `S` and `a_X : Sh((Spaces/X)_fppf) ⟶ Sh(X_étale)`
the comparison morphism of Stacks 0DGI, factored as `a_X = π_X ∘ ε_X`. The results of the files
`BigFppfToSmallEtale{Sheaf,HigherVanishing,Derived,Cohomology,FinitePushforward,
ProperDerivedPushforward}.lean` are proved there from the scheme case
`AlgebraicGeometry.SchemeFppfEtaleHigherVanishing` of Stacks 0DDS (1). That case is now the theorem
`AlgebraicGeometry.schemeFppfEtaleHigherVanishing`, so this file states them without it.

## Main results

* `AlgebraicGeometry.BigFppfSpaceSite.isIso_fppfToSmallEtale_units_and_isZero_rightDerived`:
  **Stacks 0DGF**, both parts.
* `AlgebraicGeometry.BigFppfSpaceSite.isIso_fppfToSmallEtale_derivedUnits`: **Stacks 0DGG**.
* `AlgebraicGeometry.BigFppfSpaceSite.etaleCohomologyIso`,
  `AlgebraicGeometry.BigFppfSpaceSite.isIso_etaleToFppfCohomology` and
  `AlgebraicGeometry.BigFppfSpaceSite.etaleCohomologyConstantIso`: **Stacks 0DGH**, parts (1)
  and (2) and the example.
* `AlgebraicGeometry.BigFppfSpaceSite.isIso_fppfToSmallEtaleDerivedBaseChange`: **Stacks 0DGK**.
* `AlgebraicGeometry.BigFppfSpaceSite.isIso_fppfToSmallEtaleProperDerivedBaseChange_app`:
  **Stacks 0DGJ, part (2)**.

## Implementation notes

The statements on `D⁺` hold in any model of the derived categories (`[HasDerivedCategory _]`),
except Stacks 0DGJ (2). Its comparison map is built from the base change map of Stacks 0DGD (2),
`AlgebraicGeometry.BigEtaleSpaceSite.bigToSmallEtaleDerivedBaseChange`, which is stated in the
model `HasDerivedCategory.standard`; that section uses that model, as
`BigFppfToSmallEtaleProperDerivedPushforward.lean` does. Parts (1) and the example of Stacks 0DGH
do not mention a derived category; their proofs go through `D⁺` in the standard model.

## References

* [Stacks Project, Tag 0DGF](https://stacks.math.columbia.edu/tag/0DGF)
* [Stacks Project, Tag 0DGG](https://stacks.math.columbia.edu/tag/0DGG)
* [Stacks Project, Tag 0DGH](https://stacks.math.columbia.edu/tag/0DGH)
* [Stacks Project, Tag 0DGJ](https://stacks.math.columbia.edu/tag/0DGJ)
* [Stacks Project, Tag 0DGK](https://stacks.math.columbia.edu/tag/0DGK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.BigFppfSpaceSite

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

-- `BigEtaleSpaceSite.bigToSmallAbelianInverseImage_additive` is a `local instance` of
-- `BigSmallEtaleCohomology.lean`, so the attribute is re-enabled here.
attribute [local instance] BigEtaleSpaceSite.bigToSmallAbelianInverseImage_additive

variable {S : Scheme.{u}} (T : BigFppfSpaceSite S) (E : BigEtaleSpaceSite S)
  (h : T.schemeSite = E.fppfSite)

/-- **Stacks 0DGF.** Let `X` be an algebraic space over `S`.
(1) For a sheaf of sets `F` on `X_étale`, `ε_{X,*}a_X⁻¹F = π_X⁻¹F` and `a_{X,*}a_X⁻¹F = F`: the
units `π_X⁻¹F ⟶ ε_{X,*}ε_X⁻¹π_X⁻¹F` and `F ⟶ a_{X,*}a_X⁻¹F` are isomorphisms.
(2) For an abelian sheaf `F` on `X_étale`, `R^iε_{X,*}(a_X⁻¹F) = 0` for `i > 0`. -/
@[stacks 0DGF]
theorem isIso_fppfToSmallEtale_units_and_isZero_rightDerived (X : T.Spaces) :
    (IsIso (Functor.whiskerLeft (E.bigToSmallEtaleMorphism (etaleSpace T E h X)).inverseImage
        (fppfToBigEtaleMorphism T E h X).adj.unit) ∧
      IsIso (fppfToSmallEtaleMorphism T E h X).adj.unit) ∧
    ∀ (F : Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem (etaleSpace T E h X))
      AddCommGrpCat.{u + 1}) (i : ℕ), 0 < i →
      IsZero ((((Over.postEquiv (canonicalSpaceEquivalence T E h).1
        (X := X)).inverse.sheafPushforwardContinuous
        AddCommGrpCat.{u + 1} (E.bigEtaleTopology (etaleSpace T E h X))
        (BigFppfSpaceOver.topology T X)).rightDerived i).obj
          ((CategoryTheory.Sites.abelianInverseImage (fppfToSmallEtaleMorphism T E h X)).obj F)) :=
  ⟨isIso_fppfToBigEtale_unit_whiskerLeft_and_isIso_fppfToSmallEtale_unit T E h X,
    fun F i hi ↦ isZero_rightDerived_fppfToBigEtale_abelianInverseImage_of T E h X
      (schemeFppfEtaleHigherVanishing E.fppfSite) F i hi⟩

section Units

variable (X : T.Spaces)
  [HasDerivedCategory (Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem
    (etaleSpace T E h X)) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory (Sheaf (E.bigEtaleTopology (etaleSpace T E h X)) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory (Sheaf (BigFppfSpaceOver.topology T X) AddCommGrpCat.{u + 1})]

/-- **Stacks 0DGG.** For `K` in `D⁺(X_étale)` the maps `π_X⁻¹K ⟶ Rε_{X,*}a_X⁻¹K` and
`K ⟶ Ra_{X,*}a_X⁻¹K` are isomorphisms: the units of the derived adjunctions `ε_X⁻¹ ⊣ Rε_{X,*}`
at `π_X⁻¹K` and `a_X⁻¹ ⊣ Ra_{X,*}` at `K`. -/
@[stacks 0DGG]
theorem isIso_fppfToSmallEtale_derivedUnits
    (K : DerivedCategory.Plus (Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem
      (etaleSpace T E h X)) AddCommGrpCat.{u + 1})) :
    IsIso ((Stacks.ComparingTopologies.derivedPlusAdjunction
        (fppfToBigEtaleAbelianAdjunction T E h X)).unit.app
          ((CategoryTheory.Sites.abelianInverseImage
            (E.bigToSmallEtaleMorphism (etaleSpace T E h X))).mapDerivedCategoryPlus.obj K)) ∧
      IsIso ((Stacks.ComparingTopologies.derivedPlusAdjunction
        (fppfToSmallEtaleAbelianAdjunction T E h X)).unit.app K) :=
  isIso_fppfToSmallEtale_derivedUnits_of T E h X (schemeFppfEtaleHigherVanishing E.fppfSite) K

variable [HasDerivedCategory AddCommGrpCat.{u + 1}]

/-- The canonical map `RΓ(X_étale, K) ⟶ RΓ_fppf(X, a_X⁻¹K)` is an isomorphism for every `K` in
`D⁺(X_étale)`. -/
theorem isIso_etaleToFppfDerivedGlobalSections :
    IsIso (etaleToFppfDerivedGlobalSections T E h X) :=
  isIso_etaleToFppfDerivedGlobalSections_of T E h X (schemeFppfEtaleHigherVanishing E.fppfSite)

/-- **Stacks 0DGH, part (2).** For `K` in `D⁺(X_étale)`, `H^q(X_étale, K) = H^q_fppf(X, a_X⁻¹K)`
for every `q`: the map induced on `H^q` by the canonical map
`AlgebraicGeometry.BigFppfSpaceSite.etaleToFppfDerivedGlobalSections` is an isomorphism, naturally
in `K`. -/
@[stacks 0DGH "(2)"]
theorem isIso_etaleToFppfCohomology (q : ℤ) :
    IsIso (Functor.whiskerRight (etaleToFppfDerivedGlobalSections T E h X)
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} q)) :=
  isIso_etaleToFppfCohomology_of T E h X (schemeFppfEtaleHigherVanishing E.fppfSite) q

end Units

section FinitePushforward

variable {X Y : T.Spaces} (f : Y ⟶ X)
  [HasDerivedCategory (Sheaf (BigFppfSpaceOver.topology T X) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory (Sheaf (BigFppfSpaceOver.topology T Y) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory (Sheaf (E.bigEtaleTopology (etaleSpace T E h X)) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory (Sheaf (E.bigEtaleTopology (etaleSpace T E h Y)) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory (Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem
    (etaleSpace T E h X)) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory (Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem
    (etaleSpace T E h Y)) AddCommGrpCat.{u + 1})]

/-- **Stacks 0DGK.** For a finite morphism `f : Y ⟶ X` of algebraic spaces,
`a_X⁻¹(Rf_{small,*}K) = Rf_{big,fppf,*}(a_Y⁻¹K)` for `K` in `D⁺(Y_étale)`: the base change map
`AlgebraicGeometry.BigFppfSpaceSite.fppfToSmallEtaleDerivedBaseChange`, the mate of
`Rf_{small,*} ∘ Ra_{Y,*} = Ra_{X,*} ∘ Rf_{big,fppf,*}`, is an isomorphism. -/
@[stacks 0DGK]
theorem isIso_fppfToSmallEtaleDerivedBaseChange
    (hf : Space.IsFinite T.schemeSite S T.scheme_mem f.hom) :
    IsIso (fppfToSmallEtaleDerivedBaseChange T E h f) :=
  isIso_fppfToSmallEtaleDerivedBaseChange_of T E h f (schemeFppfEtaleHigherVanishing E.fppfSite) hf

end FinitePushforward

section StandardModel

-- Stacks 0DGD (2), `BigEtaleSpaceSite.bigToSmallEtaleDerivedBaseChange`, is stated in the
-- standard model, as in `BigFppfToSmallEtaleProperDerivedPushforward.lean`.
attribute [local instance] HasDerivedCategory.standard

/-- **Stacks 0DGH, part (1).** For an abelian sheaf `F` on `X_étale`,
`H^q(X_étale, F) = H^q_fppf(X, a_X⁻¹F)` for every `q`, by the canonical map
`AlgebraicGeometry.BigFppfSpaceSite.etaleToFppfDerivedGlobalSections` at `F[0]`. -/
@[stacks 0DGH "(1)"]
def etaleCohomologyIso (X : T.Spaces)
    (F : Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem (etaleSpace T E h X))
      AddCommGrpCat.{u + 1}) (q : ℕ) :
    ((etaleGlobalSections T E h X).rightDerived q).obj F ≅
      ((fppfGlobalSections T X).rightDerived q).obj
        ((CategoryTheory.Sites.abelianInverseImage (fppfToSmallEtaleMorphism T E h X)).obj F) :=
  etaleCohomologyIso_of T E h X (schemeFppfEtaleHigherVanishing E.fppfSite) F q

/-- **The example of Stacks 0DGH.** For an abelian group `A`,
`H^q_étale(X, A) = H^q_fppf(X, A)` for the constant sheaves. -/
@[stacks 0DGH "the example of an abelian group"]
def etaleCohomologyConstantIso (X : T.Spaces) (A : AddCommGrpCat.{u + 1}) (q : ℕ) :
    ((etaleGlobalSections T E h X).rightDerived q).obj
        ((constantSheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem (etaleSpace T E h X))
          AddCommGrpCat.{u + 1}).obj A) ≅
      ((fppfGlobalSections T X).rightDerived q).obj
        ((constantSheaf (BigFppfSpaceOver.topology T X) AddCommGrpCat.{u + 1}).obj A) :=
  etaleCohomologyConstantIso_of T E h X (schemeFppfEtaleHigherVanishing E.fppfSite) A q

variable {X Y : T.Spaces} (f : Y ⟶ X)

/-- The comparison `a_X⁻¹(Rf_{small,*}K) ⟶ Rf_{big,fppf,*}(a_Y⁻¹K)` of Stacks 0DGJ (2) on
`D⁺(Y_étale)`, induced by the base change map `π_X⁻¹(Rf_{small,*}K) ⟶ Rf_{big,étale,*}(π_Y⁻¹K)`
of Stacks 0DGD (2). -/
def fppfToSmallEtaleProperDerivedBaseChange :
    (E.smallEtalePushforward (etaleMap T E h f)).rightDerivedFunctorPlus ⋙
        (CategoryTheory.Sites.abelianInverseImage
          (fppfToSmallEtaleMorphism T E h X)).mapDerivedCategoryPlus ⟶
      (CategoryTheory.Sites.abelianInverseImage
          (fppfToSmallEtaleMorphism T E h Y)).mapDerivedCategoryPlus ⋙
        (fppfAbelianPushforward T f).rightDerivedFunctorPlus :=
  fppfToSmallEtaleDerivedBaseChange_of T E h f (schemeFppfEtaleHigherVanishing E.fppfSite)

/-- **Stacks 0DGJ, part (2).** For a proper morphism `f : Y ⟶ X` of algebraic spaces and `K` in
`D⁺(Y_étale)` with torsion cohomology sheaves, `a_X⁻¹(Rf_{small,*}K) = Rf_{big,fppf,*}(a_Y⁻¹K)`:
the comparison map `AlgebraicGeometry.BigFppfSpaceSite.fppfToSmallEtaleProperDerivedBaseChange`
is an isomorphism at `K`. -/
@[stacks 0DGJ "(2)"]
theorem isIso_fppfToSmallEtaleProperDerivedBaseChange_app
    (hf : Space.IsProper T.schemeSite S T.scheme_mem f.hom)
    (K : DerivedCategory.Plus (Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem
      (etaleSpace T E h Y)) AddCommGrpCat.{u + 1}))
    (hK : BigEtaleSpaceSite.HasTorsionCohomology E (DerivedCategory.Plus.ι.obj K)) :
    IsIso ((fppfToSmallEtaleProperDerivedBaseChange T E h f).app K) :=
  isIso_fppfToSmallEtaleDerivedBaseChange_of_app_of_isProper T E h f
    (schemeFppfEtaleHigherVanishing E.fppfSite) hf K hK

end StandardModel

end AlgebraicGeometry.BigFppfSpaceSite

end
