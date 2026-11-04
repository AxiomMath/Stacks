module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigPhSmallEtaleTorsionVanishing
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.DerivedPlusAdjunctionUnitIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigPhSmallEtalePullbackSheaf
public import StacksFrontier.AlgebraicGeometry.ProEtale.BigSmall.AbelianSheaves
public import StacksFrontier.CategoryTheory.Sites.Modules.InverseImage.AbelianSheaf

/-!
# The ph and étale abelian sheaves of an algebraic space

Let `P` be a big ph site of algebraic spaces over a scheme `S`, `E` a big étale site of algebraic
spaces over the same big fppf site of schemes, and `X` an algebraic space. With `a_X = π_X ∘ ε_X`
from the big ph topos of `X` to its small étale topos, the adjunctions `ε_X⁻¹ ⊣ ε_{X,*}` and
`a_X⁻¹ ⊣ a_{X,*}` on abelian sheaves are constructed, together with the identifications
`ε_{X,*}a_X⁻¹ = π_X⁻¹` and `a_{X,*}a_X⁻¹ = 𝟭`.

## Main definitions

* `AlgebraicGeometry.BigPHSpaceSite.phToBigEtaleAbelianAdjunction`: `ε_X⁻¹ ⊣ ε_{X,*}` on abelian
  sheaves.
* `AlgebraicGeometry.BigPHSpaceSite.phToSmallEtaleAbelianAdjunction`: `a_X⁻¹ ⊣ a_{X,*}` on abelian
  sheaves, `a_{X,*}` being `ε_{X,*}` followed by restriction to the small étale site.
* `AlgebraicGeometry.BigPHSpaceSite.phToSmallEtale_abelianInverseImage_comp_pushforwardIso`:
  `ε_{X,*}a_X⁻¹ = π_X⁻¹` on abelian sheaves.
* `AlgebraicGeometry.BigPHSpaceSite.phToSmallEtale_abelianInverseImage_comp_restrictionIso`:
  `a_{X,*}a_X⁻¹ = 𝟭` on abelian sheaves.

## References

* [Stacks Project, Tag 0DGU](https://stacks.math.columbia.edu/tag/0DGU)
* [Stacks Project, Tag 0DGT](https://stacks.math.columbia.edu/tag/0DGT)
* [Stacks Project, Tag 0DD7](https://stacks.math.columbia.edu/tag/0DD7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.BigPHSpaceSite

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

attribute [local instance] BigEtaleSpaceSite.bigToSmallAbelianInverseImage_additive

variable {S : Scheme.{u}} (P : BigPHSpaceSite S) (E : BigEtaleSpaceSite S)
  (h : P.fppfSite = E.fppfSite) (X : P.Spaces)

/-- The inverse image `ε_X⁻¹` on abelian sheaves is additive. -/
instance abelianInverseImage_phToBigEtaleMorphism_additive :
    (CategoryTheory.Sites.abelianInverseImage (phToBigEtaleMorphism P E h X)).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The inverse image `a_X⁻¹` on abelian sheaves is additive. -/
instance abelianInverseImage_phToSmallEtaleMorphism_additive :
    (CategoryTheory.Sites.abelianInverseImage (phToSmallEtaleMorphism P E h X)).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The adjunction `ε_X⁻¹ ⊣ ε_{X,*}` on abelian sheaves. -/
def phToBigEtaleAbelianAdjunction :
    CategoryTheory.Sites.abelianInverseImage (phToBigEtaleMorphism P E h X) ⊣
      phToBigEtaleAbelianPushforward P E h X := by
  let ε := phToBigEtaleMorphism P E h X
  have := ε.preservesFiniteLimits
  have := ε.adj.rightAdjoint_preservesLimits
  exact (ProEtale.mapAbelianSheafAdjunction ε.adj).ofNatIsoRight
    (ProEtale.mapAbelianSheafRestrictionIso.{u + 1, u + 1, u + 1, u + 1, u + 1}
      (Over.postEquiv (canonicalSpaceEquivalence P E h).1 (X := X)).inverse)

/-- The direct image `a_{X,*}` on abelian sheaves: `ε_{X,*}` followed by restriction to the small
étale site. -/
abbrev phToSmallEtaleAbelianPushforward :
    Sheaf (BigPHSpaceOver.topology P X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem (etaleSpace P E h X))
        AddCommGrpCat.{u + 1} :=
  phToBigEtaleAbelianPushforward P E h X ⋙ E.bigToSmallEtaleRestriction (etaleSpace P E h X)

/-- `a_X⁻¹` on abelian sheaves is `ε_X⁻¹ ∘ π_X⁻¹`. -/
def phToSmallEtale_abelianInverseImageCompIso :
    CategoryTheory.Sites.abelianInverseImage (E.bigToSmallEtaleMorphism (etaleSpace P E h X)) ⋙
        CategoryTheory.Sites.abelianInverseImage (phToBigEtaleMorphism P E h X) ≅
      CategoryTheory.Sites.abelianInverseImage (phToSmallEtaleMorphism P E h X) := by
  have _ : HasBinaryBiproducts
      (Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem (etaleSpace P E h X))
        AddCommGrpCat.{u + 1}) :=
    HasBinaryBiproducts.of_hasBinaryProducts
  have _ : (CategoryTheory.Sites.abelianInverseImage
      (E.bigToSmallEtaleMorphism (etaleSpace P E h X)) ⋙
        CategoryTheory.Sites.abelianInverseImage (phToBigEtaleMorphism P E h X)).Additive :=
    Functor.additive_of_preserves_binary_products _
  have _ : (CategoryTheory.Sites.abelianInverseImage
      (phToSmallEtaleMorphism P E h X)).Additive :=
    Functor.additive_of_preserves_binary_products _
  exact ProEtale.liftSheafNatIso (BigPHSpaceOver.topology P X) _ _ (Iso.refl _)

/-- The adjunction `a_X⁻¹ ⊣ a_{X,*}` on abelian sheaves. -/
def phToSmallEtaleAbelianAdjunction :
    CategoryTheory.Sites.abelianInverseImage (phToSmallEtaleMorphism P E h X) ⊣
      phToSmallEtaleAbelianPushforward P E h X :=
  ((E.bigToSmallEtaleAbelianAdjunction (etaleSpace P E h X)).comp
    (phToBigEtaleAbelianAdjunction P E h X)).ofNatIsoLeft
      (phToSmallEtale_abelianInverseImageCompIso P E h X)

/-- `ε_{X,*}` on abelian sheaves is fully faithful. -/
def phToBigEtaleAbelianPushforwardFullyFaithful :
    (phToBigEtaleAbelianPushforward P E h X).FullyFaithful := by
  cases P with
  | mk pSchemeSite pSchemeMem pFppfSite pFppfMem pCutoffEq pInitial pInitialSmall pInitialPH
      pBound pOrdinal pOrdinalLim pInitialBounded pIsSite pRepresentative =>
    cases E with
    | mk eSchemeSite eSchemeMem eFppfSite eFppfMem eInitial eInitialSmall eInitialEtale eBound
        eOrdinal eOrdinalLim eInitialBounded eIsSite eRepresentative =>
      cases h
      exact { preimage := fun f ↦ ObjectProperty.homMk f.hom }

/-- `ε_{X,*}` on abelian sheaves is full. -/
instance : (phToBigEtaleAbelianPushforward P E h X).Full :=
  (phToBigEtaleAbelianPushforwardFullyFaithful P E h X).full

/-- `ε_{X,*}` on abelian sheaves is faithful. -/
instance : (phToBigEtaleAbelianPushforward P E h X).Faithful :=
  (phToBigEtaleAbelianPushforwardFullyFaithful P E h X).faithful

/-- **`ε_{X,*}a_X⁻¹ = π_X⁻¹` for abelian sheaves.** -/
def phToSmallEtale_abelianInverseImage_comp_pushforwardIso :
    CategoryTheory.Sites.abelianInverseImage (phToSmallEtaleMorphism P E h X) ⋙
        (Over.postEquiv (canonicalSpaceEquivalence P E h).1
          (X := X)).inverse.sheafPushforwardContinuous
          AddCommGrpCat.{u + 1} (E.bigEtaleTopology (etaleSpace P E h X))
          (BigPHSpaceOver.topology P X) ≅
      CategoryTheory.Sites.abelianInverseImage
        (E.bigToSmallEtaleMorphism (etaleSpace P E h X)) := by
  have _ : HasBinaryBiproducts
      (Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem (etaleSpace P E h X))
        AddCommGrpCat.{u + 1}) :=
    HasBinaryBiproducts.of_hasBinaryProducts
  have _ : PreservesFiniteLimits
      (CategoryTheory.Sites.abelianInverseImage (phToSmallEtaleMorphism P E h X) ⋙
        (Over.postEquiv (canonicalSpaceEquivalence P E h).1
          (X := X)).inverse.sheafPushforwardContinuous
          AddCommGrpCat.{u + 1} (E.bigEtaleTopology (etaleSpace P E h X))
          (BigPHSpaceOver.topology P X)) := by
    refine @comp_preservesFiniteLimits _ _ _ _ _ _ _ _ ?_ ?_
    · exact CategoryTheory.Sites.abelianInverseImage_preservesFiniteLimits _
    · exact @PreservesLimits.preservesFiniteLimits _ _ _ _ _
        (phToBigEtaleAbelianAdjunction P E h X).rightAdjoint_preservesLimits
  have _ : (CategoryTheory.Sites.abelianInverseImage (phToSmallEtaleMorphism P E h X) ⋙
      (Over.postEquiv (canonicalSpaceEquivalence P E h).1
          (X := X)).inverse.sheafPushforwardContinuous
        AddCommGrpCat.{u + 1} (E.bigEtaleTopology (etaleSpace P E h X))
        (BigPHSpaceOver.topology P X)).Additive :=
    Functor.additive_of_preserves_binary_products _
  have _ : (CategoryTheory.Sites.abelianInverseImage
      (E.bigToSmallEtaleMorphism (etaleSpace P E h X))).Additive :=
    Functor.additive_of_preserves_binary_products _
  exact ProEtale.liftSheafNatIso (E.bigEtaleTopology (etaleSpace P E h X)) _ _
    (Functor.isoWhiskerLeft (sheafCompose _ (forget AddCommGrpCat.{u + 1}))
      (phToSmallEtale_inverseImage_comp_phToBigEtale_pushforwardIso P E h X))

/-- **`a_{X,*}a_X⁻¹ = 𝟭` for abelian sheaves**, where the abelian direct image `a_{X,*}` is
`ε_{X,*}` followed by restriction to the small étale site of `X`. -/
def phToSmallEtale_abelianInverseImage_comp_restrictionIso :
    CategoryTheory.Sites.abelianInverseImage (phToSmallEtaleMorphism P E h X) ⋙
        (Over.postEquiv (canonicalSpaceEquivalence P E h).1
          (X := X)).inverse.sheafPushforwardContinuous
          AddCommGrpCat.{u + 1} (E.bigEtaleTopology (etaleSpace P E h X))
          (BigPHSpaceOver.topology P X) ⋙
        E.bigToSmallEtaleRestriction (etaleSpace P E h X) ≅
      𝟭 _ :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (phToSmallEtale_abelianInverseImage_comp_pushforwardIso P E h X)
      (E.bigToSmallEtaleRestriction (etaleSpace P E h X)) ≪≫
    E.bigToSmall_abelianInverseImage_comp_restrictionIso (etaleSpace P E h X)

end AlgebraicGeometry.BigPHSpaceSite

end
