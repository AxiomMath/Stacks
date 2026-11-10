module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfToSmallEtaleHigherVanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.DerivedPlusAdjunctionUnitIso
public import StacksFrontier.Algebra.Homology.DerivedCategory.InverseLimitHelpers

/-!
# Comparing the étale and fppf derived categories of an algebraic space

Let `T` be a big fppf site of algebraic spaces over a scheme `S`, `E` a big étale site of
algebraic spaces over the same big fppf site of schemes, and `X` an algebraic space. With
`a_X = π_X ∘ ε_X` from the big fppf topos of `X` to its small étale topos (Stacks 0DGI), this
file proves Stacks 0DGG: for `K` in `D⁺(X_étale)` the maps

`π_X⁻¹K ⟶ Rε_{X,*}a_X⁻¹K` and `K ⟶ Ra_{X,*}a_X⁻¹K`

are isomorphisms, granted the scheme case of Stacks 0DDS (1)
(`AlgebraicGeometry.SchemeFppfEtaleHigherVanishing`).

## Main definitions

* `AlgebraicGeometry.BigFppfSpaceSite.fppfToBigEtaleAbelianAdjunction`: `ε_X⁻¹ ⊣ ε_{X,*}` on
  abelian sheaves.
* `AlgebraicGeometry.BigFppfSpaceSite.fppfToSmallEtaleAbelianAdjunction`: `a_X⁻¹ ⊣ a_{X,*}` on
  abelian sheaves, `a_{X,*}` being `ε_{X,*}` followed by restriction to the small étale site.

## Main results

* `AlgebraicGeometry.BigFppfSpaceSite.isIso_fppfToSmallEtale_derivedUnits_of`:
  Stacks 0DGG, granted the scheme case.

## References

* [Stacks Project, Tag 0DGG](https://stacks.math.columbia.edu/tag/0DGG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u


namespace AlgebraicGeometry.BigFppfSpaceSite

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

attribute [local instance] BigEtaleSpaceSite.bigToSmallAbelianInverseImage_additive

variable {S : Scheme.{u}} (T : BigFppfSpaceSite S) (E : BigEtaleSpaceSite S)
  (h : T.schemeSite = E.fppfSite) (X : T.Spaces)

/-- The inverse image `ε_X⁻¹` on abelian sheaves is additive. -/
instance abelianInverseImage_fppfToBigEtaleMorphism_additive :
    (CategoryTheory.Sites.abelianInverseImage (fppfToBigEtaleMorphism T E h X)).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The inverse image `a_X⁻¹` on abelian sheaves is additive. -/
instance abelianInverseImage_fppfToSmallEtaleMorphism_additive :
    (CategoryTheory.Sites.abelianInverseImage (fppfToSmallEtaleMorphism T E h X)).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The direct image `ε_{X,*}` on abelian sheaves: restriction along the identification of the
big étale slice at `X` with the big fppf slice at `X`. -/
abbrev fppfToBigEtaleAbelianPushforward :
    Sheaf (BigFppfSpaceOver.topology T X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (E.bigEtaleTopology (etaleSpace T E h X)) AddCommGrpCat.{u + 1} :=
  (Over.postEquiv (canonicalSpaceEquivalence T E h).1 (X := X)).inverse.sheafPushforwardContinuous
    AddCommGrpCat.{u + 1} (E.bigEtaleTopology (etaleSpace T E h X)) (BigFppfSpaceOver.topology T X)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for limit preservation of the sheaf pushforward between the big fppf and
-- big étale sites, and for the abelian-sheaf adjunction, is deep
/-- The adjunction `ε_X⁻¹ ⊣ ε_{X,*}` on abelian sheaves. -/
def fppfToBigEtaleAbelianAdjunction :
    CategoryTheory.Sites.abelianInverseImage (fppfToBigEtaleMorphism T E h X) ⊣
      fppfToBigEtaleAbelianPushforward T E h X := by
  let ε := fppfToBigEtaleMorphism T E h X
  have _ := ε.preservesFiniteLimits
  have _ : PreservesFiniteLimits ε.pushforward :=
    @PreservesLimits.preservesFiniteLimits _ _ _ _ _
      (Functor.preservesLimits_sheafPushforwardContinuous _ _ _ _)
  exact (ProEtale.mapAbelianSheafAdjunction ε.adj).ofNatIsoRight
    (ProEtale.mapAbelianSheafRestrictionIso.{u + 1, u + 1, u + 1, u + 1, u + 1}
      (Over.postEquiv (canonicalSpaceEquivalence T E h).1 (X := X)).inverse)

/-- The direct image `a_{X,*}` on abelian sheaves: `ε_{X,*}` followed by restriction to the small
étale site. -/
abbrev fppfToSmallEtaleAbelianPushforward :
    Sheaf (BigFppfSpaceOver.topology T X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem (etaleSpace T E h X))
        AddCommGrpCat.{u + 1} :=
  fppfToBigEtaleAbelianPushforward T E h X ⋙ E.bigToSmallEtaleRestriction (etaleSpace T E h X)

/-- `a_X⁻¹` on abelian sheaves is `ε_X⁻¹ ∘ π_X⁻¹`. -/
def fppfToSmallEtale_abelianInverseImageCompIso :
    CategoryTheory.Sites.abelianInverseImage (E.bigToSmallEtaleMorphism (etaleSpace T E h X)) ⋙
        CategoryTheory.Sites.abelianInverseImage (fppfToBigEtaleMorphism T E h X) ≅
      CategoryTheory.Sites.abelianInverseImage (fppfToSmallEtaleMorphism T E h X) := by
  have _ : HasBinaryBiproducts
      (Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem (etaleSpace T E h X))
        AddCommGrpCat.{u + 1}) :=
    HasBinaryBiproducts.of_hasBinaryProducts
  have _ : (CategoryTheory.Sites.abelianInverseImage
      (E.bigToSmallEtaleMorphism (etaleSpace T E h X)) ⋙
        CategoryTheory.Sites.abelianInverseImage (fppfToBigEtaleMorphism T E h X)).Additive :=
    Functor.additive_of_preserves_binary_products _
  have _ : (CategoryTheory.Sites.abelianInverseImage
      (fppfToSmallEtaleMorphism T E h X)).Additive :=
    Functor.additive_of_preserves_binary_products _
  exact ProEtale.liftSheafNatIso (BigFppfSpaceOver.topology T X) _ _ (Iso.refl _)

/-- The adjunction `a_X⁻¹ ⊣ a_{X,*}` on abelian sheaves. -/
def fppfToSmallEtaleAbelianAdjunction :
    CategoryTheory.Sites.abelianInverseImage (fppfToSmallEtaleMorphism T E h X) ⊣
      fppfToSmallEtaleAbelianPushforward T E h X :=
  ((E.bigToSmallEtaleAbelianAdjunction (etaleSpace T E h X)).comp
    (fppfToBigEtaleAbelianAdjunction T E h X)).ofNatIsoLeft
      (fppfToSmallEtale_abelianInverseImageCompIso T E h X)

/-- `ε_{X,*}` on abelian sheaves is fully faithful. -/
def fppfToBigEtaleAbelianPushforwardFullyFaithful :
    (fppfToBigEtaleAbelianPushforward T E h X).FullyFaithful := by
  cases T with
  | mk tScheme tSchemeMem tInitial tInitialSmall tInitialFppf tBound tOrdinal tOrdinalLim
      tInitialBounded tIsSite tRepresentative =>
    cases E with
    | mk eSchemeSite eSchemeMem eFppfSite eFppfMem eInitial eInitialSmall eInitialEtale eBound
        eOrdinal eOrdinalLim eInitialBounded eIsSite eRepresentative =>
      cases h
      exact { preimage := fun f ↦ ObjectProperty.homMk f.hom }

/-- `ε_{X,*}` on abelian sheaves is full. -/
instance : (fppfToBigEtaleAbelianPushforward T E h X).Full :=
  (fppfToBigEtaleAbelianPushforwardFullyFaithful T E h X).full

/-- `ε_{X,*}` on abelian sheaves is faithful. -/
instance : (fppfToBigEtaleAbelianPushforward T E h X).Faithful :=
  (fppfToBigEtaleAbelianPushforwardFullyFaithful T E h X).faithful

variable [HasDerivedCategory (Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem
    (etaleSpace T E h X)) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory (Sheaf (E.bigEtaleTopology (etaleSpace T E h X)) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory (Sheaf (BigFppfSpaceOver.topology T X) AddCommGrpCat.{u + 1})]

omit [HasDerivedCategory (Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem
    (etaleSpace T E h X)) AddCommGrpCat.{u + 1})] in
/-- **`a_X⁻¹F` is acyclic for `ε_{X,*}`**, Stacks 0DGF (2), granted the scheme case. -/
theorem rightAcyclic_fppfToBigEtaleAbelianPushforward_of
    (hsch : SchemeFppfEtaleHigherVanishing E.fppfSite)
    (F : Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem (etaleSpace T E h X))
      AddCommGrpCat.{u + 1}) :
    (fppfToBigEtaleAbelianPushforward T E h X).rightAcyclic
      ((CategoryTheory.Sites.abelianInverseImage (fppfToSmallEtaleMorphism T E h X)).obj F) :=
  (CategoryTheory.rightAcyclic_iff_isZero_rightDerived _ _).2 fun p hp ↦
    isZero_rightDerived_fppfToBigEtale_abelianInverseImage_of T E h X hsch F p hp

omit [HasDerivedCategory (Sheaf (E.bigEtaleTopology (etaleSpace T E h X)) AddCommGrpCat.{u + 1})] in
/-- **`a_X⁻¹F` is acyclic for `a_{X,*}`**, granted the scheme case. -/
theorem rightAcyclic_fppfToSmallEtaleAbelianPushforward_of
    (hsch : SchemeFppfEtaleHigherVanishing E.fppfSite)
    (F : Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem (etaleSpace T E h X))
      AddCommGrpCat.{u + 1}) :
    (fppfToSmallEtaleAbelianPushforward T E h X).rightAcyclic
      ((CategoryTheory.Sites.abelianInverseImage (fppfToSmallEtaleMorphism T E h X)).obj F) :=
  (CategoryTheory.rightAcyclic_iff_isZero_rightDerived _ _).2 fun p hp ↦
    ((E.bigToSmallEtaleRestriction (etaleSpace T E h X)).map_isZero
      (isZero_rightDerived_fppfToBigEtale_abelianInverseImage_of T E h X hsch F p hp)).of_iso
      ((Functor.rightDerivedCompIso (fppfToBigEtaleAbelianPushforward T E h X)
        (E.bigToSmallEtaleRestriction (etaleSpace T E h X)) p).app _)

/-- Granted the scheme case, for `K` in `D⁺(X_étale)` the maps `π_X⁻¹K ⟶ Rε_{X,*}a_X⁻¹K` and
`K ⟶ Ra_{X,*}a_X⁻¹K` — the units of the derived adjunctions `ε_X⁻¹ ⊣ Rε_{X,*}` at `π_X⁻¹K` and
`a_X⁻¹ ⊣ Ra_{X,*}` at `K` — are isomorphisms (Stacks 0DGG). -/
theorem isIso_fppfToSmallEtale_derivedUnits_of
    (hsch : SchemeFppfEtaleHigherVanishing E.fppfSite)
    (K : DerivedCategory.Plus (Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem
      (etaleSpace T E h X)) AddCommGrpCat.{u + 1})) :
    IsIso ((Stacks.ComparingTopologies.derivedPlusAdjunction
        (fppfToBigEtaleAbelianAdjunction T E h X)).unit.app
          ((CategoryTheory.Sites.abelianInverseImage
            (E.bigToSmallEtaleMorphism (etaleSpace T E h X))).mapDerivedCategoryPlus.obj K)) ∧
      IsIso ((Stacks.ComparingTopologies.derivedPlusAdjunction
        (fppfToSmallEtaleAbelianAdjunction T E h X)).unit.app K) := by
  refine ⟨Stacks.ComparingTopologies.isIso_derivedPlusAdjunction_unit_app_mapDerivedCategoryPlus
    _ _ (fun F ↦ ?_) (fun F ↦ ?_) K,
    Stacks.ComparingTopologies.isIso_derivedPlusAdjunction_unit_app _
      (fun F ↦ ?_) (rightAcyclic_fppfToSmallEtaleAbelianPushforward_of T E h X hsch) K⟩
  · exact ((fppfToBigEtaleAbelianAdjunction T E h X).isIso_unit_app_iff_mem_essImage).2
      ⟨_, ⟨(fppfToSmallEtale_abelianInverseImage_comp_pushforwardIso T E h X).app F⟩⟩
  · exact (fppfToBigEtaleAbelianPushforward T E h X).rightAcyclic.prop_of_iso
      ((fppfToSmallEtale_abelianInverseImageCompIso T E h X).app F).symm
      (rightAcyclic_fppfToBigEtaleAbelianPushforward_of T E h X hsch F)
  · have := Stacks.Adjunction.isIso_unit_of_comp_iso_id (fppfToSmallEtaleAbelianAdjunction T E h X)
      (fppfToSmallEtale_abelianInverseImage_comp_restrictionIso T E h X)
    infer_instance

end AlgebraicGeometry.BigFppfSpaceSite

end
