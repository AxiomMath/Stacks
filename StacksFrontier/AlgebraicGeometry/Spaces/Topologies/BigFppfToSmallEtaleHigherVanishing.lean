module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfRepresentableTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfToSmallEtaleSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.FppfSheafConditionSmallEtale
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.SectionComplexLocalVanishing
public import StacksFrontier.CategoryTheory.Sites.Modules.InverseImage.AbelianSheaf
public import StacksFrontier.AlgebraicGeometry.ProEtale.BigSmall.AbelianSheaves
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SmallEtaleCohomologicalDescent

/-!
# The higher direct images of `ε_X` on pullbacks from the small étale site

Let `T` be a big fppf site of algebraic spaces over a scheme `S`, `E` a big étale site of
algebraic spaces over the same big fppf site of schemes, and `X` an algebraic space. For an
abelian sheaf `F` on the small étale site of `X`, the higher direct images
`R^iε_{X,*}(a_X⁻¹F)` vanish for `i > 0` (Stacks 0DGF, part (2)), granted the same statement for
schemes (Stacks 0DDS, part (1)). This file proves that reduction.

## Main results

* `AlgebraicGeometry.BigFppfSpaceSite.isZero_rightDerived_fppfToBigEtale_abelianInverseImage_of`:
  `R^iε_{X,*}(a_X⁻¹F) = 0` for `i > 0`, from the scheme case
  `AlgebraicGeometry.SchemeFppfEtaleHigherVanishing`.

## Implementation notes

By Stacks 072W, in the form
`Stacks.Cohomology.SectionComplexVanishing.isZero_rightDerived_of_locallyZero`, it suffices that
every degree `i` cohomology class of `a_X⁻¹F` over an object `V` of the big étale site of `X`
dies on an étale covering of `V`. The objects represented by schemes cover (Stacks 03MW), so
by transitivity of the topology it suffices to treat an object `h_A ⟶ X` with `A` a scheme.
There the functor `Ψ_s` of `AlgebraicGeometry.Space.schemeSliceToSpaceSliceEtale` identifies
the big fppf and big étale sites of the scheme `A` with the corresponding slices of algebraic
spaces near `h_A` (Stacks 03F3, Stacks 0DFV), restriction of `a_X⁻¹F` along it is `a_A⁻¹` of a
sheaf on the small étale site of `A` (Stacks 0DG7 and 0DDL), and the scheme case kills the class
étale-locally on `A`; `Stacks.Cohomology.SectionComplexVanishing.equalizerSieve_mem_of_restriction`
carries that back.

The scheme case, Stacks 0DDS (1), enters as the hypothesis
`AlgebraicGeometry.SchemeFppfEtaleHigherVanishing` of the main result.

## References

* [Stacks Project, Tag 0DGF](https://stacks.math.columbia.edu/tag/0DGF)
* [Stacks Project, Tag 0DDS](https://stacks.math.columbia.edu/tag/0DDS)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- **The vanishing of the higher direct images of `ε_Z` on pullbacks from the small étale
site, for schemes** (the second half of Stacks 0DDS, part (1)): for every scheme `Z` of the big
fppf site `B`, every abelian sheaf `F` on the small étale site of `Z` and every `p > 0`,
`R^pε_{Z,*}(a_Z⁻¹F) = 0`. Here `ε_{Z,*}` is restriction along the identity from the big fppf
site of `Z` to its big étale site, and `a_Z⁻¹` is the abelian inverse image along
`AlgebraicGeometry.fppfToSmallEtaleMorphism B Z`. -/
def SchemeFppfEtaleHigherVanishing (B : BigFppfSite.{u}) : Prop :=
  ∀ (Z : B.Schemes)
    (F : Sheaf (SmallEtale.topology (associatedBigEtaleSite B) Z.1 Z.2) AddCommGrpCat.{u + 1})
    (p : ℕ), 0 < p →
    IsZero ((((𝟭 (Over Z)).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (BigEtaleOver.topology (associatedBigEtaleSite B) Z.1 Z.2) (B.topology.over Z)).rightDerived
        p).obj ((CategoryTheory.Sites.abelianInverseImage (fppfToSmallEtaleMorphism B Z)).obj F))

end AlgebraicGeometry

namespace AlgebraicGeometry.BigFppfSpaceSite

variable {S : Scheme.{u}} (T : BigFppfSpaceSite S) (E : BigEtaleSpaceSite S)
  (h : T.schemeSite = E.fppfSite) (X : T.Spaces)
  (A : BigEtaleOver (associatedBigEtaleSite E.fppfSite) S E.fppf_mem)
  (s : (BigEtaleSpaceSite.schemeInclusion E).obj A ⟶ etaleSpace T E h X)

/-- The functor `Ψ_s` followed by the identification of the big étale slice at `X` with the big
fppf slice at `X`: schemes over `A`, as objects of the big fppf site of `X`. -/
abbrev schemeSliceToBigFppf :
    BigEtaleOver (associatedBigEtaleSite E.fppfSite) A.left.obj A.left.property ⥤ Over X :=
  Space.schemeSliceToSpaceSliceEtale E A s ⋙
    (Over.postEquiv (canonicalSpaceEquivalence T E h).1 (X := X)).inverse

/-- The functor `schemeSliceToBigFppf` is continuous for the fppf topology on the schemes over `A`
and the fppf topology on the slice at `X`. -/
instance schemeSliceToBigFppf_isContinuous :
    (schemeSliceToBigFppf T E h X A s).IsContinuous (E.fppfSite.topology.over A.left)
      (BigFppfSpaceOver.topology T X) := by
  cases T with
  | mk tScheme tSchemeMem tInitial tInitialSmall tInitialFppf tBound tOrdinal tOrdinalLim
      tInitialBounded tIsSite tRepresentative =>
    cases E with
    | mk eSchemeSite eSchemeMem eFppfSite eFppfMem eInitial eInitialSmall eInitialEtale eBound
        eOrdinal eOrdinalLim eInitialBounded eIsSite eRepresentative =>
      cases h
      let T' : BigFppfSpaceSite S :=
        ⟨tScheme, tSchemeMem, tInitial, tInitialSmall, tInitialFppf, tBound, tOrdinal,
          tOrdinalLim, tInitialBounded, tIsSite, tRepresentative⟩
      exact Space.schemeSliceToSpaceSlice_isContinuous T' A s

/-- Restriction of abelian sheaves along `schemeSliceToBigFppf`. -/
abbrev schemeSliceToBigFppfRestriction :
    Sheaf (BigFppfSpaceOver.topology T X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (E.fppfSite.topology.over A.left) AddCommGrpCat.{u + 1} :=
  (schemeSliceToBigFppf T E h X A s).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (E.fppfSite.topology.over A.left) (BigFppfSpaceOver.topology T X)

/-- Restriction of abelian sheaves along `schemeSliceToBigFppf` is exact and preserves injective
objects. -/
theorem schemeSliceToBigFppfRestriction_exact :
    PreservesFiniteLimits (schemeSliceToBigFppfRestriction T E h X A s) ∧
      PreservesFiniteColimits (schemeSliceToBigFppfRestriction T E h X A s) ∧
      (schemeSliceToBigFppfRestriction T E h X A s).PreservesInjectiveObjects := by
  cases T with
  | mk tScheme tSchemeMem tInitial tInitialSmall tInitialFppf tBound tOrdinal tOrdinalLim
      tInitialBounded tIsSite tRepresentative =>
    cases E with
    | mk eSchemeSite eSchemeMem eFppfSite eFppfMem eInitial eInitialSmall eInitialEtale eBound
        eOrdinal eOrdinalLim eInitialBounded eIsSite eRepresentative =>
      cases h
      let T' : BigFppfSpaceSite S :=
        ⟨tScheme, tSchemeMem, tInitial, tInitialSmall, tInitialFppf, tBound, tOrdinal,
          tOrdinalLim, tInitialBounded, tIsSite, tRepresentative⟩
      exact ⟨Space.schemeSliceRestriction_preservesFiniteLimits T' A s,
        Space.schemeSliceRestriction_preservesFiniteColimits T' A s,
        Space.schemeSliceRestriction_preservesInjectiveObjects T' A s⟩

/-- Restriction along `schemeSliceToBigFppf` preserves finite limits. -/
instance : PreservesFiniteLimits (schemeSliceToBigFppfRestriction T E h X A s) :=
  (schemeSliceToBigFppfRestriction_exact T E h X A s).1

/-- Restriction along `schemeSliceToBigFppf` preserves finite colimits. -/
instance : PreservesFiniteColimits (schemeSliceToBigFppfRestriction T E h X A s) :=
  (schemeSliceToBigFppfRestriction_exact T E h X A s).2.1

/-- Restriction along `schemeSliceToBigFppf` preserves injective objects. -/
instance : (schemeSliceToBigFppfRestriction T E h X A s).PreservesInjectiveObjects :=
  (schemeSliceToBigFppfRestriction_exact T E h X A s).2.2

/-- Restriction along `schemeSliceToBigFppf` is additive. -/
instance : (schemeSliceToBigFppfRestriction T E h X A s).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Restriction along `schemeSliceToBigFppf` preserves homology. -/
instance : (schemeSliceToBigFppfRestriction T E h X A s).PreservesHomology :=
  Functor.preservesHomologyOfExact _


/-! ### Restriction of `a_X⁻¹` to the schemes over `A` -/

/-- The small étale sheaf on the scheme `A` attached to a sheaf `G` on the small étale site of
`X`: the pullback `s_small⁻¹G` to the spaces-étale site of `h_A`, restricted along the chart
functor to the small étale site of the scheme `A`. -/
abbrev schemeChartSheaf :
    Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem (etaleSpace T E h X))
        (Type (u + 1)) ⥤
      Sheaf (SmallEtale.topology (associatedBigEtaleSite E.fppfSite) A.left.obj A.left.property)
        (Type (u + 1)) :=
  (E.smallEtaleMorphism s).inverseImage ⋙
    (Space.representedSpacesEtaleSheafEquiv E.fppfSite S E.fppf_mem A).functor

/-- The fppf restriction of sheaves of sets along `schemeSliceToBigFppf`. -/
abbrev schemeSliceToBigFppfRestrictionType :
    Sheaf (BigFppfSpaceOver.topology T X) (Type (u + 1)) ⥤
      Sheaf (E.fppfSite.topology.over A.left) (Type (u + 1)) :=
  (schemeSliceToBigFppf T E h X A s).sheafPushforwardContinuous (Type (u + 1))
    (E.fppfSite.topology.over A.left) (BigFppfSpaceOver.topology T X)

/-- Restriction along the identity from fppf to étale sheaves on the schemes over `A` is fully
faithful. -/
def fppfToBigEtalePushforwardFullyFaithful (B : BigFppfSite.{u}) (Z : B.Schemes) :
    (AlgebraicGeometry.fppfToBigEtaleMorphism B Z).pushforward.FullyFaithful :=
  letI := changeOfTopology_isContinuous B Z
  Functor.FullyFaithful.ofIso
    ({ preimage := fun f ↦ ObjectProperty.homMk f.hom } :
      ((𝟭 (Over Z)).sheafPushforwardContinuous (Type (u + 1))
        (BigEtaleOver.topology (associatedBigEtaleSite B) Z.1 Z.2)
        (B.topology.over Z)).FullyFaithful)
    (AlgebraicGeometry.fppfToBigEtale_pushforwardIso B Z).symm

/-- **`a_X⁻¹` restricted to the schemes over `A` is `a_A⁻¹`**, for sheaves of sets: restricting
`a_X⁻¹G` along `schemeSliceToBigFppf` is `a_A⁻¹` of the sheaf `schemeChartSheaf G` on the small
étale site of the scheme `A`, naturally in `G`. Both are fppf sheaves, and after forgetting to
étale sheaves both are `π_A⁻¹` of that sheaf: the first by Stacks 0DGF (1) and
`AlgebraicGeometry.Space.schemeSliceToSpaceSliceEtale_bigToSmall_inverseImageIso`, the second
by Stacks 0DDL. -/
def schemeSliceToBigFppfRestriction_inverseImageIsoType :
    (fppfToSmallEtaleMorphism T E h X).inverseImage ⋙
        schemeSliceToBigFppfRestrictionType T E h X A s ≅
      schemeChartSheaf T E h X A s ⋙
        (AlgebraicGeometry.fppfToSmallEtaleMorphism E.fppfSite A.left).inverseImage := by
  cases T with
  | mk tScheme tSchemeMem tInitial tInitialSmall tInitialFppf tBound tOrdinal tOrdinalLim
      tInitialBounded tIsSite tRepresentative =>
    cases E with
    | mk eSchemeSite eSchemeMem eFppfSite eFppfMem eInitial eInitialSmall eInitialEtale eBound
        eOrdinal eOrdinalLim eInitialBounded eIsSite eRepresentative =>
      cases h
      let T' : BigFppfSpaceSite S :=
        ⟨tScheme, tSchemeMem, tInitial, tInitialSmall, tInitialFppf, tBound, tOrdinal,
          tOrdinalLim, tInitialBounded, tIsSite, tRepresentative⟩
      let E' : BigEtaleSpaceSite S :=
        ⟨eSchemeSite, eSchemeMem, tScheme, eFppfMem, eInitial, eInitialSmall, eInitialEtale,
          eBound, eOrdinal, eOrdinalLim, eInitialBounded, eIsSite, eRepresentative⟩
      let εA := AlgebraicGeometry.fppfToBigEtaleMorphism E'.fppfSite A.left
      let πA := bigEtaleToSmallEtaleMorphism (associatedBigEtaleSite E'.fppfSite) A.left.obj
        A.left.property
      haveI := Space.schemeSliceToSpaceSliceEtale_isContinuous E' A s
      let RΨe := (Space.schemeSliceToSpaceSliceEtale E' A s).sheafPushforwardContinuous
        (Type (u + 1))
        (BigEtaleOver.topology (associatedBigEtaleSite E'.fppfSite) A.left.obj A.left.property)
        (E'.bigEtaleTopology (etaleSpace T' E' rfl X))
      have hunit : ∀ G, IsIso ((Functor.whiskerLeft πA.inverseImage εA.adj.unit).app G) :=
        fun G ↦ isIso_fppfToBigEtale_unit_app E'.fppfSite A.left G
      haveI := NatIso.isIso_of_isIso_app (Functor.whiskerLeft πA.inverseImage εA.adj.unit)
      have e₀ : ((fppfToSmallEtaleMorphism T' E' rfl X).inverseImage ⋙
            schemeSliceToBigFppfRestrictionType T' E' rfl X A s) ⋙ εA.pushforward ≅
          ((fppfToSmallEtaleMorphism T' E' rfl X).inverseImage ⋙
            (fppfToBigEtaleMorphism T' E' rfl X).pushforward) ⋙ RΨe :=
        Functor.isoWhiskerLeft ((fppfToSmallEtaleMorphism T' E' rfl X).inverseImage ⋙
            schemeSliceToBigFppfRestrictionType T' E' rfl X A s)
          (AlgebraicGeometry.fppfToBigEtale_pushforwardIso E'.fppfSite A.left) ≪≫ Iso.refl _
      have e₁ : ((fppfToSmallEtaleMorphism T' E' rfl X).inverseImage ⋙
            (fppfToBigEtaleMorphism T' E' rfl X).pushforward) ⋙ RΨe ≅
          (E'.bigToSmallEtaleMorphism (etaleSpace T' E' rfl X)).inverseImage ⋙ RΨe :=
        Functor.isoWhiskerRight
          (fppfToSmallEtale_inverseImage_comp_fppfToBigEtale_pushforwardIso T' E' rfl X) RΨe
      have e₂ := Space.schemeSliceToSpaceSliceEtale_bigToSmall_inverseImageIso E' A s
      have e₃ : (E'.smallEtaleMorphism s).inverseImage ⋙
            (Space.representedSpacesEtaleSheafEquiv E'.fppfSite S E'.fppf_mem A).functor ⋙
            πA.inverseImage ≅
          (schemeChartSheaf T' E' rfl X A s ⋙
            (AlgebraicGeometry.fppfToSmallEtaleMorphism E'.fppfSite A.left).inverseImage) ⋙
            εA.pushforward :=
        Functor.isoWhiskerLeft (schemeChartSheaf T' E' rfl X A s)
          (asIso (Functor.whiskerLeft πA.inverseImage εA.adj.unit))
      change (fppfToSmallEtaleMorphism T' E' rfl X).inverseImage ⋙
          schemeSliceToBigFppfRestrictionType T' E' rfl X A s ≅
        schemeChartSheaf T' E' rfl X A s ⋙
          (AlgebraicGeometry.fppfToSmallEtaleMorphism E'.fppfSite A.left).inverseImage
      exact ((fppfToBigEtalePushforwardFullyFaithful E'.fppfSite A.left).whiskeringRight
        _).preimageIso (e₀ ≪≫ e₁ ≪≫ e₂ ≪≫ e₃)

/-- The abelian version of `schemeChartSheaf`: the pullback `s_small⁻¹F` of an abelian sheaf
`F` on the small étale site of `X`, restricted along the chart functor to the small étale site
of the scheme `A`. -/
abbrev schemeChartSheafAb :
    Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem (etaleSpace T E h X))
        AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology (associatedBigEtaleSite E.fppfSite) A.left.obj A.left.property)
        AddCommGrpCat.{u + 1} :=
  CategoryTheory.Sites.abelianInverseImage (E.smallEtaleMorphism s) ⋙
    (Space.representedChartFunctor E.fppfSite S E.fppf_mem A).sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} (Space.representedSchemeTopology E.fppfSite S E.fppf_mem A)
      (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem
        (Space.yonedaSpace E.fppfSite S E.fppf_mem A))

/-- **`a_X⁻¹` restricted to the schemes over `A` is `a_A⁻¹`**, for abelian sheaves: restricting
`a_X⁻¹F` along `schemeSliceToBigFppf` is `a_A⁻¹` of the abelian sheaf `schemeChartSheafAb F` on
the small étale site of the scheme `A`, naturally in `F`. This is
`schemeSliceToBigFppfRestriction_inverseImageIsoType` on underlying sheaves of sets. -/
def schemeSliceToBigFppfRestriction_abelianInverseImageIso :
    CategoryTheory.Sites.abelianInverseImage (fppfToSmallEtaleMorphism T E h X) ⋙
        schemeSliceToBigFppfRestriction T E h X A s ≅
      schemeChartSheafAb T E h X A s ⋙
        CategoryTheory.Sites.abelianInverseImage
          (AlgebraicGeometry.fppfToSmallEtaleMorphism E.fppfSite A.left) := by
  have _ : HasBinaryBiproducts
      (Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem (etaleSpace T E h X))
        AddCommGrpCat.{u + 1}) :=
    HasBinaryBiproducts.of_hasBinaryProducts
  have _ : (CategoryTheory.Sites.abelianInverseImage
      (fppfToSmallEtaleMorphism T E h X)).Additive :=
    Functor.additive_of_preserves_binary_products _
  have _ : PreservesFiniteLimits (schemeChartSheafAb T E h X A s) := by
    refine @comp_preservesFiniteLimits _ _ _ _ _ _ _ _ ?_ ?_
    · exact CategoryTheory.Sites.abelianInverseImage_preservesFiniteLimits _
    · exact @PreservesLimits.preservesFiniteLimits _ _ _ _ _
        (Functor.preservesLimits_sheafPushforwardContinuous _ _ _ _)
  have _ : (schemeChartSheafAb T E h X A s).Additive :=
    Functor.additive_of_preserves_binary_products _
  have _ : (CategoryTheory.Sites.abelianInverseImage
      (AlgebraicGeometry.fppfToSmallEtaleMorphism E.fppfSite A.left)).Additive :=
    Functor.additive_of_preserves_binary_products _
  exact ProEtale.liftSheafNatIso (E.fppfSite.topology.over A.left) _ _
    (Functor.isoWhiskerLeft (sheafCompose _ (forget AddCommGrpCat.{u + 1}))
      (schemeSliceToBigFppfRestriction_inverseImageIsoType T E h X A s))

/-! ### Part (1) of Stacks 0DGF for abelian sheaves -/

/-- **`ε_{X,*}a_X⁻¹ = π_X⁻¹` for abelian sheaves**: the abelian form of
`fppfToSmallEtale_inverseImage_comp_fppfToBigEtale_pushforwardIso`, naturally in the abelian
sheaf. -/
def fppfToSmallEtale_abelianInverseImage_comp_pushforwardIso :
    CategoryTheory.Sites.abelianInverseImage (fppfToSmallEtaleMorphism T E h X) ⋙
        (Over.postEquiv (canonicalSpaceEquivalence T E h).1
          (X := X)).inverse.sheafPushforwardContinuous
          AddCommGrpCat.{u + 1} (E.bigEtaleTopology (etaleSpace T E h X))
          (BigFppfSpaceOver.topology T X) ≅
      CategoryTheory.Sites.abelianInverseImage
        (E.bigToSmallEtaleMorphism (etaleSpace T E h X)) := by
  have _ : HasBinaryBiproducts
      (Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem (etaleSpace T E h X))
        AddCommGrpCat.{u + 1}) :=
    HasBinaryBiproducts.of_hasBinaryProducts
  have _ : PreservesFiniteLimits
      (CategoryTheory.Sites.abelianInverseImage (fppfToSmallEtaleMorphism T E h X) ⋙
        (Over.postEquiv (canonicalSpaceEquivalence T E h).1
          (X := X)).inverse.sheafPushforwardContinuous
          AddCommGrpCat.{u + 1} (E.bigEtaleTopology (etaleSpace T E h X))
          (BigFppfSpaceOver.topology T X)) := by
    refine @comp_preservesFiniteLimits _ _ _ _ _ _ _ _ ?_ ?_
    · exact CategoryTheory.Sites.abelianInverseImage_preservesFiniteLimits _
    · exact @PreservesLimits.preservesFiniteLimits _ _ _ _ _
        (Functor.preservesLimits_sheafPushforwardContinuous _ _ _ _)
  have _ : (CategoryTheory.Sites.abelianInverseImage (fppfToSmallEtaleMorphism T E h X) ⋙
      (Over.postEquiv (canonicalSpaceEquivalence T E h).1
          (X := X)).inverse.sheafPushforwardContinuous
        AddCommGrpCat.{u + 1} (E.bigEtaleTopology (etaleSpace T E h X))
        (BigFppfSpaceOver.topology T X)).Additive :=
    Functor.additive_of_preserves_binary_products _
  have _ : (CategoryTheory.Sites.abelianInverseImage
      (E.bigToSmallEtaleMorphism (etaleSpace T E h X))).Additive :=
    Functor.additive_of_preserves_binary_products _
  exact ProEtale.liftSheafNatIso (E.bigEtaleTopology (etaleSpace T E h X)) _ _
    (Functor.isoWhiskerLeft (sheafCompose _ (forget AddCommGrpCat.{u + 1}))
      (fppfToSmallEtale_inverseImage_comp_fppfToBigEtale_pushforwardIso T E h X))

/-- **`a_{X,*}a_X⁻¹ = 𝟭` for abelian sheaves**, where the abelian direct image `a_{X,*}` is
`ε_{X,*}` followed by restriction to the small étale site of `X`: the abelian form of
`AlgebraicGeometry.BigFppfSpaceSite.fppfToSmallEtale_inverseImage_comp_pushforwardIso`, through
`ε_{X,*}a_X⁻¹ = π_X⁻¹` and Stacks 0DGC. -/
def fppfToSmallEtale_abelianInverseImage_comp_restrictionIso :
    CategoryTheory.Sites.abelianInverseImage (fppfToSmallEtaleMorphism T E h X) ⋙
        (Over.postEquiv (canonicalSpaceEquivalence T E h).1
          (X := X)).inverse.sheafPushforwardContinuous
          AddCommGrpCat.{u + 1} (E.bigEtaleTopology (etaleSpace T E h X))
          (BigFppfSpaceOver.topology T X) ⋙
        E.bigToSmallEtaleRestriction (etaleSpace T E h X) ≅
      𝟭 _ :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (fppfToSmallEtale_abelianInverseImage_comp_pushforwardIso T E h X)
      (E.bigToSmallEtaleRestriction (etaleSpace T E h X)) ≪≫
    E.bigToSmall_abelianInverseImage_comp_restrictionIso (etaleSpace T E h X)

/-! ### Local vanishing and the main reduction -/

/-- The sieve of arrows along which a section of an abelian presheaf restricts to zero, pulled
back along `f`, is the corresponding sieve of the restricted section. -/
private theorem equalizerSieve_pullback {𝒞 : Type*} [Category 𝒞] (P : 𝒞ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    {V W : 𝒞} (f : W ⟶ V) (x : ToType (P.obj (op V))) :
    (Presheaf.equalizerSieve (X := op V) x 0).pullback f =
      Presheaf.equalizerSieve (X := op W) (P.map f.op x) 0 := by
  ext Z g
  simp only [Sieve.pullback_apply, Presheaf.equalizerSieve_apply, map_zero, op_comp,
    Functor.map_comp, ConcreteCategory.comp_apply]

/-- Sections dying locally is invariant under isomorphism of the object. -/
private theorem equalizerSieve_mem_of_iso {𝒞 : Type*} [Category 𝒞] (J : GrothendieckTopology 𝒞)
    (P : 𝒞ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) {W₁ W₂ : 𝒞} (e : W₁ ≅ W₂)
    (h : ∀ y : ToType (P.obj (op W₁)), Presheaf.equalizerSieve (X := op W₁) y 0 ∈ J W₁)
    (z : ToType (P.obj (op W₂))) : Presheaf.equalizerSieve (X := op W₂) z 0 ∈ J W₂ := by
  have h₁ : (Presheaf.equalizerSieve (X := op W₂) z 0).pullback e.hom ∈ J W₁ := by
    rw [equalizerSieve_pullback]
    exact h _
  have h₂ := J.pullback_stable e.inv h₁
  rwa [← Sieve.pullback_comp, e.inv_hom_id, Sieve.pullback_id] at h₂

/-- **Stacks 0DGF, part (2), granted the scheme case.** For an abelian sheaf `F` on the small
étale site of an algebraic space `X`, the higher direct images `R^pε_{X,*}(a_X⁻¹F)` vanish for
`p > 0`, provided `R^pε_{Z,*}(a_Z⁻¹G) = 0` for `p > 0` for the schemes `Z` of the site
(`AlgebraicGeometry.SchemeFppfEtaleHigherVanishing`, the second half of Stacks 0DDS (1)). -/
theorem isZero_rightDerived_fppfToBigEtale_abelianInverseImage_of
    (hsch : SchemeFppfEtaleHigherVanishing E.fppfSite)
    (F : Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem (etaleSpace T E h X))
      AddCommGrpCat.{u + 1}) (p : ℕ) (hp : 0 < p) :
    IsZero ((((Over.postEquiv (canonicalSpaceEquivalence T E h).1
      (X := X)).inverse.sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} (E.bigEtaleTopology (etaleSpace T E h X))
      (BigFppfSpaceOver.topology T X)).rightDerived p).obj
        ((CategoryTheory.Sites.abelianInverseImage (fppfToSmallEtaleMorphism T E h X)).obj F)) := by
  let J := E.bigEtaleTopology (etaleSpace T E h X)
  let K := BigFppfSpaceOver.topology T X
  let u := (Over.postEquiv (canonicalSpaceEquivalence T E h).1 (X := X)).inverse
  let M := (CategoryTheory.Sites.abelianInverseImage (fppfToSmallEtaleMorphism T E h X)).obj F
  let I := injectiveResolution M
  let P := (Stacks.Cohomology.SectionComplexVanishing.pushforwardSections J K u I).homology p
  have hscheme : ∀ (A : BigEtaleOver (associatedBigEtaleSite E.fppfSite) S E.fppf_mem)
      (s : (BigEtaleSpaceSite.schemeInclusion E).obj A ⟶ etaleSpace T E h X)
      (U : BigEtaleOver (associatedBigEtaleSite E.fppfSite) A.left.obj A.left.property)
      (y : ToType (P.obj (op ((Space.schemeSliceToSpaceSliceEtale E A s).obj U)))),
      Presheaf.equalizerSieve (X := op ((Space.schemeSliceToSpaceSliceEtale E A s).obj U)) y 0 ∈
        J ((Space.schemeSliceToSpaceSliceEtale E A s).obj U) := by
    intro A s U y
    let J₀ := BigEtaleOver.topology (associatedBigEtaleSite E.fppfSite) A.left.obj
      A.left.property
    let K₀ := E.fppfSite.topology.over A.left
    let Ψ := Space.schemeSliceToSpaceSliceEtale E A s
    have : (𝟭 (Over A.left)).IsContinuous J₀ K₀ := changeOfTopology_isContinuous E.fppfSite A.left
    have hz : IsZero ((((𝟭 (Over A.left)).sheafPushforwardContinuous AddCommGrpCat.{u + 1} J₀
        K₀).rightDerived p).obj ((schemeSliceToBigFppfRestriction T E h X A s).obj M)) :=
      (hsch A.left ((schemeChartSheafAb T E h X A s).obj F) p hp).of_iso
        (((𝟭 (Over A.left)).sheafPushforwardContinuous AddCommGrpCat.{u + 1} J₀
          K₀).rightDerived p |>.mapIso
          ((schemeSliceToBigFppfRestriction_abelianInverseImageIso T E h X A s).app F))
    have : (Ψ ⋙ u).IsContinuous K₀ K :=
      inferInstanceAs ((schemeSliceToBigFppf T E h X A s).IsContinuous _ _)
    have : ((Ψ ⋙ u).sheafPushforwardContinuous AddCommGrpCat.{u + 1} K₀ K).Additive :=
      inferInstanceAs (schemeSliceToBigFppfRestriction T E h X A s).Additive
    have : ((Ψ ⋙ u).sheafPushforwardContinuous AddCommGrpCat.{u + 1} K₀ K).PreservesHomology :=
      inferInstanceAs (schemeSliceToBigFppfRestriction T E h X A s).PreservesHomology
    have : ((Ψ ⋙ u).sheafPushforwardContinuous AddCommGrpCat.{u + 1} K₀
        K).PreservesInjectiveObjects :=
      inferInstanceAs (schemeSliceToBigFppfRestriction T E h X A s).PreservesInjectiveObjects
    have : ∀ Q : (Over A.left)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
        Presheaf.IsLocallyInjective J₀ (toSheafify J₀ Q) := fun Q ↦
      Presheaf.isLocallyInjective_toSheafify'.{u + 1, u, u + 2, u + 1, u + 1} _ Q
    exact Stacks.Cohomology.SectionComplexVanishing.equalizerSieve_mem_of_restriction J K u J₀ K₀
      Ψ (Space.schemeSliceToSpaceSliceEtale_coverPreserving E A s) I p U
      (Stacks.Cohomology.SectionComplexVanishing.equalizerSieve_mem_of_isZero_rightDerived J₀ K₀
        (𝟭 _) _ p hz U) y
  refine Stacks.Cohomology.SectionComplexVanishing.isZero_rightDerived_of_locallyZero J K u I p
    fun V x ↦ ?_
  refine J.transitive (BigEtaleSpaceSite.generate_affineSchemePresieve_mem E V) _
    fun W g hg ↦ ?_
  obtain ⟨W', g₁, g₂, ⟨A, -, ⟨e⟩⟩, rfl⟩ := hg
  rw [Sieve.pullback_comp]
  refine J.pullback_stable g₁ ?_
  rw [equalizerSieve_pullback]
  let s : (BigEtaleSpaceSite.schemeInclusion E).obj A ⟶ etaleSpace T E h X := e.hom ≫ W'.hom
  let ψ : (Space.schemeSliceToSpaceSliceEtale E A s).obj
      (BigEtaleSpaceSite.schemeOverObj E A (𝟙 A)) ≅ W' :=
    (Over.map s).mapIso (BigEtaleSpaceSite.overSchemeInclusion_schemeOverIso E A (𝟙 A)) ≪≫
      Over.isoMk e (by simp [s])
  exact equalizerSieve_mem_of_iso J P ψ (hscheme A s _) _

end AlgebraicGeometry.BigFppfSpaceSite

end
