module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfToSmallEtaleDerived
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigSmallEtaleFinitePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigSmallEtaleDerivedProperPushforward
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperPushforwardBaseChangeUnconditional
public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionComparisonIso
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryPlusCompIsoh
public import StacksFrontier.Algebra.Homology.DerivedCategory.BaseChangeBoundedBelow
public import StacksFrontier.CategoryTheory.Sites.Localization.PushforwardAdjunction

/-!
# Pullback from the small étale site and derived direct image along a finite morphism

Let `T` be a big fppf site of algebraic spaces over a scheme `S`, `E` a big étale site of
algebraic spaces over the same big fppf site of schemes, and `f : Y ⟶ X` a finite morphism of
algebraic spaces. This file proves Stacks 0DGK,
`a_X⁻¹(Rf_{small,*}K) = Rf_{big,fppf,*}(a_Y⁻¹K)` for `K` in `D⁺(Y_étale)`, granted the scheme
case of Stacks 0DDS (1) (`AlgebraicGeometry.SchemeFppfEtaleHigherVanishing`).

## Main definitions

* `AlgebraicGeometry.BigFppfSpaceSite.fppfAbelianPushforward`: `f_{big,fppf,*}` on abelian
  sheaves.
* `AlgebraicGeometry.BigFppfSpaceSite.fppfToBigEtale_comp_fppfAbelianPushforwardIso`: the big
  square of Stacks 0DGI on abelian sheaves, `ε_{X,*} ∘ f_{big,fppf,*} = f_{big,étale,*} ∘ ε_{Y,*}`.
* `AlgebraicGeometry.BigFppfSpaceSite.fppfToBigEtale_rightDerivedPushforwardIso`: the same
  for the derived functors on `D⁺` (Stacks 0D6E), for any `f`.
* `AlgebraicGeometry.BigFppfSpaceSite.fppfToSmallEtale_rightDerivedPushforwardIsoOfIsFinite_of`:
  Stacks 0DGK, granted the scheme case.

## Implementation notes

The source reduces étale locally on the target to schemes and quotes the scheme case. Here the
comparison is made on the spaces themselves, through the big étale site, as in the proof of
Stacks 0DGL (2): `ε_{X,*}` is fully faithful, so `M ≅ ε_X⁻¹ Rε_{X,*} M` on `D⁺`
(`Stacks.ComparingTopologies.isIso_derivedPlusAdjunction_counit_app_of_fullyFaithful`), and

`Rε_{X,*} Rf_{big,fppf,*} a_Y⁻¹ = Rf_{big,étale,*} Rε_{Y,*} a_Y⁻¹ = Rf_{big,étale,*} π_Y⁻¹
  = π_X⁻¹ Rf_{small,*}`

by Stacks 0D6E, Stacks 0DGG and Stacks 0DGD for finite `f`, both direct images along a finite
morphism being exact (Stacks 0A4K). Every step is a natural isomorphism. The scheme case enters
only through Stacks 0DGG.

## References

* [Stacks Project, Tag 0DGK](https://stacks.math.columbia.edu/tag/0DGK)
* [Stacks Project, Tag 0DGD](https://stacks.math.columbia.edu/tag/0DGD)
* [Stacks Project, Tag 0D6E](https://stacks.math.columbia.edu/tag/0D6E)
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
  (h : T.schemeSite = E.fppfSite) {X Y : T.Spaces} (f : Y ⟶ X)

set_option synthInstance.maxHeartbeats 400000 in
/-- The direct image `f_{big,fppf,*}` of abelian sheaves on the big fppf sites, as the right
adjoint attached to cocontinuity of `Over.map f`. -/
abbrev fppfAbelianPushforward :
    Sheaf (BigFppfSpaceOver.topology T Y) AddCommGrpCat.{u + 1} ⥤
      Sheaf (BigFppfSpaceOver.topology T X) AddCommGrpCat.{u + 1} :=
  (Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
    (BigFppfSpaceOver.topology T Y) (BigFppfSpaceOver.topology T X)

set_option synthInstance.maxHeartbeats 400000 in
/-- **The big square of Stacks 0DGI on abelian sheaves**:
`ε_{X,*} ∘ f_{big,fppf,*} = f_{big,étale,*} ∘ ε_{Y,*}`. -/
def fppfToBigEtale_comp_fppfAbelianPushforwardIso :
    fppfAbelianPushforward T f ⋙ fppfToBigEtaleAbelianPushforward T E h X ≅
      fppfToBigEtaleAbelianPushforward T E h Y ⋙
        E.bigEtalePushforward (etaleMap T E h f) := by
  let JeX := E.bigEtaleTopology (etaleSpace T E h X)
  let JeY := E.bigEtaleTopology (etaleSpace T E h Y)
  let JfX := BigFppfSpaceOver.topology T X
  let JfY := BigFppfSpaceOver.topology T Y
  let eX := (Over.postEquiv (canonicalSpaceEquivalence T E h).1 (X := X)).inverse
  let eY := (Over.postEquiv (canonicalSpaceEquivalence T E h).1 (X := Y)).inverse
  let be := Over.pullback (etaleMap T E h f)
  let bf := Over.pullback f
  haveI hbpE : be.IsContinuous JeX JeY :=
    (StacksRelocalization.isMorphismOfSites_overPullback E.topology (etaleMap T E h f)).isContinuous
  haveI hbpF : bf.IsContinuous JfX JfY :=
    (StacksRelocalization.isMorphismOfSites_overPullback T.topology f).isContinuous
  haveI : (be ⋙ eY).IsContinuous JeX JfY := Functor.isContinuous_comp be eY JeX JeY JfY
  haveI : (eX ⋙ bf).IsContinuous JeX JfY := Functor.isContinuous_comp eX bf JeX JfX JfY
  let ρF := (Over.mapPullbackAdj f).sheafPushforwardCocontinuousIso AddCommGrpCat.{u + 1}
    (J := JfY) (K := JfX)
  let ρE := (Over.mapPullbackAdj (etaleMap T E h f)).sheafPushforwardCocontinuousIso
    AddCommGrpCat.{u + 1} (J := JeY) (K := JeX)
  exact Functor.isoWhiskerRight ρF _ ≪≫
    Functor.sheafPushforwardContinuousComp eX bf AddCommGrpCat.{u + 1} JeX JfX JfY ≪≫
    Functor.sheafPushforwardContinuousIso (pullbackChangeOfTopologyIso T E h f).symm
      AddCommGrpCat.{u + 1} JeX JfY ≪≫
    (Functor.sheafPushforwardContinuousComp be eY AddCommGrpCat.{u + 1} JeX JeY JfY).symm ≪≫
    Functor.isoWhiskerLeft _ ρE.symm

/-- **The small square of Stacks 0DGI on abelian sheaves**:
`a_{X,*} ∘ f_{big,fppf,*} = f_{small,*} ∘ a_{Y,*}`, the big square followed by Stacks 0DF8 for the
identity base change. -/
def fppfToSmallEtale_comp_fppfAbelianPushforwardIso :
    fppfAbelianPushforward T f ⋙ fppfToSmallEtaleAbelianPushforward T E h X ≅
      fppfToSmallEtaleAbelianPushforward T E h Y ⋙ E.smallEtalePushforward (etaleMap T E h f) :=
  let f' := etaleMap T E h f
  let rX : E.smallEtaleRestriction (𝟙 (etaleSpace T E h X)) ≅
      E.bigToSmallEtaleRestriction (etaleSpace T E h X) :=
    Functor.sheafPushforwardContinuousIso (E.inclusionFunctorIdIso (etaleSpace T E h X))
      AddCommGrpCat.{u + 1} _ _
  let rY : E.smallEtaleRestriction (𝟙 (etaleSpace T E h Y)) ≅
      E.bigToSmallEtaleRestriction (etaleSpace T E h Y) :=
    Functor.sheafPushforwardContinuousIso (E.inclusionFunctorIdIso (etaleSpace T E h Y))
      AddCommGrpCat.{u + 1} _ _
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (fppfToBigEtale_comp_fppfAbelianPushforwardIso T E h f) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (fppfToBigEtaleAbelianPushforward T E h Y)
      (Functor.isoWhiskerLeft _ rX.symm ≪≫
        E.bigEtalePushforwardRestrictionIso f' (𝟙 _) (𝟙 _) f' (IsPullback.of_id_fst) ≪≫
        Functor.isoWhiskerRight rY _) ≪≫
    (Functor.associator _ _ _).symm

/-- The direct image `a_{Z,*}` of abelian sheaves from the big fppf site of `Z` to the small étale
site of `Z` preserves injective objects. -/
instance fppfToSmallEtaleAbelianPushforward_preservesInjectiveObjects (Z : T.Spaces) :
    (fppfToSmallEtaleAbelianPushforward T E h Z).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (fppfToSmallEtaleAbelianAdjunction T E h Z)

/-- The direct image `ε_{Z,*}` of abelian sheaves from the big fppf site of `Z` to the big étale
site of `Z` preserves injective objects. -/
instance fppfToBigEtaleAbelianPushforward_preservesInjectiveObjects (Z : T.Spaces) :
    (fppfToBigEtaleAbelianPushforward T E h Z).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (fppfToBigEtaleAbelianAdjunction T E h Z)

variable [HasDerivedCategory (Sheaf (BigFppfSpaceOver.topology T X) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory (Sheaf (BigFppfSpaceOver.topology T Y) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory (Sheaf (E.bigEtaleTopology (etaleSpace T E h X)) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory (Sheaf (E.bigEtaleTopology (etaleSpace T E h Y)) AddCommGrpCat.{u + 1})]

/-- **Stacks 0D6E for `ε` and `f`**: `Rε_{X,*} ∘ Rf_{big,fppf,*} = Rf_{big,étale,*} ∘ Rε_{Y,*}` on
`D⁺((Spaces/Y)_fppf)`, for any morphism `f : Y ⟶ X`. Both `f_{big,fppf,*}` and `ε_{Y,*}` preserve
injective objects, being right adjoint to exact functors, so each composite is derived as the
composite of the derived functors, and the underived composites agree by the big square of Stacks
0DGI. -/
def fppfToBigEtale_rightDerivedPushforwardIso :
    (fppfAbelianPushforward T f).rightDerivedFunctorPlus ⋙
        (fppfToBigEtaleAbelianPushforward T E h X).rightDerivedFunctorPlus ≅
      (fppfToBigEtaleAbelianPushforward T E h Y).rightDerivedFunctorPlus ⋙
        (E.bigEtalePushforward (etaleMap T E h f)).rightDerivedFunctorPlus :=
  (Functor.rightDerivedFunctorPlusCompIso _ _).symm ≪≫
    Functor.rightDerivedFunctorPlusNatIso (fppfToBigEtale_comp_fppfAbelianPushforwardIso T E h f) ≪≫
    Functor.rightDerivedFunctorPlusCompIso _ _

omit [HasDerivedCategory (Sheaf (BigFppfSpaceOver.topology T X) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory (Sheaf (BigFppfSpaceOver.topology T Y) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory (Sheaf (E.bigEtaleTopology (etaleSpace T E h X)) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory (Sheaf (E.bigEtaleTopology (etaleSpace T E h Y)) AddCommGrpCat.{u + 1})] in
/-- A finite morphism of the big fppf site of algebraic spaces is finite as a morphism of the big
étale site. -/
theorem isFinite_etaleMap (hf : Space.IsFinite T.schemeSite S T.scheme_mem f.hom) :
    Space.IsFinite E.fppfSite S E.fppf_mem (etaleMap T E h f).hom := by
  cases T with
  | mk tScheme tSchemeMem tInitial tInitialSmall tInitialFppf tBound tOrdinal tOrdinalLim
      tInitialBounded tIsSite tRepresentative =>
    cases E with
    | mk eSchemeSite eSchemeMem eFppfSite eFppfMem eInitial eInitialSmall eInitialEtale eBound
        eOrdinal eOrdinalLim eInitialBounded eIsSite eRepresentative =>
      cases h
      exact hf

variable [HasDerivedCategory (Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem
    (etaleSpace T E h X)) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory (Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem
    (etaleSpace T E h Y)) AddCommGrpCat.{u + 1})]

/-- **Stacks 0DGK, granted the scheme case.** Let `f : Y ⟶ X` be a finite morphism of algebraic
spaces. Then `a_X⁻¹(Rf_{small,*}K) ≅ Rf_{big,fppf,*}(a_Y⁻¹K)`, naturally in `K` in
`D⁺(Y_étale)`. -/
def fppfToSmallEtale_rightDerivedPushforwardIsoOfIsFinite_of
    (hsch : SchemeFppfEtaleHigherVanishing E.fppfSite)
    (hf : Space.IsFinite T.schemeSite S T.scheme_mem f.hom) :
    (E.smallEtalePushforward (etaleMap T E h f)).rightDerivedFunctorPlus ⋙
        (CategoryTheory.Sites.abelianInverseImage
          (fppfToSmallEtaleMorphism T E h X)).mapDerivedCategoryPlus ≅
      (CategoryTheory.Sites.abelianInverseImage
          (fppfToSmallEtaleMorphism T E h Y)).mapDerivedCategoryPlus ⋙
        (fppfAbelianPushforward T f).rightDerivedFunctorPlus := by
  let f' := etaleMap T E h f
  have hf' := isFinite_etaleMap T E h f hf
  have hp : Space.IsProper E.fppfSite S E.fppf_mem f'.hom :=
    ((Space.isFinite_iff_isAffineHom_and_isProper E.fppfSite S E.fppf_mem
      (etaleSpace T E h Y).2 (etaleSpace T E h X).2 f'.hom).mp hf').2
  have h0A3U : ∀ {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X)
      (f' : X' ⟶ Y') (sq : IsPullback g' f' f g), _root_.AlgebraicGeometry.IsProper f →
        IsIso (Stacks.EtaleCohomology.smallEtaleSetBaseChange.{u, 0} g' f' f g sq.w) :=
    fun f g g' f' sq hpr ↦ haveI := hpr
      Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_isProper f g g' f' sq
  have := E.smallEtalePushforward_preservesFiniteColimits_of_isFinite f' hf'
  have := E.bigEtalePushforward_preservesFiniteColimits_of_isFinite f' hf'
  let πX := CategoryTheory.Sites.abelianInverseImage
    (E.bigToSmallEtaleMorphism (etaleSpace T E h X))
  let πY := CategoryTheory.Sites.abelianInverseImage
    (E.bigToSmallEtaleMorphism (etaleSpace T E h Y))
  let εX := CategoryTheory.Sites.abelianInverseImage (fppfToBigEtaleMorphism T E h X)
  let fs := E.smallEtalePushforward f'
  let fe := E.bigEtalePushforward f'
  have _ : fe.Additive := Functor.additive_of_preserves_binary_products _
  have _ : fs.Additive := Functor.additive_of_preserves_binary_products _
  -- `𝟭 ≅ ε_X⁻¹ ∘ Rε_{X,*}` on `D⁺((Spaces/X)_fppf)`
  haveI : ∀ M, IsIso ((Stacks.ComparingTopologies.derivedPlusAdjunction
      (fppfToBigEtaleAbelianAdjunction T E h X)).counit.app M) := fun M ↦
    Stacks.ComparingTopologies.isIso_derivedPlusAdjunction_counit_app_of_fullyFaithful
      (fppfToBigEtaleAbelianAdjunction T E h X) M
  haveI := NatIso.isIso_of_isIso_app
    (Stacks.ComparingTopologies.derivedPlusAdjunction
      (fppfToBigEtaleAbelianAdjunction T E h X)).counit
  let c := asIso
    (Stacks.ComparingTopologies.derivedPlusAdjunction
      (fppfToBigEtaleAbelianAdjunction T E h X)).counit
  -- `π_Y⁻¹ ≅ Rε_{Y,*} ∘ a_Y⁻¹` on `D⁺(Y_étale)` (Stacks 0DGG)
  haveI : ∀ K, IsIso ((Functor.whiskerLeft πY.mapDerivedCategoryPlus
      (Stacks.ComparingTopologies.derivedPlusAdjunction
        (fppfToBigEtaleAbelianAdjunction T E h Y)).unit).app K) := fun K ↦
    (isIso_fppfToSmallEtale_derivedUnits_of T E h Y hsch K).1
  haveI := NatIso.isIso_of_isIso_app (Functor.whiskerLeft πY.mapDerivedCategoryPlus
    (Stacks.ComparingTopologies.derivedPlusAdjunction
      (fppfToBigEtaleAbelianAdjunction T E h Y)).unit)
  let uY := asIso (Functor.whiskerLeft πY.mapDerivedCategoryPlus
    (Stacks.ComparingTopologies.derivedPlusAdjunction
      (fppfToBigEtaleAbelianAdjunction T E h Y)).unit)
  let aY := Functor.mapDerivedCategoryPlusCompIsoh
    (fppfToSmallEtale_abelianInverseImageCompIso T E h Y)
  let aX := Functor.mapDerivedCategoryPlusCompIsoh
    (fppfToSmallEtale_abelianInverseImageCompIso T E h X)
  -- `π_Y⁻¹ ∘ Rf_{big,étale,*} ≅ Rf_{small,*} ∘ π_X⁻¹` (Stacks 0DGD, finite case)
  let d : πY.mapDerivedCategoryPlus ⋙ fe.rightDerivedFunctorPlus ≅
      fs.rightDerivedFunctorPlus ⋙ πX.mapDerivedCategoryPlus :=
    Functor.isoWhiskerLeft _ (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus fe) ≪≫
      Functor.mapDerivedCategoryPlusCompIsoh (Iso.refl (πY ⋙ fe)) ≪≫
      (Functor.mapDerivedCategoryPlusCompIsoh
        (E.bigToSmallEtaleAbelianPushforwardIso f' hp h0A3U)).symm ≪≫
      Functor.isoWhiskerRight (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus fs).symm _
  let D := fppfToBigEtale_rightDerivedPushforwardIso T E h f
  let AX := (CategoryTheory.Sites.abelianInverseImage
    (fppfToSmallEtaleMorphism T E h X)).mapDerivedCategoryPlus
  let AY := (CategoryTheory.Sites.abelianInverseImage
    (fppfToSmallEtaleMorphism T E h Y)).mapDerivedCategoryPlus
  let EX := εX.mapDerivedCategoryPlus
  let EY := (CategoryTheory.Sites.abelianInverseImage
    (fppfToBigEtaleMorphism T E h Y)).mapDerivedCategoryPlus
  let RεX := (fppfToBigEtaleAbelianPushforward T E h X).rightDerivedFunctorPlus
  let RεY := (fppfToBigEtaleAbelianPushforward T E h Y).rightDerivedFunctorPlus
  let RF := (fppfAbelianPushforward T f).rightDerivedFunctorPlus
  let PX := πX.mapDerivedCategoryPlus
  let PY := πY.mapDerivedCategoryPlus
  let Rfs := fs.rightDerivedFunctorPlus
  let Rfe := fe.rightDerivedFunctorPlus
  have i₁ : Rfs ⋙ AX ≅ (Rfs ⋙ PX) ⋙ EX := Functor.isoWhiskerLeft Rfs aX.symm
  have i₂ : (Rfs ⋙ PX) ⋙ EX ≅ (PY ⋙ Rfe) ⋙ EX := Functor.isoWhiskerRight d.symm EX
  have i₃ : (PY ⋙ Rfe) ⋙ EX ≅ ((PY ⋙ EY ⋙ RεY) ⋙ Rfe) ⋙ EX :=
    Functor.isoWhiskerRight (Functor.isoWhiskerRight uY Rfe) EX
  have i₄ : ((PY ⋙ EY ⋙ RεY) ⋙ Rfe) ⋙ EX ≅ ((AY ⋙ RεY) ⋙ Rfe) ⋙ EX :=
    Functor.isoWhiskerRight (Functor.isoWhiskerRight (Functor.isoWhiskerRight aY RεY) Rfe) EX
  have i₅ : ((AY ⋙ RεY) ⋙ Rfe) ⋙ EX ≅ (AY ⋙ RF ⋙ RεX) ⋙ EX :=
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft AY D.symm) EX
  have i₆ : (AY ⋙ RF ⋙ RεX) ⋙ EX ≅ AY ⋙ RF :=
    Functor.isoWhiskerLeft (AY ⋙ RF) c
  exact i₁ ≪≫ i₂ ≪≫ i₃ ≪≫ i₄ ≪≫ i₅ ≪≫ i₆

/-- **The small square of Stacks 0DGI on `D⁺`**: `Rf_{small,*} ∘ Ra_{Y,*} = Ra_{X,*} ∘
Rf_{big,fppf,*}` (Stacks 0D6E), for any `f`. -/
def fppfToSmallEtale_rightDerivedPushforwardIso :
    (fppfToSmallEtaleAbelianPushforward T E h Y).rightDerivedFunctorPlus ⋙
        (E.smallEtalePushforward (etaleMap T E h f)).rightDerivedFunctorPlus ≅
      (fppfAbelianPushforward T f).rightDerivedFunctorPlus ⋙
        (fppfToSmallEtaleAbelianPushforward T E h X).rightDerivedFunctorPlus :=
  (Functor.rightDerivedFunctorPlusCompIso _ _).symm ≪≫
    Functor.rightDerivedFunctorPlusNatIso
      (fppfToSmallEtale_comp_fppfAbelianPushforwardIso T E h f).symm ≪≫
    Functor.rightDerivedFunctorPlusCompIso _ _

/-- **The base change map of Stacks 0DGK**, `a_X⁻¹(Rf_{small,*}K) ⟶ Rf_{big,fppf,*}(a_Y⁻¹K)`: the
mate, for the adjunctions `a⁻¹ ⊣ Ra_*` on `D⁺`, of the square
`Rf_{small,*} ∘ Ra_{Y,*} = Ra_{X,*} ∘ Rf_{big,fppf,*}`. -/
def fppfToSmallEtaleDerivedBaseChange :
    (E.smallEtalePushforward (etaleMap T E h f)).rightDerivedFunctorPlus ⋙
        (CategoryTheory.Sites.abelianInverseImage
          (fppfToSmallEtaleMorphism T E h X)).mapDerivedCategoryPlus ⟶
      (CategoryTheory.Sites.abelianInverseImage
          (fppfToSmallEtaleMorphism T E h Y)).mapDerivedCategoryPlus ⋙
        (fppfAbelianPushforward T f).rightDerivedFunctorPlus :=
  ((mateEquiv
    (Stacks.ComparingTopologies.derivedPlusAdjunction (fppfToSmallEtaleAbelianAdjunction T E h Y))
    (Stacks.ComparingTopologies.derivedPlusAdjunction
      (fppfToSmallEtaleAbelianAdjunction T E h X))).symm
    (TwoSquare.mk _ _ _ _ (fppfToSmallEtale_rightDerivedPushforwardIso T E h f).hom)).natTrans

/-- **Stacks 0DGK, granted the scheme case.** For a finite morphism `f : Y ⟶ X` of algebraic
spaces the base change map `a_X⁻¹(Rf_{small,*}K) ⟶ Rf_{big,fppf,*}(a_Y⁻¹K)` is an isomorphism for
every `K` in `D⁺(Y_étale)`. -/
theorem isIso_fppfToSmallEtaleDerivedBaseChange_of
    (hsch : SchemeFppfEtaleHigherVanishing E.fppfSite)
    (hf : Space.IsFinite T.schemeSite S T.scheme_mem f.hom) :
    IsIso (fppfToSmallEtaleDerivedBaseChange T E h f) := by
  have : IsIso (TwoSquare.mk _ _ _ _
      (fppfToSmallEtale_rightDerivedPushforwardIso T E h f).hom).natTrans :=
    inferInstanceAs (IsIso (fppfToSmallEtale_rightDerivedPushforwardIso T E h f).hom)
  have : ∀ K, IsIso ((fppfToSmallEtaleDerivedBaseChange T E h f).app K) := fun K ↦
    Stacks.ComparingTopologies.isIso_mateEquiv_symm_app _ _ _
      (fun L ↦ (isIso_fppfToSmallEtale_derivedUnits_of T E h Y hsch L).2)
      (fun L ↦ (isIso_fppfToSmallEtale_derivedUnits_of T E h X hsch L).2) K
      ((fppfToSmallEtale_rightDerivedPushforwardIsoOfIsFinite_of T E h f hsch hf).app K)
  exact NatIso.isIso_of_isIso_app _

end AlgebraicGeometry.BigFppfSpaceSite

end
