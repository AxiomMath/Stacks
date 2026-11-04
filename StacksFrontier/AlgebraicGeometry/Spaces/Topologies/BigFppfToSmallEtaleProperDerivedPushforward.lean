module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfToSmallEtaleFinitePushforward
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.BoundedBelowRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigSmallEtaleTorsionDerivedPushforwardUnconditional

/-!
# Derived direct image along a proper morphism and the big fppf topos (towards Stacks 0DGJ (2))

Let `T` be a big fppf site of algebraic spaces over a scheme `S`, `E` a big étale site of
algebraic spaces over the same big fppf site of schemes, and `f : Y ⟶ X` a morphism of algebraic
spaces. This file builds the comparison of Stacks 0DGJ, part (2),
`Rf_{small,*} ∘ a_X⁻¹ ⟶ a_Y⁻¹ ∘ Rf_{big,fppf,*}` on `D⁺(Y_étale)`, from a comparison
`Rf_{small,*} ∘ π_X⁻¹ ⟶ π_Y⁻¹ ∘ Rf_{big,étale,*}` for the big étale site (Stacks 0DGD, part (2)),
and shows that the first is invertible wherever the second is.

## Main definitions

* `Stacks.DerivedFunctor.plusTwoSquareOfTotalRightDerived`: a comparison
  `RF ⋙ P ⟶ Q ⋙ RG` of unbounded right derived functors composed with exact functors, restricted
  to bounded below derived categories.
* `AlgebraicGeometry.BigFppfSpaceSite.fppfToBigEtale_rightDerivedPushforwardInverseImageIso_of`:
  `ε_X⁻¹ ∘ Rf_{big,étale,*} ∘ π_Y⁻¹ ≅ a_Y⁻¹ ∘ Rf_{big,fppf,*}`, granted the scheme case of
  Stacks 0DDS (1).
* `AlgebraicGeometry.BigFppfSpaceSite.fppfToSmallEtaleDerivedBaseChangeOfBigEtale`: the
  comparison for `a` induced by one for `π`.

## Main results

* `Stacks.DerivedFunctor.isIso_plusTwoSquareOfTotalRightDerived_app` and
  `AlgebraicGeometry.BigFppfSpaceSite.isIso_fppfToSmallEtaleDerivedBaseChangeOfBigEtale_app`:
  invertibility is inherited objectwise.

## Implementation notes

The source shows that `Rε_{X,*}` of the base change map is invertible and then argues by
induction on cohomology sheaves that a map `a_X⁻¹L ⟶ M` inverted by `Rε_{X,*}` is invertible.
Here, as in the proof of Stacks 0DGK, the induction is avoided: `ε_{X,*}` is fully faithful, so
`ε_X⁻¹ ∘ Rε_{X,*} = 𝟭` on `D⁺`
(`Stacks.ComparingTopologies.isIso_derivedPlusAdjunction_counit_app_of_fullyFaithful`), and the
comparison is `ε_X⁻¹` applied to the big étale one, followed by the isomorphisms
`π_Y⁻¹ = Rε_{Y,*} ∘ a_Y⁻¹` (Stacks 0DGG) and
`Rf_{big,étale,*} ∘ Rε_{Y,*} = Rε_{X,*} ∘ Rf_{big,fppf,*}` (Stacks 0D6E). The scheme case of
Stacks 0DDS (1) enters only through Stacks 0DGG; it is carried as
`AlgebraicGeometry.SchemeFppfEtaleHigherVanishing` until it is proved.

The comparison for the big étale site is stated on unbounded derived categories; it is read on
`D⁺` through `Stacks.DerivedFunctor.rightDerivedFunctorPlusCompιIso`, the inclusion
`D⁺ ⥤ D` being fully faithful.

## References

* [Stacks Project, Tag 0DGJ](https://stacks.math.columbia.edu/tag/0DGJ)
* [Stacks Project, Tag 0DGD](https://stacks.math.columbia.edu/tag/0DGD)
* [Stacks Project, Tag 0DGG](https://stacks.math.columbia.edu/tag/0DGG)
* [Stacks Project, Tag 0D6E](https://stacks.math.columbia.edu/tag/0D6E)
* [Stacks Project, Tag 05T5](https://stacks.math.columbia.edu/tag/05T5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.DerivedFunctor

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

universe vA₁ uA₁ vA₂ uA₂ vB₁ uB₁ vB₂ uB₂ wG wA₁ wA₂ wB₁ wB₂

variable {A₁ : Type uA₁} [Category.{vA₁} A₁] [Abelian A₁] [IsGrothendieckAbelian.{wG} A₁]
  [HasDerivedCategory.{wA₁} A₁]
  {A₂ : Type uA₂} [Category.{vA₂} A₂] [Abelian A₂] [HasDerivedCategory.{wA₂} A₂]
  {B₁ : Type uB₁} [Category.{vB₁} B₁] [Abelian B₁] [IsGrothendieckAbelian.{wG} B₁]
  [HasDerivedCategory.{wB₁} B₁]
  {B₂ : Type uB₂} [Category.{vB₂} B₂] [Abelian B₂] [HasDerivedCategory.{wB₂} B₂]
  (F : A₁ ⥤ A₂) [F.Additive] (G : B₁ ⥤ B₂) [G.Additive]
  (P : A₂ ⥤ B₂) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  (Q : A₁ ⥤ B₁) [Q.Additive] [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]

/-- The comparison `RF ⋙ P ⟶ Q ⋙ RG` of unbounded right derived functors composed with exact
functors, read on bounded below objects through the inclusions `D⁺ ⥤ D` and the identifications
`RF⁺ ⋙ ι ≅ ι ⋙ RF` of Stacks 05T5. -/
def plusTwoSquareComparison
    (β : totalRightDerived F ⋙ P.mapDerivedCategory ⟶
      Q.mapDerivedCategory ⋙ totalRightDerived G) :
    (F.rightDerivedFunctorPlus ⋙ P.mapDerivedCategoryPlus) ⋙ DerivedCategory.Plus.ι ⟶
      (Q.mapDerivedCategoryPlus ⋙ G.rightDerivedFunctorPlus) ⋙ DerivedCategory.Plus.ι :=
  Functor.whiskerRight (rightDerivedFunctorPlusCompιIso F).hom P.mapDerivedCategory ≫
    Functor.whiskerLeft DerivedCategory.Plus.ι β ≫
    Functor.whiskerLeft Q.mapDerivedCategoryPlus (rightDerivedFunctorPlusCompιIso G).inv

/-- **A comparison of unbounded right derived functors restricts to `D⁺`**: the natural
transformation `RF⁺ ⋙ P ⟶ Q ⋙ RG⁺` of functors on bounded below derived categories whose image
under `D⁺ ⥤ D` is `plusTwoSquareComparison`. -/
def plusTwoSquareOfTotalRightDerived
    (β : totalRightDerived F ⋙ P.mapDerivedCategory ⟶
      Q.mapDerivedCategory ⋙ totalRightDerived G) :
    F.rightDerivedFunctorPlus ⋙ P.mapDerivedCategoryPlus ⟶
      Q.mapDerivedCategoryPlus ⋙ G.rightDerivedFunctorPlus :=
  ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimage
    (plusTwoSquareComparison F G P Q β)

/-- The restriction to `D⁺` of a comparison of unbounded right derived functors is invertible at
every bounded below object at which the comparison is. -/
theorem isIso_plusTwoSquareOfTotalRightDerived_app
    (β : totalRightDerived F ⋙ P.mapDerivedCategory ⟶
      Q.mapDerivedCategory ⋙ totalRightDerived G)
    (K : DerivedCategory.Plus A₁) [IsIso (β.app (DerivedCategory.Plus.ι.obj K))] :
    IsIso ((plusTwoSquareOfTotalRightDerived F G P Q β).app K) := by
  have h : DerivedCategory.Plus.ι.map ((plusTwoSquareOfTotalRightDerived F G P Q β).app K) =
      (plusTwoSquareComparison F G P Q β).app K :=
    congrArg (fun φ => NatTrans.app φ K)
      (((ObjectProperty.fullyFaithfulι _).whiskeringRight _).map_preimage
        (plusTwoSquareComparison F G P Q β))
  have : IsIso (DerivedCategory.Plus.ι.map
      ((plusTwoSquareOfTotalRightDerived F G P Q β).app K)) := by
    rw [h]
    have h₁ : IsIso (P.mapDerivedCategory.map
        ((rightDerivedFunctorPlusCompιIso F).hom.app K)) := inferInstance
    have h₂ : IsIso (β.app (DerivedCategory.Plus.ι.obj K)) := inferInstance
    have h₃ : IsIso ((rightDerivedFunctorPlusCompιIso G).inv.app
        (Q.mapDerivedCategoryPlus.obj K)) := inferInstance
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h₁ (@IsIso.comp_isIso _ _ _ _ _ _ _ h₂ h₃)
  exact isIso_of_reflects_iso _ DerivedCategory.Plus.ι

end Stacks.DerivedFunctor

namespace AlgebraicGeometry.BigFppfSpaceSite

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

attribute [local instance] BigEtaleSpaceSite.bigToSmallAbelianInverseImage_additive

variable {S : Scheme.{u}} (T : BigFppfSpaceSite S) (E : BigEtaleSpaceSite S)
  (h : T.schemeSite = E.fppfSite) {X Y : T.Spaces} (f : Y ⟶ X)

section AnyModel

variable [HasDerivedCategory (Sheaf (BigFppfSpaceOver.topology T X) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory (Sheaf (BigFppfSpaceOver.topology T Y) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory (Sheaf (E.bigEtaleTopology (etaleSpace T E h X)) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory (Sheaf (E.bigEtaleTopology (etaleSpace T E h Y)) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory (Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem
    (etaleSpace T E h X)) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory (Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem
    (etaleSpace T E h Y)) AddCommGrpCat.{u + 1})]

/-- **The fppf side of the comparison, through the big étale site.** Granted the scheme case of
Stacks 0DDS (1), `ε_X⁻¹ ∘ Rf_{big,étale,*} ∘ π_Y⁻¹ ≅ a_Y⁻¹ ∘ Rf_{big,fppf,*}` on `D⁺(Y_étale)`: by
Stacks 0DGG, `π_Y⁻¹ = Rε_{Y,*} ∘ a_Y⁻¹`; by Stacks 0D6E,
`Rf_{big,étale,*} ∘ Rε_{Y,*} = Rε_{X,*} ∘ Rf_{big,fppf,*}`; and `ε_X⁻¹ ∘ Rε_{X,*} = 𝟭`, the derived
counit being invertible since `ε_{X,*}` is fully faithful. -/
def fppfToBigEtale_rightDerivedPushforwardInverseImageIso_of
    (hsch : SchemeFppfEtaleHigherVanishing E.fppfSite) :
    ((CategoryTheory.Sites.abelianInverseImage
          (E.bigToSmallEtaleMorphism (etaleSpace T E h Y))).mapDerivedCategoryPlus ⋙
        (E.bigEtalePushforward (etaleMap T E h f)).rightDerivedFunctorPlus) ⋙
        (CategoryTheory.Sites.abelianInverseImage
          (fppfToBigEtaleMorphism T E h X)).mapDerivedCategoryPlus ≅
      (CategoryTheory.Sites.abelianInverseImage
          (fppfToSmallEtaleMorphism T E h Y)).mapDerivedCategoryPlus ⋙
        (fppfAbelianPushforward T f).rightDerivedFunctorPlus := by
  let πY := CategoryTheory.Sites.abelianInverseImage
    (E.bigToSmallEtaleMorphism (etaleSpace T E h Y))
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
  let D := fppfToBigEtale_rightDerivedPushforwardIso T E h f
  let AY := (CategoryTheory.Sites.abelianInverseImage
    (fppfToSmallEtaleMorphism T E h Y)).mapDerivedCategoryPlus
  let EX := (CategoryTheory.Sites.abelianInverseImage
    (fppfToBigEtaleMorphism T E h X)).mapDerivedCategoryPlus
  let EY := (CategoryTheory.Sites.abelianInverseImage
    (fppfToBigEtaleMorphism T E h Y)).mapDerivedCategoryPlus
  let RεY := (fppfToBigEtaleAbelianPushforward T E h Y).rightDerivedFunctorPlus
  let RεX := (fppfToBigEtaleAbelianPushforward T E h X).rightDerivedFunctorPlus
  let RF := (fppfAbelianPushforward T f).rightDerivedFunctorPlus
  let PY := πY.mapDerivedCategoryPlus
  let Rfe := (E.bigEtalePushforward (etaleMap T E h f)).rightDerivedFunctorPlus
  exact Functor.isoWhiskerRight (Functor.isoWhiskerRight uY Rfe) EX ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerRight (Functor.isoWhiskerRight aY RεY) Rfe) EX ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft AY D.symm) EX ≪≫
    Functor.isoWhiskerLeft (AY ⋙ RF) c

/-- **The derived comparison for `a`, from one for `π`.** A natural transformation
`β : Rf_{small,*} ∘ π_X⁻¹ ⟶ π_Y⁻¹ ∘ Rf_{big,étale,*}` on `D⁺(Y_étale)` induces, granted the scheme
case of Stacks 0DDS (1), a natural transformation
`Rf_{small,*} ∘ a_X⁻¹ ⟶ a_Y⁻¹ ∘ Rf_{big,fppf,*}`: write `a_X⁻¹ = ε_X⁻¹ ∘ π_X⁻¹`, apply `ε_X⁻¹` to
`β`, and conclude with `fppfToBigEtale_rightDerivedPushforwardInverseImageIso_of`. -/
def fppfToSmallEtaleDerivedBaseChangeOfBigEtale
    (hsch : SchemeFppfEtaleHigherVanishing E.fppfSite)
    (β : (E.smallEtalePushforward (etaleMap T E h f)).rightDerivedFunctorPlus ⋙
        (CategoryTheory.Sites.abelianInverseImage
          (E.bigToSmallEtaleMorphism (etaleSpace T E h X))).mapDerivedCategoryPlus ⟶
      (CategoryTheory.Sites.abelianInverseImage
          (E.bigToSmallEtaleMorphism (etaleSpace T E h Y))).mapDerivedCategoryPlus ⋙
        (E.bigEtalePushforward (etaleMap T E h f)).rightDerivedFunctorPlus) :
    (E.smallEtalePushforward (etaleMap T E h f)).rightDerivedFunctorPlus ⋙
        (CategoryTheory.Sites.abelianInverseImage
          (fppfToSmallEtaleMorphism T E h X)).mapDerivedCategoryPlus ⟶
      (CategoryTheory.Sites.abelianInverseImage
          (fppfToSmallEtaleMorphism T E h Y)).mapDerivedCategoryPlus ⋙
        (fppfAbelianPushforward T f).rightDerivedFunctorPlus :=
  (Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryPlusCompIsoh
      (fppfToSmallEtale_abelianInverseImageCompIso T E h X)).symm).hom ≫
    Functor.whiskerRight β (CategoryTheory.Sites.abelianInverseImage
      (fppfToBigEtaleMorphism T E h X)).mapDerivedCategoryPlus ≫
    (fppfToBigEtale_rightDerivedPushforwardInverseImageIso_of T E h f hsch).hom

/-- The comparison of `fppfToSmallEtaleDerivedBaseChangeOfBigEtale` is invertible at every `K`
at which `β` is. -/
theorem isIso_fppfToSmallEtaleDerivedBaseChangeOfBigEtale_app
    (hsch : SchemeFppfEtaleHigherVanishing E.fppfSite)
    (β : (E.smallEtalePushforward (etaleMap T E h f)).rightDerivedFunctorPlus ⋙
        (CategoryTheory.Sites.abelianInverseImage
          (E.bigToSmallEtaleMorphism (etaleSpace T E h X))).mapDerivedCategoryPlus ⟶
      (CategoryTheory.Sites.abelianInverseImage
          (E.bigToSmallEtaleMorphism (etaleSpace T E h Y))).mapDerivedCategoryPlus ⋙
        (E.bigEtalePushforward (etaleMap T E h f)).rightDerivedFunctorPlus)
    (K : DerivedCategory.Plus (Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem
      (etaleSpace T E h Y)) AddCommGrpCat.{u + 1}))
    [IsIso (β.app K)] :
    IsIso ((fppfToSmallEtaleDerivedBaseChangeOfBigEtale T E h f hsch β).app K) := by
  simp only [fppfToSmallEtaleDerivedBaseChangeOfBigEtale, NatTrans.comp_app,
    Functor.whiskerRight_app]
  infer_instance

end AnyModel

section StandardModel

attribute [local instance] HasDerivedCategory.standard

/-- The comparison of Stacks 0DGJ, part (2), `Rf_{small,*} ∘ a_X⁻¹ ⟶ a_Y⁻¹ ∘ Rf_{big,fppf,*}` on
`D⁺(Y_étale)`, granted the scheme case of Stacks 0DDS (1): the one induced by the base change map
`Rf_{small,*} ∘ π_X⁻¹ ⟶ π_Y⁻¹ ∘ Rf_{big,étale,*}` of Stacks 0DGD, part (2). -/
def fppfToSmallEtaleDerivedBaseChange_of (hsch : SchemeFppfEtaleHigherVanishing E.fppfSite) :
    (E.smallEtalePushforward (etaleMap T E h f)).rightDerivedFunctorPlus ⋙
        (CategoryTheory.Sites.abelianInverseImage
          (fppfToSmallEtaleMorphism T E h X)).mapDerivedCategoryPlus ⟶
      (CategoryTheory.Sites.abelianInverseImage
          (fppfToSmallEtaleMorphism T E h Y)).mapDerivedCategoryPlus ⋙
        (fppfAbelianPushforward T f).rightDerivedFunctorPlus :=
  fppfToSmallEtaleDerivedBaseChangeOfBigEtale T E h f hsch
    (Stacks.DerivedFunctor.plusTwoSquareOfTotalRightDerived _ _ _ _
      (BigEtaleSpaceSite.bigToSmallEtaleDerivedBaseChange E (etaleMap T E h f)))

/-- **Stacks 0DGJ, part (2), granted the scheme case of Stacks 0DDS (1) and the derived base
change of Stacks 0DGD, part (2).** -/
theorem isIso_fppfToSmallEtaleDerivedBaseChange_of_app
    (hsch : SchemeFppfEtaleHigherVanishing E.fppfSite)
    (hbc : ∀ (K : DerivedCategory (Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem
        (etaleSpace T E h Y)) AddCommGrpCat.{u + 1})) (n : ℤ), K.IsGE n →
      BigEtaleSpaceSite.HasTorsionCohomology E K →
        IsIso ((BigEtaleSpaceSite.bigToSmallEtaleDerivedBaseChange E (etaleMap T E h f)).app K))
    (K : DerivedCategory.Plus (Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem
      (etaleSpace T E h Y)) AddCommGrpCat.{u + 1}))
    (hK : BigEtaleSpaceSite.HasTorsionCohomology E (DerivedCategory.Plus.ι.obj K)) :
    IsIso ((fppfToSmallEtaleDerivedBaseChange_of T E h f hsch).app K) := by
  obtain ⟨n, hn⟩ := K.property
  have := hbc (DerivedCategory.Plus.ι.obj K) n hn hK
  have := Stacks.DerivedFunctor.isIso_plusTwoSquareOfTotalRightDerived_app _ _ _ _
    (BigEtaleSpaceSite.bigToSmallEtaleDerivedBaseChange E (etaleMap T E h f)) K
  exact isIso_fppfToSmallEtaleDerivedBaseChangeOfBigEtale_app T E h f hsch _ K

/-- A proper morphism of the big fppf site of algebraic spaces is proper as a morphism of the big
étale site. -/
theorem isProper_etaleMap (hf : Space.IsProper T.schemeSite S T.scheme_mem f.hom) :
    Space.IsProper E.fppfSite S E.fppf_mem (etaleMap T E h f).hom := by
  cases T with
  | mk tScheme tSchemeMem tInitial tInitialSmall tInitialFppf tBound tOrdinal tOrdinalLim
      tInitialBounded tIsSite tRepresentative =>
    cases E with
    | mk eSchemeSite eSchemeMem eFppfSite eFppfMem eInitial eInitialSmall eInitialEtale eBound
        eOrdinal eOrdinalLim eInitialBounded eIsSite eRepresentative =>
      cases h
      exact hf

/-- **Stacks 0DGJ, part (2), granted the scheme case of Stacks 0DDS (1).** For a proper morphism
`f : Y ⟶ X` of algebraic spaces and `K` in `D⁺(Y_étale)` with torsion cohomology sheaves, the
comparison `a_X⁻¹(Rf_{small,*}K) ⟶ Rf_{big,fppf,*}(a_Y⁻¹K)` is invertible. -/
theorem isIso_fppfToSmallEtaleDerivedBaseChange_of_app_of_isProper
    (hsch : SchemeFppfEtaleHigherVanishing E.fppfSite)
    (hf : Space.IsProper T.schemeSite S T.scheme_mem f.hom)
    (K : DerivedCategory.Plus (Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem
      (etaleSpace T E h Y)) AddCommGrpCat.{u + 1}))
    (hK : BigEtaleSpaceSite.HasTorsionCohomology E (DerivedCategory.Plus.ι.obj K)) :
    IsIso ((fppfToSmallEtaleDerivedBaseChange_of T E h f hsch).app K) :=
  isIso_fppfToSmallEtaleDerivedBaseChange_of_app T E h f hsch
    (fun K n hn hT ↦ BigEtaleSpaceSite.isIso_bigToSmallEtaleDerivedBaseChange_app_of_isProper E
      (etaleMap T E h f) (isProper_etaleMap T E h f hf) K n hn hT) K hK

end StandardModel

end AlgebraicGeometry.BigFppfSpaceSite

end
