module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigPhToSmallEtaleDerivedTorsion
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigPhSmallEtaleProperPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfToSmallEtaleProperDerivedPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigSmallEtaleTorsionDerivedPushforwardUnconditional

/-!
# Derived direct image along a proper morphism and the big ph topos (Stacks 0DGX (2))

Let `P` be a big ph site of algebraic spaces over a scheme `S`, `E` a big étale site over the same
big fppf site of schemes, and `f : Y ⟶ X` a proper morphism of algebraic spaces. Stacks 0DGX,
part (2), says that `a_X⁻¹(Rf_{small,*}K) = Rf_{big,ph,*}(a_Y⁻¹K)` for `K` in `D⁺(Y_étale)` with
torsion cohomology sheaves.

## Main definitions

* `AlgebraicGeometry.BigPHSpaceSite.phAbelianPushforward`: `f_{big,ph,*}` on abelian sheaves.
* `AlgebraicGeometry.BigPHSpaceSite.phToBigEtale_rightDerivedPushforwardIso`: Stacks 0D6E for `ε`
  and `f`, `Rε_{X,*} ∘ Rf_{big,ph,*} = Rf_{big,étale,*} ∘ Rε_{Y,*}`.
* `AlgebraicGeometry.BigPHSpaceSite.phToSmallEtaleDerivedBaseChange`: the comparison
  `Rf_{small,*} ∘ a_X⁻¹ ⟶ a_Y⁻¹ ∘ Rf_{big,ph,*}` on `D⁺(Y_étale)`.

## Main results

* `AlgebraicGeometry.BigPHSpaceSite.isIso_phToSmallEtaleDerivedBaseChange_app_of_isProper` and
  `AlgebraicGeometry.BigPHSpaceSite.phToSmallEtaleDerivedPushforwardIsoOfIsProper`:
  **Stacks 0DGX, part (2)**.

## Implementation notes

The source shows that `Rε_{X,*}` of the base change map is invertible, through
`Rε_{X,*}Rf_{big,ph,*}a_Y⁻¹K = Rf_{big,étale,*}Rε_{Y,*}a_Y⁻¹K = Rf_{big,étale,*}π_Y⁻¹K
= π_X⁻¹Rf_{small,*}K = Rε_{X,*}a_X⁻¹Rf_{small,*}K` (Stacks 0D6E, 0DGU, 0DGD (2), 0DGU), and then
argues by induction on cohomology sheaves that a map `a_X⁻¹L ⟶ M` inverted by `Rε_{X,*}` is
invertible. As in the fppf development of Stacks 0DGJ
(`StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfToSmallEtaleProperDerivedPushforward`),
the induction is avoided: `ε_{X,*}` is fully faithful, so `ε_X⁻¹ ∘ Rε_{X,*} = 𝟭` on `D⁺`, and the
comparison is defined as `ε_X⁻¹` applied to the étale base change map of Stacks 0DGD, part (2),
followed by the unit `π_Y⁻¹ ⟶ Rε_{Y,*}a_Y⁻¹` of Stacks 0DGU, Stacks 0D6E, and that counit. The only
step that is not invertible on all of `D⁺` is the unit; it is invertible at `K` with torsion
cohomology sheaves by Stacks 0DGU, and the base change map of Stacks 0DGD is invertible there for
`f` proper.

The derived categories are in the model `HasDerivedCategory.standard`, that of Stacks 0DGU and of
Stacks 0DGD (2).

## References

* [Stacks Project, Tag 0DGX](https://stacks.math.columbia.edu/tag/0DGX)
* [Stacks Project, Tag 0DGD](https://stacks.math.columbia.edu/tag/0DGD)
* [Stacks Project, Tag 0DGU](https://stacks.math.columbia.edu/tag/0DGU)
* [Stacks Project, Tag 0D6E](https://stacks.math.columbia.edu/tag/0D6E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.BigPHSpaceSite

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

attribute [local instance] BigEtaleSpaceSite.bigToSmallAbelianInverseImage_additive
  HasDerivedCategory.standard

variable {S : Scheme.{u}} (P : BigPHSpaceSite S) (E : BigEtaleSpaceSite S)
  (h : P.fppfSite = E.fppfSite) {X Y : P.Spaces} (f : Y ⟶ X)

/-- The direct image `f_{big,ph,*}` of abelian sheaves on the big ph sites, as the right
adjoint attached to cocontinuity of `Over.map f`. -/
abbrev phAbelianPushforward :
    Sheaf (BigPHSpaceOver.topology P Y) AddCommGrpCat.{u + 1} ⥤
      Sheaf (BigPHSpaceOver.topology P X) AddCommGrpCat.{u + 1} :=
  (Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
    (BigPHSpaceOver.topology P Y) (BigPHSpaceOver.topology P X)

/-- **The big square of Stacks 0DGW on abelian sheaves**:
`ε_{X,*} ∘ f_{big,ph,*} = f_{big,étale,*} ∘ ε_{Y,*}`. -/
def phToBigEtale_comp_phAbelianPushforwardIso :
    phAbelianPushforward P f ⋙ phToBigEtaleAbelianPushforward P E h X ≅
      phToBigEtaleAbelianPushforward P E h Y ⋙
        E.bigEtalePushforward (etaleMap P E h f) := by
  let JeX := E.bigEtaleTopology (etaleSpace P E h X)
  let JeY := E.bigEtaleTopology (etaleSpace P E h Y)
  let JpX := BigPHSpaceOver.topology P X
  let JpY := BigPHSpaceOver.topology P Y
  let eX := (Over.postEquiv (canonicalSpaceEquivalence P E h).1 (X := X)).inverse
  let eY := (Over.postEquiv (canonicalSpaceEquivalence P E h).1 (X := Y)).inverse
  let be := Over.pullback (etaleMap P E h f)
  let bf := Over.pullback f
  haveI hbpE : be.IsContinuous JeX JeY :=
    (StacksRelocalization.isMorphismOfSites_overPullback E.topology (etaleMap P E h f)).isContinuous
  haveI hbpF : bf.IsContinuous JpX JpY :=
    (StacksRelocalization.isMorphismOfSites_overPullback P.topology f).isContinuous
  haveI : (be ⋙ eY).IsContinuous JeX JpY := Functor.isContinuous_comp be eY JeX JeY JpY
  haveI : (eX ⋙ bf).IsContinuous JeX JpY := Functor.isContinuous_comp eX bf JeX JpX JpY
  let ρF := (Over.mapPullbackAdj f).sheafPushforwardCocontinuousIso AddCommGrpCat.{u + 1}
    (J := JpY) (K := JpX)
  let ρE := (Over.mapPullbackAdj (etaleMap P E h f)).sheafPushforwardCocontinuousIso
    AddCommGrpCat.{u + 1} (J := JeY) (K := JeX)
  exact Functor.isoWhiskerRight ρF _ ≪≫
    Functor.sheafPushforwardContinuousComp eX bf AddCommGrpCat.{u + 1} JeX JpX JpY ≪≫
    Functor.sheafPushforwardContinuousIso (pullbackChangeOfTopologyIso P E h f).symm
      AddCommGrpCat.{u + 1} JeX JpY ≪≫
    (Functor.sheafPushforwardContinuousComp be eY AddCommGrpCat.{u + 1} JeX JeY JpY).symm ≪≫
    Functor.isoWhiskerLeft _ ρE.symm

/-- The direct image `ε_{Z,*}` of abelian sheaves from the big ph site to the big étale site
preserves injective objects. -/
instance phToBigEtaleAbelianPushforward_preservesInjectiveObjects (Z : P.Spaces) :
    (phToBigEtaleAbelianPushforward P E h Z).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (phToBigEtaleAbelianAdjunction P E h Z)

/-- **Stacks 0D6E for `ε` and `f`**: `Rε_{X,*} ∘ Rf_{big,ph,*} = Rf_{big,étale,*} ∘ Rε_{Y,*}` on
`D⁺((Spaces/Y)_ph)`, for any morphism `f : Y ⟶ X`. Both `f_{big,ph,*}` and `ε_{Y,*}` preserve
injective objects, being right adjoint to exact functors, so each composite is derived as the
composite of the derived functors, and the underived composites agree by the big square of Stacks
0DGI. -/
def phToBigEtale_rightDerivedPushforwardIso :
    (phAbelianPushforward P f).rightDerivedFunctorPlus ⋙
        (phToBigEtaleAbelianPushforward P E h X).rightDerivedFunctorPlus ≅
      (phToBigEtaleAbelianPushforward P E h Y).rightDerivedFunctorPlus ⋙
        (E.bigEtalePushforward (etaleMap P E h f)).rightDerivedFunctorPlus :=
  (Functor.rightDerivedFunctorPlusCompIso _ _).symm ≪≫
    Functor.rightDerivedFunctorPlusNatIso (phToBigEtale_comp_phAbelianPushforwardIso P E h f) ≪≫
    Functor.rightDerivedFunctorPlusCompIso _ _


/-- **The comparison of Stacks 0DGX (2), from one for `π`.** A natural transformation
`β : Rf_{small,*} ∘ π_X⁻¹ ⟶ π_Y⁻¹ ∘ Rf_{big,étale,*}` on `D⁺(Y_étale)` induces a natural
transformation `Rf_{small,*} ∘ a_X⁻¹ ⟶ a_Y⁻¹ ∘ Rf_{big,ph,*}`: write `a_X⁻¹ = ε_X⁻¹ ∘ π_X⁻¹`, apply
`ε_X⁻¹` to `β`, then the unit `π_Y⁻¹ ⟶ Rε_{Y,*}ε_Y⁻¹π_Y⁻¹ = Rε_{Y,*}a_Y⁻¹`, Stacks 0D6E
`Rf_{big,étale,*} ∘ Rε_{Y,*} = Rε_{X,*} ∘ Rf_{big,ph,*}`, and the counit `ε_X⁻¹ ∘ Rε_{X,*} = 𝟭`
(invertible, `ε_{X,*}` being fully faithful). -/
def phToSmallEtaleDerivedBaseChangeOfBigEtale
    (β : (E.smallEtalePushforward (etaleMap P E h f)).rightDerivedFunctorPlus ⋙
        (CategoryTheory.Sites.abelianInverseImage
          (E.bigToSmallEtaleMorphism (etaleSpace P E h X))).mapDerivedCategoryPlus ⟶
      (CategoryTheory.Sites.abelianInverseImage
          (E.bigToSmallEtaleMorphism (etaleSpace P E h Y))).mapDerivedCategoryPlus ⋙
        (E.bigEtalePushforward (etaleMap P E h f)).rightDerivedFunctorPlus) :
    (E.smallEtalePushforward (etaleMap P E h f)).rightDerivedFunctorPlus ⋙
        (CategoryTheory.Sites.abelianInverseImage
          (phToSmallEtaleMorphism P E h X)).mapDerivedCategoryPlus ⟶
      (CategoryTheory.Sites.abelianInverseImage
          (phToSmallEtaleMorphism P E h Y)).mapDerivedCategoryPlus ⋙
        (phAbelianPushforward P f).rightDerivedFunctorPlus := by
  let πY := CategoryTheory.Sites.abelianInverseImage
    (E.bigToSmallEtaleMorphism (etaleSpace P E h Y))
  haveI : ∀ M, IsIso ((Stacks.ComparingTopologies.derivedPlusAdjunction
      (phToBigEtaleAbelianAdjunction P E h X)).counit.app M) := fun M ↦
    Stacks.ComparingTopologies.isIso_derivedPlusAdjunction_counit_app_of_fullyFaithful
      (phToBigEtaleAbelianAdjunction P E h X) M
  haveI := NatIso.isIso_of_isIso_app
    (Stacks.ComparingTopologies.derivedPlusAdjunction
      (phToBigEtaleAbelianAdjunction P E h X)).counit
  let c := asIso
    (Stacks.ComparingTopologies.derivedPlusAdjunction
      (phToBigEtaleAbelianAdjunction P E h X)).counit
  let uY := Functor.whiskerLeft πY.mapDerivedCategoryPlus
    (Stacks.ComparingTopologies.derivedPlusAdjunction
      (phToBigEtaleAbelianAdjunction P E h Y)).unit
  let aY := Functor.mapDerivedCategoryPlusCompIsoh
    (phToSmallEtale_abelianInverseImageCompIso P E h Y)
  let D := phToBigEtale_rightDerivedPushforwardIso P E h f
  let AY := (CategoryTheory.Sites.abelianInverseImage
    (phToSmallEtaleMorphism P E h Y)).mapDerivedCategoryPlus
  let EX := (CategoryTheory.Sites.abelianInverseImage
    (phToBigEtaleMorphism P E h X)).mapDerivedCategoryPlus
  let RεY := (phToBigEtaleAbelianPushforward P E h Y).rightDerivedFunctorPlus
  let RF := (phAbelianPushforward P f).rightDerivedFunctorPlus
  let Rfe := (E.bigEtalePushforward (etaleMap P E h f)).rightDerivedFunctorPlus
  exact (Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryPlusCompIsoh
      (phToSmallEtale_abelianInverseImageCompIso P E h X)).symm).hom ≫
    Functor.whiskerRight β EX ≫
    Functor.whiskerRight (Functor.whiskerRight uY Rfe) EX ≫
    (Functor.isoWhiskerRight (Functor.isoWhiskerRight (Functor.isoWhiskerRight aY RεY) Rfe) EX ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft AY D.symm) EX ≪≫
      Functor.isoWhiskerLeft (AY ⋙ RF) c).hom

/-- The comparison of `phToSmallEtaleDerivedBaseChangeOfBigEtale` is invertible at every `K` at
which `β` is and at which the unit `π_Y⁻¹K ⟶ Rε_{Y,*}a_Y⁻¹K` of Stacks 0DGU is. -/
theorem isIso_phToSmallEtaleDerivedBaseChangeOfBigEtale_app
    (β : (E.smallEtalePushforward (etaleMap P E h f)).rightDerivedFunctorPlus ⋙
        (CategoryTheory.Sites.abelianInverseImage
          (E.bigToSmallEtaleMorphism (etaleSpace P E h X))).mapDerivedCategoryPlus ⟶
      (CategoryTheory.Sites.abelianInverseImage
          (E.bigToSmallEtaleMorphism (etaleSpace P E h Y))).mapDerivedCategoryPlus ⋙
        (E.bigEtalePushforward (etaleMap P E h f)).rightDerivedFunctorPlus)
    (K : DerivedCategory.Plus (Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem
      (etaleSpace P E h Y)) AddCommGrpCat.{u + 1}))
    [IsIso (β.app K)]
    [IsIso ((Stacks.ComparingTopologies.derivedPlusAdjunction
        (phToBigEtaleAbelianAdjunction P E h Y)).unit.app
          ((CategoryTheory.Sites.abelianInverseImage
            (E.bigToSmallEtaleMorphism (etaleSpace P E h Y))).mapDerivedCategoryPlus.obj K))] :
    IsIso ((phToSmallEtaleDerivedBaseChangeOfBigEtale P E h f β).app K) := by
  simp only [phToSmallEtaleDerivedBaseChangeOfBigEtale, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app]
  infer_instance

/-- The comparison of Stacks 0DGX, part (2), `Rf_{small,*} ∘ a_X⁻¹ ⟶ a_Y⁻¹ ∘ Rf_{big,ph,*}` on
`D⁺(Y_étale)`: the one induced by the base change map
`Rf_{small,*} ∘ π_X⁻¹ ⟶ π_Y⁻¹ ∘ Rf_{big,étale,*}` of Stacks 0DGD, part (2). -/
def phToSmallEtaleDerivedBaseChange :
    (E.smallEtalePushforward (etaleMap P E h f)).rightDerivedFunctorPlus ⋙
        (CategoryTheory.Sites.abelianInverseImage
          (phToSmallEtaleMorphism P E h X)).mapDerivedCategoryPlus ⟶
      (CategoryTheory.Sites.abelianInverseImage
          (phToSmallEtaleMorphism P E h Y)).mapDerivedCategoryPlus ⋙
        (phAbelianPushforward P f).rightDerivedFunctorPlus :=
  phToSmallEtaleDerivedBaseChangeOfBigEtale P E h f
    (Stacks.DerivedFunctor.plusTwoSquareOfTotalRightDerived _ _ _ _
      (BigEtaleSpaceSite.bigToSmallEtaleDerivedBaseChange E (etaleMap P E h f)))

/-- **Stacks 0DGX, part (2), as invertibility of the comparison.** For a proper morphism
`f : Y ⟶ X` of algebraic spaces and `K` in `D⁺(Y_étale)` with torsion cohomology sheaves, the
comparison `a_X⁻¹(Rf_{small,*}K) ⟶ Rf_{big,ph,*}(a_Y⁻¹K)` is invertible. -/
theorem isIso_phToSmallEtaleDerivedBaseChange_app_of_isProper
    (hf : Space.IsProper P.fppfSite S P.fppf_mem f.hom)
    (K : DerivedCategory.Plus (Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem
      (etaleSpace P E h Y)) AddCommGrpCat.{u + 1}))
    (hK : ∀ i : ℤ, Stacks.Torsion.torsionSheafProperty _
      ((DerivedCategory.homologyFunctor _ i).obj (DerivedCategory.Plus.ι.obj K))) :
    IsIso ((phToSmallEtaleDerivedBaseChange P E h f).app K) := by
  obtain ⟨n, hn⟩ := K.property
  have : (DerivedCategory.Plus.ι.obj K).IsGE n := hn
  have := BigEtaleSpaceSite.isIso_bigToSmallEtaleDerivedBaseChange_app_of_isProper E
    (etaleMap P E h f) (isProper_etaleMap P E h f hf) (DerivedCategory.Plus.ι.obj K) n hn hK
  have := Stacks.DerivedFunctor.isIso_plusTwoSquareOfTotalRightDerived_app _ _ _ _
    (BigEtaleSpaceSite.bigToSmallEtaleDerivedBaseChange E (etaleMap P E h f)) K
  have := (isIso_phToSmallEtale_derivedUnits P E h Y K hK).1
  exact isIso_phToSmallEtaleDerivedBaseChangeOfBigEtale_app P E h f _ K

/-- **Stacks 0DGX, part (2).** Let `f : Y ⟶ X` be a proper morphism of algebraic spaces over `S`
and `K` an object of `D⁺(Y_étale)` whose cohomology sheaves are torsion. Then
`a_X⁻¹(Rf_{small,*}K) = Rf_{big,ph,*}(a_Y⁻¹K)`, by the canonical comparison
`AlgebraicGeometry.BigPHSpaceSite.phToSmallEtaleDerivedBaseChange`. -/
@[stacks 0DGX "(2)"]
def phToSmallEtaleDerivedPushforwardIsoOfIsProper
    (hf : Space.IsProper P.fppfSite S P.fppf_mem f.hom)
    (K : DerivedCategory.Plus (Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem
      (etaleSpace P E h Y)) AddCommGrpCat.{u + 1}))
    (hK : ∀ i : ℤ, Stacks.Torsion.torsionSheafProperty _
      ((DerivedCategory.homologyFunctor _ i).obj (DerivedCategory.Plus.ι.obj K))) :
    (CategoryTheory.Sites.abelianInverseImage
        (phToSmallEtaleMorphism P E h X)).mapDerivedCategoryPlus.obj
        ((E.smallEtalePushforward (etaleMap P E h f)).rightDerivedFunctorPlus.obj K) ≅
      (phAbelianPushforward P f).rightDerivedFunctorPlus.obj
        ((CategoryTheory.Sites.abelianInverseImage
          (phToSmallEtaleMorphism P E h Y)).mapDerivedCategoryPlus.obj K) :=
  haveI := isIso_phToSmallEtaleDerivedBaseChange_app_of_isProper P E h f hf K hK
  asIso ((phToSmallEtaleDerivedBaseChange P E h f).app K)

end AlgebraicGeometry.BigPHSpaceSite

end
