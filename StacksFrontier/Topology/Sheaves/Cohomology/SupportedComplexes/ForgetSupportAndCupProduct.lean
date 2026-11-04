module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormula
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportedSectionsCanonicalMaps
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportedSectionsDerivedTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.DerivedSymmetryAndUnit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ConstraintNaturality
public import StacksFrontier.AlgebraicGeometry.RingedSpace.KFlatResolution
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ForgetSupportAndPullback
import StacksFrontier.AlgebraicGeometry.ClosedImmersion.DerivedPushforwardComparison
import StacksCore.Tactic.StacksAttribute

/-!
# Forgetting support and the cup product: the diagram chase

Let `Z` be a closed subset of a ringed space `(X, 𝒪_X)`, let `i : (Z, 𝒪_X|_Z) ⟶ (X, 𝒪_X)` be
the inclusion and let `K`, `M` be objects of `D(𝒪_X)`. This file reduces the square

```
H^a(X, K) × H^b_Z(X, M) -----> H^{a+b}_Z(X, K ⊗^L M)
    |                                  |
    v                                  v
H^a(X, K) × H^b(X, M) -------> H^{a+b}(X, K ⊗^L M)
```

of [Stacks, Tag 0G77] to an equation between the identifications of the corepresenting objects.
The square itself is
`Stacks.Cohomology.SupportedComplexes.forgetSupport_supportedCupProduct_square`.

## Main results

* `comp_counit_of_tensorMate` is the diagram chase, for an abstract comparison isomorphism,
  abstract tensor bifunctors, an abstract projection-formula map and abstract commutativity
  constraints.
* `forgetSupport_supportedCupProduct` is the chase at the derived categories of `X` and `Z`.
* `forgetSupport_supportedCupProduct_of_corepresentingCompatible` is the chase for the cup
  product `supportedCupProduct` of [Stacks, Tag 0G76], with the map of [Stacks, Tag 0G75], the
  invertibility of the projection-formula map ([Stacks, Tag 0B55]) and the naturality of the
  commutativity constraint of [Stacks, Tag 0FPT] supplied.
* `ShiftedUnitCorepresentingCompatible` is the compatibility of the identifications of the
  corepresenting objects `𝒪[-p]` with the comparisons `𝒪_X[-p] ⟶ i_*𝒪_Z[-p]`, and
  `forgetSupport_supportedCupProductOfClasses` is the square in the source's degrees from it.

## Implementation notes

The comparisons `ρ` and `ρV` are `shiftedUnitToPushforward` at `p = a + b` and `p = b`, the
derived comparisons `𝒪_X[-p] ⟶ i_*𝒪_Z[-p]`; `χ` is
`Stacks.RingedSpace.derivedPullbackShiftedUnitTensorIso`, the identification
`𝒪_Z[-a-b] ≅ (𝒪_X[-a])|_Z ⊗^L 𝒪_Z[-b]`, and `χX` is `Stacks.RingedSpace.shiftedUnitTensorIso`,
the identification `𝒪_X[-a-b] ≅ 𝒪_X[-a] ⊗^L 𝒪_X[-b]` of [Stacks, Tag 0FNH]. The compatibility
`ShiftedUnitCorepresentingCompatible` is a hypothesis of
`forgetSupport_supportedCupProductOfClasses`; it concerns the projection-formula map of
[Stacks, Tag 0B53] at the pair `(𝒪_Z[-b], 𝒪_X[-a])`, and so a compatibility of the comparison
of [Stacks, Tag 079U] with shifts.

## References

* [Stacks Project, Lemma 20.34.11 (Tag 0G77)](https://stacks.math.columbia.edu/tag/0G77)
* [Stacks Project, Remark 20.34.9 (Tag 0G75)](https://stacks.math.columbia.edu/tag/0G75)
* [Stacks Project, Remark 20.34.10 (Tag 0G76)](https://stacks.math.columbia.edu/tag/0G76)
* [Stacks Project, Lemma 20.34.1 (Tag 0A3B)](https://stacks.math.columbia.edu/tag/0A3B)
* [Stacks Project, Lemma 20.34.4 (Tag 0G70)](https://stacks.math.columbia.edu/tag/0G70)
* [Stacks Project, Lemma 20.28.6 (Tag 0B53)](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Lemma 20.28.8 (Tag 0B55)](https://stacks.math.columbia.edu/tag/0B55)
* [Stacks Project, Tag 0E2K](https://stacks.math.columbia.edu/tag/0E2K)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.DerivedTensor.RingedSite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedProjectionFormula
open Stacks.ClosedImmersion (mapDerivedCategoryIsoTotalRightDerived)
open Stacks.RingedSpace (shiftedUnitObject shiftedUnitTensorIso
  derivedPullbackShiftedUnitTensorIso)

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.AssociatedSheaf.hasModuleSheafify
  Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective

namespace Stacks.Cohomology.SupportedComplexes

/-- **The diagram chase behind [Stacks, Tag 0G77].** Let `cmp : P ≅ RP` be a comparison
isomorphism, let `Li` be a functor, let `TX`, `TZ` be bifunctors and let `pf` be a
projection-formula family `TX (RP E) C ⟶ RP (TZ E (Li C))`, natural in both arguments by `hpfL`
and `hpfR`, invertible at the two pairs occurring below. Let `bX`, `bZ` be commutativity
constraints for `TX` and `TZ`, natural by `hbX` and `hbZ`. Given a map `t : TZ (Li K) N ⟶ GKM`
whose transport through the comparison and `pf` factors `eKM` as in `hmate`, and
identifications `χ`, `χX` compatible with the comparisons `ρ`, `ρV` as in `hbk`, the square
formed by `(ξ, η) ↦ χ ≫ (Li ξ ⊗ η) ≫ t`, the forgetful maps `α ↦ ρ ≫ P α ≫ e` and the
ordinary product `(ξ, β) ↦ χX ≫ (ξ ⊗ β)` commutes. -/
theorem comp_counit_of_tensorMate {A B : Type*} [Category* A] [Category* B]
    {P RP : B ⥤ A} (cmp : P ≅ RP) (Li : A ⥤ B) (TX : A ⥤ A ⥤ A) (TZ : B ⥤ B ⥤ B)
    (pf : ∀ (E : B) (C : A), (TX.obj (RP.obj E)).obj C ⟶ RP.obj ((TZ.obj E).obj (Li.obj C)))
    (hpfL : ∀ {E E' : B} (e : E ⟶ E') (C : A),
      (TX.map (RP.map e)).app C ≫ pf E' C = pf E C ≫ RP.map ((TZ.map e).app (Li.obj C)))
    (hpfR : ∀ (E : B) {C C' : A} (k : C ⟶ C'),
      (TX.obj (RP.obj E)).map k ≫ pf E C' = pf E C ≫ RP.map ((TZ.obj E).map (Li.map k)))
    (bX : ∀ A₁ A₂ : A, (TX.obj A₁).obj A₂ ≅ (TX.obj A₂).obj A₁)
    (hbX : ∀ {A₁ A₁' A₂ A₂' : A} (a : A₁ ⟶ A₁') (b : A₂ ⟶ A₂'),
      ((TX.map a).app A₂ ≫ (TX.obj A₁').map b) ≫ (bX A₁' A₂').hom =
        (bX A₁ A₂).hom ≫ ((TX.map b).app A₁ ≫ (TX.obj A₂').map a))
    (bZ : ∀ B₁ B₂ : B, (TZ.obj B₁).obj B₂ ≅ (TZ.obj B₂).obj B₁)
    (hbZ : ∀ {B₁ B₁' B₂ B₂' : B} (a : B₁ ⟶ B₁') (b : B₂ ⟶ B₂'),
      ((TZ.map a).app B₂ ≫ (TZ.obj B₁').map b) ≫ (bZ B₁' B₂').hom =
        (bZ B₁ B₂).hom ≫ ((TZ.map b).app B₁ ≫ (TZ.obj B₂').map a))
    {K M U VX WX : A} {N GKM V W : B}
    (eM : P.obj N ⟶ M) (eKM : P.obj GKM ⟶ (TX.obj K).obj M)
    (t : (TZ.obj (Li.obj K)).obj N ⟶ GKM)
    (hpfNK : IsIso (pf N K)) (hpfVU : IsIso (pf V U))
    (hmate : P.map t ≫ eKM =
      P.map (bZ (Li.obj K) N).hom ≫ cmp.hom.app ((TZ.obj N).obj (Li.obj K)) ≫
        CategoryTheory.inv (I := hpfNK) (pf N K) ≫
        (TX.map (cmp.inv.app N)).app K ≫ (TX.map eM).app K ≫ (bX M K).hom)
    (χ : W ⟶ (TZ.obj (Li.obj U)).obj V) (χX : WX ⟶ (TX.obj U).obj VX)
    (ρ : WX ⟶ P.obj W) (ρV : VX ⟶ P.obj V)
    (hbk : ρ ≫ P.map χ ≫ P.map (bZ (Li.obj U) V).hom ≫
        cmp.hom.app ((TZ.obj V).obj (Li.obj U)) ≫
        CategoryTheory.inv (I := hpfVU) (pf V U) ≫ (bX (RP.obj V) U).hom ≫
        (TX.obj U).map (cmp.inv.app V) =
      χX ≫ (TX.obj U).map ρV)
    (ξ : U ⟶ K) (η : V ⟶ N) :
    ρ ≫ P.map (χ ≫ (TZ.map (Li.map ξ)).app V ≫ (TZ.obj (Li.obj K)).map η ≫ t) ≫ eKM =
      χX ≫ (TX.map ξ).app VX ≫ (TX.obj K).map (ρV ≫ P.map η ≫ eM) := by
  have := hpfNK
  have := hpfVU
  have hpf : pf V U ≫ RP.map ((TZ.map η).app (Li.obj U) ≫ (TZ.obj N).map (Li.map ξ)) =
      (TX.map (RP.map η)).app U ≫ (TX.obj (RP.obj N)).map ξ ≫ pf N K := by
    rw [Functor.map_comp, reassoc_of% (hpfL η U).symm, (hpfR N ξ).symm]
  have hpfi : RP.map ((TZ.map η).app (Li.obj U) ≫ (TZ.obj N).map (Li.map ξ)) ≫
        CategoryTheory.inv (pf N K) =
      CategoryTheory.inv (pf V U) ≫
        (TX.map (RP.map η)).app U ≫ (TX.obj (RP.obj N)).map ξ := by
    rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
    simpa only [Category.assoc] using hpf
  have hbraidP : P.map ((TZ.map (Li.map ξ)).app V) ≫ P.map ((TZ.obj (Li.obj K)).map η) ≫
        P.map (bZ (Li.obj K) N).hom =
      P.map (bZ (Li.obj U) V).hom ≫ P.map ((TZ.map η).app (Li.obj U)) ≫
        P.map ((TZ.obj N).map (Li.map ξ)) := by
    simp only [← Functor.map_comp]
    exact congrArg P.map (by rw [← Category.assoc, hbZ])
  have hcmpnat : P.map ((TZ.map η).app (Li.obj U)) ≫ P.map ((TZ.obj N).map (Li.map ξ)) ≫
        cmp.hom.app ((TZ.obj N).obj (Li.obj K)) =
      cmp.hom.app ((TZ.obj V).obj (Li.obj U)) ≫
        RP.map ((TZ.map η).app (Li.obj U) ≫ (TZ.obj N).map (Li.map ξ)) := by
    rw [← Category.assoc, ← Functor.map_comp]
    exact cmp.hom.naturality _
  have hcollapse : (TX.map (RP.map η)).app U ≫ (TX.map (cmp.inv.app N)).app U ≫
        (TX.map eM).app U =
      (TX.map (cmp.inv.app V ≫ P.map η ≫ eM)).app U := by
    have h : RP.map η ≫ cmp.inv.app N ≫ eM = cmp.inv.app V ≫ P.map η ≫ eM := by
      rw [← Category.assoc, cmp.inv.naturality, Category.assoc]
    simp only [← NatTrans.comp_app, ← Functor.map_comp, h]
  have hbraidX : (TX.map (cmp.inv.app V ≫ P.map η ≫ eM)).app U ≫
        (TX.obj M).map ξ ≫ (bX M K).hom =
      (bX (RP.obj V) U).hom ≫ (TX.map ξ).app (RP.obj V) ≫
        (TX.obj K).map (cmp.inv.app V ≫ P.map η ≫ eM) := by
    rw [← Category.assoc, hbX]
  simp only [Functor.map_comp, Category.assoc]
  rw [hmate]
  rw [reassoc_of% hbraidP, reassoc_of% hcmpnat, reassoc_of% hpfi,
    reassoc_of% ((TX.map (cmp.inv.app N)).naturality ξ),
    reassoc_of% ((TX.map eM).naturality ξ), reassoc_of% hcollapse, hbraidX]
  simp only [Functor.map_comp]
  rw [reassoc_of% ((TX.map ξ).naturality (cmp.inv.app V)).symm, reassoc_of% hbk,
    reassoc_of% ((TX.map ξ).naturality ρV)]

variable (X : RingedSpace.{u, u}) (Z : Set X.carrier) (hZ : IsClosed Z)

variable [PreservesFiniteLimits (modulePushforward (closedSubsetInclusion X Z))]
  [PreservesFiniteColimits (modulePushforward (closedSubsetInclusion X Z))]

/-- **The diagram chase of [Stacks, Tag 0G77] at the derived categories of `X` and `Z`.**
For a map `t : Li^*K ⊗^𝐋 R𝓗_Z(M) ⟶ R𝓗_Z(K ⊗^𝐋 M)` satisfying the adjunction equation `hmate`
of [Stacks, Tag 0G75], invertible projection-formula maps, natural commutativity constraints and
identifications `χ`, `χX` of corepresenting objects compatible with `ρ`, `ρV` as in `hbk`,
forgetting the support of `χ ≫ (Li^*ξ ⊗ η) ≫ t` is `χX ≫ (ξ ⊗ (η with support forgotten))`. -/
theorem forgetSupport_supportedCupProduct
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (hpfNK : IsIso (projectionFormulaMap (closedSubsetInclusion X Z)
      ((derivedSupportedSectionsOnClosed X Z hZ).obj M) K))
    (t : ((derivedTensorProductFunctor (closedSubsetRingedSpace X Z).sheaf).obj
          ((derivedPullback (closedSubsetInclusion X Z)).obj K)).obj
          ((derivedSupportedSectionsOnClosed X Z hZ).obj M) ⟶
        (derivedSupportedSectionsOnClosed X Z hZ).obj
          (((derivedTensorProductFunctor X.sheaf).obj K).obj M))
    (hmate : (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory.map t ≫
          (derivedPushforwardAdjunction X Z hZ).counit.app
            (((derivedTensorProductFunctor X.sheaf).obj K).obj M) =
        (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory.map
            ((canonicalDerivedTensorProduct (closedSubsetRingedSpace X Z).sheaf).braidingIso
              (AlgebraicGeometry.RingedSpace.ringedSite (closedSubsetRingedSpace X Z))
              ((derivedPullback (closedSubsetInclusion X Z)).obj K)
              ((derivedSupportedSectionsOnClosed X Z hZ).obj M)).hom ≫
          (mapDerivedCategoryIsoTotalRightDerived
              (modulePushforward (closedSubsetInclusion X Z))).hom.app
            (((derivedTensorProductFunctor (closedSubsetRingedSpace X Z).sheaf).obj
              ((derivedSupportedSectionsOnClosed X Z hZ).obj M)).obj
                ((derivedPullback (closedSubsetInclusion X Z)).obj K)) ≫
          CategoryTheory.inv (I := hpfNK) (projectionFormulaMap (closedSubsetInclusion X Z)
            ((derivedSupportedSectionsOnClosed X Z hZ).obj M) K) ≫
          ((derivedTensorProductFunctor X.sheaf).map
            ((mapDerivedCategoryIsoTotalRightDerived
                (modulePushforward (closedSubsetInclusion X Z))).inv.app
              ((derivedSupportedSectionsOnClosed X Z hZ).obj M))).app K ≫
          ((derivedTensorProductFunctor X.sheaf).map
            ((derivedPushforwardAdjunction X Z hZ).counit.app M)).app K ≫
          ((canonicalDerivedTensorProduct X.sheaf).braidingIso
            (AlgebraicGeometry.RingedSpace.ringedSite X) M K).hom)
    (hbX : ∀ {A₁ A₁' A₂ A₂' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
        (a : A₁ ⟶ A₁') (b : A₂ ⟶ A₂'),
      (((derivedTensorProductFunctor X.sheaf).map a).app A₂ ≫
            ((derivedTensorProductFunctor X.sheaf).obj A₁').map b) ≫
          ((canonicalDerivedTensorProduct X.sheaf).braidingIso
            (AlgebraicGeometry.RingedSpace.ringedSite X) A₁' A₂').hom =
        ((canonicalDerivedTensorProduct X.sheaf).braidingIso
            (AlgebraicGeometry.RingedSpace.ringedSite X) A₁ A₂).hom ≫
          (((derivedTensorProductFunctor X.sheaf).map b).app A₁ ≫
            ((derivedTensorProductFunctor X.sheaf).obj A₂').map a))
    (hbZ : ∀ {B₁ B₁' B₂ B₂' : DerivedCategory
          (SheafOfModules.{u} (structureSheafRing (closedSubsetRingedSpace X Z)))}
        (a : B₁ ⟶ B₁') (b : B₂ ⟶ B₂'),
      (((derivedTensorProductFunctor (closedSubsetRingedSpace X Z).sheaf).map a).app B₂ ≫
            ((derivedTensorProductFunctor (closedSubsetRingedSpace X Z).sheaf).obj B₁').map b) ≫
          ((canonicalDerivedTensorProduct (closedSubsetRingedSpace X Z).sheaf).braidingIso
            (AlgebraicGeometry.RingedSpace.ringedSite (closedSubsetRingedSpace X Z))
            B₁' B₂').hom =
        ((canonicalDerivedTensorProduct (closedSubsetRingedSpace X Z).sheaf).braidingIso
            (AlgebraicGeometry.RingedSpace.ringedSite (closedSubsetRingedSpace X Z))
            B₁ B₂).hom ≫
          (((derivedTensorProductFunctor (closedSubsetRingedSpace X Z).sheaf).map b).app B₁ ≫
            ((derivedTensorProductFunctor (closedSubsetRingedSpace X Z).sheaf).obj B₂').map a))
    {U VX WX : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    {V W : DerivedCategory (SheafOfModules.{u} (structureSheafRing (closedSubsetRingedSpace X Z)))}
    (hpfVU : IsIso (projectionFormulaMap (closedSubsetInclusion X Z) V U))
    (χ : W ⟶ ((derivedTensorProductFunctor (closedSubsetRingedSpace X Z).sheaf).obj
      ((derivedPullback (closedSubsetInclusion X Z)).obj U)).obj V)
    (χX : WX ⟶ ((derivedTensorProductFunctor X.sheaf).obj U).obj VX)
    (ρ : WX ⟶ (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory.obj W)
    (ρV : VX ⟶ (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory.obj V)
    (hbk : ρ ≫ (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory.map χ ≫
          (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory.map
            ((canonicalDerivedTensorProduct (closedSubsetRingedSpace X Z).sheaf).braidingIso
              (AlgebraicGeometry.RingedSpace.ringedSite (closedSubsetRingedSpace X Z))
              ((derivedPullback (closedSubsetInclusion X Z)).obj U) V).hom ≫
          (mapDerivedCategoryIsoTotalRightDerived
              (modulePushforward (closedSubsetInclusion X Z))).hom.app
            (((derivedTensorProductFunctor (closedSubsetRingedSpace X Z).sheaf).obj V).obj
              ((derivedPullback (closedSubsetInclusion X Z)).obj U)) ≫
          CategoryTheory.inv (I := hpfVU)
            (projectionFormulaMap (closedSubsetInclusion X Z) V U) ≫
          ((canonicalDerivedTensorProduct X.sheaf).braidingIso
            (AlgebraicGeometry.RingedSpace.ringedSite X)
            ((derivedPushforward (closedSubsetInclusion X Z)).obj V) U).hom ≫
          ((derivedTensorProductFunctor X.sheaf).obj U).map
            ((mapDerivedCategoryIsoTotalRightDerived
                (modulePushforward (closedSubsetInclusion X Z))).inv.app V) =
        χX ≫ ((derivedTensorProductFunctor X.sheaf).obj U).map ρV)
    (ξ : U ⟶ K)
    (η : V ⟶ (derivedSupportedSectionsOnClosed X Z hZ).obj M) :
    ρ ≫ (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory.map
          (χ ≫ ((derivedTensorProductFunctor (closedSubsetRingedSpace X Z).sheaf).map
              ((derivedPullback (closedSubsetInclusion X Z)).map ξ)).app V ≫
            ((derivedTensorProductFunctor (closedSubsetRingedSpace X Z).sheaf).obj
              ((derivedPullback (closedSubsetInclusion X Z)).obj K)).map η ≫ t) ≫
        (derivedPushforwardAdjunction X Z hZ).counit.app
          (((derivedTensorProductFunctor X.sheaf).obj K).obj M) =
      χX ≫ ((derivedTensorProductFunctor X.sheaf).map ξ).app VX ≫
        ((derivedTensorProductFunctor X.sheaf).obj K).map
          (ρV ≫ (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory.map η ≫
            (derivedPushforwardAdjunction X Z hZ).counit.app M) :=
  comp_counit_of_tensorMate
    (mapDerivedCategoryIsoTotalRightDerived (modulePushforward (closedSubsetInclusion X Z)))
    (derivedPullback (closedSubsetInclusion X Z))
    (derivedTensorProductFunctor X.sheaf)
    (derivedTensorProductFunctor (closedSubsetRingedSpace X Z).sheaf)
    (projectionFormulaMap (closedSubsetInclusion X Z))
    (projectionFormulaMap_natural_left (closedSubsetInclusion X Z))
    (projectionFormulaMap_natural_right (closedSubsetInclusion X Z))
    ((canonicalDerivedTensorProduct X.sheaf).braidingIso
      (AlgebraicGeometry.RingedSpace.ringedSite X))
    hbX
    ((canonicalDerivedTensorProduct (closedSubsetRingedSpace X Z).sheaf).braidingIso
      (AlgebraicGeometry.RingedSpace.ringedSite (closedSubsetRingedSpace X Z)))
    hbZ
    ((derivedPushforwardAdjunction X Z hZ).counit.app M)
    ((derivedPushforwardAdjunction X Z hZ).counit.app
      (((derivedTensorProductFunctor X.sheaf).obj K).obj M))
    t hpfNK hpfVU hmate χ χX ρ ρV hbk ξ η

/-- **The diagram chase of [Stacks, Tag 0G77] for the cup product of [Stacks, Tag 0G76].**
This is `forgetSupport_supportedCupProduct` with the map of [Stacks, Tag 0G75] and its adjunction
equation (`supportedTensorMap`, `supportedTensorMap_mate`), the invertibility of the
projection-formula map of [Stacks, Tag 0B53]
(`isIso_projectionFormulaMap_closedSubsetInclusion_of_isClosed`, [Stacks, Tag 0B55]) and the
naturality of the commutativity constraint of [Stacks, Tag 0FPT] supplied; the identifications
of the corepresenting objects are arbitrary, subject to `hbk`. -/
theorem forgetSupport_supportedCupProduct_of_corepresentingCompatible
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    {U VX WX : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    {V W : DerivedCategory (SheafOfModules.{u}
      (structureSheafRing (closedSubsetRingedSpace X Z)))}
    (χ : W ⟶ ((derivedTensorProductFunctor (closedSubsetRingedSpace X Z).sheaf).obj
      ((derivedPullback (closedSubsetInclusion X Z)).obj U)).obj V)
    (χX : WX ⟶ ((derivedTensorProductFunctor X.sheaf).obj U).obj VX)
    (ρ : WX ⟶ (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory.obj W)
    (ρV : VX ⟶ (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory.obj V)
    (hbk : ρ ≫ (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory.map χ ≫
          (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory.map
            ((canonicalDerivedTensorProduct (closedSubsetRingedSpace X Z).sheaf).braidingIso
              (AlgebraicGeometry.RingedSpace.ringedSite (closedSubsetRingedSpace X Z))
              ((derivedPullback (closedSubsetInclusion X Z)).obj U) V).hom ≫
          (mapDerivedCategoryIsoTotalRightDerived
              (modulePushforward (closedSubsetInclusion X Z))).hom.app
            (((derivedTensorProductFunctor (closedSubsetRingedSpace X Z).sheaf).obj V).obj
              ((derivedPullback (closedSubsetInclusion X Z)).obj U)) ≫
          CategoryTheory.inv
            (I := isIso_projectionFormulaMap_closedSubsetInclusion_of_isClosed X Z hZ V U)
            (projectionFormulaMap (closedSubsetInclusion X Z) V U) ≫
          ((canonicalDerivedTensorProduct X.sheaf).braidingIso
            (AlgebraicGeometry.RingedSpace.ringedSite X)
            ((derivedPushforward (closedSubsetInclusion X Z)).obj V) U).hom ≫
          ((derivedTensorProductFunctor X.sheaf).obj U).map
            ((mapDerivedCategoryIsoTotalRightDerived
                (modulePushforward (closedSubsetInclusion X Z))).inv.app V) =
        χX ≫ ((derivedTensorProductFunctor X.sheaf).obj U).map ρV)
    (ξ : U ⟶ K)
    (η : V ⟶ (derivedSupportedSectionsOnClosed X Z hZ).obj M) :
    ρ ≫ (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory.map
          (supportedCupProduct X Z hZ K M χ ξ η) ≫
        (derivedPushforwardAdjunction X Z hZ).counit.app
          (((derivedTensorProductFunctor X.sheaf).obj K).obj M) =
      χX ≫ ((derivedTensorProductFunctor X.sheaf).map ξ).app VX ≫
        ((derivedTensorProductFunctor X.sheaf).obj K).map
          (ρV ≫ (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory.map η ≫
            (derivedPushforwardAdjunction X Z hZ).counit.app M) :=
  forgetSupport_supportedCupProduct X Z hZ K M
    (isIso_projectionFormulaMap_closedSubsetInclusion_of_isClosed X Z hZ _ K)
    (supportedTensorMap X Z hZ K M) (supportedTensorMap_mate X Z hZ K M)
    (fun a b ↦ by
      simpa only [Category.assoc] using DerivedTensorProduct.braidingIso_hom_naturality
        (AlgebraicGeometry.RingedSpace.ringedSite X)
        (canonicalDerivedTensorProduct X.sheaf) a b)
    (fun a b ↦ by
      simpa only [Category.assoc] using DerivedTensorProduct.braidingIso_hom_naturality
        (AlgebraicGeometry.RingedSpace.ringedSite (closedSubsetRingedSpace X Z))
        (canonicalDerivedTensorProduct (closedSubsetRingedSpace X Z).sheaf) a b)
    (isIso_projectionFormulaMap_closedSubsetInclusion_of_isClosed X Z hZ V U)
    χ χX ρ ρV hbk ξ η

/-! ### The square at the corepresenting objects of [Stacks, Tag 0G70] -/

section CanonicalComparisons

variable (a b : ℤ)

/-- **The compatibility of the degree identifications of the cup product with the comparisons
`ρ` of [Stacks, Tag 0G70].**  This is the hypothesis `hbk` of
`forgetSupport_supportedCupProduct_of_corepresentingCompatible` at the corepresenting objects
`𝒪_X[-a-b]`, `𝒪_X[-a]`, `𝒪_X[-b]` on `X` and `𝒪_Z[-a-b]`, `𝒪_Z[-b]` on `Z`, with `χ` the
identification `𝒪_Z[-a-b] ≅ (𝒪_X[-a])|_Z ⊗^L 𝒪_Z[-b]` of
`Stacks.RingedSpace.derivedPullbackShiftedUnitTensorIso`, `χX` the identification
`𝒪_X[-a-b] ≅ 𝒪_X[-a] ⊗^L 𝒪_X[-b]` of `Stacks.RingedSpace.shiftedUnitTensorIso`, and `ρ`, `ρV`
the comparisons `shiftedUnitToPushforward` at the degrees `a + b` and `b`. -/
def ShiftedUnitCorepresentingCompatible : Prop :=
  shiftedUnitToPushforward Z (a + b) ≫
        (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory.map
          (derivedPullbackShiftedUnitTensorIso (closedSubsetInclusion X Z) a b).hom ≫
        (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory.map
          ((canonicalDerivedTensorProduct (closedSubsetRingedSpace X Z).sheaf).braidingIso
            (AlgebraicGeometry.RingedSpace.ringedSite (closedSubsetRingedSpace X Z))
            ((derivedPullback (closedSubsetInclusion X Z)).obj (shiftedUnitObject X a))
            (shiftedUnitObject (closedSubsetRingedSpace X Z) b)).hom ≫
        (mapDerivedCategoryIsoTotalRightDerived
            (modulePushforward (closedSubsetInclusion X Z))).hom.app
          (((derivedTensorProductFunctor (closedSubsetRingedSpace X Z).sheaf).obj
            (shiftedUnitObject (closedSubsetRingedSpace X Z) b)).obj
              ((derivedPullback (closedSubsetInclusion X Z)).obj (shiftedUnitObject X a))) ≫
        CategoryTheory.inv
          (I := isIso_projectionFormulaMap_closedSubsetInclusion_of_isClosed X Z hZ
            (shiftedUnitObject (closedSubsetRingedSpace X Z) b) (shiftedUnitObject X a))
          (projectionFormulaMap (closedSubsetInclusion X Z)
            (shiftedUnitObject (closedSubsetRingedSpace X Z) b) (shiftedUnitObject X a)) ≫
        ((canonicalDerivedTensorProduct X.sheaf).braidingIso
          (AlgebraicGeometry.RingedSpace.ringedSite X)
          ((derivedPushforward (closedSubsetInclusion X Z)).obj
            (shiftedUnitObject (closedSubsetRingedSpace X Z) b))
          (shiftedUnitObject X a)).hom ≫
        ((derivedTensorProductFunctor X.sheaf).obj (shiftedUnitObject X a)).map
          ((mapDerivedCategoryIsoTotalRightDerived
              (modulePushforward (closedSubsetInclusion X Z))).inv.app
            (shiftedUnitObject (closedSubsetRingedSpace X Z) b)) =
      (shiftedUnitTensorIso X a b).hom ≫
        ((derivedTensorProductFunctor X.sheaf).obj (shiftedUnitObject X a)).map
          (shiftedUnitToPushforward Z b)

/-- **The square of [Stacks, Tag 0G77] in the source's degrees, from the compatibility of the
identifications of the corepresenting objects.** The three groups are corepresented by the
shifted structure sheaves of [Stacks, Tag 0G70], the degree identifications are those of
`Stacks.RingedSpace.shiftedUnitTensorIso`, and forgetting support is `shiftedUnitToPushforward`.
The square for the cup product of [Stacks, Tag 0G76] with no hypothesis is
`Stacks.Cohomology.SupportedComplexes.forgetSupport_supportedCupProduct_square`. -/
theorem forgetSupport_supportedCupProductOfClasses
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (hbk : ShiftedUnitCorepresentingCompatible X Z hZ a b)
    (ξ : shiftedUnitObject X a ⟶ K)
    (η : shiftedUnitObject (closedSubsetRingedSpace X Z) b ⟶
      (derivedSupportedSectionsOnClosed X Z hZ).obj M) :
    shiftedUnitToPushforward Z (a + b) ≫
          (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory.map
            (supportedCupProductOfClasses X Z hZ K M a b ξ η) ≫
          (derivedPushforwardAdjunction X Z hZ).counit.app
            (((derivedTensorProductFunctor X.sheaf).obj K).obj M) =
        (shiftedUnitTensorIso X a b).hom ≫
          ((derivedTensorProductFunctor X.sheaf).map ξ).app (shiftedUnitObject X b) ≫
          ((derivedTensorProductFunctor X.sheaf).obj K).map
            (shiftedUnitToPushforward Z b ≫
              (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory.map η ≫
              (derivedPushforwardAdjunction X Z hZ).counit.app M) :=
  forgetSupport_supportedCupProduct_of_corepresentingCompatible X Z hZ K M
    (derivedPullbackShiftedUnitTensorIso (closedSubsetInclusion X Z) a b).hom
    (shiftedUnitTensorIso X a b).hom
    (shiftedUnitToPushforward Z (a + b))
    (shiftedUnitToPushforward Z b)
    hbk ξ η

end CanonicalComparisons

end Stacks.Cohomology.SupportedComplexes

end
