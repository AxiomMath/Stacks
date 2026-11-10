module

public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.BraidingIsoSymmetry
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.ShiftedStructureSheafTensorPullback
import StacksCore.Tactic.StacksAttribute

/-!
# Forgetting support commutes with the cup product

Let `Z` be a closed subset of a ringed space `(X, 𝒪_X)` with inclusion `i`, and let `K`, `M` be
objects of `D(𝒪_X)`. The square

```
H^a(X, K) × H^b_Z(X, M) -----> H^{a+b}_Z(X, K ⊗^L M)
    |                                  |
    v                                  v
H^a(X, K) × H^b(X, M) -------> H^{a+b}(X, K ⊗^L M)
```

commutes, where the verticals forget support in the second factor, the top arrow is the cup
product with support of [Stacks, Tag 0G76] and the bottom arrow is the ordinary cup product.
This is [Stacks, Tag 0G77].

## Main results

* `Stacks.Cohomology.SupportedComplexes.transposeClean_of_comparisonCompatible`: the
  cancellation of two commutativity constraints, over arbitrary categories, an arbitrary functor,
  arbitrary bifunctors and an arbitrary constraint which is natural and involutive.
* `Stacks.Cohomology.SupportedComplexes.ShiftedUnitTensorComparisonCompatible`: the comparison
  of [Stacks, Tag 079U] carries the degree identification `𝒪_X[-a-b] ≅ 𝒪_X[-a] ⊗^𝐋 𝒪_X[-b]` on
  `X` to the one on `Z`, under the identifications `Li^*(𝒪_X[-p]) ≅ 𝒪_Z[-p]`, and
  `shiftedUnitTensorComparisonCompatible` proves it.
* `Stacks.Cohomology.SupportedComplexes.forgetSupport_supportedCupProduct_square`:
  [Stacks, Tag 0G77].

## References

* [Stacks Project, Lemma 20.34.11 (Tag 0G77)](https://stacks.math.columbia.edu/tag/0G77)
* [Stacks Project, Remark 20.34.10 (Tag 0G76)](https://stacks.math.columbia.edu/tag/0G76)
* [Stacks Project, Lemma 20.34.4 (Tag 0G70)](https://stacks.math.columbia.edu/tag/0G70)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.DerivedTensor.RingedSite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedProjectionFormula
open Stacks.RingedSpace (shiftedUnitObject shiftedUnitTensorIso
  derivedPullbackShiftedUnitTensorIso derivedPullbackShiftedUnitIso)
open scoped CategoryTheory.Prod

universe v₁ v₂ u₁ u₂ u

namespace Stacks.Cohomology.SupportedComplexes

section Abstract

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- **The two commutativity constraints of the transposed equation of [Stacks, Tag 0G77]
cancel.**

Let `L` be a functor, `TC`, `TD` bifunctors and `bD` a commutativity constraint for `TD`, natural
in both variables by `hbD` and involutive by `hbinv`.  Let `ka`, `kb`, `kw` identify the images
under `L` of three objects of `C` with three objects of `D`, let `χX`, `χZ` be identifications of
`WX`, `WZ` with the two tensor products, let `cmp` compare `L` of a tensor product with the tensor
product of the images, and let `χ` be `χZ` transported into the left factor `L.obj UX` by `ka`.

Then the equation `hcmp` — `cmp` carries `χX` to `χZ` under `ka` and `kb` — gives the equation in
which one constraint stands on each side, which is the shape
`Stacks.Cohomology.SupportedComplexes.ShiftedUnitTransposeClean` has. -/
theorem transposeClean_of_comparisonCompatible (L : C ⥤ D) (TC : C ⥤ C ⥤ C) (TD : D ⥤ D ⥤ D)
    (bD : ∀ B₁ B₂ : D, (TD.obj B₁).obj B₂ ≅ (TD.obj B₂).obj B₁)
    (hbD : ∀ {B₁ B₁' B₂ B₂' : D} (p : B₁ ⟶ B₁') (q : B₂ ⟶ B₂'),
      ((TD.map p).app B₂ ≫ (TD.obj B₁').map q) ≫ (bD B₁' B₂').hom =
        (bD B₁ B₂).hom ≫ ((TD.map q).app B₁ ≫ (TD.obj B₂').map p))
    (hbinv : ∀ B₁ B₂ : D, (bD B₁ B₂).inv = (bD B₂ B₁).hom)
    {UX VX WX : C} {UZ VZ WZ : D}
    (ka : L.obj UX ≅ UZ) (kb : L.obj VX ≅ VZ) (kw : L.obj WX ≅ WZ)
    (χX : WX ⟶ (TC.obj UX).obj VX) (χZ : WZ ⟶ (TD.obj UZ).obj VZ)
    (cmp : L.obj ((TC.obj UX).obj VX) ⟶ (TD.obj (L.obj UX)).obj (L.obj VX))
    (χ : WZ ⟶ (TD.obj (L.obj UX)).obj VZ)
    (hχ : χ = χZ ≫ (TD.map ka.inv).app VZ)
    (hcmp : kw.hom ≫ χZ =
      L.map χX ≫ cmp ≫ (TD.map ka.hom).app (L.obj VX) ≫ (TD.obj UZ).map kb.hom) :
    kw.hom ≫ χ ≫ (bD (L.obj UX) VZ).hom =
      L.map χX ≫ cmp ≫ (bD (L.obj VX) (L.obj UX)).inv ≫
        (TD.map kb.hom).app (L.obj UX) := by
  have hbraid : (bD (L.obj VX) (L.obj UX)).inv ≫ (TD.map kb.hom).app (L.obj UX) =
      (TD.obj (L.obj UX)).map kb.hom ≫ (bD (L.obj UX) VZ).hom := by
    rw [hbinv]
    have h := hbD (CategoryStruct.id (L.obj UX)) kb.hom
    simp only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
      Category.comp_id] at h
    exact h.symm
  have hka : (TD.map ka.hom).app (L.obj VX) ≫ (TD.obj UZ).map kb.hom ≫
      (TD.map ka.inv).app VZ = (TD.obj (L.obj UX)).map kb.hom := by
    have hn := (TD.map ka.hom).naturality kb.hom
    have hcancel : (TD.map ka.hom).app VZ ≫ (TD.map ka.inv).app VZ =
        CategoryStruct.id _ := by
      rw [← NatTrans.comp_app, ← TD.map_comp, ka.hom_inv_id, CategoryTheory.Functor.map_id,
        NatTrans.id_app]
    rw [← Category.assoc, ← hn, Category.assoc, hcancel, Category.comp_id]
  rw [hχ, hbraid]
  simp only [Category.assoc]
  rw [reassoc_of% hcmp, reassoc_of% hka]

end Abstract

section AtTheCanonicalObjects

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.AssociatedSheaf.hasModuleSheafify
  Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective

variable (X : RingedSpace.{u, u}) (Z : Set X.carrier) (hZ : IsClosed Z) (a b : ℤ)

variable [PreservesFiniteLimits (modulePushforward (closedSubsetInclusion X Z))]
  [PreservesFiniteColimits (modulePushforward (closedSubsetInclusion X Z))]

/-- **The comparison of [Stacks, Tag 079U] carries the degree identification of
[Stacks, Tag 0FNH] on `X` to the one on the closed subspace `Z`.**

The three objects are the shifted structure sheaves of [Stacks, Tag 0G70] in the degrees `a + b`,
`a` and `b`; the two horizontal maps are the identification
`𝒪_W[-a-b] ≅ 𝒪_W[-a] ⊗^𝐋_{𝒪_W} 𝒪_W[-b]` of [Stacks, Tag 0FNH] on `W = X` and on `W = Z`, which
is `Stacks.RingedSpace.shiftedUnitTensorIso`; and the three vertical maps are the identifications
`Li^*(𝒪_X[-p]) ≅ 𝒪_Z[-p]` of `Stacks.RingedSpace.derivedPullbackShiftedUnitIso`, which is
[Stacks, Tag 01CD] shifted along [Stacks, Tag 06YJ].

Nothing is quantified over beyond the ringed space, the closed subset and the two degrees, so
this is a single equation that is true or false, and no choice of data can satisfy it trivially.
It mentions no commutativity constraint of [Stacks, Tag 0FPT], no derived sections with support,
no map of [Stacks, Tag 0G75], no projection-formula map of [Stacks, Tag 0B53], no adjunction of
[Stacks, Tag 079W] and neither cohomology class.
-/
def ShiftedUnitTensorComparisonCompatible : Prop :=
  (derivedPullbackShiftedUnitIso (closedSubsetInclusion X Z) (a + b)).hom ≫
      (shiftedUnitTensorIso (closedSubsetRingedSpace X Z) a b).hom =
    (derivedPullback (closedSubsetInclusion X Z)).map (shiftedUnitTensorIso X a b).hom ≫
      (pullbackTensorComparison (closedSubsetInclusion X Z)).app
        (shiftedUnitObject X a, shiftedUnitObject X b) ≫
      ((derivedTensorProductFunctor (closedSubsetRingedSpace X Z).sheaf).map
          (derivedPullbackShiftedUnitIso (closedSubsetInclusion X Z) a).hom).app
        ((derivedPullback (closedSubsetInclusion X Z)).obj (shiftedUnitObject X b)) ≫
      ((derivedTensorProductFunctor (closedSubsetRingedSpace X Z).sheaf).obj
          (shiftedUnitObject (closedSubsetRingedSpace X Z) a)).map
        (derivedPullbackShiftedUnitIso (closedSubsetInclusion X Z) b).hom

omit [PreservesFiniteLimits (modulePushforward (closedSubsetInclusion X Z))]
  [PreservesFiniteColimits (modulePushforward (closedSubsetInclusion X Z))] in
/-- **The residual equation of [Stacks, Tag 0G77] follows from the compatibility of the comparison
of [Stacks, Tag 079U] with the degree identification of [Stacks, Tag 0FNH].**

`Stacks.Cohomology.SupportedComplexes.ShiftedUnitTransposeClean` carries a commutativity
constraint of [Stacks, Tag 0FPT] on each side.  They cancel, by the naturality of the constraint
(`Stacks.Cohomology.SupportedComplexes.braidingIso_hom_naturality_closedSubset`) and its
involutivity (`Stacks.Cohomology.SupportedComplexes.braidingIso_inv_eq_braidingIso_hom`), leaving
`ShiftedUnitTensorComparisonCompatible`. -/
theorem shiftedUnitTransposeClean_of_comparisonCompatible
    (hcmp : ShiftedUnitTensorComparisonCompatible X Z a b) :
    ShiftedUnitTransposeClean X Z a b :=
  transposeClean_of_comparisonCompatible
    (derivedPullback (closedSubsetInclusion X Z))
    (derivedTensorProductFunctor X.sheaf)
    (derivedTensorProductFunctor (closedSubsetRingedSpace X Z).sheaf)
    ((canonicalDerivedTensorProduct (closedSubsetRingedSpace X Z).sheaf).braidingIso
      (AlgebraicGeometry.RingedSpace.ringedSite (closedSubsetRingedSpace X Z)))
    (braidingIso_hom_naturality_closedSubset X Z)
    (braidingIso_inv_eq_braidingIso_hom (closedSubsetRingedSpace X Z))
    (derivedPullbackShiftedUnitIso (closedSubsetInclusion X Z) a)
    (derivedPullbackShiftedUnitIso (closedSubsetInclusion X Z) b)
    (derivedPullbackShiftedUnitIso (closedSubsetInclusion X Z) (a + b))
    (shiftedUnitTensorIso X a b).hom
    (shiftedUnitTensorIso (closedSubsetRingedSpace X Z) a b).hom
    ((pullbackTensorComparison (closedSubsetInclusion X Z)).app
      (shiftedUnitObject X a, shiftedUnitObject X b))
    (derivedPullbackShiftedUnitTensorIso (closedSubsetInclusion X Z) a b).hom
    rfl hcmp

/-- **The one hypothesis of [Stacks, Tag 0G77] left at the canonical corepresenting objects
follows from the compatibility of the comparison of [Stacks, Tag 079U] with [Stacks, Tag 0FNH].**
It is `Stacks.Cohomology.SupportedComplexes.shiftedUnitCorepresentingCompatible_of_transposeClean`
fed `shiftedUnitTransposeClean_of_comparisonCompatible`. -/
theorem shiftedUnitCorepresentingCompatible_of_comparisonCompatible
    (hcmp : ShiftedUnitTensorComparisonCompatible X Z a b) :
    ShiftedUnitCorepresentingCompatible X Z hZ a b :=
  shiftedUnitCorepresentingCompatible_of_transposeClean X Z hZ a b
    (shiftedUnitTransposeClean_of_comparisonCompatible X Z a b hcmp)

/-- **The square of [Stacks, Tag 0G77] follows from the compatibility of the comparison of
[Stacks, Tag 079U] with the degree identification of the cup product.** -/
theorem forgetSupportSquare_of_comparisonCompatible
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (hcmp : ShiftedUnitTensorComparisonCompatible X Z a b)
    (ξ : shiftedUnitObject X a ⟶ K)
    (η : shiftedUnitObject (closedSubsetRingedSpace X Z) b ⟶
      (derivedSupportedSectionsOnClosed X Z hZ).obj M) :
    ForgetSupportSquare X Z hZ a b K M ξ η :=
  forgetSupportSquare_of_transposeClean X Z hZ a b K M
    (shiftedUnitTransposeClean_of_comparisonCompatible X Z a b hcmp) ξ η

omit [PreservesFiniteLimits (modulePushforward (closedSubsetInclusion X Z))]
  [PreservesFiniteColimits (modulePushforward (closedSubsetInclusion X Z))] in
/-- **The comparison of [Stacks, Tag 079U] carries the degree identification of the cup product
on `X` to the one on the closed subspace `Z`.** This is
`Stacks.RingedSpace.derivedPullbackShiftedUnitIso_comp_shiftedUnitTensorIso` at the inclusion of
`Z`. -/
theorem shiftedUnitTensorComparisonCompatible : ShiftedUnitTensorComparisonCompatible X Z a b :=
  Stacks.RingedSpace.derivedPullbackShiftedUnitIso_comp_shiftedUnitTensorIso
    (closedSubsetInclusion X Z) a b

end AtTheCanonicalObjects

section Square

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.AssociatedSheaf.hasModuleSheafify
  Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective

/-- **Stacks Project, Tag 0G77.** Let `Z` be a closed subset of a ringed space `(X, 𝒪_X)` and let
`K`, `M` be objects of `D(𝒪_X)`. The square

```
H^a(X, K) × H^b_Z(X, M) -----> H^{a+b}_Z(X, K ⊗^L M)
    |                                  |
    v                                  v
H^a(X, K) × H^b(X, M) -------> H^{a+b}(X, K ⊗^L M)
```

commutes, where the top arrow is the cup product of [Stacks, Tag 0G76], the bottom arrow is the
cup product of [Stacks, Tag 0FP2] and the verticals forget support. A class of `H^a(X, K)` is a
morphism `ξ : 𝒪_X[-a] ⟶ K` and a class of `H^b_Z(X, M) = H^b(Z, R𝓗_Z(M))` is a morphism
`η : 𝒪_Z[-b] ⟶ R𝓗_Z(M)` ([Stacks, Tag 0G70]); forgetting support is precomposition with the
comparison `𝒪_X[-p] ⟶ i_*𝒪_Z[-p]` followed by the counit `i_*R𝓗_Z(-) ⟶ -` of
[Stacks, Tag 0A3B]. -/
@[stacks 0G77]
theorem forgetSupport_supportedCupProduct_square (X : RingedSpace.{u, u}) (Z : Set X.carrier)
    (hZ : IsClosed Z) (a b : ℤ) (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (ξ : shiftedUnitObject X a ⟶ K)
    (η : shiftedUnitObject (closedSubsetRingedSpace X Z) b ⟶
      (derivedSupportedSectionsOnClosed X Z hZ).obj M) :
    letI := pushforward_preservesFiniteLimits X Z
    letI := pushforward_preservesFiniteColimits X Z hZ
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
  let := pushforward_preservesFiniteLimits X Z
  let := pushforward_preservesFiniteColimits X Z hZ
  forgetSupportSquare_of_comparisonCompatible X Z hZ a b K M
    (shiftedUnitTensorComparisonCompatible X Z a b) ξ η

/-- The square at nonzero degrees, with the identity class on `X` and the unit of
`i_* ⊣ R𝓗_Z` at `𝒪_Z[-2]` as the class supported on `Z`. -/
example (X : RingedSpace.{u, u}) (Z : Set X.carrier) (hZ : IsClosed Z) :
    letI := pushforward_preservesFiniteLimits X Z
    letI := pushforward_preservesFiniteColimits X Z hZ
    ForgetSupportSquare X Z hZ 1 2 (shiftedUnitObject X 1)
      ((modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory.obj
        (shiftedUnitObject (closedSubsetRingedSpace X Z) 2))
      (𝟙 (shiftedUnitObject X 1))
      ((derivedPushforwardAdjunction X Z hZ).unit.app
        (shiftedUnitObject (closedSubsetRingedSpace X Z) 2)) :=
  forgetSupport_supportedCupProduct_square X Z hZ 1 2 _ _ _ _

end Square

end Stacks.Cohomology.SupportedComplexes

end
