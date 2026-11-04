module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormula
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaClosedEmbeddingUnconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportedSectionsDerivedAdjunction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.DerivedSymmetryAndUnit
import StacksFrontier.AlgebraicGeometry.ClosedImmersion.DerivedPushforwardComparison
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.ShiftedStructureSheafTensor
public import StacksFrontier.AlgebraicGeometry.RingedSpace.KFlatResolution
import StacksCore.Tactic.StacksAttribute

/-!
# The map `K|_Z ⊗^L R𝓗_Z(M) ⟶ R𝓗_Z(K ⊗^L M)` and the cup product with support

Let `(X, 𝒪_X)` be a ringed space and let `i : Z ⟶ X` be the inclusion of a closed subset. For
`K` and `M` in `D(𝒪_X)` there is a canonical map

`K|_Z ⊗^L_{𝒪_X|_Z} R𝓗_Z(M) ⟶ R𝓗_Z(K ⊗^L_{𝒪_X} M)`

in `D(𝒪_X|_Z)`, where `K|_Z = i^{-1}K` is the restriction of `K` to `Z`. This is
[Stacks, Tag 0G75]. The structure sheaf of `Z` is literally `i^{-1}𝒪_X`, so the stalk maps of
`i` are isomorphisms and `i` is flat — `isFlat_closedSubsetInclusion` — whence module pullback
along `i` is exact — `pullbackExact` — and the derived pullback `Li^*` computes `i^{-1}`.
Accordingly `K|_Z` below is `(derivedPullback i).obj K`.

The source constructs the map by adjointness of `i_*` and `R𝓗_Z` ([Stacks, Tag 0A3B] part (1)):
it suffices to produce a map

`i_*(K|_Z ⊗^L_{𝒪_X|_Z} R𝓗_Z(M)) ⟶ K ⊗^L_{𝒪_X} M`,

and that map is the projection formula for `i` followed by the adjunction counit
`i_*R𝓗_Z(M) ⟶ M`. The projection formula is the map of [Stacks, Tag 0B53], which is invertible
for a homeomorphism onto a closed subset by [Stacks, Tag 0B55].

Remark [Stacks, Tag 0G76] reads that map as a cup product. A class in `H^a(X, K)` is a morphism
`𝒪_X[-a] ⟶ K` and, by [Stacks, Tag 0G70], a class in `H^b_Z(X, M)` is a morphism
`𝒪_Z[-b] ⟶ R𝓗_Z(M)` on `Z`. Restricting the first to `Z`, tensoring the two on `Z` and
following with the map above gives `𝒪_Z[-a-b] ⟶ R𝓗_Z(K ⊗^L M)`, a class in
`H^{a+b}_Z(X, K ⊗^L M)`. That composite is `supportedCupProduct`.

## Main definitions

* `supportedTensorMateMap` is the displayed composite `i_*(K|_Z ⊗^L R𝓗_Z(M)) ⟶ K ⊗^L M` that
  the canonical map is adjoint to.
* `supportedTensorMap` is the canonical map of [Stacks, Tag 0G75] itself.
* `shiftedStructureSheaf` is the structure sheaf in cohomological degree `i`, the object
  corepresenting `H^i`.
* `supportedCupProduct` is the cup product of [Stacks, Tag 0G76].
* `supportedCupProductOfClasses` is the same product in the source's degree-indexed shape, on
  classes out of shifted structure sheaves.

## Main results

* `supportedTensorMap_mate` is the adjunction equation that characterizes the canonical map, and
  `supportedTensorMap_unique` says the equation determines it, so that nothing else — in
  particular neither the zero map nor the negative of the canonical map — inhabits the type and
  satisfies the characterization.
* `nonempty_closedPushforward_adjunction` is the existence of the adjunction of Tag 0A3B part (1)
  for every ringed space and every closed subset.
* `additive_derivedPushforward_closedSubsetInclusion` records that `Ri_*` is additive here.
* `supportedCupProduct_mate` characterizes the cup product by the adjunction of Tag 0A3B, in
  the same way `supportedTensorMap_mate` characterizes the map it is built from.
* `supportedCupProduct_unit` is the degree-zero normalization `1 ∪ η = η`.

## Implementation notes

**The three inputs of the construction.** Exactness of `i_*`, [Stacks, Tag 08KS], is
`pushforward_preservesFiniteLimits X Z` and `pushforward_preservesFiniteColimits X Z hZ`; the
adjunction `i_* ⊣ R𝓗_Z` of [Stacks, Tag 0A3B] part (1) is the term
`derivedPushforwardAdjunction X Z hZ`; and invertibility of the projection-formula map of
[Stacks, Tag 0B53] is
`isIso_projectionFormulaMap_closedSubsetInclusion_of_isClosed X Z hZ`, which is
[Stacks, Tag 0B55] for the inclusion of a closed subset.

**Functoriality.** Tag 0G75 asserts that the displayed map exists and is canonical; the
declarations below supply the map, the adjunction equation that pins it down and its uniqueness
subject to that equation. Functoriality in `K` and in `M` is not recorded, because the
commutativity constraint of [Stacks, Tag 0FPT] used below is supplied one pair of objects at a
time rather than as a natural isomorphism: the chosen K-flat model it is built from,
`AlgebraicGeometry.RingedSite.kFlatModel`, is a function on objects and not a functor. Every
other step of the composite is already natural.

**The corepresenting objects of the cup product.** `supportedCupProduct` is the source's
four-step composite for an arbitrary morphism `χ` out of an arbitrary object `W`, so that it
applies to any presentation of the groups; `supportedCupProductOfClasses` instantiates it at the
shifted structure sheaves, with `χ` the source's own identification
`𝒪_Z[-a-b] = (𝒪_X[-a])|_Z ⊗^L 𝒪_Z[-b]`, which is
`Stacks.RingedSpace.derivedPullbackShiftedUnitTensorIso`.

**The degree-zero normalization.** `supportedCupProduct_unit` is stated for a pair of left
unitors given as data, since the unitors for the derived tensor product of sheaves of modules
are not recorded in the spelling used here. What it proves is that the cup product's own
bookkeeping — restriction of the first class, tensoring with the second, then the map of
Tag 0G75 — collapses to the identity on the second class, which is what fixes the construction
rather than its negative or the zero map.

**The order of the tensor factors.** The source writes `K|_Z ⊗^L R𝓗_Z(M)` and
`R𝓗_Z(K ⊗^L M)`, with the restriction and `K` in the first slot. The projection formula puts
the pulled-back factor second, so the commutativity constraint of [Stacks, Tag 0FPT] is applied
once on `D(𝒪_X|_Z)` and once on `D(𝒪_X)`.

**The two models of pushforward.** [Stacks, Tag 0A3B] uses the functor induced on derived
categories by the exact functor `i_*`, while the projection formula of [Stacks, Tag 0B53] is
stated for the total right derived functor `Ri_*`. The two are identified by
`Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived`, which is [Stacks, Tag 0E2K];
the composite passes through it in both directions.

## References

* [Stacks Project, Tag 0G75](https://stacks.math.columbia.edu/tag/0G75)
* [Stacks Project, Tag 0G76](https://stacks.math.columbia.edu/tag/0G76)
* [Stacks Project, Tag 0G70](https://stacks.math.columbia.edu/tag/0G70)
* [Stacks Project, Tag 0A3B](https://stacks.math.columbia.edu/tag/0A3B)
* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 0B55](https://stacks.math.columbia.edu/tag/0B55)
* [Stacks Project, Tag 0E2K](https://stacks.math.columbia.edu/tag/0E2K)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 0FNH](https://stacks.math.columbia.edu/tag/0FNH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction Stacks.SheafOfModules.SupportedSections
open Stacks.DerivedTensor.RingedSite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedProjectionFormula

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.AssociatedSheaf.hasModuleSheafify
  Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective

namespace Stacks.Cohomology.SupportedComplexes

variable (X : RingedSpace.{u, u}) (Z : Set X.carrier) (hZ : IsClosed Z)

/-- Pushforward along the inclusion of a closed subset is exact, and the derived adjunction
`i_* ⊣ R𝓗_Z` of Tag 0A3B part (1) exists. So the two exactness binders and the adjunction
parameter of `supportedTensorMap` below are inhabited for every ringed space and every closed
subset. -/
theorem nonempty_closedPushforward_adjunction :
    letI := pushforward_preservesFiniteLimits X Z
    letI := pushforward_preservesFiniteColimits X Z hZ
    Nonempty ((modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory ⊣
      derivedSupportedSectionsOnClosed X Z hZ) :=
  derivedPushforward_adj_derivedSupportedSectionsOnClosed X Z hZ

/-! ### The two models of derived pushforward along the inclusion of a closed subset -/

section Comparison

variable [PreservesFiniteLimits (modulePushforward (closedSubsetInclusion X Z))]
  [PreservesFiniteColimits (modulePushforward (closedSubsetInclusion X Z))]

/-- **[Stacks, Tag 0E2K] for the inclusion of a closed subset.** Pushforward along `i` is exact,
so the functor it induces on derived categories is already its own total right derived functor;
this is the comparison with the `Ri_*` that the projection formula of Tag 0B53 is stated for. -/
abbrev closedPushforwardComparison :
    (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory ≅
      derivedPushforward (closedSubsetInclusion X Z) :=
  Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived
    (modulePushforward (closedSubsetInclusion X Z))

end Comparison

/-! ### The displayed composite and the canonical map of Tag 0G75 -/

/-- The composite `i_*(K|_Z ⊗^L R𝓗_Z(M)) ⟶ K ⊗^L M` that the canonical map of Tag 0G75 is
adjoint to.

Reading the factors in order: the commutativity constraint of Tag 0FPT moves the restriction
into the second tensor slot; `closedPushforwardComparison` passes to the total right derived
pushforward; the inverse of the projection-formula map of Tag 0B53, invertible by Tag 0B55, is
the identification `i_*(R𝓗_Z(M) ⊗^L K|_Z) = i_*R𝓗_Z(M) ⊗^L K`; the comparison comes back; the
counit of Tag 0A3B is the arrow `i_*R𝓗_Z(M) ⟶ M`; and the commutativity constraint restores the
order `K ⊗^L M`. -/
def supportedTensorMateMap
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    letI := pushforward_preservesFiniteLimits X Z
    letI := pushforward_preservesFiniteColimits X Z hZ
    (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory.obj
        (((derivedTensorProductFunctor (closedSubsetRingedSpace X Z).sheaf).obj
            ((derivedPullback (closedSubsetInclusion X Z)).obj K)).obj
          ((derivedSupportedSectionsOnClosed X Z hZ).obj M)) ⟶
      ((derivedTensorProductFunctor X.sheaf).obj K).obj M :=
  letI := pushforward_preservesFiniteLimits X Z
  letI := pushforward_preservesFiniteColimits X Z hZ
  (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory.map
      ((canonicalDerivedTensorProduct (closedSubsetRingedSpace X Z).sheaf).braidingIso
        (AlgebraicGeometry.RingedSpace.ringedSite (closedSubsetRingedSpace X Z))
        ((derivedPullback (closedSubsetInclusion X Z)).obj K)
        ((derivedSupportedSectionsOnClosed X Z hZ).obj M)).hom ≫
    (closedPushforwardComparison X Z).hom.app _ ≫
    CategoryTheory.inv
      (I := isIso_projectionFormulaMap_closedSubsetInclusion_of_isClosed X Z hZ _ K)
      (projectionFormulaMap (closedSubsetInclusion X Z)
        ((derivedSupportedSectionsOnClosed X Z hZ).obj M) K) ≫
    ((derivedTensorProductFunctor X.sheaf).map
      ((closedPushforwardComparison X Z).inv.app
        ((derivedSupportedSectionsOnClosed X Z hZ).obj M))).app K ≫
    ((derivedTensorProductFunctor X.sheaf).map
      ((derivedPushforwardAdjunction X Z hZ).counit.app M)).app K ≫
    ((canonicalDerivedTensorProduct X.sheaf).braidingIso
      (AlgebraicGeometry.RingedSpace.ringedSite X) M K).hom

/-- **Stacks Project, Tag 0G75.** For `K` and `M` in `D(𝒪_X)` and `i : Z ⟶ X` the inclusion of
a closed subset, the canonical map `K|_Z ⊗^L_{𝒪_X|_Z} R𝓗_Z(M) ⟶ R𝓗_Z(K ⊗^L_{𝒪_X} M)` in
`D(𝒪_X|_Z)`: the map corresponding to `supportedTensorMateMap` under the adjunction
`i_* ⊣ R𝓗_Z` of Tag 0A3B. -/
@[stacks 0G75 "the canonical map `K|_Z ⊗^L R𝓗_Z(M) ⟶ R𝓗_Z(K ⊗^L M)`; not functoriality in \
  either complex"]
def supportedTensorMap
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    ((derivedTensorProductFunctor (closedSubsetRingedSpace X Z).sheaf).obj
        ((derivedPullback (closedSubsetInclusion X Z)).obj K)).obj
        ((derivedSupportedSectionsOnClosed X Z hZ).obj M) ⟶
      (derivedSupportedSectionsOnClosed X Z hZ).obj
        (((derivedTensorProductFunctor X.sheaf).obj K).obj M) :=
  derivedSupportedSectionsLift X Z hZ (supportedTensorMateMap X Z hZ K M)

/-- **Stacks Project, Tag 0G75.** The adjunction equation characterizing the canonical map:
pushing it forward and composing with the counit of Tag 0A3B gives the displayed composite.
This is what "by adjointness of `i_*` and `R𝓗_Z`" means in the source. -/
@[stacks 0G75 "the adjunction equation characterizing the canonical map"]
theorem supportedTensorMap_mate
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    letI := pushforward_preservesFiniteLimits X Z
    letI := pushforward_preservesFiniteColimits X Z hZ
    (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory.map
          (supportedTensorMap X Z hZ K M) ≫
        (derivedPushforwardAdjunction X Z hZ).counit.app
          (((derivedTensorProductFunctor X.sheaf).obj K).obj M) =
      supportedTensorMateMap X Z hZ K M :=
  modulePushforward_map_derivedSupportedSectionsLift_comp_counit X Z hZ
    (supportedTensorMateMap X Z hZ K M)

/-- The adjunction equation determines the canonical map of Tag 0G75: no other morphism of that
type satisfies it. Together with `supportedTensorMap_mate` this says the map is the unique
solution of the characterization, so the construction is not under-determined. -/
theorem supportedTensorMap_unique
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (g : ((derivedTensorProductFunctor (closedSubsetRingedSpace X Z).sheaf).obj
        ((derivedPullback (closedSubsetInclusion X Z)).obj K)).obj
        ((derivedSupportedSectionsOnClosed X Z hZ).obj M) ⟶
      (derivedSupportedSectionsOnClosed X Z hZ).obj
        (((derivedTensorProductFunctor X.sheaf).obj K).obj M))
    (hg : letI := pushforward_preservesFiniteLimits X Z
      letI := pushforward_preservesFiniteColimits X Z hZ
      (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory.map g ≫
        (derivedPushforwardAdjunction X Z hZ).counit.app
          (((derivedTensorProductFunctor X.sheaf).obj K).obj M) =
      supportedTensorMateMap X Z hZ K M) :
    g = supportedTensorMap X Z hZ K M := by
  let _ := pushforward_preservesFiniteLimits X Z
  let _ := pushforward_preservesFiniteColimits X Z hZ
  exact ((derivedPushforwardAdjunction X Z hZ).homEquiv _ _).symm_apply_eq.mp
    ((Adjunction.homEquiv_symm_apply _ _ _ g).trans hg)

/-! ### Derived pushforward along the inclusion of a closed subset is additive -/

section Additive

variable [PreservesFiniteLimits (modulePushforward (closedSubsetInclusion X Z))]
  [PreservesFiniteColimits (modulePushforward (closedSubsetInclusion X Z))]

/-- Derived pushforward along the inclusion of a closed subset is an additive functor: it is
isomorphic, by the comparison of Tag 0E2K, to the functor induced on derived categories by the
exact functor `i_*`. -/
theorem additive_derivedPushforward_closedSubsetInclusion :
    (derivedPushforward (closedSubsetInclusion X Z)).Additive :=
  Functor.additive_of_iso (closedPushforwardComparison X Z)

end Additive

/-! ### The cup product with support in a closed subset -/

/-- The structure sheaf of `W` placed in cohomological degree `i`, that is `𝒪_W[-i]`. A
morphism out of it into `K` is a cohomology class in `H^i(W, K)`. -/
abbrev shiftedStructureSheaf (W : RingedSpace.{u, u}) (i : ℤ) :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing W)) :=
  (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (structureSheafRing W)) i).obj
    (SheafOfModules.unit (structureSheafRing W))

/-- **Stacks Project, Tag 0G76.** The cup product of a class `ξ` on `X` with a class `η`
supported on `Z`: restrict `ξ` to `Z`, tensor the two on `Z`, and follow with the map of
Tag 0G75. Reading `W = 𝒪_Z[-a-b]`, `U = 𝒪_X[-a]` and `V = 𝒪_Z[-b]`, and reading morphisms
out of `𝒪_Z[-n]` into `R𝓗_Z(-)` as classes in `H^n_Z(X, -)` by Tag 0G70, this is the source's
`H^a(X, K) × H^b_Z(X, M) ⟶ H^{a+b}_Z(X, K ⊗^L M)`. The source's identification
`𝒪_Z[-a-b] = (𝒪_X[-a])|_Z ⊗^L 𝒪_Z[-b]` is the morphism `χ`. -/
@[stacks 0G76 "the cup product `H^a(X, K) × H^b_Z(X, M) ⟶ H^(a+b)_Z(X, K ⊗^L M)`, as the \
  source's four-step composite over an arbitrary presentation of the three groups by \
  corepresenting objects; the source's own presentation by shifted structure sheaves is \
  `supportedCupProductOfClasses`", sga "4½ Cycle 1.2.2" "(1.2.2.3), special case"]
def supportedCupProduct
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    {U : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    {V W : DerivedCategory (SheafOfModules.{u}
      (structureSheafRing (closedSubsetRingedSpace X Z)))}
    (χ : W ⟶ ((derivedTensorProductFunctor (closedSubsetRingedSpace X Z).sheaf).obj
      ((derivedPullback (closedSubsetInclusion X Z)).obj U)).obj V)
    (ξ : U ⟶ K) (η : V ⟶ (derivedSupportedSectionsOnClosed X Z hZ).obj M) :
    W ⟶ (derivedSupportedSectionsOnClosed X Z hZ).obj
      (((derivedTensorProductFunctor X.sheaf).obj K).obj M) :=
  χ ≫ ((derivedTensorProductFunctor (closedSubsetRingedSpace X Z).sheaf).map
      ((derivedPullback (closedSubsetInclusion X Z)).map ξ)).app V ≫
    ((derivedTensorProductFunctor (closedSubsetRingedSpace X Z).sheaf).obj
      ((derivedPullback (closedSubsetInclusion X Z)).obj K)).map η ≫
    supportedTensorMap X Z hZ K M

/-- The cup product is the four-step composite of the source: the identification `χ`, the
restriction of `ξ` to `Z`, the tensoring with `η`, and the map of Tag 0G75. Stated so that a
consumer can see the construction. -/
theorem supportedCupProduct_eq
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    {U : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    {V W : DerivedCategory (SheafOfModules.{u}
      (structureSheafRing (closedSubsetRingedSpace X Z)))}
    (χ : W ⟶ ((derivedTensorProductFunctor (closedSubsetRingedSpace X Z).sheaf).obj
      ((derivedPullback (closedSubsetInclusion X Z)).obj U)).obj V)
    (ξ : U ⟶ K) (η : V ⟶ (derivedSupportedSectionsOnClosed X Z hZ).obj M) :
    supportedCupProduct X Z hZ K M χ ξ η =
      χ ≫ ((derivedTensorProductFunctor (closedSubsetRingedSpace X Z).sheaf).map
          ((derivedPullback (closedSubsetInclusion X Z)).map ξ)).app V ≫
        ((derivedTensorProductFunctor (closedSubsetRingedSpace X Z).sheaf).obj
          ((derivedPullback (closedSubsetInclusion X Z)).obj K)).map η ≫
        supportedTensorMap X Z hZ K M :=
  rfl

/-- Precomposing the cup product with a morphism is the cup product taken with the composed
identification. -/
theorem comp_supportedCupProduct
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    {U : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    {V W W' : DerivedCategory (SheafOfModules.{u}
      (structureSheafRing (closedSubsetRingedSpace X Z)))}
    (χ' : W' ⟶ W)
    (χ : W ⟶ ((derivedTensorProductFunctor (closedSubsetRingedSpace X Z).sheaf).obj
      ((derivedPullback (closedSubsetInclusion X Z)).obj U)).obj V)
    (ξ : U ⟶ K) (η : V ⟶ (derivedSupportedSectionsOnClosed X Z hZ).obj M) :
    χ' ≫ supportedCupProduct X Z hZ K M χ ξ η =
      supportedCupProduct X Z hZ K M (χ' ≫ χ) ξ η :=
  (Category.assoc _ _ _).symm

/-- **Stacks Project, Tag 0G76.** The cup product of a class `ξ ∈ H^a(X, K)` and a class
`η ∈ H^b_Z(X, M) = H^b(Z, R𝓗_Z(M))`, landing in
`H^{a+b}_Z(X, K ⊗^L M) = H^{a+b}(Z, R𝓗_Z(K ⊗^L M))`: restrict `ξ` to `Z`, tensor the two classes
on `Z` and follow with the map of Tag 0G75, after the identification
`𝒪_Z[-a-b] = (𝒪_X[-a])|_Z ⊗^L 𝒪_Z[-b]` of the corepresenting objects. -/
@[stacks 0G76 "the cup product `H^a(X, K) × H^b_Z(X, M) ⟶ H^(a+b)_Z(X, K ⊗^L M)` on classes \
  represented by morphisms out of shifted structure sheaves, in the source's degrees",
  sga "4½ Cycle 1.2.2" "(1.2.2.2)"]
def supportedCupProductOfClasses
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (a b : ℤ)
    (ξ : shiftedStructureSheaf X a ⟶ K)
    (η : shiftedStructureSheaf (closedSubsetRingedSpace X Z) b ⟶
      (derivedSupportedSectionsOnClosed X Z hZ).obj M) :
    shiftedStructureSheaf (closedSubsetRingedSpace X Z) (a + b) ⟶
      (derivedSupportedSectionsOnClosed X Z hZ).obj
        (((derivedTensorProductFunctor X.sheaf).obj K).obj M) :=
  supportedCupProduct X Z hZ K M
    (Stacks.RingedSpace.derivedPullbackShiftedUnitTensorIso
      (closedSubsetInclusion X Z) a b).hom ξ η

/-- The cup product in the source's degrees is `supportedCupProduct` taken with the canonical
identification `𝒪_Z[-a-b] = (𝒪_X[-a])|_Z ⊗^L 𝒪_Z[-b]` of Tag 0FNH. -/
theorem supportedCupProductOfClasses_eq
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (a b : ℤ) (ξ : shiftedStructureSheaf X a ⟶ K)
    (η : shiftedStructureSheaf (closedSubsetRingedSpace X Z) b ⟶
      (derivedSupportedSectionsOnClosed X Z hZ).obj M) :
    supportedCupProductOfClasses X Z hZ K M a b ξ η =
      supportedCupProduct X Z hZ K M
        (Stacks.RingedSpace.derivedPullbackShiftedUnitTensorIso
          (closedSubsetInclusion X Z) a b).hom ξ η :=
  rfl

/-- The adjunction equation characterizing the cup product: pushing it forward and composing
with the counit of Tag 0A3B gives the composite on `X` of the identification, the restricted
class and the displayed map `supportedTensorMateMap` of Tag 0G75. -/
theorem supportedCupProduct_mate
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    {U : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    {V W : DerivedCategory (SheafOfModules.{u}
      (structureSheafRing (closedSubsetRingedSpace X Z)))}
    (χ : W ⟶ ((derivedTensorProductFunctor (closedSubsetRingedSpace X Z).sheaf).obj
      ((derivedPullback (closedSubsetInclusion X Z)).obj U)).obj V)
    (ξ : U ⟶ K) (η : V ⟶ (derivedSupportedSectionsOnClosed X Z hZ).obj M) :
    letI := pushforward_preservesFiniteLimits X Z
    letI := pushforward_preservesFiniteColimits X Z hZ
    (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory.map
          (supportedCupProduct X Z hZ K M χ ξ η) ≫
        (derivedPushforwardAdjunction X Z hZ).counit.app
          (((derivedTensorProductFunctor X.sheaf).obj K).obj M) =
      (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory.map
          (χ ≫ ((derivedTensorProductFunctor (closedSubsetRingedSpace X Z).sheaf).map
              ((derivedPullback (closedSubsetInclusion X Z)).map ξ)).app V ≫
            ((derivedTensorProductFunctor (closedSubsetRingedSpace X Z).sheaf).obj
              ((derivedPullback (closedSubsetInclusion X Z)).obj K)).map η) ≫
        supportedTensorMateMap X Z hZ K M := by
  let _ := pushforward_preservesFiniteLimits X Z
  let _ := pushforward_preservesFiniteColimits X Z hZ
  have hassoc : χ ≫ ((derivedTensorProductFunctor (closedSubsetRingedSpace X Z).sheaf).map
          ((derivedPullback (closedSubsetInclusion X Z)).map ξ)).app V ≫
        ((derivedTensorProductFunctor (closedSubsetRingedSpace X Z).sheaf).obj
          ((derivedPullback (closedSubsetInclusion X Z)).obj K)).map η ≫
          supportedTensorMap X Z hZ K M =
      (χ ≫ ((derivedTensorProductFunctor (closedSubsetRingedSpace X Z).sheaf).map
          ((derivedPullback (closedSubsetInclusion X Z)).map ξ)).app V ≫
        ((derivedTensorProductFunctor (closedSubsetRingedSpace X Z).sheaf).obj
          ((derivedPullback (closedSubsetInclusion X Z)).obj K)).map η) ≫
        supportedTensorMap X Z hZ K M :=
    ((Category.assoc _ _ _).trans
      (congrArg (fun k => χ ≫ k) (Category.assoc _ _ _))).symm
  have hmc := (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory.map_comp
    (χ ≫ ((derivedTensorProductFunctor (closedSubsetRingedSpace X Z).sheaf).map
        ((derivedPullback (closedSubsetInclusion X Z)).map ξ)).app V ≫
      ((derivedTensorProductFunctor (closedSubsetRingedSpace X Z).sheaf).obj
        ((derivedPullback (closedSubsetInclusion X Z)).obj K)).map η)
    (supportedTensorMap X Z hZ K M)
  rw [supportedCupProduct_eq, hassoc, hmc, Category.assoc, supportedTensorMap_mate]

/-- **The degree-zero normalization `1 ∪ η = η`.** Cupping the unit class of `𝒪_X` in degree
zero with a class `η` supported on `Z`, and reading the result through the left unitor
`𝒪_X[0] ⊗^L M ≅ M`, returns `η`. The two unitors are carried: `unitorX` on `X`, and on `Z` the
natural transformation `u` out of `(𝒪_X[0])|_Z ⊗^L -`, of which `χ` is a section by `hχ`;
`hu` is their compatibility with the map of Tag 0G75. This is what fixes the construction: the
zero map, and the negative of the cup product, both fail it. -/
theorem supportedCupProduct_unit
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (unitorX : ((derivedTensorProductFunctor X.sheaf).obj (shiftedStructureSheaf X 0)).obj M ⟶ M)
    (u : (derivedTensorProductFunctor (closedSubsetRingedSpace X Z).sheaf).obj
        ((derivedPullback (closedSubsetInclusion X Z)).obj (shiftedStructureSheaf X 0)) ⟶
      𝟭 (DerivedCategory (SheafOfModules.{u}
        (structureSheafRing (closedSubsetRingedSpace X Z)))))
    (hu : supportedTensorMap X Z hZ (shiftedStructureSheaf X 0) M ≫
      (derivedSupportedSectionsOnClosed X Z hZ).map unitorX =
        u.app ((derivedSupportedSectionsOnClosed X Z hZ).obj M))
    {V : DerivedCategory (SheafOfModules.{u}
      (structureSheafRing (closedSubsetRingedSpace X Z)))}
    (χ : V ⟶ ((derivedTensorProductFunctor (closedSubsetRingedSpace X Z).sheaf).obj
      ((derivedPullback (closedSubsetInclusion X Z)).obj (shiftedStructureSheaf X 0))).obj V)
    (hχ : χ ≫ u.app V = 𝟙 V)
    (η : V ⟶ (derivedSupportedSectionsOnClosed X Z hZ).obj M) :
    supportedCupProduct X Z hZ (shiftedStructureSheaf X 0) M χ (𝟙 _) η ≫
      (derivedSupportedSectionsOnClosed X Z hZ).map unitorX = η := by
  have hnat := u.naturality η
  rw [CategoryTheory.Functor.id_map] at hnat
  have hid : ((derivedTensorProductFunctor (closedSubsetRingedSpace X Z).sheaf).map
      ((derivedPullback (closedSubsetInclusion X Z)).map
        (𝟙 (shiftedStructureSheaf X 0)))).app V = 𝟙 _ := by
    have e1 := (derivedPullback (closedSubsetInclusion X Z)).map_id
      (shiftedStructureSheaf X 0)
    have e2 := (derivedTensorProductFunctor (closedSubsetRingedSpace X Z).sheaf).map_id
      ((derivedPullback (closedSubsetInclusion X Z)).obj (shiftedStructureSheaf X 0))
    exact (congrArg (fun g =>
        ((derivedTensorProductFunctor (closedSubsetRingedSpace X Z).sheaf).map g).app V) e1).trans
      (congrArg (fun t => NatTrans.app t V) e2)
  refine (congrArg (fun a => (χ ≫ a ≫
    ((derivedTensorProductFunctor (closedSubsetRingedSpace X Z).sheaf).obj
      ((derivedPullback (closedSubsetInclusion X Z)).obj (shiftedStructureSheaf X 0))).map η ≫
      supportedTensorMap X Z hZ (shiftedStructureSheaf X 0) M) ≫
    (derivedSupportedSectionsOnClosed X Z hZ).map unitorX) hid).trans ?_
  refine (congrArg (fun k => (χ ≫ k) ≫
    (derivedSupportedSectionsOnClosed X Z hZ).map unitorX)
    (Category.id_comp (((derivedTensorProductFunctor (closedSubsetRingedSpace X Z).sheaf).obj
      ((derivedPullback (closedSubsetInclusion X Z)).obj (shiftedStructureSheaf X 0))).map η ≫
      supportedTensorMap X Z hZ (shiftedStructureSheaf X 0) M))).trans ?_
  refine (Category.assoc χ (((derivedTensorProductFunctor (closedSubsetRingedSpace X Z).sheaf).obj
      ((derivedPullback (closedSubsetInclusion X Z)).obj (shiftedStructureSheaf X 0))).map η ≫
    supportedTensorMap X Z hZ (shiftedStructureSheaf X 0) M)
    ((derivedSupportedSectionsOnClosed X Z hZ).map unitorX)).trans ?_
  refine (congrArg (fun k => χ ≫ k) (Category.assoc
    (((derivedTensorProductFunctor (closedSubsetRingedSpace X Z).sheaf).obj
      ((derivedPullback (closedSubsetInclusion X Z)).obj (shiftedStructureSheaf X 0))).map η)
    (supportedTensorMap X Z hZ (shiftedStructureSheaf X 0) M)
    ((derivedSupportedSectionsOnClosed X Z hZ).map unitorX))).trans ?_
  refine (congrArg (fun k => χ ≫
    ((derivedTensorProductFunctor (closedSubsetRingedSpace X Z).sheaf).obj
      ((derivedPullback (closedSubsetInclusion X Z)).obj
        (shiftedStructureSheaf X 0))).map η ≫ k) hu).trans ?_
  refine (congrArg (fun k => χ ≫ k) hnat).trans ?_
  refine (Category.assoc χ (u.app V) η).symm.trans ?_
  exact (congrArg (fun k => k ≫ η) hχ).trans (Category.id_comp η)

end Stacks.Cohomology.SupportedComplexes

end
