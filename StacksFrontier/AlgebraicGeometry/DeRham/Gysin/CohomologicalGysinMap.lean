module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGELTSingle
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.SingleObject
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.CohomologyVanishesLocally
public import StacksFrontier.AlgebraicGeometry.AffineMorphismCohomology.Normalized
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinMap
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinMapCutOut
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportedSectionsCanonicalMaps
public import StacksFrontier.Topology.Sheaves.RingedSpace.SheafifyOpens
public import StacksCore.Tactic.StacksAttribute

/-!
# The Gysin map on cohomology

Let `X` be a ringed space, let `Z ⊆ X` be a closed subset and let `c ≥ 0`.  Write
`Rℋ_Z : D(𝒪_X) ⥤ D(𝒪_X|_Z)` for the derived functor of sections supported on `Z` and
`ℋ ^i_Z(ℱ)` for its degree-`i` cohomology sheaf.  Assume

`ℋ ^i_Z(ℱ) = 0` for `i = 0, …, c - 1`.

Then there is a canonical morphism of `D(𝒪_X)`

`i_*ℋ ^c_Z(ℱ)` placed in degree `c` `⟶ ℱ` placed in degree `0`,

and applying `H^{q+c}(X, -)` to it turns a sheaf-level Gysin map
`γ : 𝒜 ⟶ i_*ℋ ^c_Z(ℱ)` into a map of cohomology groups

`γ^{q} : H^q(X, 𝒜) ⟶ H^{q + c}(X, ℱ)`.

Taking `𝒜 = i_*Ω^p_{Z/S}`, `ℱ = Ω^{p+c}_{X/S}` and `γ = γ^p` the Gysin map of relative
differential forms gives the Gysin map `γ^{p, q}` of [Stacks, Tag 0G8A].

## Main definitions

* `singleHomologyToOfIsGE`: for an object `K` of a derived category with no cohomology below
  degree `c`, the canonical morphism `H^c(K)` placed in degree `c` `⟶ K`.
* `localCohomologySingleToDerived`: the instance of the previous map at `K = Rℋ_Z(ℱ)`, that is
  the comparison `ℋ ^c_Z(ℱ)[-c] ⟶ Rℋ_Z(ℱ)` the vanishing hypothesis provides.
* `isZero_localCohomologySheafOfComplex_of_neg`: the local cohomology sheaves of a module placed
  in degree `0` vanish in the negative degrees, so the vanishing hypothesis below has content
  only in the degrees `0 ≤ i < c` the source asks about.
* `supportedGysinEdge`: **the Gysin edge morphism** `i_*ℋ ^c_Z(ℱ)[-c] ⟶ ℱ`, the previous map
  pushed forward and followed by the counit of `i_* ⊣ Rℋ_Z`.
* `derivedGlobalSections` and `cohomologyDerivedSingleIso`: derived global sections on a ringed
  space, and the identification of the degree-`m` cohomology of the derived global sections of a
  module placed in degree `a` with the cohomology group `H^{m - a}(X, -)`.
* `cohomologyMapOfSingleHom`: the map `H^q(X, 𝒜) ⟶ H^{q+c}(X, ℱ)` induced by a morphism
  `𝒜[-c] ⟶ ℱ` of the derived category.
* `gysinCohomologyMap`: **[Stacks, Tag 0G8A]**, the Gysin map on cohomology.
* `equationGysinCohomologyMap`: the same for the Gysin map `γ^p_{f₁, …, f_c}` of a family of
  equations, [Stacks, Tag 0G83].
* `equationGysinHodgeMap`: **[Stacks, Tag 0G8A]** for that Gysin map, with the source written as
  the Hodge cohomology `H^q(Z, Ω^p_{Z/S})` of the closed subscheme, and with no hypothesis on
  `Z` beyond the source's own — the equations cut it out.  The number of equations is an
  arbitrary `c : ℕ`, the source's `c ≥ 0`, the empty family included.
* `equationGysinHodgeMapEmpty`: the previous map at the empty family, with both of its
  hypotheses proved rather than assumed — the witness that the `c = 0` end of the source's
  range is covered.

The same reading of the source on the closed subscheme, for an *arbitrary* sheaf-level Gysin map
rather than the one of a family of equations, is
`Stacks.DeRham.CohomologicalGysin.gysinHodgeMap` of
`StacksFrontier.AlgebraicGeometry.DeRham.Gysin.CohomologicalGysinHodgeGeneral`, which imports this
file.

## Implementation notes

**The construction is the source's.**  The source composes four steps: functoriality of `H^q`
applied to `γ^p`; the passage `H^q(Z, ℋ ^c_Z(ℱ)) ⟶ H^q(Z, Rℋ_Z(ℱ)[c])`; the identification
`H^q(Z, -) = H^q(X, i_*-)`; and the adjunction map `i_*Rℋ_Z(ℱ) ⟶ ℱ`.  Here the second and
fourth are performed at the level of the derived category, before any cohomology is taken, which
is what `supportedGysinEdge` is; the first and third are then absorbed into one application of
`H^{q+c}(X, -)` on `X`, because every sheaf in sight is read on `X` through the direct image
along the inclusion of the closed subset.  That is the convention the Gysin map itself is stated
in by `AlgebraicGeometry.Scheme.Hom.gysinMap`, whose source is `i_*Ω^p_{Z/S}`.  The source's
own `H^q(Z, Ω^p_{Z/S})` is recovered in `equationGysinHodgeMap`: a closed immersion is an affine
morphism and `Ω^p_{Z/S}` is quasi-coherent, so the comparison `H^q(Z, ℳ) = H^q(X, i_*ℳ)` is the
affine-pushforward isomorphism of [Stacks, Tag 089W], available as
`Stacks.AffineCohomologyResolution.cohomologyPushforwardIso` and pinned there by its
characterisation on an injective resolution.  Nothing in that third step is particular to the
Gysin map of a family of equations, and
`StacksFrontier.AlgebraicGeometry.DeRham.Gysin.CohomologicalGysinHodgeGeneral` performs it at
`gysinCohomologyMap` itself, for an arbitrary sheaf-level `γ` and arbitrary quasi-coherent
coefficients on `Z`; `equationGysinHodgeMap` factors through that general form by definition.

**Where the vanishing hypothesis enters** is the second step, and only there.  The object
`Rℋ_Z(ℱ)` has no cohomology below degree `c` exactly when the hypothesis holds, by
`DerivedCategory.isGE_iff`, and then `τ^{≥c}Rℋ_Z(ℱ) ⟶ Rℋ_Z(ℱ)` is invertible while the one-step
truncation `τ^{≥c}τ^{<c+1}` is `ℋ ^c_Z(ℱ)` placed in degree `c`, by
`DerivedCategory.truncGELTIsoHomologyFunctorCompSingleFunctor`.  The composite is
`singleHomologyToOfIsGE`, which the library did not have: the mirror statement for an object
with no cohomology *above* a degree is
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.truncGEIsoSingleHomology`, and the shape needed
here was available only inside the existential of
`DerivedCategory.exists_truncGESucc_triangle`, out of which no map can be written down.

**The adjunction is a term.**  The fourth step needs the counit of `i_* ⊣ Rℋ_Z`, so the
existence statement `derivedPushforward_adj_derivedSupportedSectionsOnClosed` of [Stacks, Tag
0A3B] does not suffice; `Stacks.Cohomology.SupportedComplexes.derivedPushforwardAdjunction` is the
chosen term, whose unit is pinned as the canonical comparison.

**Cohomology groups** are `Hgroup`, the right derived functors of global sections, and the
passage between them and the homology of derived global sections is
`Stacks.DerivedFunctor.homologyTotalRightDerivedSingleShiftIso`, which is where the degree shift
by `c` is performed.  Its `hres` hypothesis — existence of K-injective resolutions — is
`exists_isKInjective_quasiIso_moduleSheaves`.

**The vanishing in degrees `i < c` is a hypothesis here, and the source's sufficient condition for
it is available.**  The source remarks that it holds when `X → S` is smooth and `Z → X` is Koszul
regular, by [Stacks, Tag 0G7P].  The library's 0G7P is
`isZero_homology_derivedSupportedSections_of_locallyKoszulRegular_of_ne` of
`Stacks.Perfect.LocalCohomologyDegrees`, in
`StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.KoszulFlatVanishingLocal`, and its
`i < c` half `isZero_homology_derivedSupportedSections_of_locallyKoszulRegular_of_lt` has exactly
the shape of `hvan` below: for `X` a scheme, `ℱ` flat and quasi-coherent and `Z` locally cut out by
a Koszul-regular sequence of `c` elements, it discharges the hypothesis directly, no comparison of
spellings intervening, `localCohomologySheafOfComplex` being an abbreviation for the homology of
`derivedSupportedSectionsOnClosed`.  The hypothesis is kept because this construction is stated for
an arbitrary ringed space and an arbitrary module, where neither of 0G7P's inputs is available.

**The description of the kernel of restriction of `p`-forms is *not* a hypothesis of the tagged
map.**  `equationGysinHodgeMap` takes `hcut`, the hypothesis of [Stacks, Tag 0G83] itself — the
equations generate the ideal sheaf of `Z` — and the description
`AlgebraicGeometry.Scheme.Hom.FormKernelGeneratedByEquations` that the sheaf-level Gysin map
descends along is derived from it by
`AlgebraicGeometry.Scheme.Hom.formKernelGeneratedByEquations_of_isCutOutByEquations` of
`StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinMapCutOut`, so the sheaf-level map used is the
unconditional `AlgebraicGeometry.Scheme.Hom.gysinMap`.  The intermediate
`equationGysinCohomologyMap` still takes the description, because the projection formula of
[Stacks, Tag 0G8C] is stated at that generality; nothing tagged assumes it.

**Four instances are supplied locally.**  `Abelian` and `HasDerivedCategory` for
`Mod(𝒪_X)` on a ringed space are found by instance search in the supported-sections files, but
not once the differential-forms chain of `StacksDraft.AlgebraicGeometry.DeRham.Complex` is also
imported: the search for `HasSheafify` and `GrothendieckTopology.WEqualsLocallyBijective` on the
open-cover site then fails, and with it everything built on `Abelian`.  The first two of those
four are the shared `scoped instance`s of
`Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat` and
`opensWEqualsLocallyBijectiveAddCommGrpCat`, named locally for an arbitrary ringed space here
exactly as `Stacks.Cohomology.StrictlyPerfectInvertibility` names them for the same reason; the
other two, `moduleSheavesAbelian` and `moduleSheavesHasDerivedCategory`, are restated below and
restore both at the default elaboration budget.

## References

* [Stacks Project, Tag 0G8A](https://stacks.math.columbia.edu/tag/0G8A)
* [Stacks Project, Tag 0G86](https://stacks.math.columbia.edu/tag/0G86)
* [Stacks Project, Tag 0G83](https://stacks.math.columbia.edu/tag/0G83)
* [Stacks Project, Tag 0A3B](https://stacks.math.columbia.edu/tag/0A3B)
* [Stacks Project, Tag 0G7P](https://stacks.math.columbia.edu/tag/0G7P)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.SupportedComplexes
open Stacks.SheafOfModules.SupportedSections (supportedSectionsOnClosedFunctor)

namespace Stacks.DeRham.CohomologicalGysin

universe u

open DerivedCategory

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat
  Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat

/-- Sheaves of modules on a ringed space have a derived category. -/
local instance moduleSheavesHasDerivedCategory (X : RingedSpace.{u, u}) :
    HasDerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X)) :=
  HasDerivedCategory.standard _

/-- Sheaves of modules on a ringed space, at the spelling the cohomological Gysin map of
[Stacks, Tag 0G8A] is stated in. -/
abbrev RModules (X : RingedSpace.{u, u}) : Type (u + 1) :=
  _root_.SheafOfModules.{u} (structureSheafRing X)

/-! ### A one-step truncation out of the bottom cohomology object -/

section Truncation

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

/-- **An object with no cohomology below `c` receives a canonical map from `H^c(K)[-c]`.** For
such a `K` the projection `K ⟶ τ^{≥c}K` is invertible, so `τ^{≥c}K` is `τ^{≥c}τ^{<c+1}K`, which
is `H^c(K)` placed in degree `c` by
`DerivedCategory.truncGELTIsoHomologyFunctorCompSingleFunctor`.

This is the mirror image of
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.truncGEIsoSingleHomology`, which is the
corresponding statement for an object with no cohomology *above* a degree. -/
def singleHomologyToOfIsGE (K : DerivedCategory C) (c : ℤ) (hK : TStructure.t.IsGE K c) :
    (singleFunctor C c).obj ((homologyFunctor C c).obj K) ⟶ K :=
  have : IsIso ((TStructure.t.truncGEπ c).app K) :=
    (TStructure.t.isGE_iff_isIso_truncGEπ_app c K).1 hK
  (truncGELTIsoHomologyFunctorCompSingleFunctor c).inv.app K ≫
    (TStructure.t.truncGE c).map ((TStructure.t.truncLTι (c + 1)).app K) ≫
      inv ((TStructure.t.truncGEπ c).app K)

end Truncation

/-! ### The Gysin edge morphism -/

section Supported

variable {X : RingedSpace.{u, u}} (Z : Set X.carrier) (hZ : IsClosed Z)

/-- Sheaves of `𝒪_X|_Z`-modules, for `Z` a closed subset of a ringed space `X`. -/
abbrev SupportedModules (X : RingedSpace.{u, u}) (Z : Set X.carrier) : Type (u + 1) :=
  _root_.SheafOfModules.{u}
    (structureSheafRing (closedSubsetRingedSpace X Z))

/-- **The local cohomology sheaves of a module placed in degree `0` vanish in the negative
degrees.** `Rℋ _Z` is the derived functor of a left-exact functor, so on a module placed in
degree `0` it has no cohomology below degree `0`: the object agrees with the bounded-below
right derived functor, which is `IsGE 0` by
`CategoryTheory.Functor.isGE_rightDerivedFunctorPlus_obj`, and the agreement is
`Stacks.Perfect.CechAugmentation.nonempty_obj_iso_rightDerivedFunctorPlus`, whose hypothesis
that the derivation unit inverts the K-injective complexes is
`Stacks.Perfect.CechAugmentation.isIso_app_quotient_obj_of_isKInjective`.

This is what says that the vanishing hypothesis of `gysinCohomologyMap` — stated, as the
`DerivedCategory.isGE_iff` interface demands, for every integer `i < c` — has content only in
the degrees `0 ≤ i < c` that [Stacks, Tag 0G8A] asks about, and in particular that it is
discharged outright when `c = 0`. -/
theorem isZero_localCohomologySheafOfComplex_of_neg
    (F : _root_.SheafOfModules.{u} (structureSheafRing X)) (i : ℤ) (hi : i < 0) :
    IsZero (localCohomologySheafOfComplex X Z hZ i ((singleFunctor _ (0 : ℤ)).obj F)) := by
  let : IsGrothendieckAbelian.{u} (_root_.SheafOfModules.{u} (structureSheafRing X)) :=
    inferInstance
  let : EnoughInjectives (_root_.SheafOfModules.{u} (structureSheafRing X)) :=
    IsGrothendieckAbelian.enoughInjectives
  have hcomp : ∀ I : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing X)) ℤ,
      I.IsKInjective →
      IsIso ((derivedSupportedSectionsOnClosedUnit X Z hZ).app
        ((HomotopyCategory.quotient (_root_.SheafOfModules.{u} (structureSheafRing X))
          (ComplexShape.up ℤ)).obj I)) := fun I hI =>
    Stacks.Perfect.CechAugmentation.isIso_app_quotient_obj_of_isKInjective
      (supportedSectionsOnClosedFunctor X Z hZ) (derivedSupportedSectionsOnClosed X Z hZ)
      (derivedSupportedSectionsOnClosedUnit X Z hZ)
      (exists_isKInjective_quasiIso_moduleSheaves X) I hI
  obtain ⟨eplus⟩ :=
    Stacks.Perfect.CechAugmentation.nonempty_obj_iso_rightDerivedFunctorPlus
      (supportedSectionsOnClosedFunctor X Z hZ) (derivedSupportedSectionsOnClosed X Z hZ)
      (derivedSupportedSectionsOnClosedUnit X Z hZ) hcomp
      ((DerivedCategory.Plus.singleFunctor
        (_root_.SheafOfModules.{u} (structureSheafRing X)) 0).obj F) 0
      (by
        change ((DerivedCategory.singleFunctor
          (_root_.SheafOfModules.{u} (structureSheafRing X)) 0).obj F).IsGE 0
        infer_instance)
  have := CategoryTheory.Functor.isGE_rightDerivedFunctorPlus_obj
    (supportedSectionsOnClosedFunctor X Z hZ)
    ((DerivedCategory.Plus.singleFunctor
      (_root_.SheafOfModules.{u} (structureSheafRing X)) 0).obj F) 0
  refine IsZero.of_iso (DerivedCategory.Plus.isZero_homology_of_isGE
    ((supportedSectionsOnClosedFunctor X Z hZ).rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor
        (_root_.SheafOfModules.{u} (structureSheafRing X)) 0).obj F)) 0 i hi)
    ((DerivedCategory.homologyFunctor _ i).mapIso ?_)
  exact (derivedSupportedSectionsOnClosed X Z hZ).mapIso
      ((DerivedCategory.Plus.singleFunctorιIso
        (_root_.SheafOfModules.{u} (structureSheafRing X)) 0).app F).symm ≪≫ eplus

/-- **The comparison `ℋ ^c_Z(K)[-c] ⟶ Rℋ_Z(K)`** supplied by the vanishing of the local
cohomology sheaves `ℋ ^i_Z(K)` in the degrees `i < c`: with that vanishing `Rℋ_Z(K)` has no
cohomology below degree `c`, which is what `singleHomologyToOfIsGE` consumes. -/
def localCohomologySingleToDerived (c : ℤ)
    (K : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X)))
    (hvan : ∀ i : ℤ, i < c → IsZero (localCohomologySheafOfComplex X Z hZ i K)) :
    (singleFunctor (SupportedModules X Z) c).obj (localCohomologySheafOfComplex X Z hZ c K) ⟶
      (derivedSupportedSectionsOnClosed X Z hZ).obj K :=
  singleHomologyToOfIsGE _ c ((DerivedCategory.isGE_iff _ c).2 hvan)

/-- **The Gysin edge morphism** `i_*ℋ ^c_Z(K)[-c] ⟶ K` of `D(𝒪_X)`: the comparison
`localCohomologySingleToDerived` pushed forward along the inclusion of the closed subset,
followed by the counit of the adjunction `i_* ⊣ Rℋ_Z` of [Stacks, Tag 0A3B].

Pushforward along an exact functor commutes with placing an object in a single degree, by
`CategoryTheory.Functor.mapDerivedCategorySingleFunctor`, which is how the source of the
composite is read as a single complex on `X`. -/
def supportedGysinEdge (c : ℤ)
    (K : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X)))
    (hvan : ∀ i : ℤ, i < c → IsZero (localCohomologySheafOfComplex X Z hZ i K)) :
    (singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) c).obj
        ((modulePushforward (closedSubsetInclusion X Z)).obj
          (localCohomologySheafOfComplex X Z hZ c K)) ⟶ K :=
  letI := pushforward_preservesFiniteLimits X Z
  letI := pushforward_preservesFiniteColimits X Z hZ
  ((modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategorySingleFunctor c).inv.app
      (localCohomologySheafOfComplex X Z hZ c K) ≫
    (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory.map
      (localCohomologySingleToDerived Z hZ c K hvan) ≫
    (derivedPushforwardAdjunction X Z hZ).counit.app K

end Supported

/-! ### The map on cohomology -/

section Cohomology

variable {X : RingedSpace.{u, u}} (Z : Set X.carrier) (hZ : IsClosed Z)

/-- Derived global sections on a ringed space, the unbounded right derived functor of
`Γ(X, -) : Mod(𝒪_X) ⥤ Ab`. -/
abbrev derivedGlobalSections (X : RingedSpace.{u, u}) :
    DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory AddCommGrpCat.{u} :=
  Stacks.DerivedFunctor.totalRightDerived
    (secF (structureSheafRing X) (⊤ : Opens X.carrier))

/-- The derivation unit of `derivedGlobalSections`. -/
abbrev derivedGlobalSectionsUnit (X : RingedSpace.{u, u}) :=
  (Stacks.DerivedFunctor.homotopyMap
      (secF (structureSheafRing X)
        (⊤ : Opens X.carrier))).totalRightDerivedUnit
    DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (_root_.SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))

/-- **The degree-`m` cohomology of the derived global sections of `𝒜` placed in degree `a` is the
cohomology group `H^{m - a}(X, 𝒜)`.** This is
`Stacks.DerivedFunctor.homologyTotalRightDerivedSingleShiftIso`, whose hypothesis that
K-injective resolutions exist is `exists_isKInjective_quasiIso_moduleSheaves`. -/
def cohomologyDerivedSingleIso (X : RingedSpace.{u, u})
    (A : _root_.SheafOfModules.{u} (structureSheafRing X))
    (a m : ℤ) (n : ℕ) (hn : m - a = n) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).obj
        ((derivedGlobalSections X).obj ((singleFunctor _ a).obj A)) ≅
      Hgroup (structureSheafRing X) ⊤ n A :=
  Stacks.DerivedFunctor.homologyTotalRightDerivedSingleShiftIso _ _
    (derivedGlobalSectionsUnit X) (exists_isKInjective_quasiIso_moduleSheaves X) A a m n hn

/-- **The map on cohomology induced by a morphism `𝒜[-c] ⟶ ℱ` of the derived category**: apply
derived global sections, take cohomology in degree `q + c`, and read both sides as cohomology
groups through `cohomologyDerivedSingleIso`. The degree shift by `c` happens here. -/
def cohomologyMapOfSingleHom (X : RingedSpace.{u, u})
    (A F : _root_.SheafOfModules.{u} (structureSheafRing X)) (c q : ℕ)
    (φ : (singleFunctor _ (c : ℤ)).obj A ⟶ (singleFunctor _ (0 : ℤ)).obj F) :
    Hgroup (structureSheafRing X) ⊤ q A ⟶
      Hgroup (structureSheafRing X) ⊤ (q + c) F :=
  (cohomologyDerivedSingleIso X A (c : ℤ) ((q : ℤ) + (c : ℤ)) q (by omega)).inv ≫
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} ((q : ℤ) + (c : ℤ))).map
      ((derivedGlobalSections X).map φ) ≫
    (cohomologyDerivedSingleIso X F (0 : ℤ) ((q : ℤ) + (c : ℤ)) (q + c) (by omega)).hom

/-- **Stacks Project, Tag 0G8A: the Gysin map on cohomology.** Let `Z` be a closed subset of a
ringed space `X`, let `c ≥ 0`, let `ℱ` be an `𝒪_X`-module and assume

`ℋ ^i_Z(ℱ) = 0` for `i = 0, …, c - 1`.

A sheaf-level Gysin map `γ : 𝒜 ⟶ i_*ℋ ^c_Z(ℱ)` then induces

`γ^q : H^q(X, 𝒜) ⟶ H^{q + c}(X, ℱ)`

for every `q`: place `γ` in degree `c`, follow it by the Gysin edge morphism
`supportedGysinEdge`, and apply cohomology.

The source's `γ^{p, q}` is the case `𝒜 = i_*Ω^p_{Z/S}`, `ℱ = Ω^{p+c}_{X/S}` and `γ = γ^p`; the
case where `γ` is the Gysin map of a family of equations is `equationGysinCohomologyMap`, and
the source read on the closed subscheme as `H^q(Z, -)` — at this same generality in `γ` — is
`gysinHodgeMap` of
`StacksFrontier.AlgebraicGeometry.DeRham.Gysin.CohomologicalGysinHodgeGeneral`.

The hypothesis `hvan` is stated for every integer `i < c`, which is what `DerivedCategory.isGE_iff`
consumes; it has content only in the degrees `0 ≤ i < c` that the source names, because the
negative ones are `isZero_localCohomologySheafOfComplex_of_neg`. -/
def gysinCohomologyMap (c : ℕ)
    (A F : _root_.SheafOfModules.{u} (structureSheafRing X))
    (hvan : ∀ i : ℤ, i < (c : ℤ) → IsZero (localCohomologySheafOfComplex X Z hZ i
      ((singleFunctor _ (0 : ℤ)).obj F)))
    (γ : A ⟶ (modulePushforward (closedSubsetInclusion X Z)).obj
      (localCohomologySheafOfComplex X Z hZ (c : ℤ) ((singleFunctor _ (0 : ℤ)).obj F)))
    (q : ℕ) :
    Hgroup (structureSheafRing X) ⊤ q A ⟶
      Hgroup (structureSheafRing X) ⊤ (q + c) F :=
  cohomologyMapOfSingleHom X A F c q
    ((singleFunctor _ (c : ℤ)).map γ ≫
      supportedGysinEdge Z hZ (c : ℤ) ((singleFunctor _ (0 : ℤ)).obj F) hvan)

end Cohomology

/-! ### The Gysin map of a family of equations, on cohomology -/

section EquationChart

open Stacks.Perfect.CechDerivedSupport (equationsClosedSet isClosed_equationsClosedSet)
open AlgebraicGeometry.Scheme.Hom
open scoped AlgebraicGeometry

variable {Z X S : Scheme.{u}}

/-- **Stacks Project, Tag 0G8A for the Gysin map of a family of equations.** Let `π : X ⟶ S` be a
morphism of schemes, let `f₁, …, f_c ∈ Γ(X, 𝒪_X)` with `c ≥ 0` arbitrary, let `i : Z ⟶ X` be the
closed subscheme they cut out, and assume the local cohomology sheaves
`ℋ ^j_Z(Ω^{p+c}_{X/S})` vanish for `j = 0, …, c - 1`. Then the Gysin map
`γ^p_{f₁, …, f_c}` of [Stacks, Tag 0G83] induces

`γ^{p, q} : H^q(Z, Ω^p_{Z/S}) ⟶ H^{q + c}(X, Ω^{p + c}_{X/S})`,

the source being read on `X` as `H^q(X, i_*Ω^p_{Z/S})`, which is the shape
`AlgebraicGeometry.Scheme.Hom.gysinMap` has its source in; `equationGysinHodgeMap` is the same
map with the source written as `H^q(Z, Ω^p_{Z/S})`.

`hker` is the description of the kernel of restriction of `p`-forms that
`gysinMapOfFormKernel` itself assumes. It is an input of this auxiliary definition only, and is
*not* an assumption of the tagged [Stacks, Tag 0G8A] below: `equationGysinHodgeMap` takes
instead the source's own hypothesis that the equations cut out `Z` and derives `hker` from it
with `AlgebraicGeometry.Scheme.Hom.formKernelGeneratedByEquations_of_isCutOutByEquations`. The
hypothesis is kept here because the projection formula of [Stacks, Tag 0G8C] is stated at this
generality.

**`c = 0` is included.** The empty family is allowed, as it is in the source: then
`equationsClosedSet f` is the whole of `X`, the vanishing hypothesis `hvan` is vacuous, and the
map is the one the construction degenerates to on the empty family, with no convention imposed
by hand. Nothing below `c = 1` is special-cased: every ingredient —
`AlgebraicGeometry.Scheme.Hom.gysinMapOfFormKernel`, `gysinWedgeHom`, `formFractionClass` and
`gysinCohomologyMap` — is already stated for an arbitrary `c : ℕ`. -/
def equationGysinCohomologyMap (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (p : ℕ)
    [(relativeDifferentialForms π ((p : ℤ) + (c : ℤ))).IsQuasicoherent]
    (hker : FormKernelGeneratedByEquations i π f (p : ℤ))
    (hvan : ∀ j : ℤ, j < (c : ℤ) →
      IsZero (localCohomologySheafOfComplex X.toRingedSpace (equationsClosedSet f)
        (isClosed_equationsClosedSet f) j ((singleFunctor _ (0 : ℤ)).obj
          (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))))))
    (q : ℕ) :
    Hgroup X.ringCatSheaf ⊤ q
        ((Scheme.Modules.pushforward i).obj (relativeDifferentialForms (i ≫ π) (p : ℤ))) ⟶
      Hgroup X.ringCatSheaf ⊤ (q + c)
        (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))) :=
  gysinCohomologyMap (equationsClosedSet f) (isClosed_equationsClosedSet f) c _ _ hvan
    (gysinMapOfFormKernel i π f p hker) q

/-- **Stacks Project, Tag 0G8A for the Gysin map of a family of equations, on Hodge
cohomology.** This is `equationGysinCohomologyMap` with its source written as the Hodge
cohomology of the closed subscheme,

`γ^{p, q} : H^q(Z, Ω^p_{Z/S}) ⟶ H^{q + c}(X, Ω^{p + c}_{X/S})`,

which is the shape of the source. The two sources are identified by the affine-pushforward
comparison of [Stacks, Tag 089W]: a closed immersion is an affine morphism and `Ω^p_{Z/S}` is
quasi-coherent, so `H^q(Z, Ω^p_{Z/S}) = H^q(X, i_*Ω^p_{Z/S})`. That comparison is not a free
choice — `Stacks.AffineCohomologyResolution.cohomologyPushforwardIso_hom_eq` and
`cohomologyPushforwardIso_zero_hom` pin it.

**The kernel description is not assumed here.** The hypothesis on `Z` is the source's own, that
the equations cut out the closed subscheme, and the description of the kernel of restriction of
`p`-forms that `gysinMapOfFormKernel` needs is derived from it by
`AlgebraicGeometry.Scheme.Hom.formKernelGeneratedByEquations_of_isCutOutByEquations`. The
sheaf-level Gysin map used is therefore exactly `AlgebraicGeometry.Scheme.Hom.gysinMap`, the
unconditional [Stacks, Tag 0G83].

`hcut` also pins the closed subset the vanishing hypothesis `hvan` is about. The local cohomology
sheaves are taken with supports in the common zero locus of the equations, and that locus is the
image of `Z` exactly because the equations cut `Z` out, by
`Stacks.Gysin.equationsClosedSet_eq_range`; so `hvan` is the source's `ℋ^j_Z(Ω^{p+c}_{X/S}) = 0`
and not a condition about some larger closed set.

**The whole range `c ≥ 0` of the source is covered**, the empty family included. For `c = 0` the
common zero locus `equationsClosedSet f` is the complement of the empty supremum of principal
opens, that is the whole of `X`; `hcut` asks exactly that the ideal sheaf of `i` vanish, which is
the source's `Z = X`, and is satisfied — so the case is not vacuous — by
`Stacks.Gysin.isCutOutByEquations_id_of_isEmpty`; and the map goes
`H^q(Z, Ω^p_{Z/S}) ⟶ H^q(X, Ω^{p+0}_{X/S})`, an endomorphism of `H^q(X, Ω^p_{X/S})` for
`i = 𝟙 X` up to the degree identification `p + 0 = p`.

The vanishing hypothesis `hvan` is *not* vacuous at `c = 0` — read at `c = 0` it still
quantifies over the negative integers, because `DerivedCategory.isGE_iff`, which is what
consumes it, is stated for every integer below the bound. It is instead **discharged**:
`isZero_localCohomologySheafOfComplex_of_neg` proves the vanishing in the negative degrees for
any module placed in degree `0`, which is exactly the whole of `hvan` when `c = 0`. So the
`c = 0` case of this construction carries no hypothesis at all, which is what
`equationGysinHodgeMapEmpty` records.

No convention is imposed for that case: it is the one general construction read at `c = 0`,
nothing being special-cased below `c = 1`. The degeneration is carried by the ingredients
themselves — the empty product of the equations is `1`, so the fraction `ω̃ / (f₁ ⋯ f_c)` is `ω̃`,
and the empty wedge `d f₁ ∧ ⋯ ∧ d f_c` is the unit of `Ω^•_{X/S}` by
`AlgebraicGeometry.Scheme.Hom.gysinWedgeHom_empty_apply`. That the resulting map *is* the
identity is **not** claimed: it would need the degeneration `ℋ^0_Z(ℱ) = ℱ` at `Z` the whole
space, which the supported-sections files state for no closed subset in particular, together
with the counit of `i_* ⊣ Rℋ_Z` computed there. Tag 0G8A asks for the construction of `γ^{p,q}`
and that is what is built, for every `c ≥ 0`. -/
def equationGysinHodgeMap (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (p : ℕ)
    [(relativeDifferentialForms π ((p : ℤ) + (c : ℤ))).IsQuasicoherent]
    (hcut : Stacks.Gysin.IsCutOutByEquations i f)
    (hvan : ∀ j : ℤ, j < (c : ℤ) →
      IsZero (localCohomologySheafOfComplex X.toRingedSpace (equationsClosedSet f)
        (isClosed_equationsClosedSet f) j ((singleFunctor _ (0 : ℤ)).obj
          (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))))))
    (q : ℕ) :
    Hgroup Z.ringCatSheaf ⊤ q (relativeDifferentialForms (i ≫ π) (p : ℤ)) ⟶
      Hgroup X.ringCatSheaf ⊤ (q + c)
        (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))) :=
  ((Stacks.AffineCohomologyResolution.cohomologyPushforwardIso i q).app
      ⟨relativeDifferentialForms (i ≫ π) (p : ℤ),
        isQuasicoherent_relativeDifferentialForms (i ≫ π) p⟩).hom ≫
    equationGysinCohomologyMap i π f p
      (formKernelGeneratedByEquations_of_isCutOutByEquations i π hcut p) hvan q

/-- **The `c = 0` case of `equationGysinHodgeMap`, with nothing assumed.** The empty family of
equations is allowed by [Stacks, Tag 0G8A] — it is the case `c = 0` of its `c ≥ 0` — and this is
the construction read there: the closed immersion is `𝟙 X`, the hypothesis that the equations
cut it out is `Stacks.Gysin.isCutOutByEquations_id_of_isEmpty`, and the vanishing of the local
cohomology sheaves below degree `0` is `isZero_localCohomologySheafOfComplex_of_neg`.

Both hypotheses of `equationGysinHodgeMap` are therefore *proved* here rather than assumed, so
this witnesses that the `c = 0` end of the range is covered and non-vacuous. The quasi-coherence
instance is likewise found, by
`AlgebraicGeometry.Scheme.Hom.isQuasicoherent_relativeDifferentialForms_natCast_add`.

That the resulting endomorphism of `H^q(X, Ω^p_{X/S})` *is* the identity is not claimed; see the
discussion in `equationGysinHodgeMap`. -/
def equationGysinHodgeMapEmpty (π : X ⟶ S) (p q : ℕ) :
    Hgroup X.ringCatSheaf ⊤ q (relativeDifferentialForms (𝟙 X ≫ π) (p : ℤ)) ⟶
      Hgroup X.ringCatSheaf ⊤ (q + 0)
        (relativeDifferentialForms π ((p : ℤ) + ((0 : ℕ) : ℤ))) :=
  equationGysinHodgeMap (𝟙 X) π Fin.elim0 p
    (Stacks.Gysin.isCutOutByEquations_id_of_isEmpty _)
    (fun j hj => isZero_localCohomologySheafOfComplex_of_neg _ _ _ j (by exact_mod_cast hj)) q

end EquationChart

end Stacks.DeRham.CohomologicalGysin

end
