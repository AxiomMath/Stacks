module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.DeterminantChangeOfEquations
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.SupportCounitComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportedPullbackOpenImmersion

/-!
# Excision for `i_* R𝓗_T` along an open immersion, at the `supportPush` spelling

Let `f : (X', 𝒪_{X'}) ⟶ (X, 𝒪_X)` be an open immersion of ringed spaces, let `Z ⊆ X` be closed
and let `Z' = f^{-1}(Z)`.  [Stacks, Tag 0G78] along an open immersion is in this repository, as
`Stacks.Cohomology.SupportedComplexes.isIso_supportedPullbackMap_of_isOpenImmersion`, but it is
stated at the `derivedSupportedSectionsOnClosed` spelling of `R𝓗_Z`, that is for the canonical
map

`L(f|_{Z'})^* R𝓗_Z(K) ⟶ R𝓗_{Z'}(Lf^* K)`

in `D(𝒪_{X'}|_{Z'})`, one object at a time.  Its consumers — the comparison of
[Stacks, Tag 0G7L] `Stacks.Perfect.SupportedFraction.cechToDerivedSupport` and the classes of
[Stacks, Tag 0G7Q] built on it — work with `Stacks.Perfect.SupportedFraction.supportPush`, the
endofunctor `i_* R𝓗_T` of `D(𝒪_X)`, with its counit
`Stacks.Perfect.SupportedFraction.supportPushCounit` of [Stacks, Tag 0G72] and with the
augmentation of [Stacks, Tag 0G7L].  This file carries the result across: it produces excision
as a natural isomorphism of endofunctors and transports the counit and the augmentation along
it.

## Main definitions

* `transposeNatTrans`: the transpose of a natural transformation `S ⋙ P ⟶ T` along an
  adjunction `P ⊣ R`, as a natural transformation `S ⟶ T ⋙ R`.
* `supportedPullbackBaseChangeNatIso`: the base-change transformation of [Stacks, Tag 08HY] for
  the square of the restriction, as a **natural isomorphism** `Ri_* ⋙ Lf^* ≅ L(f|_{Z'})^* ⋙
  Ri'_*`; the components are
  `Stacks.Cohomology.SupportedComplexes.supportedPullbackBaseChangeMap`.
* `supportedPullbackMateNatTrans` and `supportedPullbackNatTrans`: the displayed composite of
  [Stacks, Tag 0G78] and **the canonical map of [Stacks, Tag 0G78] itself, as natural
  transformations**.  The second is `Stacks.Cohomology.SupportedComplexes.supportedPullbackMap`
  at every object (`supportedPullbackNatTrans_app`), which is what gives that map its naturality
  in `K`; the library had it only object by object.
* `derivedSupportedPushforwardPullbackIso`: **excision for `i_* R𝓗_Z`**, the natural isomorphism
  `i_* R𝓗_Z ⋙ Lf^* ≅ Lf^* ⋙ i'_* R𝓗_{Z'}`.
* `supportPushPullbackIso`: the same isomorphism read at the `supportPush` spelling of a scheme.

## Main results

* `isIso_supportedPullbackNatTrans`: the canonical map of [Stacks, Tag 0G78] is a natural
  isomorphism along an open immersion, with no hypothesis beyond `IsClosed Z`.
* `derivedSupportedPushforwardPullbackIso_hom_comp_counit` and
  `derivedSupportedPushforwardPullbackIso_hom_comp_derivedSupportedSectionsToId`: **the counit
  carried along the transport.**  The excision isomorphism takes the canonical map
  `i'_* R𝓗_{Z'}(Lf^* K) ⟶ Lf^* K` of [Stacks, Tag 0G72] on `X'` to the derived pullback of the
  one on `X`.  The first is stated for the counit of the adjunction of [Stacks, Tag 0A3B], the
  second for the derived-functor transition
  `Stacks.Cohomology.SupportedComplexes.derivedSupportedSectionsToId` that
  `supportPushCounit` abbreviates; the two are the same map by
  `Stacks.Perfect.SupportCounitComparison`'s
  `derivedSupportedSectionsToId_eq_derivedPushforwardAdjunction_counit`.
* `supportPushPullbackIso_hom_comp_supportPushCounit`: the same, literally at
  `supportPushCounit`.
* `derivedSupportedSectionsToId_comp_map_comp_pullbackIso_hom`: **the augmentation carried along
  the transport.**  A map `v : A ⟶ i_* R𝓗_Z(K)` satisfying the triangle of [Stacks, Tag 0G7L]
  for some `u : A ⟶ K` — that is, `counit ≫ v = i_* R𝓗_Z(u)` — is carried by `Lf^*` and the
  excision isomorphism to a map satisfying the same triangle on `X'` for `Lf^* u`.
* `derivedSupportedSectionsToId_comp_map_cechToDerivedSupport_comp_pullbackIso_hom`: that
  statement at `Stacks.Perfect.SupportedFraction.cechToDerivedSupport` and the augmentation of
  the extended alternating Čech complex, which is the form the Čech classes consume.

## Implementation notes

**The route.**  Excision at the pushed-forward spelling is the three-step chain

`i_* R𝓗_Z ⋙ Lf^* ≅ Ri_* R𝓗_Z ⋙ Lf^* ≅ R𝓗_Z ⋙ L(f|_{Z'})^* ⋙ Ri'_* ≅ Lf^* ⋙ R𝓗_{Z'} ⋙ i'_*`,

whose middle step is the base-change isomorphism of [Stacks, Tag 08HY] — free for an open
immersion by
`Stacks.Cohomology.SupportedComplexes.isIso_supportedPullbackBaseChangeMap_of_isOpenImmersion`
— and whose last step is [Stacks, Tag 0G78].  The two outer steps are the comparison
`Stacks.Cohomology.SupportedComplexes.closedPushforwardComparison` of the exact direct image,
and they cancel against each other in the counit compatibility.  **The order of the factors is
chosen to be the order of the commutative triangle**
`Stacks.Cohomology.SupportedComplexes.supportedPullbackMap_triangle`: with the comparison on
`X'` applied *before* the map of [Stacks, Tag 0G78] rather than after, the counit compatibility
is that triangle with one pair of mutually inverse comparisons cancelled, and no naturality step
is needed.

**The canonical map and the comparison of functors are the same map.**  The repository also has
`Stacks.Cohomology.SupportedComplexes.derivedSupportedSectionsOnClosedPullbackNatIso`, a natural
isomorphism between the same two composite functors obtained from the uniqueness of right
derived functors.  It is **proved equal to the canonical map of [Stacks, Tag 0G78]** by
`Stacks.Cohomology.SupportedComplexes`
`.supportedPullbackNatTrans_eq_derivedSupportedSectionsOnClosedPullbackNatIso`, and as
isomorphisms of functors by
`…asIso_supportedPullbackNatTrans_eq_derivedSupportedSectionsOnClosedPullbackNatIso`
(`StacksFrontier/AlgebraicGeometry/Perfect/SupportClosedSubset/SupportedPullbackComparison.lean`).
This file is nevertheless written with the canonical map, because the counit compatibility is
read off the commutative triangle of [Stacks, Tag 0G78] directly; with the identification in
hand either description may now be used.

**Naturality of the canonical map of [Stacks, Tag 0G78].**  The library builds that map object
by object, as the adjoint transpose of a displayed composite.  Here the composite is assembled
as a natural transformation out of its four factors and then transposed along the adjunction of
[Stacks, Tag 0A3B] once and for all, by `transposeNatTrans`; `supportedPullbackNatTrans_app`
says the components are the library's map, so the naturality is new information about it.

**Two declarations are stated at variable categories on purpose.**  `transposeNatTrans` and
`map_comp_cancel` are formal and could be inlined, but assembling their proofs at the derived
categories of sheaves of modules exceeds the default heartbeat limit, and raising it with
`set_option` is not permitted.  For the same reason the counit compatibility is proved after a
`show` that spells the excision isomorphism's component out: the two spellings of the composite
functor are definitionally equal but not interchangeable under the transparency at which `simp`
and `rw` re-typecheck their goals.

**Carried hypotheses.**  Everything carries `hZ : IsClosed Z` (needed to write `R𝓗_Z` down at
all) and `SheafedSpace.IsOpenImmersion f`; `IsClosed Z'` is *not* a hypothesis, being
`Stacks.Cohomology.SupportedComplexes.isClosed_closedSubsetPreimage`.  There is **no
quasi-coherence hypothesis** and no hypothesis on the coefficient sheaf anywhere, except that
`Stacks.Perfect.SupportedFraction.cechToDerivedSupport` itself asks for `F.IsQuasicoherent`, so
the last theorem inherits it.  No retrocompactness of the open complement appears.

**What is NOT here.**  Nothing identifies the excision isomorphism with the *abelian* excision
`Stacks.Perfect.LocalCohomologyExcision.localCohomologyRestrictNatIso` through
`Stacks.Perfect.GysinAbelianSquare.supportCohomologySheafFunctorLocalCohomologyIso`; that
coherence between two independently constructed isomorphisms is **not** what the Gysin
globalisation of [Stacks, Tag 0G86] needs, and was never on its critical path once
`Stacks.Gysin.gysinTarget` was respelled as the degree-`c` cohomology sheaf of
`i_* R𝓗_Z(ℱ[0])`: the chart transport of that globalisation *is* `supportPushPullbackIso` with
`DerivedCategory.homologyFunctor _ c` applied to it, namely
`Stacks.Gysin.supportCohomologyRestrictIso`, so the two sides of the match are one isomorphism
and no identification with the abelian excision arises.  Nor is a transitivity statement for two
nested opens missing: `Stacks.Gysin.derivedSupportedPushforwardPullbackIso_comp` of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinTargetExcisionComp.lean` is the compatibility of
this file's excision with a composite of two open immersions, and
`Stacks.Gysin.supportCohomologyPullbackIso_comp` is that compatibility in degree `n`.
Nothing here is a statement about the degree-`c` cohomology sheaf of the comparison, so nothing
here is a locality statement for
`Stacks.Perfect.SupportedFraction.cokernelLastDifToSupport` or for the classes of
[Stacks, Tag 0G7Q].  Nothing is claimed for a morphism of ringed spaces that is not an open
immersion.

**No declaration here carries a `@[stacks ...]` attribute**: every statement is a transport of
one that does.

## References

* [Stacks Project, Remark 20.34.12 (Tag 0G78)](https://stacks.math.columbia.edu/tag/0G78)
* [Stacks Project, Lemma 20.34.1 (Tag 0A3B)](https://stacks.math.columbia.edu/tag/0A3B)
* [Stacks Project, Lemma 20.34.6 (Tag 0G72)](https://stacks.math.columbia.edu/tag/0G72)
* [Stacks Project, Remark 36.6.6 (Tag 0G7L)](https://stacks.math.columbia.edu/tag/0G7L)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
-/
@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.SupportedComplexes
open Stacks.SheafOfModules.SupportedSections
open Stacks.Perfect.SupportCounitComparison
  (derivedSupportedSectionsToId_eq_derivedPushforwardAdjunction_counit)
open Stacks.Perfect.SupportedQuasicoherent (derivedSupportedPushforward
  derivedSupportedPushforwardUnit)

universe u

namespace Stacks.Perfect.SupportPushExcision

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Transposing a natural transformation along an adjunction -/

/-- The transpose of a natural transformation `S ⋙ P ⟶ T` along an adjunction `P ⊣ R`, as a
natural transformation `S ⟶ T ⋙ R`: at each object it is the adjoint transpose, and naturality
is the naturality of the unit together with that of the given transformation.

Stated at variable categories on purpose: the instances it is used at below are large enough
that assembling the naturality proof there exceeds the default heartbeat limit. -/
def transposeNatTrans {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {P : D ⥤ C} {R : C ⥤ D} (adj : P ⊣ R) {S : E ⥤ D} {T : E ⥤ C} (mu : S ⋙ P ⟶ T) :
    S ⟶ T ⋙ R where
  app K := adj.unit.app (S.obj K) ≫ R.map (mu.app K)
  naturality K K' k := by
    have hu := adj.unit.naturality (S.map k)
    have hm := mu.naturality k
    dsimp only [Functor.comp_map, Functor.id_map] at hu hm ⊢
    rw [← Category.assoc, hu, Category.assoc, Category.assoc, ← R.map_comp, ← R.map_comp, hm]

/-- The components of `transposeNatTrans` are the adjoint transposes. -/
theorem transposeNatTrans_app {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {P : D ⥤ C} {R : C ⥤ D} (adj : P ⊣ R) {S : E ⥤ D} {T : E ⥤ C} (mu : S ⋙ P ⟶ T) (K : E) :
    (transposeNatTrans adj mu).app K = adj.homEquiv (S.obj K) (T.obj K) (mu.app K) := rfl

/-- Cancelling a pair of mutually inverse maps under a functor.  Stated at variable categories
because the instance it is used at below is large enough that the rewriting exceeds the default
heartbeat limit. -/
theorem map_comp_cancel {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) {A B E : C}
    (a : A ⟶ B) (b : B ⟶ A) (hab : a ≫ b = 𝟙 A) (g : A ⟶ E) :
    F.map a ≫ F.map b ≫ F.map g = F.map g := by
  rw [← F.map_comp_assoc, hab, F.map_id, Category.id_comp]

section RingedSpaces

variable {X' X : RingedSpace.{u, u}} (f : X' ⟶ X) [SheafedSpace.IsOpenImmersion f]
  (Z : Set X.carrier)

/-! ### The base-change transformation of Tag 08HY as a natural isomorphism -/

/-- **The base-change transformation of [Stacks, Tag 08HY] for the square of the restriction,
as a natural isomorphism** `Ri_* ⋙ Lf^* ≅ L(f|_{Z'})^* ⋙ Ri'_*`, for `f` an open immersion.

The components are `Stacks.Cohomology.SupportedComplexes.supportedPullbackBaseChangeMap`,
invertible by
`Stacks.Cohomology.SupportedComplexes.isIso_supportedPullbackBaseChangeMap_of_isOpenImmersion`,
and the naturality is that of
`Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeNatTrans`. -/
def supportedPullbackBaseChangeNatIso :
    derivedPushforward (closedSubsetInclusion X Z) ⋙ derivedPullback f ≅
      derivedPullback (closedSubsetRestriction f Z) ⋙
        derivedPushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z)) :=
  NatIso.ofComponents
    (fun M => @asIso _ _ _ _ _ (isIso_supportedPullbackBaseChangeMap_of_isOpenImmersion f Z M))
    (fun g => (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeNatTrans
      (closedSubsetRestriction f Z) (closedSubsetInclusion X' (closedSubsetPreimage f Z))
      (closedSubsetInclusion X Z) f
      (closedSubsetRestriction_comp_closedSubsetInclusion f Z)).naturality g)

/-- The components of the base-change natural isomorphism are the base-change maps. -/
theorem supportedPullbackBaseChangeNatIso_hom_app
    (M : DerivedCategory (SheafOfModules.{u}
      (structureSheafRing (closedSubsetRingedSpace X Z)))) :
    (supportedPullbackBaseChangeNatIso f Z).hom.app M = supportedPullbackBaseChangeMap f Z M :=
  rfl

variable (hZ : IsClosed Z)

/-! ### The canonical map of Tag 0G78 as a natural transformation -/

/-- The composite `i'_* L(f|_{Z'})^* R𝓗_Z ⟶ Lf^*` of
`Stacks.Cohomology.SupportedComplexes.supportedPullbackMateMap`, read as a natural
transformation: every factor of that composite is the component of one. -/
def supportedPullbackMateNatTrans :
    letI := pushforward_preservesFiniteLimits X Z
    letI := pushforward_preservesFiniteColimits X Z hZ
    letI := pushforward_preservesFiniteLimits X' (closedSubsetPreimage f Z)
    letI := pushforward_preservesFiniteColimits X' (closedSubsetPreimage f Z)
      (isClosed_closedSubsetPreimage f Z hZ)
    derivedSupportedSectionsOnClosed X Z hZ ⋙
        derivedPullback (closedSubsetRestriction f Z) ⋙
        (modulePushforward
          (closedSubsetInclusion X' (closedSubsetPreimage f Z))).mapDerivedCategory ⟶
      derivedPullback f :=
  letI := pushforward_preservesFiniteLimits X Z
  letI := pushforward_preservesFiniteColimits X Z hZ
  letI := pushforward_preservesFiniteLimits X' (closedSubsetPreimage f Z)
  letI := pushforward_preservesFiniteColimits X' (closedSubsetPreimage f Z)
    (isClosed_closedSubsetPreimage f Z hZ)
  Functor.whiskerLeft (derivedSupportedSectionsOnClosed X Z hZ ⋙
      derivedPullback (closedSubsetRestriction f Z))
      (closedPushforwardComparison X' (closedSubsetPreimage f Z)).hom ≫
    Functor.whiskerLeft (derivedSupportedSectionsOnClosed X Z hZ)
      (supportedPullbackBaseChangeNatIso f Z).inv ≫
    Functor.whiskerLeft (derivedSupportedSectionsOnClosed X Z hZ)
      (Functor.whiskerRight (closedPushforwardComparison X Z).inv (derivedPullback f)) ≫
    Functor.whiskerRight (derivedPushforwardAdjunction X Z hZ).counit (derivedPullback f)

/-- The components of `supportedPullbackMateNatTrans` are the displayed composites of
[Stacks, Tag 0G78]. -/
theorem supportedPullbackMateNatTrans_app
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    letI := pushforward_preservesFiniteLimits X Z
    letI := pushforward_preservesFiniteColimits X Z hZ
    letI := pushforward_preservesFiniteLimits X' (closedSubsetPreimage f Z)
    letI := pushforward_preservesFiniteColimits X' (closedSubsetPreimage f Z)
      (isClosed_closedSubsetPreimage f Z hZ)
    (supportedPullbackMateNatTrans f Z hZ).app K =
      supportedPullbackMateMap f Z hZ K := by
  let := pushforward_preservesFiniteLimits X Z
  let := pushforward_preservesFiniteColimits X Z hZ
  let := pushforward_preservesFiniteLimits X' (closedSubsetPreimage f Z)
  let := pushforward_preservesFiniteColimits X' (closedSubsetPreimage f Z)
    (isClosed_closedSubsetPreimage f Z hZ)
  exact rfl

/-- **The canonical map of [Stacks, Tag 0G78] as a natural transformation**
`R𝓗_Z ⋙ L(f|_{Z'})^* ⟶ Lf^* ⋙ R𝓗_{Z'}`, for `f` an open immersion.

Its components are
`Stacks.Cohomology.SupportedComplexes.supportedPullbackMap`; the naturality comes from that of
the displayed composite, transposed along the adjunction of [Stacks, Tag 0A3B] part (1). -/
def supportedPullbackNatTrans :
    derivedSupportedSectionsOnClosed X Z hZ ⋙
        derivedPullback (closedSubsetRestriction f Z) ⟶
      derivedPullback f ⋙
        derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z)
          (isClosed_closedSubsetPreimage f Z hZ) :=
  letI := pushforward_preservesFiniteLimits X Z
  letI := pushforward_preservesFiniteColimits X Z hZ
  letI := pushforward_preservesFiniteLimits X' (closedSubsetPreimage f Z)
  letI := pushforward_preservesFiniteColimits X' (closedSubsetPreimage f Z)
    (isClosed_closedSubsetPreimage f Z hZ)
  transposeNatTrans (derivedPushforwardAdjunction X' (closedSubsetPreimage f Z)
    (isClosed_closedSubsetPreimage f Z hZ)) (supportedPullbackMateNatTrans f Z hZ)

/-- The components of `supportedPullbackNatTrans` are the canonical maps of
[Stacks, Tag 0G78]. -/
theorem supportedPullbackNatTrans_app
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    letI := pushforward_preservesFiniteLimits X Z
    letI := pushforward_preservesFiniteColimits X Z hZ
    letI := pushforward_preservesFiniteLimits X' (closedSubsetPreimage f Z)
    letI := pushforward_preservesFiniteColimits X' (closedSubsetPreimage f Z)
      (isClosed_closedSubsetPreimage f Z hZ)
    (supportedPullbackNatTrans f Z hZ).app K =
      supportedPullbackMap f Z hZ (isClosed_closedSubsetPreimage f Z hZ) K := by
  let := pushforward_preservesFiniteLimits X Z
  let := pushforward_preservesFiniteColimits X Z hZ
  let := pushforward_preservesFiniteLimits X' (closedSubsetPreimage f Z)
  let := pushforward_preservesFiniteColimits X' (closedSubsetPreimage f Z)
    (isClosed_closedSubsetPreimage f Z hZ)
  exact rfl

/-- **The canonical map of [Stacks, Tag 0G78] is a natural isomorphism along an open
immersion.**  Invertibility at each object is
`Stacks.Cohomology.SupportedComplexes.isIso_supportedPullbackMap_of_isOpenImmersion`. -/
instance isIso_supportedPullbackNatTrans : IsIso (supportedPullbackNatTrans f Z hZ) := by
  let := pushforward_preservesFiniteLimits X Z
  let := pushforward_preservesFiniteColimits X Z hZ
  let := pushforward_preservesFiniteLimits X' (closedSubsetPreimage f Z)
  let := pushforward_preservesFiniteColimits X' (closedSubsetPreimage f Z)
    (isClosed_closedSubsetPreimage f Z hZ)
  have : ∀ K, IsIso ((supportedPullbackNatTrans f Z hZ).app K) := by
    intro K
    rw [supportedPullbackNatTrans_app]
    exact isIso_supportedPullbackMap_of_isOpenImmersion f Z hZ
      (isClosed_closedSubsetPreimage f Z hZ) K
  exact NatIso.isIso_of_isIso_app _

/-! ### Excision for `i_* R𝓗_Z` -/

/-- **Excision for `i_* R𝓗_Z` along an open immersion of ringed spaces.**  For an open immersion
`f : X' ⟶ X`, a closed `Z ⊆ X` and `Z' = f^{-1}(Z)`,

`i_* R𝓗_Z ⋙ Lf^* ≅ Lf^* ⋙ i'_* R𝓗_{Z'}`.

The chain is: the comparison of the exact direct image passes to `Ri_*`; the base-change
isomorphism of [Stacks, Tag 08HY] for the Cartesian square of the restriction moves `Lf^*`
across `Ri_*`; the comparison of the exact direct image comes back on `X'`; and the canonical
map of [Stacks, Tag 0G78], invertible by `isIso_supportedPullbackNatTrans`, is applied under
`i'_*`.

The order of the last two factors is the order of the commutative triangle
`Stacks.Cohomology.SupportedComplexes.supportedPullbackMap_triangle`, which is what
`derivedSupportedPushforwardPullbackIso_hom_comp_counit` consumes. -/
def derivedSupportedPushforwardPullbackIso :
    derivedSupportedPushforward X Z hZ ⋙ derivedPullback f ≅
      derivedPullback f ⋙ derivedSupportedPushforward X' (closedSubsetPreimage f Z)
        (isClosed_closedSubsetPreimage f Z hZ) :=
  letI := pushforward_preservesFiniteLimits X Z
  letI := pushforward_preservesFiniteColimits X Z hZ
  letI := pushforward_preservesFiniteLimits X' (closedSubsetPreimage f Z)
  letI := pushforward_preservesFiniteColimits X' (closedSubsetPreimage f Z)
    (isClosed_closedSubsetPreimage f Z hZ)
  Functor.isoWhiskerLeft (derivedSupportedSectionsOnClosed X Z hZ)
      (Functor.isoWhiskerRight (closedPushforwardComparison X Z) (derivedPullback f)) ≪≫
    Functor.isoWhiskerLeft (derivedSupportedSectionsOnClosed X Z hZ)
      (supportedPullbackBaseChangeNatIso f Z) ≪≫
    Functor.isoWhiskerLeft (derivedSupportedSectionsOnClosed X Z hZ ⋙
        derivedPullback (closedSubsetRestriction f Z))
      (closedPushforwardComparison X' (closedSubsetPreimage f Z)).symm ≪≫
    Functor.isoWhiskerRight (asIso (supportedPullbackNatTrans f Z hZ))
      (modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z))).mapDerivedCategory

/-- The components of the excision isomorphism, factor by factor. -/
theorem derivedSupportedPushforwardPullbackIso_hom_app
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    letI := pushforward_preservesFiniteLimits X Z
    letI := pushforward_preservesFiniteColimits X Z hZ
    letI := pushforward_preservesFiniteLimits X' (closedSubsetPreimage f Z)
    letI := pushforward_preservesFiniteColimits X' (closedSubsetPreimage f Z)
      (isClosed_closedSubsetPreimage f Z hZ)
    (derivedSupportedPushforwardPullbackIso f Z hZ).hom.app K =
      (derivedPullback f).map ((closedPushforwardComparison X Z).hom.app
          ((derivedSupportedSectionsOnClosed X Z hZ).obj K)) ≫
        supportedPullbackBaseChangeMap f Z ((derivedSupportedSectionsOnClosed X Z hZ).obj K) ≫
        (closedPushforwardComparison X' (closedSubsetPreimage f Z)).inv.app
            ((derivedPullback (closedSubsetRestriction f Z)).obj
              ((derivedSupportedSectionsOnClosed X Z hZ).obj K)) ≫
          (modulePushforward
                (closedSubsetInclusion X' (closedSubsetPreimage f Z))).mapDerivedCategory.map
            ((supportedPullbackNatTrans f Z hZ).app K) := by
  let := pushforward_preservesFiniteLimits X Z
  let := pushforward_preservesFiniteColimits X Z hZ
  let := pushforward_preservesFiniteLimits X' (closedSubsetPreimage f Z)
  let := pushforward_preservesFiniteColimits X' (closedSubsetPreimage f Z)
    (isClosed_closedSubsetPreimage f Z hZ)
  exact rfl

/-- **The excision isomorphism carries the counit of [Stacks, Tag 0A3B] to the counit.**  For
every `K` in `D(𝒪_X)`,

`Θ_K ≫ (i'_* R𝓗_{Z'}(Lf^* K) ⟶ Lf^* K) = Lf^*(i_* R𝓗_Z(K) ⟶ K)`,

with `Θ` the isomorphism of `derivedSupportedPushforwardPullbackIso`.  This is the commutative
triangle `Stacks.Cohomology.SupportedComplexes.supportedPullbackMap_triangle` of
[Stacks, Tag 0G78], with the comparison of the exact direct image cancelled on the left. -/
theorem derivedSupportedPushforwardPullbackIso_hom_comp_counit
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    letI := pushforward_preservesFiniteLimits X Z
    letI := pushforward_preservesFiniteColimits X Z hZ
    letI := pushforward_preservesFiniteLimits X' (closedSubsetPreimage f Z)
    letI := pushforward_preservesFiniteColimits X' (closedSubsetPreimage f Z)
      (isClosed_closedSubsetPreimage f Z hZ)
    (derivedSupportedPushforwardPullbackIso f Z hZ).hom.app K ≫
        (derivedPushforwardAdjunction X' (closedSubsetPreimage f Z)
          (isClosed_closedSubsetPreimage f Z hZ)).counit.app ((derivedPullback f).obj K) =
      (derivedPullback f).map ((derivedPushforwardAdjunction X Z hZ).counit.app K) := by
  let := pushforward_preservesFiniteLimits X Z
  let := pushforward_preservesFiniteColimits X Z hZ
  let := pushforward_preservesFiniteLimits X' (closedSubsetPreimage f Z)
  let := pushforward_preservesFiniteColimits X' (closedSubsetPreimage f Z)
    (isClosed_closedSubsetPreimage f Z hZ)
  have htri := supportedPullbackMap_triangle f Z hZ
    (isClosed_closedSubsetPreimage f Z hZ) K
  rw [← supportedPullbackNatTrans_app] at htri
  change ((derivedPullback f).map ((closedPushforwardComparison X Z).hom.app
            ((derivedSupportedSectionsOnClosed X Z hZ).obj K)) ≫
          supportedPullbackBaseChangeMap f Z ((derivedSupportedSectionsOnClosed X Z hZ).obj K) ≫
          (closedPushforwardComparison X' (closedSubsetPreimage f Z)).inv.app
              ((derivedPullback (closedSubsetRestriction f Z)).obj
                ((derivedSupportedSectionsOnClosed X Z hZ).obj K)) ≫
            (modulePushforward
                  (closedSubsetInclusion X' (closedSubsetPreimage f Z))).mapDerivedCategory.map
              ((supportedPullbackNatTrans f Z hZ).app K)) ≫
        (derivedPushforwardAdjunction X' (closedSubsetPreimage f Z)
          (isClosed_closedSubsetPreimage f Z hZ)).counit.app ((derivedPullback f).obj K) =
      (derivedPullback f).map ((derivedPushforwardAdjunction X Z hZ).counit.app K)
  rw [Category.assoc, Category.assoc, Category.assoc, htri]
  exact map_comp_cancel (derivedPullback f) _ _
    ((closedPushforwardComparison X Z).hom_inv_id_app _) _

/-- **The excision isomorphism carries the canonical map of [Stacks, Tag 0G72] to itself.**  The
same statement as `derivedSupportedPushforwardPullbackIso_hom_comp_counit`, with the counit
spelled as the derived-functor transition
`Stacks.Cohomology.SupportedComplexes.derivedSupportedSectionsToId` at the chosen derived
functor — the spelling that `Stacks.Perfect.SupportedFraction.supportPushCounit` abbreviates.

The two spellings are the same map by
`Stacks.Perfect.SupportCounitComparison`'s
`derivedSupportedSectionsToId_eq_derivedPushforwardAdjunction_counit`. -/
theorem derivedSupportedPushforwardPullbackIso_hom_comp_derivedSupportedSectionsToId
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    letI := pushforward_preservesFiniteLimits X Z
    letI := pushforward_preservesFiniteColimits X Z hZ
    letI := pushforward_preservesFiniteLimits X' (closedSubsetPreimage f Z)
    letI := pushforward_preservesFiniteColimits X' (closedSubsetPreimage f Z)
      (isClosed_closedSubsetPreimage f Z hZ)
    (derivedSupportedPushforwardPullbackIso f Z hZ).hom.app K ≫
        (derivedSupportedSectionsToId X' (closedSubsetPreimage f Z)
            (derivedSupportedPushforward X' (closedSubsetPreimage f Z)
              (isClosed_closedSubsetPreimage f Z hZ))
            (derivedSupportedPushforwardUnit X' (closedSubsetPreimage f Z)
              (isClosed_closedSubsetPreimage f Z hZ))).app ((derivedPullback f).obj K) =
      (derivedPullback f).map ((derivedSupportedSectionsToId X Z
        (derivedSupportedPushforward X Z hZ) (derivedSupportedPushforwardUnit X Z hZ)).app K) := by
  let := pushforward_preservesFiniteLimits X Z
  let := pushforward_preservesFiniteColimits X Z hZ
  let := pushforward_preservesFiniteLimits X' (closedSubsetPreimage f Z)
  let := pushforward_preservesFiniteColimits X' (closedSubsetPreimage f Z)
    (isClosed_closedSubsetPreimage f Z hZ)
  rw [derivedSupportedSectionsToId_eq_derivedPushforwardAdjunction_counit X Z hZ,
    derivedSupportedSectionsToId_eq_derivedPushforwardAdjunction_counit X'
      (closedSubsetPreimage f Z) (isClosed_closedSubsetPreimage f Z hZ)]
  exact derivedSupportedPushforwardPullbackIso_hom_comp_counit f Z hZ K

/-- **The comparison of [Stacks, Tag 0G7L] is carried along the excision isomorphism.**  Let
`v : A ⟶ i_* R𝓗_Z(K)` be a map whose composite with the canonical map
`i_* R𝓗_Z(A) ⟶ A` of [Stacks, Tag 0G72] is `i_* R𝓗_Z` applied to some `u : A ⟶ K` — the
commuting triangle that characterises the comparison of [Stacks, Tag 0G7L].  Then
`Lf^*(v)` followed by the excision isomorphism satisfies the same triangle on `X'`, for
`Lf^*(u)`.

So the transport carries both the counit of [Stacks, Tag 0G72] and the augmentation: the
characterisation of the comparison is preserved, with the augmentation `u` replaced by its
derived pullback. -/
theorem derivedSupportedSectionsToId_comp_map_comp_pullbackIso_hom
    (A K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (v : A ⟶ (derivedSupportedPushforward X Z hZ).obj K) (u : A ⟶ K)
    (hv : (derivedSupportedSectionsToId X Z (derivedSupportedPushforward X Z hZ)
          (derivedSupportedPushforwardUnit X Z hZ)).app A ≫ v =
        (derivedSupportedPushforward X Z hZ).map u) :
    letI := pushforward_preservesFiniteLimits X Z
    letI := pushforward_preservesFiniteColimits X Z hZ
    letI := pushforward_preservesFiniteLimits X' (closedSubsetPreimage f Z)
    letI := pushforward_preservesFiniteColimits X' (closedSubsetPreimage f Z)
      (isClosed_closedSubsetPreimage f Z hZ)
    (derivedSupportedSectionsToId X' (closedSubsetPreimage f Z)
            (derivedSupportedPushforward X' (closedSubsetPreimage f Z)
              (isClosed_closedSubsetPreimage f Z hZ))
            (derivedSupportedPushforwardUnit X' (closedSubsetPreimage f Z)
              (isClosed_closedSubsetPreimage f Z hZ))).app ((derivedPullback f).obj A) ≫
        (derivedPullback f).map v ≫
          (derivedSupportedPushforwardPullbackIso f Z hZ).hom.app K =
      (derivedSupportedPushforward X' (closedSubsetPreimage f Z)
        (isClosed_closedSubsetPreimage f Z hZ)).map ((derivedPullback f).map u) := by
  let := pushforward_preservesFiniteLimits X Z
  let := pushforward_preservesFiniteColimits X Z hZ
  let := pushforward_preservesFiniteLimits X' (closedSubsetPreimage f Z)
  let := pushforward_preservesFiniteColimits X' (closedSubsetPreimage f Z)
    (isClosed_closedSubsetPreimage f Z hZ)
  rw [← cancel_epi ((derivedSupportedPushforwardPullbackIso f Z hZ).hom.app A),
    ← Category.assoc,
    derivedSupportedPushforwardPullbackIso_hom_comp_derivedSupportedSectionsToId f Z hZ A,
    ← Functor.map_comp_assoc, hv]
  exact (derivedSupportedPushforwardPullbackIso f Z hZ).hom.naturality u

end RingedSpaces

/-! ### The same, at the `supportPush` spelling of a scheme -/

section Schemes

variable {Y : Scheme.{u}} {X' : RingedSpace.{u, u}} (f : X' ⟶ Y.toRingedSpace)
  [SheafedSpace.IsOpenImmersion f] {T : Set Y} (hT : IsClosed T)

/-- **Excision for `i_* R𝓗_T` at the `supportPush` spelling.**  This is
`derivedSupportedPushforwardPullbackIso` read at `Stacks.Perfect.SupportedFraction.supportPush`,
the spelling in which the comparison of [Stacks, Tag 0G7L] and the Čech classes of
[Stacks, Tag 0G7Q] are written. -/
def supportPushPullbackIso :
    Stacks.Perfect.SupportedFraction.supportPush hT ⋙ derivedPullback f ≅
      derivedPullback f ⋙ derivedSupportedPushforward X' (closedSubsetPreimage f T)
        (isClosed_closedSubsetPreimage f T hT) :=
  derivedSupportedPushforwardPullbackIso f T hT

/-- **The excision isomorphism carries `supportPushCounit` to the counit on `X'`.**  This is
`derivedSupportedPushforwardPullbackIso_hom_comp_derivedSupportedSectionsToId` read at the
`supportPush` spelling. -/
theorem supportPushPullbackIso_hom_comp_supportPushCounit
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))) :
    (supportPushPullbackIso f hT).hom.app K ≫
        (derivedSupportedSectionsToId X' (closedSubsetPreimage f T)
            (derivedSupportedPushforward X' (closedSubsetPreimage f T)
              (isClosed_closedSubsetPreimage f T hT))
            (derivedSupportedPushforwardUnit X' (closedSubsetPreimage f T)
              (isClosed_closedSubsetPreimage f T hT))).app ((derivedPullback f).obj K) =
      (derivedPullback f).map
        ((Stacks.Perfect.SupportedFraction.supportPushCounit hT).app K) :=
  derivedSupportedPushforwardPullbackIso_hom_comp_derivedSupportedSectionsToId f T hT K

/-- **The comparison of [Stacks, Tag 0G7L] for the extended alternating Čech complex, carried
along the excision isomorphism.**  The derived pullback of
`Stacks.Perfect.SupportedFraction.cechToDerivedSupport`, followed by the excision isomorphism,
satisfies on `X'` the triangle of [Stacks, Tag 0G7L] for the derived pullback of the
augmentation: preceded by the canonical map of [Stacks, Tag 0G72] it is `i'_* R𝓗_{T'}` applied
to `Lf^*` of the augmentation.

This is `derivedSupportedSectionsToId_comp_map_comp_pullbackIso_hom` applied to the triangle
`Stacks.Perfect.SupportedFraction.derivedSupportedSectionsToId_comp_cechToDerivedSupport`; it is
the statement in which the counit of [Stacks, Tag 0G72] and the augmentation of
[Stacks, Tag 0G7L] are both carried across the transport. -/
theorem derivedSupportedSectionsToId_comp_map_cechToDerivedSupport_comp_pullbackIso_hom
    {m : ℕ} (e : Fin m → Γ(Y, ⊤)) (F : Y.Modules) [F.IsQuasicoherent]
    (hTe : Stacks.Perfect.CechDerivedSupport.equationsClosedSet e ⊆ T) :
    (derivedSupportedSectionsToId X' (closedSubsetPreimage f T)
            (derivedSupportedPushforward X' (closedSubsetPreimage f T)
              (isClosed_closedSubsetPreimage f T hT))
            (derivedSupportedPushforwardUnit X' (closedSubsetPreimage f T)
              (isClosed_closedSubsetPreimage f T hT))).app
          ((derivedPullback f).obj (DerivedCategory.Q.obj
            ((Stacks.Perfect.ExtendedAlternatingCech.extendedAlternatingCech e F).complex.extend
              ComplexShape.embeddingUpNat))) ≫
        (derivedPullback f).map
            (Stacks.Perfect.SupportedFraction.cechToDerivedSupport e F hT hTe) ≫
          (supportPushPullbackIso f hT).hom.app
            ((DerivedCategory.singleFunctor Y.Modules 0).obj F) =
      (derivedSupportedPushforward X' (closedSubsetPreimage f T)
          (isClosed_closedSubsetPreimage f T hT)).map
        ((derivedPullback f).map
          (Stacks.Perfect.ExtendedAlternatingCech.Augmentation.augmentation e F)) :=
  derivedSupportedSectionsToId_comp_map_comp_pullbackIso_hom f T hT _ _ _ _
    (Stacks.Perfect.SupportedFraction.derivedSupportedSectionsToId_comp_cechToDerivedSupport
      e F hT hTe)

end Schemes

end Stacks.Perfect.SupportPushExcision

end
