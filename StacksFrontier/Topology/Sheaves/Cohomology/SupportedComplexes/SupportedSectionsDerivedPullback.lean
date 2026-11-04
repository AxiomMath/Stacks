module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangeMap
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaClosedEmbeddingUnconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ClosedSubsetPullbackLeftExact
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportedSectionsCanonicalMaps
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportedSectionsDerivedTensor
import StacksCore.Tactic.StacksAttribute

/-!
# The canonical map `L(f|_{Z'})^* R𝓗_Z(K) ⟶ R𝓗_{Z'}(Lf^* K)`

Let `f : (X', 𝒪_{X'}) ⟶ (X, 𝒪_X)` be a morphism of ringed spaces, let `Z ⊆ X` be a closed
subset and let `Z' = f^{-1}(Z)`, a closed subset of `X'`. Restricting the structure sheaves
makes `Z` and `Z'` into ringed spaces, and `f` restricts to a morphism
`f|_{Z'} : (Z', 𝒪_{X'}|_{Z'}) ⟶ (Z, 𝒪_X|_Z)` fitting in the commutative square

```
(Z', 𝒪_{X'}|_{Z'}) --i'--> (X', 𝒪_{X'})
      |                          |
   f|_{Z'}                       f
      v                          v
(Z, 𝒪_X|_Z)  ------i----> (X, 𝒪_X)
```

For `K` in `D(𝒪_X)` there is a canonical map

`L(f|_{Z'})^* R𝓗_Z(K) ⟶ R𝓗_{Z'}(Lf^* K)`

in `D(𝒪_{X'}|_{Z'})`. By the adjunction `i'_* ⊣ R𝓗_{Z'}` of [Stacks, Tag 0A3B] part (1), giving
such a map is the same as giving a map `i'_*L(f|_{Z'})^* R𝓗_Z(K) ⟶ Lf^* K`, and that map is the
inverse of the base-change transformation of [Stacks, Tag 08HY] followed by the derived pullback
along `f` of the adjunction map `i_* R𝓗_Z(K) ⟶ K`.

## Main definitions

* `inverseImageRingedSpaceLift`: the universal property of an inverse-image ringed space —
  a morphism to `(T, j^{-1}𝒪_S)` over a continuous map `k` is a morphism to `(S, 𝒪_S)` over
  `k ≫ j`.
* `closedSubsetPreimage`: the closed subset `Z' = f^{-1}(Z)` of `X'`.
* `closedSubsetRestriction`: the induced morphism of ringed spaces `f|_{Z'}`.
* `supportedPullbackMateMap`: the composite `i'_*L(f|_{Z'})^* R𝓗_Z(K) ⟶ Lf^* K` that the
  canonical map is adjoint to.
* `supportedPullbackMap`: the canonical map of [Stacks, Tag 0G78] itself.

## Main results

* `closedSubsetRestriction_comp_closedSubsetInclusion`: the square above commutes, which is what
  the base-change transformation of [Stacks, Tag 08HY] is attached to.
* `supportedPullbackMap_mate` is the adjunction equation characterizing the canonical map, and
  `supportedPullbackMap_unique` says that the equation determines it, so nothing else — in
  particular neither the zero map nor the negative of the canonical map — inhabits the type and
  satisfies the characterization.
* `cohomologySupportedOn_derivedPullback`: **derived pullback preserves cohomological support**,
  for an arbitrary morphism of ringed spaces and an arbitrary subset.
* `isIso_supportedPullbackBaseChangeMap`: **the source's own assertion that the map of functors
  `Lf^* ∘ i_* ⟶ i'_* ∘ L(f|_{Z'})^*` of [Stacks, Tag 08HY] is an isomorphism in this case** —
  invertible for every object of `D(𝒪_X|_Z)`, not merely at `R𝓗_Z(K)`. This is what makes the
  canonical map unconditional.
* `isZero_derivedPullback_closedSubsetInclusion_of_supported` and
  `cohomologySupportedOn_compl_of_isZero_derivedPullback`: restriction to a subset `W` of a
  ringed space detects cohomological support off `W`, in both directions.

## Implementation notes

**The restricted morphism.** The ringed space on a closed subset is
`Stacks.Cohomology.SupportedComplexes.closedSubsetRingedSpace`, an inverse-image ringed space
`(Z, i^{-1}𝒪_X)`, and such a space has a universal property: because pushforward of sheaves on
spaces is *strictly* functorial, `j_*(k_*ℱ) = (k ≫ j)_*ℱ` on the nose, a structure-sheaf datum
`j^{-1}𝒪_S ⟶ k_*𝒪_Y` is by the inverse-image/direct-image adjunction the same thing as a datum
`𝒪_S ⟶ (k ≫ j)_*𝒪_Y`, that is, a morphism of ringed spaces `Y ⟶ S` over `k ≫ j`. That is
`inverseImageRingedSpaceLift`, and `f|_{Z'}` is the lift of `i' ≫ f` along the restriction of
the continuous map of `f` to `Z' → Z`; the commutativity of the square is the lift property,
with no transport, the two composites `Z' → X` being equal by definition.

**The isomorphism the source asserts, and how it is proved here.** The construction needs the
base-change
transformation `Lf^*(Ri_*M) ⟶ Ri'_*(L(f|_{Z'})^*M)` of [Stacks, Tag 08HY] to be invertible,
which the source checks on stalks using that `i_*` and `i'_*` are exact and that
`𝒪_{Z,z} = 𝒪_{X,z}`. That is `isIso_supportedPullbackBaseChangeMap`, proved here for **every**
`M` in `D(𝒪_X|_Z)` and not merely at `M = R𝓗_Z(K)`, so nothing about `R𝓗_Z` enters it.

The source's stalkwise check is not run, because a description of the derived stalks of `Lf^*`
at a ringed space would be needed and `derivedPullbackStalkIso` is available only for a
morphism of schemes. What replaces it is the observation that the invertibility is the
essential-image half of [Stacks, Tag 0AEF] part (2) applied twice. By the adjoint
characterization of [Stacks, Tag 08HY] the base-change map is the unit of `Li'^* ⊣ Ri'_*` at
`Lf^*(Ri_*M)` followed by `Ri'_*` of three isomorphisms — the two composition isomorphisms of
[Stacks, Tag 0D5S] and the derived counit `Li^*(Ri_*M) ⟶ M`, invertible because `Ri_*` is fully
faithful for a closed-subset inclusion. A unit of an adjunction with fully faithful right
adjoint is invertible exactly on the essential image, and `Lf^*(Ri_*M)` lies there because it
has its cohomology supported on `Z'`.

**Support under derived pullback.** That last point is `cohomologySupportedOn_derivedPullback`,
the one piece of genuinely new mathematics in this file: derived pullback along an arbitrary
morphism of ringed spaces carries complexes supported on `Z` to complexes supported on
`f^{-1}(Z)`. It is proved without derived stalks, by restricting to the complementary subset.
`closedSubsetRingedSpace` and `closedSubsetRestriction` are defined for an *arbitrary* subset,
so the commuting square of `closedSubsetRestriction_comp_closedSubsetInclusion` is available at
`Z^c` as well, and the composition isomorphism of [Stacks, Tag 0D5S] identifies the restriction
of `Lf^*K` to `f^{-1}(Z^c)` with the pullback along `f|_{f^{-1}(Z^c)}` of the restriction of `K`
to `Z^c`. The latter vanishes, and `Lf^*` is exact — `derivedPullback_isTriangulated` — hence
additive, so it takes a zero object to a zero object.

That restriction to a subset detects support in both directions is
`isZero_derivedPullback_closedSubsetInclusion_of_supported` and
`cohomologySupportedOn_compl_of_isZero_derivedPullback`. Both are read off degreewise:
`i_W^*` is exact for every subset `W`, by `pullbackExact`, so it commutes with the cohomology
sheaves, and on stalks it is base change along the germ map by [Stacks, Tag 0098]. The germ maps
of `i_W` are invertible — this is exactly the source's `𝒪_{Z,z} = 𝒪_{X,z}` — which is what makes
the second direction available: base change along an invertible germ map not only preserves but
*reflects* zero objects, which is `isZero_of_isZero_stalkBaseChange`.

**The exactness binders are inhabited.** The four `PreservesFiniteLimits` and
`PreservesFiniteColimits` hypotheses on `i_*` and `i'_*` are exactness of pushforward along a
closed embedding, [Stacks, Tag 08KS]; they are instance binders only because the library states
them as theorems rather than instances, `hZ` not being an instance argument, and they are
discharged for every ringed space and every closed subset by
`Stacks.Cohomology.SupportedComplexes.pushforward_preservesFiniteLimits` and
`Stacks.Cohomology.SupportedComplexes.pushforward_preservesFiniteColimits`, the latter at `hZ`
and at `isClosed_closedSubsetPreimage`.

**Two models of pushforward from a closed subset.** The adjunction `i_* ⊣ R𝓗_Z` is stated for
the functor `(modulePushforward i).mapDerivedCategory` induced by the exact functor `i_*`, while
the base-change transformation is stated for the total right derived functor `Ri_*`. The
comparison between them is `closedPushforwardComparison`, which is [Stacks, Tag 0E2K] for a
closed-subset inclusion, and the two occurrences of it below are the only reassociations in the
composite.

## References

* [Stacks Project, Remark 20.34.12 (Tag 0G78)](https://stacks.math.columbia.edu/tag/0G78)
* [Stacks Project, Lemma 20.34.1 (Tag 0A3B)](https://stacks.math.columbia.edu/tag/0A3B)
* [Stacks Project, Lemma 20.34.2 (Tag 0AEF)](https://stacks.math.columbia.edu/tag/0AEF)
* [Stacks Project, Remark 20.28.3 (Tag 08HY)](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 0E2K](https://stacks.math.columbia.edu/tag/0E2K)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

namespace Stacks.Cohomology.SupportedComplexes

attribute [local instance] HasDerivedCategory.standard

/-! ### The universal property of an inverse-image ringed space -/

/-- **The universal property of an inverse-image ringed space.** Let `j : T ⟶ S` be a continuous
map into the space of a ringed space `S`, and let `Y` be a ringed space with a continuous map
`k : Y ⟶ T`. A structure-sheaf datum `𝒪_S ⟶ (k ≫ j)_*𝒪_Y`, that is, a morphism of ringed spaces
`Y ⟶ S` over `k ≫ j`, determines a morphism of ringed spaces `Y ⟶ (T, j^{-1}𝒪_S)` over `k`. -/
def inverseImageRingedSpaceLift (S : RingedSpace.{u, u}) {T : TopCat.{u}} (j : T ⟶ S.carrier)
    {Y : RingedSpace.{u, u}} (k : Y.carrier ⟶ T)
    (φ : S.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} j).obj
      ((TopCat.Sheaf.pushforward CommRingCat.{u} k).obj Y.sheaf)) :
    Y ⟶ AlgebraicGeometry.RingedSpace.inverseImage S j :=
  InducedCategory.homMk
    { base := k
      c := (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} j).homEquiv
        S.sheaf ((TopCat.Sheaf.pushforward CommRingCat.{u} k).obj Y.sheaf)).symm φ).hom }

/-- The lift of `inverseImageRingedSpaceLift` lies over the given continuous map. -/
@[simp]
theorem inverseImageRingedSpaceLift_base (S : RingedSpace.{u, u}) {T : TopCat.{u}}
    (j : T ⟶ S.carrier) {Y : RingedSpace.{u, u}} (k : Y.carrier ⟶ T)
    (φ : S.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} j).obj
      ((TopCat.Sheaf.pushforward CommRingCat.{u} k).obj Y.sheaf)) :
    (inverseImageRingedSpaceLift S j k φ).hom.base = k :=
  rfl

/-- Composing the lift of `inverseImageRingedSpaceLift` with the canonical morphism
`(T, j^{-1}𝒪_S) ⟶ (S, 𝒪_S)` returns the given structure-sheaf datum: the structure-sheaf
component of the composite is `φ`. -/
theorem inverseImageRingedSpaceLift_comp_c (S : RingedSpace.{u, u}) {T : TopCat.{u}}
    (j : T ⟶ S.carrier) {Y : RingedSpace.{u, u}} (k : Y.carrier ⟶ T)
    (φ : S.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} j).obj
      ((TopCat.Sheaf.pushforward CommRingCat.{u} k).obj Y.sheaf)) :
    (inverseImageRingedSpaceLift S j k φ ≫
        AlgebraicGeometry.RingedSpace.inverseImageProjection S j).hom.c = φ.hom := by
  show (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} j).unit.app
    S.sheaf).hom ≫ _) = _
  exact congrArg (fun a => a.hom)
    (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} j).homEquiv S.sheaf
      ((TopCat.Sheaf.pushforward CommRingCat.{u} k).obj Y.sheaf)).apply_symm_apply φ)

/-! ### The morphism of ringed spaces induced on the closed subsets -/

variable {X' X : RingedSpace.{u, u}} (f : X' ⟶ X) (Z : Set X.carrier)

/-- The preimage `Z' = f^{-1}(Z)` of a subset of a ringed space along a morphism of ringed
spaces. -/
def closedSubsetPreimage : Set X'.carrier :=
  ⇑f.hom.base ⁻¹' Z

/-- The preimage of a closed subset is closed. -/
theorem isClosed_closedSubsetPreimage (hZ : IsClosed Z) :
    IsClosed (closedSubsetPreimage f Z) :=
  hZ.preimage f.hom.base.hom.continuous

/-- The continuous map `Z' ⟶ Z` underlying the restriction of `f`. -/
def closedSubsetRestrictionBase : TopCat.of (closedSubsetPreimage f Z) ⟶ TopCat.of Z :=
  TopCat.ofHom ⟨fun z' => ⟨f.hom.base z'.1, z'.2⟩,
    Continuous.subtype_mk (f.hom.base.hom.continuous.comp continuous_subtype_val) _⟩

/-- The structure-sheaf datum of the restriction of `f`: the one of the composite `i' ≫ f`, read
through the strict functoriality `i_*(f|_{Z'})_* = (i' ≫ f)_*` of pushforward of sheaves. -/
def closedSubsetRestrictionC :
    X.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u}
        (ClosedImmersionSheaves.closedSubsetInclusion Z)).obj
      ((TopCat.Sheaf.pushforward CommRingCat.{u} (closedSubsetRestrictionBase f Z)).obj
        (closedSubsetRingedSpace X' (closedSubsetPreimage f Z)).sheaf) :=
  ⟨(closedSubsetInclusion X' (closedSubsetPreimage f Z) ≫ f).hom.c⟩

/-- **The morphism of ringed spaces `f|_{Z'} : (Z', 𝒪_{X'}|_{Z'}) ⟶ (Z, 𝒪_X|_Z)` induced by a
morphism `f : X' ⟶ X` and a subset `Z ⊆ X` with preimage `Z' = f^{-1}(Z)`.** It lies over the
restriction of the continuous map of `f`, and it is the unique such morphism whose composite with
the inclusion of `Z` is `i' ≫ f`. -/
def closedSubsetRestriction :
    closedSubsetRingedSpace X' (closedSubsetPreimage f Z) ⟶ closedSubsetRingedSpace X Z :=
  inverseImageRingedSpaceLift X (ClosedImmersionSheaves.closedSubsetInclusion Z)
    (Y := closedSubsetRingedSpace X' (closedSubsetPreimage f Z))
    (closedSubsetRestrictionBase f Z) (closedSubsetRestrictionC f Z)

/-- The restriction of `f` lies over the restriction of the continuous map of `f`. -/
@[simp]
theorem closedSubsetRestriction_base :
    (closedSubsetRestriction f Z).hom.base = closedSubsetRestrictionBase f Z :=
  rfl

/-- **The square of the restriction commutes:** `f|_{Z'} ≫ i = i' ≫ f` as morphisms of ringed
spaces `(Z', 𝒪_{X'}|_{Z'}) ⟶ (X, 𝒪_X)`. -/
theorem closedSubsetRestriction_comp_closedSubsetInclusion :
    closedSubsetRestriction f Z ≫ closedSubsetInclusion X Z =
      closedSubsetInclusion X' (closedSubsetPreimage f Z) ≫ f := by
  apply InducedCategory.hom_ext
  refine PresheafedSpace.hext _ _ rfl ?_
  exact heq_of_eq (inverseImageRingedSpaceLift_comp_c X
    (ClosedImmersionSheaves.closedSubsetInclusion Z)
    (Y := closedSubsetRingedSpace X' (closedSubsetPreimage f Z))
    (closedSubsetRestrictionBase f Z) (closedSubsetRestrictionC f Z))

/-! ### Restriction to a subset detects cohomological support -/

/-- **Base change along an invertible germ map reflects zero objects.** If the germ map of `p` at
`y` is invertible then restriction of scalars along it is an equivalence of categories of stalk
modules, hence a quasi-inverse of the base change functor `𝒪_{Y',y} ⊗_{𝒪_{Y,p y}} -`; so the
latter sends no nonzero module to zero.

This is the half of [Stacks, Tag 0098] that the support statements below need in the direction
of reflection, and it is where `𝒪_{Z,z} = 𝒪_{X,z}` — the source's reason for the stalkwise step
of [Stacks, Tag 0G78] — actually enters. -/
theorem isZero_of_isZero_stalkBaseChange {Y' Y : RingedSpace.{u, u}} (p : Y' ⟶ Y)
    (y : Y'.carrier) (hp : IsIso (Stacks.RingedSpace.stalkRingMap p y))
    {A : ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := Y.carrier)
      (structureSheafRing Y).obj (p.hom.base y))}
    (hA : IsZero ((Stacks.RingedSpace.stalkBaseChange p y).obj A)) :
    IsZero A := by
  let _ := Stacks.RingedSpace.structureStalkCommRing Y (p.hom.base y)
  let _ := Stacks.RingedSpace.structureStalkCommRing Y' y
  let e : _ ≃+* _ := (@asIso _ _ _ _ _ hp).ringCatIsoToRingEquiv
  have : (ModuleCat.restrictScalars.{u, u, u}
      (Stacks.RingedSpace.stalkRingMap p y).hom).IsEquivalence :=
    ModuleCat.restrictScalars_isEquivalence_of_ringEquiv e
  let F := ModuleCat.restrictScalars.{u, u, u} (Stacks.RingedSpace.stalkRingMap p y).hom
  have adj1 : Stacks.RingedSpace.stalkBaseChange p y ⊣ F :=
    ModuleCat.extendRestrictScalarsAdj.{u, u, u} (Stacks.RingedSpace.stalkRingMap p y).hom
  have : F.Additive := adj1.right_adjoint_additive
  exact (Functor.map_isZero F (hA.of_iso
    ((adj1.leftAdjointUniq F.asEquivalence.symm.toAdjunction).app A).symm)).of_iso
    (F.asEquivalence.counitIso.app A).symm

section SubsetSupport

variable (Y : RingedSpace.{u, u}) (W : Set Y.carrier)

/-- The germ maps of the inclusion of a subset of a ringed space are invertible: the structure
sheaf of `(W, 𝒪_Y|_W)` is the inverse image `i^{-1}𝒪_Y`, so no base change takes place. No
hypothesis on `W` is used. -/
theorem isIso_stalkRingMap_closedSubsetInclusion (w : (closedSubsetRingedSpace Y W).carrier) :
    IsIso (Stacks.RingedSpace.stalkRingMap (closedSubsetInclusion Y W) w) :=
  AlgebraicGeometry.RingedSpace.isIso_stalkRingMap_inverseImageProjection Y
    (ClosedImmersionSheaves.closedSubsetInclusion W) w

/-- A sheaf of `𝒪_Y`-modules all of whose stalks on `W` vanish restricts to zero on
`(W, 𝒪_Y|_W)`. -/
theorem isZero_modulePullback_closedSubsetInclusion_of_stalk_isZero
    (N : SheafOfModules.{u} (structureSheafRing Y))
    (hN : ∀ w : Y.carrier, w ∈ W →
      IsZero ((AlgebraicGeometry.SheafOfModules.stalkFunctor
        (structureSheafRing Y) w).obj N)) :
    IsZero ((modulePullback (closedSubsetInclusion Y W)).obj N) := by
  refine Stacks.Cohomology.PushforwardRestriction.isZero_sheafOfModules_of_stalk_isZero
    (structureSheafRing (closedSubsetRingedSpace Y W)) _ fun w => ?_
  rw [← AlgebraicGeometry.SheafOfModules.isZero_stalkFunctor_obj_iff]
  refine IsZero.of_iso ?_ ((Stacks.RingedSpace.stalkModulePullbackFunctorIso
    (closedSubsetInclusion Y W) w).app N)
  exact Functor.map_isZero (Stacks.RingedSpace.stalkBaseChange (closedSubsetInclusion Y W) w)
    (hN _ w.2)

/-- Conversely, if a sheaf of `𝒪_Y`-modules restricts to zero on `(W, 𝒪_Y|_W)` then all its
stalks on `W` vanish: the restriction has stalk the base change of the stalk, and base change
along the invertible germ map reflects zero objects. -/
theorem isZero_stalk_of_isZero_modulePullback_closedSubsetInclusion
    (N : SheafOfModules.{u} (structureSheafRing Y))
    (hN : IsZero ((modulePullback (closedSubsetInclusion Y W)).obj N))
    (w : Y.carrier) (hw : w ∈ W) :
    IsZero ((AlgebraicGeometry.SheafOfModules.stalkFunctor
      (structureSheafRing Y) w).obj N) := by
  have hadd := AlgebraicGeometry.SheafOfModules.stalkFunctor_additive
    (structureSheafRing (closedSubsetRingedSpace Y W))
    (⟨w, hw⟩ : (closedSubsetRingedSpace Y W).carrier)
  exact isZero_of_isZero_stalkBaseChange (closedSubsetInclusion Y W) ⟨w, hw⟩
    (isIso_stalkRingMap_closedSubsetInclusion Y W ⟨w, hw⟩)
    ((Functor.map_isZero (AlgebraicGeometry.SheafOfModules.stalkFunctor
      (structureSheafRing (closedSubsetRingedSpace Y W))
      (⟨w, hw⟩ : (closedSubsetRingedSpace Y W).carrier)) hN).of_iso
      ((Stacks.RingedSpace.stalkModulePullbackFunctorIso
      (closedSubsetInclusion Y W) ⟨w, hw⟩).app N).symm)

/-- A complex restricts to zero on `W` iff the restrictions of its cohomology sheaves do: pullback
along the inclusion of a subset is exact, so `L(i_W)^*` is computed degreewise. -/
private theorem isZero_derivedPullback_closedSubsetInclusion_iff
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    IsZero ((derivedPullback (closedSubsetInclusion Y W)).obj E) ↔ ∀ n : ℤ,
      IsZero ((modulePullback (closedSubsetInclusion Y W)).obj
        ((DerivedCategory.homologyFunctor _ n).obj E)) := by
  let _ := preservesFiniteLimits_modulePullback_closedSubsetInclusion Y W
  let _ := preservesColimits_modulePullback (closedSubsetInclusion Y W)
  let _ : PreservesFiniteColimits (modulePullback (closedSubsetInclusion Y W)) := inferInstance
  rw [((Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory
    (closedSubsetInclusion Y W)).app E).isZero_iff]
  have e := fun n : ℤ => (exactFunctorDerivedHomologyIso
    (modulePullback (closedSubsetInclusion Y W)) n).app E
  exact ⟨fun h n => (e n).isZero_iff.1 (Functor.map_isZero (DerivedCategory.homologyFunctor _ n) h),
    fun h => DerivedCategory.isZero_of_forall_isZero_homology fun n => (e n).isZero_iff.2 (h n)⟩

/-- **A complex supported off `W` restricts to zero on `W`.** Pullback along the inclusion of a
subset is exact, so `L(i_W)^*` is computed degreewise and commutes with the cohomology sheaves;
those vanish on `W` by hypothesis, and a complex with no cohomology is a zero object. -/
theorem isZero_derivedPullback_closedSubsetInclusion_of_supported
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    (hE : AlgebraicGeometry.CohomologySupportedOn
      (structureSheafRing Y) Wᶜ E) :
    IsZero ((derivedPullback (closedSubsetInclusion Y W)).obj E) := by
  refine (isZero_derivedPullback_closedSubsetInclusion_iff Y W E).2 fun n => ?_
  refine isZero_modulePullback_closedSubsetInclusion_of_stalk_isZero Y W _ fun w hw => ?_
  rw [AlgebraicGeometry.SheafOfModules.isZero_stalkFunctor_obj_iff]
  exact hE n w (by simpa using hw)

/-- **A complex restricting to zero on `W` is supported off `W`.** The converse of
`isZero_derivedPullback_closedSubsetInclusion_of_supported`, by the same degreewise computation
read backwards. -/
theorem cohomologySupportedOn_compl_of_isZero_derivedPullback
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    (hE : IsZero ((derivedPullback (closedSubsetInclusion Y W)).obj E)) :
    AlgebraicGeometry.CohomologySupportedOn
      (structureSheafRing Y) Wᶜ E := by
  intro n w hw
  rw [← AlgebraicGeometry.SheafOfModules.isZero_stalkFunctor_obj_iff]
  exact isZero_stalk_of_isZero_modulePullback_closedSubsetInclusion Y W _
    ((isZero_derivedPullback_closedSubsetInclusion_iff Y W E).1 hE n) w
    (by simpa using hw : w ∈ W)

end SubsetSupport

/-- **Derived pullback preserves cohomological support:** if `K` in `D(𝒪_X)` has its cohomology
sheaves supported on `Z` then `Lf^*K` has its cohomology sheaves supported on `f^{-1}(Z)`.

No hypothesis on `Z` is used, and no description of the derived stalks of `Lf^*` is needed. The
argument restricts to the complementary subset `X ∖ Z`, where it is a formal consequence of the
composition isomorphism of [Stacks, Tag 0D5S] for the commuting square of
`closedSubsetRestriction_comp_closedSubsetInclusion` at `Z^c`: the restriction of `Lf^*K` to
`f^{-1}(X ∖ Z)` is the pullback along `f|_{f^{-1}(X∖Z)}` of the restriction of `K` to `X ∖ Z`,
which vanishes; and `Lf^*` is exact, hence additive, so it takes the zero object to a zero
object. -/
theorem cohomologySupportedOn_derivedPullback
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (hE : AlgebraicGeometry.CohomologySupportedOn
      (structureSheafRing X) Z E) :
    AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X')
      (closedSubsetPreimage f Z) ((derivedPullback f).obj E) := by
  have hpre : (closedSubsetPreimage f Zᶜ)ᶜ = closedSubsetPreimage f Z := by
    simp [closedSubsetPreimage, Set.preimage_compl]
  rw [← hpre]
  refine cohomologySupportedOn_compl_of_isZero_derivedPullback X'
    (closedSubsetPreimage f Zᶜ) _ ?_
  let cmp := Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
      (closedSubsetInclusion X' (closedSubsetPreimage f Zᶜ)) f ≪≫
    eqToIso (congrArg
      (fun t : closedSubsetRingedSpace X' (closedSubsetPreimage f Zᶜ) ⟶ X => derivedPullback t)
      (closedSubsetRestriction_comp_closedSubsetInclusion f Zᶜ).symm) ≪≫
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
      (closedSubsetRestriction f Zᶜ) (closedSubsetInclusion X Zᶜ)).symm
  refine IsZero.of_iso ?_ (cmp.app E)
  show IsZero ((derivedPullback (closedSubsetRestriction f Zᶜ)).obj
    ((derivedPullback (closedSubsetInclusion X Zᶜ)).obj E))
  refine Functor.map_isZero (derivedPullback (closedSubsetRestriction f Zᶜ))
    (isZero_derivedPullback_closedSubsetInclusion_of_supported X Zᶜ E ?_)
  rwa [compl_compl]

/-! ### The canonical map of Tag 0G78 -/

variable (hZ : IsClosed Z)

/-- **The base-change transformation of [Stacks, Tag 08HY] for the square of the restriction**,
at an object of `D(𝒪_X|_Z)`: the canonical map `Lf^*(Ri_*M) ⟶ Ri'_*(L(f|_{Z'})^*M)`. -/
abbrev supportedPullbackBaseChangeMap
    (M : DerivedCategory (SheafOfModules.{u}
      (structureSheafRing (closedSubsetRingedSpace X Z)))) :
    (derivedPullback f).obj ((derivedPushforward (closedSubsetInclusion X Z)).obj M) ⟶
      (derivedPushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z))).obj
        ((derivedPullback (closedSubsetRestriction f Z)).obj M) :=
  Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap (closedSubsetRestriction f Z)
    (closedSubsetInclusion X' (closedSubsetPreimage f Z)) (closedSubsetInclusion X Z) f
    (closedSubsetRestriction_comp_closedSubsetInclusion f Z) M

include hZ in
/-- **[Stacks, Tag 0G78]: the map of functors of [Stacks, Tag 08HY] is an isomorphism in this
case**, for every object of `D(𝒪_X|_Z)`. The
base-change transformation of [Stacks, Tag 08HY] for the square of the restriction,

`Lf^*(Ri_*M) ⟶ Ri'_*(L(f|_{Z'})^*M)`,

is an isomorphism for every `M`, in particular at `M = R𝓗_Z(K)`.

This is the essential-image half of [Stacks, Tag 0AEF] part (2) applied twice. The base-change
map is, by [Stacks, Tag 08HY]'s adjoint characterization, the unit of `Li'^* ⊣ Ri'_*` at
`Lf^*(Ri_*M)` followed by `Ri'_*` of a composite of three isomorphisms: the two composition
isomorphisms of [Stacks, Tag 0D5S], and the derived counit `Li^*(Ri_*M) ⟶ M`, which is
invertible because `Ri_*` is fully faithful for a closed-subset inclusion. So only the unit is
in question, and the unit of an adjunction with fully faithful right adjoint is invertible
exactly on the essential image of that right adjoint. The source `Lf^*(Ri_*M)` lies there:
`Ri_*M` has its cohomology supported on `Z`, derived pullback carries that to support on
`Z' = f^{-1}(Z)` by `cohomologySupportedOn_derivedPullback`, and [Stacks, Tag 0AEF] part (2)
puts every `Z'`-supported complex in the essential image of `Ri'_*`. -/
@[stacks 0G78 "the Remark's own assertion that the map of functors Lf^* i_* -> i'_* L(f|Z')^* \
  of Remark 20.28.3 (Tag 08HY) is an isomorphism in this case, proved for every M in D(O_X|Z), \
  in particular at M = RHZ(K); the source's stalkwise justification is replaced by the \
  essential-image half of Tag 0AEF part (2)"]
theorem isIso_supportedPullbackBaseChangeMap
    (M : DerivedCategory (SheafOfModules.{u}
      (structureSheafRing (closedSubsetRingedSpace X Z)))) :
    IsIso (supportedPullbackBaseChangeMap f Z M) := by
  have hZ' : IsClosed (closedSubsetPreimage f Z) := isClosed_closedSubsetPreimage f Z hZ
  have hcounit : IsIso ((derivedAdjunction (closedSubsetInclusion X Z)).counit.app M) :=
    isIso_derivedAdjunction_counit_app_closedSubsetInclusion X Z hZ M
  have hsupp : AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X')
      (closedSubsetPreimage f Z)
      ((derivedPullback f).obj ((derivedPushforward (closedSubsetInclusion X Z)).obj M)) :=
    cohomologySupportedOn_derivedPullback f Z _
      (cohomologySupportedOn_derivedPushforward_closedSubsetInclusion X Z hZ M)
  have hff := fullyFaithful_derivedPushforward_closedSubsetInclusion X'
    (closedSubsetPreimage f Z) hZ'
  let _ := hff.full
  let _ := hff.faithful
  have hunit : IsIso ((derivedAdjunction (closedSubsetInclusion X'
      (closedSubsetPreimage f Z))).unit.app
      ((derivedPullback f).obj ((derivedPushforward (closedSubsetInclusion X Z)).obj M))) :=
    (Adjunction.isIso_unit_app_iff_mem_essImage _).mpr
      (essImage_derivedPushforward_closedSubsetInclusion_of_supported X'
        (closedSubsetPreimage f Z) hZ' _ hsupp)
  have heq : supportedPullbackBaseChangeMap f Z M =
      Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap (closedSubsetRestriction f Z)
        (closedSubsetInclusion X' (closedSubsetPreimage f Z)) (closedSubsetInclusion X Z) f
        (closedSubsetRestriction_comp_closedSubsetInclusion f Z) M := rfl
  rw [heq, Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap_eq,
    Adjunction.homEquiv_unit]
  infer_instance

variable [PreservesFiniteLimits (modulePushforward (closedSubsetInclusion X Z))]
  [PreservesFiniteColimits (modulePushforward (closedSubsetInclusion X Z))]
  [PreservesFiniteLimits
    (modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z)))]
  [PreservesFiniteColimits
    (modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z)))]

/-- The composite `i'_*L(f|_{Z'})^* R𝓗_Z(K) ⟶ Lf^* K` that the canonical map of
[Stacks, Tag 0G78] is adjoint to.

The inverse of the base-change transformation of [Stacks, Tag 08HY] is taken at the
invertibility proved by `isIso_supportedPullbackBaseChangeMap`, from which no data is chosen:
`CategoryTheory.inv` names the unique two-sided inverse.

Reading the factors in order: `closedPushforwardComparison` for `i'` passes to the total right
derived pushforward; the inverse of the base-change transformation is the identification
`Ri'_*(L(f|_{Z'})^* R𝓗_Z(K)) = Lf^*(Ri_* R𝓗_Z(K))`; the comparison for `i` comes back; and the
derived pullback along `f` of the adjunction map `i_* R𝓗_Z(K) ⟶ K` of [Stacks, Tag 0A3B] is the
last arrow. -/
def supportedPullbackMateMap
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z))).mapDerivedCategory.obj
        ((derivedPullback (closedSubsetRestriction f Z)).obj
          ((derivedSupportedSectionsOnClosed X Z hZ).obj K)) ⟶
      (derivedPullback f).obj K :=
  haveI : IsIso (supportedPullbackBaseChangeMap f Z
      ((derivedSupportedSectionsOnClosed X Z hZ).obj K)) :=
    isIso_supportedPullbackBaseChangeMap f Z hZ _
  (closedPushforwardComparison X' (closedSubsetPreimage f Z)).hom.app _ ≫
    CategoryTheory.inv
      (supportedPullbackBaseChangeMap f Z ((derivedSupportedSectionsOnClosed X Z hZ).obj K)) ≫
    (derivedPullback f).map ((closedPushforwardComparison X Z).inv.app _) ≫
    (derivedPullback f).map ((derivedPushforwardAdjunction X Z hZ).counit.app K)

/-- **[Stacks, Tag 0G78].** Let `f : (X', 𝒪_{X'}) ⟶ (X, 𝒪_X)` be a morphism of ringed spaces,
let `Z ⊆ X` be closed and let `Z' = f^{-1}(Z)`. For `K` in `D(𝒪_X)` the canonical map

`L(f|_{Z'})^* R𝓗_Z(K) ⟶ R𝓗_{Z'}(Lf^* K)`

in `D(𝒪_{X'}|_{Z'})`: the map corresponding to `supportedPullbackMateMap` under the adjunction
`i'_* ⊣ R𝓗_{Z'}` of [Stacks, Tag 0A3B] part (1). -/
@[stacks 0G78 "the canonical map and the adjunction equation characterizing it; the \
  invertibility of the base-change transformation of Tag 08HY, which is the stalkwise step of \
  the source, is isIso_supportedPullbackBaseChangeMap above"]
def supportedPullbackMap (hZ' : IsClosed (closedSubsetPreimage f Z))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (derivedPullback (closedSubsetRestriction f Z)).obj
        ((derivedSupportedSectionsOnClosed X Z hZ).obj K) ⟶
      (derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z) hZ').obj
        ((derivedPullback f).obj K) :=
  derivedSupportedSectionsLift X' (closedSubsetPreimage f Z) hZ'
    (supportedPullbackMateMap f Z hZ K)

/-- **[Stacks, Tag 0G78], the adjunction equation characterizing the canonical map.** Pushing the
canonical map forward from `Z'` and composing with the adjunction map
`i'_* R𝓗_{Z'}(Lf^* K) ⟶ Lf^* K` of [Stacks, Tag 0A3B] gives the displayed composite. This is the
unique factorization that the source obtains from part (3) of [Stacks, Tag 0AEF]. -/
@[stacks 0G78 "the factorization of the pulled-back adjunction map through the adjunction map \
  on the preimage"]
theorem supportedPullbackMap_mate (hZ' : IsClosed (closedSubsetPreimage f Z))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (modulePushforward
            (closedSubsetInclusion X' (closedSubsetPreimage f Z))).mapDerivedCategory.map
          (supportedPullbackMap f Z hZ hZ' K) ≫
        (derivedPushforwardAdjunction X' (closedSubsetPreimage f Z) hZ').counit.app
          ((derivedPullback f).obj K) =
      supportedPullbackMateMap f Z hZ K :=
  modulePushforward_map_derivedSupportedSectionsLift_comp_counit X'
    (closedSubsetPreimage f Z) hZ' (supportedPullbackMateMap f Z hZ K)

/-- The adjunction equation determines the canonical map of [Stacks, Tag 0G78]: no other
morphism of that type satisfies it. Together with `supportedPullbackMap_mate` this says the map
is the unique solution of the characterization, so the construction is not under-determined. -/
@[stacks 0G78 "the uniqueness the Remark asserts: 'we find that the south-east arrow factors \
  UNIQUELY over the south-west arrow'. This is the half of the universality of Tag 0AEF part \
  (3) that supportedPullbackMap_mate does not state, and it is what makes the canonical map \
  canonical -- neither the zero map nor the negative of it satisfies the characterization"]
theorem supportedPullbackMap_unique (hZ' : IsClosed (closedSubsetPreimage f Z))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (g : (derivedPullback (closedSubsetRestriction f Z)).obj
        ((derivedSupportedSectionsOnClosed X Z hZ).obj K) ⟶
      (derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z) hZ').obj
        ((derivedPullback f).obj K))
    (hg : (modulePushforward
              (closedSubsetInclusion X' (closedSubsetPreimage f Z))).mapDerivedCategory.map g ≫
          (derivedPushforwardAdjunction X' (closedSubsetPreimage f Z) hZ').counit.app
            ((derivedPullback f).obj K) =
        supportedPullbackMateMap f Z hZ K) :
    g = supportedPullbackMap f Z hZ hZ' K := by
  have h : ((derivedPushforwardAdjunction X' (closedSubsetPreimage f Z) hZ').homEquiv _ _).symm g =
      supportedPullbackMateMap f Z hZ K :=
    (Adjunction.homEquiv_symm_apply
      (derivedPushforwardAdjunction X' (closedSubsetPreimage f Z) hZ') _ _ g).trans hg
  have h' := ((derivedPushforwardAdjunction X' (closedSubsetPreimage f Z) hZ').homEquiv
    _ _).apply_symm_apply g
  rw [h] at h'
  exact h'.symm

/-- **[Stacks, Tag 0G78], the commutative triangle of the source.** Composing the base-change
transformation of [Stacks, Tag 08HY] with the pushforward from `Z'` of the canonical map and the
adjunction map `i'_* R𝓗_{Z'}(Lf^* K) ⟶ Lf^* K` gives the derived pullback along `f` of the
adjunction map `i_* R𝓗_Z(K) ⟶ K`.

This is `supportedPullbackMap_mate` with the inverse of the base-change transformation cleared
from the statement, so it is the triangle of the source read literally: the diagonal arrow out
of `Lf^*(i_* R𝓗_Z(K))` factors through the adjunction map on the preimage. -/
@[stacks 0G78 "the commutative triangle, with the base-change transformation of Tag 08HY on the \
  left"]
theorem supportedPullbackMap_triangle (hZ' : IsClosed (closedSubsetPreimage f Z))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    supportedPullbackBaseChangeMap f Z ((derivedSupportedSectionsOnClosed X Z hZ).obj K) ≫
          (closedPushforwardComparison X' (closedSubsetPreimage f Z)).inv.app _ ≫
          (modulePushforward
              (closedSubsetInclusion X' (closedSubsetPreimage f Z))).mapDerivedCategory.map
            (supportedPullbackMap f Z hZ hZ' K) ≫
          (derivedPushforwardAdjunction X' (closedSubsetPreimage f Z) hZ').counit.app
            ((derivedPullback f).obj K) =
      (derivedPullback f).map ((closedPushforwardComparison X Z).inv.app _) ≫
        (derivedPullback f).map ((derivedPushforwardAdjunction X Z hZ).counit.app K) := by
  rw [supportedPullbackMap_mate]
  simp only [supportedPullbackMateMap, Iso.inv_hom_id_app_assoc, IsIso.hom_inv_id_assoc]

end Stacks.Cohomology.SupportedComplexes

end
