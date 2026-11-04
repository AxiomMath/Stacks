module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportBaseChangeInternalHom
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Perfect.TorIndependence
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackPerfectAndPseudoCoherent
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0E2M: flat base change for sheaf Hom with exact support

Consider a cartesian diagram of schemes

```
Z' --i'--> X'
|g         |f
Z --i----> X
```

in which `i` is a closed immersion. When `Z` and `X'` are Tor independent over `X`, the section
of the source opened by [Stacks, Tag 0E2J] attaches to it the canonical map

`Lg^* R ℰom(𝒪_Z, K) ⟶ R ℰom(𝒪_{Z'}, Lf^*K)`

of [Stacks, Tag 0E2K], `Stacks.Duality.ExactSupportBaseChange.baseChangeSheafHomExactSupportMap`.
[Stacks, Tag 0E2M] says that it is an isomorphism when `f` is flat, `i` is pseudo-coherent and
`K ∈ D⁺_QCoh(𝒪_X)`; this file proves it.

## The proof

By [Stacks, Tag 0E2L]
(`isIso_baseChangeSheafHomExactSupportMap_app_iff_isIso_derivedPullbackSheafHomMap`, in the
namespace `Stacks.Duality.ExactSupportBaseChange`) the map is an isomorphism exactly when the base
change map

`Lf^* R𝓗om(Ri_*𝒪_Z, K) ⟶ R𝓗om(Lf^*Ri_*𝒪_Z, Lf^*K)`

of Cohomology, Remark [Stacks, Tag 08I3] is. The latter is an isomorphism by [Stacks, Tag 0GM7] (2)
(`isIso_derivedPullbackSheafHomMap_of_isPseudoCoherent`, in the namespace
`Stacks.Cohomology.DerivedInternalHomPullback`): `f` is flat, `Ri_*𝒪_Z` is pseudo-coherent because
`i` is ([Stacks, Tag 0AVX], in the form
`AlgebraicGeometry.Scheme.isPseudoCoherent_pushforward_derivedStructureSheaf`), and `K` is bounded
below, hence locally bounded below. This is the source's first proof with the affine computation of
More on Algebra, Lemma 0ATK replaced by its sheaf-level form, [Stacks, Tag 0GM7], which is proved
by exactly that local computation.

## Hypotheses

The statement is at exactly the source's hypotheses. Tor independence of `Z` and `X'` over `X`,
which the situation of [Stacks, Tag 0E2J] needs for the map to exist, is not assumed: it follows
from the flatness of `f` (`AlgebraicGeometry.torIndependent_of_flat_right`). `K ∈ D⁺_QCoh(𝒪_X)` is
spelled, as elsewhere in this development, as the conjunction of boundedness below
(`DerivedCategoryB.IsBoundedBelow`) and quasi-coherence of the cohomology sheaves
(`Stacks.DerivedQCoh.IsDQCoh`). The proof uses only the first; the source records the same fact in
the footnote to its second proof ("it suffices to assume `K` is in `D⁺(𝒪_X)`"), and
`isIso_baseChangeSheafHomExactSupportMap_app_of_flat_of_isBoundedBelow` states that form.

## Main results

* `AlgebraicGeometry.RingedSpace.isLocallyBoundedBelow_of_isBoundedBelow`: a bounded below object
  is locally bounded below.
* `Stacks.Duality.ExactSupportBaseChange.isIso_derivedPullbackSheafHomMap_pushforward_of_flat`:
  [Stacks, Tag 0GM7] (2) at `Ri_*𝒪_Z`.
* `isIso_baseChangeSheafHomExactSupportMap_app_of_flat_of_isBoundedBelow`, in the namespace
  `Stacks.Duality.ExactSupportBaseChange`: the map of [Stacks, Tag 0E2K] is an isomorphism for
  `K ∈ D⁺(𝒪_X)`.
* `baseChangeSheafHomExactSupportMap_isIso_of_flat_pseudoCoherent`, in the namespace
  `Stacks.Duality.ExactSupportBaseChange`: **[Stacks, Tag 0E2M].**

## References

* [Stacks Project, Tag 0E2M](https://stacks.math.columbia.edu/tag/0E2M)
* [Stacks Project, Tag 0E2K](https://stacks.math.columbia.edu/tag/0E2K)
* [Stacks Project, Tag 0E2L](https://stacks.math.columbia.edu/tag/0E2L)
* [Stacks Project, Tag 0GM7](https://stacks.math.columbia.edu/tag/0GM7)
* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
* [Stacks Project, Tag 0AVX](https://stacks.math.columbia.edu/tag/0AVX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

/-- A bounded below object of `D(𝒪_X)` is locally bounded below: take the whole space as the
neighbourhood of every point. -/
theorem isLocallyBoundedBelow_of_isBoundedBelow {X : RingedSpace.{u, u}}
    (E : DerivedCategory (StrictlyPerfect.OXMod.{u, u, u} X))
    (hE : DerivedCategoryB.IsBoundedBelow E) : IsLocallyBoundedBelow X E := by
  obtain ⟨n₀, hn₀⟩ := hE
  exact fun _ => ⟨⊤, trivial, n₀, fun i hi => (restrictModules X ⊤).map_isZero (hn₀ i hi)⟩

end AlgebraicGeometry.RingedSpace

open AlgebraicGeometry
open Stacks.Cohomology.DerivedInternalHomPullback

namespace Stacks.Duality.ExactSupportBaseChange

variable {Z' X' Z X : AlgebraicGeometry.Scheme.{u}} {i' : Z' ⟶ X'} {g : Z' ⟶ Z} {f : X' ⟶ X}
  {i : Z ⟶ X}

-- As in `StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackMap`: the
-- derived pullback and the derived internal Hom name the structure sheaf of a ringed space
-- differently, and the two spellings agree only after unfolding these definitions.
attribute [local implicit_reducible] structureSheafRing CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

/-- **[Stacks, Tag 0GM7] (2) at `Ri_*𝒪_Z`.** For a flat morphism `f : X' ⟶ X`, a pseudo-coherent
closed immersion `i : Z ⟶ X` and a bounded below `K ∈ D(𝒪_X)`, the canonical map of
[Stacks, Tag 08I3]

`Lf^* R𝓗om(Ri_*𝒪_Z, K) ⟶ R𝓗om(Lf^*Ri_*𝒪_Z, Lf^*K)`

is an isomorphism: `Ri_*𝒪_Z` is pseudo-coherent by [Stacks, Tag 0AVX]
(`AlgebraicGeometry.Scheme.isPseudoCoherent_pushforward_derivedStructureSheaf`, stated for the
pushforward along the exact functor `i_*`, which `derivedPushforwardComparison` identifies with the
total right derived functor `Ri_*`) and `K` is in particular locally bounded below. -/
theorem isIso_derivedPullbackSheafHomMap_pushforward_of_flat (f : X' ⟶ X)
    [AlgebraicGeometry.Flat f] (i : Z ⟶ X) [IsClosedImmersion i] [PseudoCoherent i]
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hK : DerivedCategoryB.IsBoundedBelow K) :
    IsIso (Stacks.Cohomology.DerivedInternalHomPullback.derivedPullbackSheafHomMap
      f.toLRSHom.toShHom
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
        i.toLRSHom.toShHom).obj (unitObject Z.toSheafedSpace)) K) := by
  have h₀ := isIso_derivedPullbackSheafHomMap_of_isPseudoCoherent
    f.toLRSHom.toShHom (fun x => Flat.stalkMap f x)
    ((RingedSpaceModuleAdjunction.modulePushforward
        (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i).i).mapDerivedCategory.obj
          (RingedSite.derivedStructureSheaf (Stacks.SheafOfModules.ringedSite Z.sheaf)))
    (Scheme.isPseudoCoherent_pushforward_derivedStructureSheaf i inferInstance) K
    (RingedSpace.isLocallyBoundedBelow_of_isBoundedBelow K hK)
  have hu : RingedSite.derivedStructureSheaf (Stacks.SheafOfModules.ringedSite Z.sheaf) =
      unitObject Z.toSheafedSpace := rfl
  let e : (RingedSpaceModuleAdjunction.modulePushforward
        (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i).i).mapDerivedCategory.obj
          (RingedSite.derivedStructureSheaf (Stacks.SheafOfModules.ringedSite Z.sheaf)) ≅
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
        i.toLRSHom.toShHom).obj (unitObject Z.toSheafedSpace) :=
    eqToIso (congrArg (RingedSpaceModuleAdjunction.modulePushforward
        (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i).i).mapDerivedCategory.obj hu) ≪≫
      (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i).derivedPushforwardComparison.app
        (unitObject Z.toSheafedSpace)
  refine (isIso_map_derivedPullbackSheafHomMap_iff_of_iso f.toLRSHom.toShHom (𝟭 _) e K).1 ?_
  exact h₀

/-- **The map of [Stacks, Tag 0E2K] is invertible on `D⁺(𝒪_X)` along a flat morphism.** In a
cartesian square of schemes whose right-hand column `i` is a pseudo-coherent closed immersion and
whose bottom row `f` is flat, the map `Lg^* R ℰom(𝒪_Z, K) ⟶ R ℰom(𝒪_{Z'}, Lf^*K)` is an
isomorphism for every bounded below `K`, whatever the proof `htor` of Tor independence it is
built from.

[Stacks, Tag 0E2L] reduces it to the map of [Stacks, Tag 08I3] at `Ri_*𝒪_Z`, which is invertible
by [Stacks, Tag 0GM7] (2), `isIso_derivedPullbackSheafHomMap_pushforward_of_flat`. -/
theorem isIso_baseChangeSheafHomExactSupportMap_app_of_flat_of_isBoundedBelow
    (sq : IsPullback i' g f i) [IsClosedImmersion i] [AlgebraicGeometry.Flat f]
    [PseudoCoherent i] (htor : AlgebraicGeometry.TorIndependent i f)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hbb : DerivedCategoryB.IsBoundedBelow K) :
    IsIso ((baseChangeSheafHomExactSupportMap sq htor).app K) :=
  (isIso_baseChangeSheafHomExactSupportMap_app_iff_isIso_derivedPullbackSheafHomMap K sq htor).2
    (isIso_derivedPullbackSheafHomMap_pushforward_of_flat f i K hbb)

/-- **Stacks Project, Tag 0E2M.** Consider a cartesian square of schemes

```
Z' --i'--> X'
|g         |f
Z --i----> X
```

with `i` a closed immersion, and assume `f` is flat and `i` pseudo-coherent. Then the canonical
base change map of [Stacks, Tag 0E2K]

`Lg^* R ℰom(𝒪_Z, K) ⟶ R ℰom(𝒪_{Z'}, Lf^*K)`

is an isomorphism for `K` in `D⁺_QCoh(𝒪_X)`, which is `hbb` together with `_hqc`.

The Tor independence of `Z` and `X'` over `X` that the map is built from is not a hypothesis: it
is supplied by the flatness of `f`, `AlgebraicGeometry.torIndependent_of_flat_right`. The proof
uses only that `K` is bounded below, as the footnote to the source's second proof records;
`isIso_baseChangeSheafHomExactSupportMap_app_of_flat_of_isBoundedBelow` is that statement. -/
@[stacks 0E2M]
theorem baseChangeSheafHomExactSupportMap_isIso_of_flat_pseudoCoherent
    (sq : IsPullback i' g f i) [IsClosedImmersion i] [AlgebraicGeometry.Flat f]
    [PseudoCoherent i]
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hbb : DerivedCategoryB.IsBoundedBelow K)
    (_hqc : @Stacks.DerivedQCoh.IsDQCoh _ _ _
      (structureSheafRing X.toRingedSpace) _ _ _ _ _ K) :
    IsIso ((baseChangeSheafHomExactSupportMap sq
      (AlgebraicGeometry.torIndependent_of_flat_right i f)).app K) :=
  isIso_baseChangeSheafHomExactSupportMap_app_of_flat_of_isBoundedBelow sq _ K hbb

end Stacks.Duality.ExactSupportBaseChange

end
