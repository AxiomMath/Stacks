module

public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportFlatBaseChangeIso

/-!
# Flat base change for sheaf Hom with exact support, at a locally bounded below object

Consider a cartesian square of schemes

```
Z' --i'--> X'
|g         |f
Z --i----> X
```

with `i` a pseudo-coherent closed immersion and `f` flat. Stacks 0E2M says that the base change
map `Lg^* R ℰom(𝒪_Z, K) ⟶ R ℰom(𝒪_{Z'}, Lf^*K)` is an isomorphism for `K ∈ D⁺_QCoh(𝒪_X)`. The
proof only uses that `K` is *locally* bounded below: it reduces, through Stacks 0E2L, to the map
of Stacks 08I3 at `Ri_*𝒪_Z`, which is invertible by Stacks 0GM7 (2) for a locally bounded below
target. This file records that form, which is the one needed on a non-quasi-compact scheme, where
a relative dualizing complex is only locally bounded.

## Main results

* `isIso_derivedPullbackSheafHomMap_pushforward_of_flat_of_isLocallyBoundedBelow`: the map
  `Lf^* R𝓗om(Ri_*𝒪_Z, K) ⟶ R𝓗om(Lf^*Ri_*𝒪_Z, Lf^*K)` is an isomorphism for `f` flat and `K`
  locally bounded below.
* `isIso_baseChangeSheafHomExactSupportMap_app_of_flat_of_isLocallyBoundedBelow`: the base change
  map `Lg^* R ℰom(𝒪_Z, K) ⟶ R ℰom(𝒪_{Z'}, Lf^*K)` is an isomorphism for `f` flat and `K` locally
  bounded below.

## References

* [Stacks Project, Tag 0E2M](https://stacks.math.columbia.edu/tag/0E2M)
* [Stacks Project, Tag 0GM7](https://stacks.math.columbia.edu/tag/0GM7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance 10000] HasDerivedCategory.standard

open AlgebraicGeometry
open Stacks.Cohomology.DerivedInternalHomPullback

namespace Stacks.Duality.ExactSupportBaseChange

variable {Z' X' Z X : AlgebraicGeometry.Scheme.{u}} {i' : Z' ⟶ X'} {g : Z' ⟶ Z} {f : X' ⟶ X}
  {i : Z ⟶ X}

attribute [local implicit_reducible] structureSheafRing CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

/-- **Stacks 0GM7 (2) at `Ri_*𝒪_Z`, for a locally bounded below target.** For a flat morphism
`f : X' ⟶ X`, a pseudo-coherent closed immersion `i : Z ⟶ X` and a locally bounded below
`K ∈ D(𝒪_X)`, the canonical map `Lf^* R𝓗om(Ri_*𝒪_Z, K) ⟶ R𝓗om(Lf^*Ri_*𝒪_Z, Lf^*K)` is an
isomorphism. -/
theorem isIso_derivedPullbackSheafHomMap_pushforward_of_flat_of_isLocallyBoundedBelow
    (f : X' ⟶ X) [AlgebraicGeometry.Flat f] (i : Z ⟶ X) [IsClosedImmersion i] [PseudoCoherent i]
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hK : RingedSpace.IsLocallyBoundedBelow X.toRingedSpace K) :
    IsIso (Stacks.Cohomology.DerivedInternalHomPullback.derivedPullbackSheafHomMap
      f.toLRSHom.toShHom
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
        i.toLRSHom.toShHom).obj (unitObject Z.toSheafedSpace)) K) := by
  have h₀ := isIso_derivedPullbackSheafHomMap_of_isPseudoCoherent
    f.toLRSHom.toShHom (fun x => Flat.stalkMap f x)
    ((RingedSpaceModuleAdjunction.modulePushforward
        (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i).i).mapDerivedCategory.obj
          (RingedSite.derivedStructureSheaf (Stacks.SheafOfModules.ringedSite Z.sheaf)))
    (Scheme.isPseudoCoherent_pushforward_derivedStructureSheaf i inferInstance) K hK
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
  exact (isIso_map_derivedPullbackSheafHomMap_iff_of_iso f.toLRSHom.toShHom (𝟭 _) e K).1 h₀

/-- **The map of Stacks 0E2K is invertible at a locally bounded below object along a flat
morphism.** In a cartesian square of schemes whose right-hand column `i` is a pseudo-coherent
closed immersion and whose bottom row `f` is flat, `Lg^* R ℰom(𝒪_Z, K) ⟶ R ℰom(𝒪_{Z'}, Lf^*K)`
is an isomorphism for every locally bounded below `K`. -/
theorem isIso_baseChangeSheafHomExactSupportMap_app_of_flat_of_isLocallyBoundedBelow
    (sq : IsPullback i' g f i) [IsClosedImmersion i] [AlgebraicGeometry.Flat f]
    [PseudoCoherent i] (htor : AlgebraicGeometry.TorIndependent i f)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hK : RingedSpace.IsLocallyBoundedBelow X.toRingedSpace K) :
    IsIso ((baseChangeSheafHomExactSupportMap sq htor).app K) :=
  (isIso_baseChangeSheafHomExactSupportMap_app_iff_isIso_derivedPullbackSheafHomMap K sq htor).2
    (isIso_derivedPullbackSheafHomMap_pushforward_of_flat_of_isLocallyBoundedBelow f i K hK)

end Stacks.Duality.ExactSupportBaseChange

end
