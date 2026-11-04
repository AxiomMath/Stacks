module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.RightTensor
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackTensorDual
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectDerivedPullback
import StacksCore.Tactic.StacksAttribute

/-!
# Base change for a derived internal hom out of a perfect object

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a cartesian square of schemes, `K ∈ D(𝒪_X)`, `K' ∈ D(𝒪_{X'})` and `φ : L(g')^*K ⟶ K'` such that
the map of Stacks 0DJ7 is an isomorphism at every point of `X'` and in every degree, which is
condition (1) of Stacks 0DJ8.  Then for every perfect `E ∈ D(𝒪_X)` the same holds for the
comparison

`L(g')^*R𝓗om(E, K) ⟶ R𝓗om(L(g')^*E, K')`.

This is Stacks 0DJA (2).  For `E` perfect, `R𝓗om(E, K) = K ⊗^L R𝓗om(E, 𝒪_X)` by Tag 08DQ, and
`L(g')^*R𝓗om(E, 𝒪_X) = R𝓗om(L(g')^*E, 𝒪_{X'})` by Tag 0GM7 (1); under these identifications
the comparison is the one of Stacks 0DJA (1) for the derived tensor product with
`R𝓗om(E, 𝒪_X)`.

## Main results

* `AlgebraicGeometry.isIso_baseChangeCohomologyMap_baseChangeSheafHomComparison_of_isPerfect`

## References

* [Stacks Project, Tag 0DJA](https://stacks.math.columbia.edu/tag/0DJA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Prod

universe u

namespace AlgebraicGeometry

open Stacks.Cohomology.DerivedPullbackTensor Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedInternalHomPullback
open Stacks.Cohomology.DerivedProjectionFormula (singleUnit)

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] abelianModulesSheafTensor

attribute [local implicit_reducible] structureSheafRing CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}

/-- **Stacks 0DJA (2).** For a cartesian square of schemes, if the map of Stacks 0DJ7 at
`(K, K', φ)` is an isomorphism at every point of `X'` and in every degree, then so is the one at
the comparison `L(g')^*R𝓗om(E, K) ⟶ R𝓗om(L(g')^*E, K')`, for every perfect `E` in `D(𝒪_X)`. -/
@[stacks 0DJA "(2)"]
theorem isIso_baseChangeCohomologyMap_baseChangeSheafHomComparison_of_isPerfect
    (hpb : IsPullback g' f' f g) (E K : DerivedCategory X.Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E)
    (K' : DerivedCategory X'.Modules) (φ : (derivedPullback g'.toLRSHom.toShHom).obj K ⟶ K')
    (h : ∀ (x' : X') (n : ℤ), IsIso (baseChangeCohomologyMap f g f' g' hpb.w K K' φ x' n))
    (x' : X') (n : ℤ) :
    IsIso (baseChangeCohomologyMap f g f' g' hpb.w
      (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op E)).obj K)
      (((Stacks.SheafOfModules.derivedSheafHom X'.sheaf).obj
        (op ((derivedPullback g'.toLRSHom.toShHom).obj E))).obj K')
      (Stacks.Cohomology.DerivedBaseChangeComparison.baseChangeSheafHomComparison
        g'.toLRSHom.toShHom E K K' φ) x' n) := by
  let D := ((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op E)).obj
    (singleUnit X.toRingedSpace)
  have hPE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X'.toRingedSpace)
      ((derivedPullback g'.toLRSHom.toShHom).obj E) :=
    AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback
      g'.toLRSHom.toShHom E hE
  have hμ : IsIso (tensorDualToSheafHom X.toRingedSpace E K) :=
    isIso_tensorDualToSheafHom X.toRingedSpace E K hE
  have hμ' : IsIso (tensorDualToSheafHom X'.toRingedSpace
      ((derivedPullback g'.toLRSHom.toShHom).obj E) K') :=
    isIso_tensorDualToSheafHom X'.toRingedSpace _ K' hPE
  have hε : IsIso (derivedPullbackDualMap g'.toLRSHom.toShHom E) :=
    isIso_derivedPullbackDualMap g'.toLRSHom.toShHom E hE
  have hτ : IsIso ((internalHomTensorUncurried X'.toRingedSpace).map
      (𝟙 K' ×ₘ derivedPullbackDualMap g'.toLRSHom.toShHom E) ≫
      tensorDualToSheafHom X'.toRingedSpace ((derivedPullback g'.toLRSHom.toShHom).obj E) K') :=
    IsIso.comp_isIso' (Iso.isIso_hom ((internalHomTensorUncurried X'.toRingedSpace).mapIso
      (Iso.prod (Iso.refl K') (@asIso _ _ _ _ _ hε)))) hμ'
  have key := isIso_baseChangeCohomologyMap_pullbackTensorIso_of_isPullback hpb K D K' φ h x' n
  have h1 := (isIso_baseChangeCohomologyMap_iff_of_isIso_target f g f' g' hpb.w _ _ _ _ _ hτ
    x' n).2 key
  have h2 := isIso_baseChangeCohomologyMap_of_eq hpb.w _ _ _ _
    (map_tensorDualToSheafHom_comp_baseChangeSheafHomComparison g'.toLRSHom.toShHom E K K' φ)
    x' n h1
  exact (isIso_baseChangeCohomologyMap_iff_of_isIso_source f g f' g' hpb.w _ _ _ _ hμ _ x'
    n).1 h2

end AlgebraicGeometry
