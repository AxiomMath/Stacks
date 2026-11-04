module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeAffineLeray
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeAffineOpenSquare
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The pullback map on cohomology over a compatible pair of affine opens

Conclusion (c) of [Stacks, Tag 0EX3] compares two computations, and both of them are
computations of one and the same map. For a cartesian square
```
X'' --h'--> X'
|f''        |f'
Y'' --h-->  Y'
```
an affine open `V` of `Y'`, an affine open `W` of `Y''` with `W ≤ h⁻¹(V)` and a quasi-coherent
`𝒪_{X'}`-module `F'`, write

* `k : f''⁻¹(W) ⟶ f'⁻¹(V)` for the horizontal morphism of the square restricted to that pair of
  opens, the square being cartesian by
  `Stacks.AlgebraicGeometry.TopDegreeBaseChange.isPullback_resLE_of_isPullback`;
* `G` for the restriction of `F'` to `f'⁻¹(V)`.

This file defines the map

`H^n(f'⁻¹(V), G) ⟶ H^n(f''⁻¹(W), k^* G)`

as `H^n` of the unit `G ⟶ k_* k^* G` of the adjunction `k^* ⊣ k_*`, read through the Leray
comparison `H^n(f''⁻¹(W), k^* G) ≅ H^n(f'⁻¹(V), k_* k^* G)` of `BaseChangeAffineLeray.lean` —
which is [Stacks, Tag 089W] along the affine `k` — and the characterising identity that says
exactly this: composing the map with that comparison returns `H^n` of the unit.

## Main definitions

* `…TopDegreeBaseChange.affineOpenCohomologyPullbackMap`: **the pullback map on cohomology over
  a compatible pair of affine opens**, `H^n(f'⁻¹(V), G) ⟶ H^n(f''⁻¹(W), k^* G)`, as a morphism
  of `Γ(f'⁻¹(V), ⊤)`-modules, with no hypothesis on `Y'`, on `Y''`, on `f'` or on `h`.

## Main results

* `…TopDegreeBaseChange.isAffineHom_resLE_of_isPullback`: **the restricted `h'` is affine**, for
  a cartesian square and a compatible pair of affine opens.
* `…TopDegreeBaseChange`
  `.affineOpenCohomologyPullbackMap_comp_cohomologyPullbackIsoPushforward_hom`: **the
  characterising identity**, `affineOpenCohomologyPullbackMap ≫ (Leray comparison).hom =
  H^n(unit)`.

## Implementation notes

*Why the Leray comparison enters inverted.* The unit of `k^* ⊣ k_*` is a morphism of
`𝒪_{f'⁻¹(V)}`-modules `G ⟶ k_* k^* G`, so applying `H^n(f'⁻¹(V), -)` to it lands in the
cohomology of the direct image, not in the cohomology upstairs. Since `k` is affine and `k^* G`
is quasi-coherent, those two agree, by `cohomologyPullbackIsoPushforward`; composing with the
inverse of that isomorphism is what turns `H^n` of the unit into a map to `H^n(f''⁻¹(W), k^* G)`.
The characterising identity records that the construction is nothing more than this bookkeeping.

*Affineness of `k` is discharged, not assumed.* `V` and `W` are affine, so the restricted `h` is
a morphism of affine schemes and hence affine by
`AlgebraicGeometry.isAffineHom_of_isAffine`; `k` is its base change along the restricted square,
so `CategoryTheory.MorphismProperty.IsStableUnderBaseChange.of_isPullback` makes `k` affine too.
This is the technique `cohomologyPullbackIsoTensorCohomology` and
`cohomologyPullbackIsoTensorCohomologyAffineOpens` use, and `isAffineHom_resLE_of_isPullback`
names its conclusion so that the characterising identity can state the instance it needs.

*The defining inequality of `k` is an explicit argument.* As in
`BaseChangeAffineOpenTensorCohomology.lean`, the inequality `f''⁻¹(W) ≤ (h')⁻¹(f'⁻¹(V))` that
`AlgebraicGeometry.Scheme.Hom.resLE` consumes is taken as an argument `hle` rather than
repeated; `preimage_le_preimage_of_isPullback` proves it, and any two proofs agree, so a
consumer may supply whichever one it has.

*Quasi-coherence is supplied where it is needed.* The coefficient over the pair of opens is the
restriction of `F'` to `f'⁻¹(V)`, quasi-coherent by
`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_restrictFunctor`, so quasi-coherence of `F'`
itself is all that either declaration asks for, and it is asked for as an explicit argument.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.Cohomology.AffineBase
open Stacks.RingedSpace

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {X' Y' X'' Y'' : Scheme.{u}} {f' : X' ⟶ Y'} {h' : X'' ⟶ X'} {f'' : X'' ⟶ Y''}
  {h : Y'' ⟶ Y'}

/-- **The horizontal morphism of a cartesian square restricted to a compatible pair of affine
opens is affine.** For a cartesian square
```
X'' --h'--> X'
|f''        |f'
Y'' --h-->  Y'
```
an affine open `V` of `Y'` and an affine open `W` of `Y''` with `W ≤ h⁻¹(V)`, the morphism
`h' ∣ : f''⁻¹(W) ⟶ f'⁻¹(V)` is affine. The restricted square is cartesian
(`isPullback_resLE_of_isPullback`) and its bottom edge `h ∣_ V^W : W ⟶ V` is a morphism of
affine schemes, hence affine; affineness is stable under base change. -/
@[ega "II 1.2.5" "special case", sga "3 III 0.1.7" "0.1.7(a), special case"]
theorem isAffineHom_resLE_of_isPullback (hsq : IsPullback h' f'' f' h) {V : Y'.Opens}
    [IsAffine (V : Scheme)] {W : Y''.Opens} [IsAffine (W : Scheme)] (hWV : W ≤ h ⁻¹ᵁ V)
    (hle : f'' ⁻¹ᵁ W ≤ h' ⁻¹ᵁ (f' ⁻¹ᵁ V)) :
    IsAffineHom (h'.resLE (f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W) hle) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom)
    (isPullback_resLE_of_isPullback hsq hWV).flip inferInstance

/-- **The pullback map on cohomology over a compatible pair of affine opens.** For a cartesian
square
```
X'' --h'--> X'
|f''        |f'
Y'' --h-->  Y'
```
an affine open `V` of `Y'`, an affine open `W` of `Y''` with `W ≤ h⁻¹(V)`, a quasi-coherent
`𝒪_{X'}`-module `F'` and a degree `n`, the map

`H^n(f'⁻¹(V), F'|) ⟶ H^n(f''⁻¹(W), (h' ∣)^* (F'|))`

of `Γ(f'⁻¹(V), ⊤)`-modules, the target being read through restriction of scalars along
`(h' ∣)^♯`. It is `H^n(f'⁻¹(V), -)` of the unit `F'| ⟶ (h' ∣)_* (h' ∣)^* (F'|)` of the
adjunction `(h' ∣)^* ⊣ (h' ∣)_*`, followed by the inverse of the Leray comparison
`cohomologyPullbackIsoPushforward` along the affine `h' ∣`. There is no hypothesis on `Y'`, on
`Y''`, on `f'` or on `h`: affineness of `h' ∣` comes from affineness of `V` and of `W`, by
`isAffineHom_resLE_of_isPullback`. This is the common target of the two computations in
conclusion (c) of [Stacks, Tag 0EX3] over such a pair of opens. -/
def affineOpenCohomologyPullbackMap (hsq : IsPullback h' f'' f' h) {V : Y'.Opens}
    [IsAffine (V : Scheme)] {W : Y''.Opens} [IsAffine (W : Scheme)] (hWV : W ≤ h ⁻¹ᵁ V)
    (hle : f'' ⁻¹ᵁ W ≤ h' ⁻¹ᵁ (f' ⁻¹ᵁ V)) (F' : X'.Modules) (hF' : F'.IsQuasicoherent) (n : ℕ) :
    ((moduleGlobalSections (f' ⁻¹ᵁ V : Scheme)).rightDerived n).obj
        ((Scheme.Modules.restrictFunctor (f' ⁻¹ᵁ V).ι).obj F') ⟶
      (ModuleCat.restrictScalars
          (h'.resLE (f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W) hle).appTop.hom).obj
        (((moduleGlobalSections (f'' ⁻¹ᵁ W : Scheme)).rightDerived n).obj
          ((Scheme.Modules.pullback (h'.resLE (f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W) hle)).obj
            ((Scheme.Modules.restrictFunctor (f' ⁻¹ᵁ V).ι).obj F'))) :=
  haveI := hF'
  haveI := isAffineHom_resLE_of_isPullback hsq hWV hle
  ((moduleGlobalSections (f' ⁻¹ᵁ V : Scheme)).rightDerived n).map
      ((Scheme.Modules.pullbackPushforwardAdjunction
          (h'.resLE (f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W) hle)).unit.app
        ((Scheme.Modules.restrictFunctor (f' ⁻¹ᵁ V).ι).obj F')) ≫
    (cohomologyPullbackIsoPushforward (h'.resLE (f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W) hle)
      ((Scheme.Modules.restrictFunctor (f' ⁻¹ᵁ V).ι).obj F')
      (Scheme.Modules.isQuasicoherent_restrictFunctor (f' ⁻¹ᵁ V).ι F') n).inv

/-- **The pullback map on cohomology over a pair of affine opens, composed with the Leray
comparison, is `H^n` of the unit.** This is the identity that makes
`affineOpenCohomologyPullbackMap` usable: it says the map is `H^n(f'⁻¹(V), -)` of the unit
`F'| ⟶ (h' ∣)_* (h' ∣)^* (F'|)` and nothing besides, the Leray comparison
`cohomologyPullbackIsoPushforward` being the only other ingredient. -/
theorem affineOpenCohomologyPullbackMap_comp_cohomologyPullbackIsoPushforward_hom
    (hsq : IsPullback h' f'' f' h) {V : Y'.Opens} [IsAffine (V : Scheme)] {W : Y''.Opens}
    [IsAffine (W : Scheme)] (hWV : W ≤ h ⁻¹ᵁ V) (hle : f'' ⁻¹ᵁ W ≤ h' ⁻¹ᵁ (f' ⁻¹ᵁ V))
    (F' : X'.Modules) (hF' : F'.IsQuasicoherent) (n : ℕ) :
    haveI := hF'
    haveI := isAffineHom_resLE_of_isPullback hsq hWV hle
    affineOpenCohomologyPullbackMap hsq hWV hle F' hF' n ≫
        (cohomologyPullbackIsoPushforward (h'.resLE (f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W) hle)
          ((Scheme.Modules.restrictFunctor (f' ⁻¹ᵁ V).ι).obj F')
          (Scheme.Modules.isQuasicoherent_restrictFunctor (f' ⁻¹ᵁ V).ι F') n).hom =
      ((moduleGlobalSections (f' ⁻¹ᵁ V : Scheme)).rightDerived n).map
        ((Scheme.Modules.pullbackPushforwardAdjunction
            (h'.resLE (f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W) hle)).unit.app
          ((Scheme.Modules.restrictFunctor (f' ⁻¹ᵁ V).ι).obj F')) := by
  have := hF'
  have := isAffineHom_resLE_of_isPullback hsq hWV hle
  simp [affineOpenCohomologyPullbackMap]

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
