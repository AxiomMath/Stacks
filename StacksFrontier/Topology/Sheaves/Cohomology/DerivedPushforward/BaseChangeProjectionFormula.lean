module

public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeProjectionFormula
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangeMap
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangeMapAsMap

/-!
# `Rg_*` of the derived base change map is a projection-formula map

For a commutative square of ringed spaces

```
X' --g'--> X
|          |
f'         f
v          v
S' --g-->  S
```

the derived base change map of [Stacks, Tag 08HY] is a morphism
`Lg^*(Rf_*K) ⟶ Rf'_*(L(g')^*K)`.  Applying `Rg_*` to it gives a morphism

`Rg_*Lg^*(Rf_*K) ⟶ Rg_*Rf'_*(L(g')^*K)`,

and this file identifies it: it is the projection-formula morphism of the adjunction
`Lf^* ⊣ Rf_*` attached to the canonical comparison

`Lf^* ⋙ (Rg_*Lg^*) ⟶ (Rg'_*L(g')^*) ⋙ Lf^*`,

followed by the conjugate isomorphism `Rf_*Rg'_* ≅ Rg_*Rf'_*` of the two iterated derived
pushforwards.

## Main results

* `Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap_eq_baseChangeMap` — the derived
  base change map is the base change map of its square of adjunctions.
* `Stacks.Cohomology.DerivedBaseChange.derivedPushforward_map_derivedBaseChangeMap_eq` — `Rg_*`
  of the derived base change map is the projection-formula morphism followed by the conjugate
  isomorphism.
* `Stacks.Cohomology.DerivedBaseChange.isIso_derivedPushforward_map_derivedBaseChangeMap_iff` —
  `Rg_*` of the derived base change map is invertible if and only if the projection-formula
  morphism is.

## References

* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
* [Stacks Project, Tag 08I9](https://stacks.math.columbia.edu/tag/08I9)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open RingedSpaceModuleAdjunction Stacks.DerivedPullback.Composition
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward
  derivedAdjunction)

namespace Stacks.Cohomology.DerivedBaseChange

universe u

attribute [local instance] HasDerivedCategory.standard

noncomputable section

variable {X' X S' S : RingedSpace.{u, u}}
  (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S) (sq : g' ≫ f = f' ≫ g)

/-- The derived base change map of [Stacks, Tag 08HY] is the base change map of its square of
adjunctions `Lf^* ⊣ Rf_*` and `L(f')^* ⊣ Rf'_*`, formed with the comparison of the two iterated
derived pullbacks around the square. -/
alias derivedBaseChangeMap_eq_baseChangeMap := derivedBaseChangeMap_eq_map

/-- For a commutative square of ringed spaces, the direct image under `g` of the derived base
change map of [Stacks, Tag 08HY] at `K` is the projection-formula morphism of `Lf^* ⊣ Rf_*`
attached to the canonical comparison `Lf^* ⋙ Rg_*Lg^* ⟶ Rg'_*L(g')^* ⋙ Lf^*`, followed by the
conjugate isomorphism `Rf_*Rg'_* ≅ Rg_*Rf'_*`. -/
theorem derivedPushforward_map_derivedBaseChangeMap_eq
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (derivedPushforward g).map (derivedBaseChangeMap g' f' f g sq K) =
      (Stacks.CategoryTheory.BaseChange.projectionTwoSquare (derivedAdjunction f)
          (derivedAdjunction g) (derivedAdjunction g')
          (derivedPullbackCompIsoLeft g' f' f g sq)
          (derivedPullbackCompIsoCanonical g' f)).app K ≫
        (Stacks.CategoryTheory.BaseChange.rightCompositeIso (derivedAdjunction f)
          (derivedAdjunction f') (derivedAdjunction g) (derivedAdjunction g')
          (derivedPullbackCompIsoLeft g' f' f g sq)
          (derivedPullbackCompIsoCanonical g' f)).hom.app
            ((derivedPullback g').obj K) := by
  rw [derivedBaseChangeMap_eq_baseChangeMap]
  exact Stacks.CategoryTheory.BaseChange.pushforward_map_eq (derivedAdjunction f)
    (derivedAdjunction f') (derivedAdjunction g) (derivedAdjunction g')
    (derivedPullbackCompIsoLeft g' f' f g sq) (derivedPullbackCompIsoCanonical g' f) K

/-- The direct image under `g` of the derived base change map at `K` is invertible if and only
if the projection-formula morphism of `Lf^* ⊣ Rf_*` at `K` is. -/
theorem isIso_derivedPushforward_map_derivedBaseChangeMap_iff
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    IsIso ((derivedPushforward g).map (derivedBaseChangeMap g' f' f g sq K)) ↔
      IsIso ((Stacks.CategoryTheory.BaseChange.projectionTwoSquare (derivedAdjunction f)
        (derivedAdjunction g) (derivedAdjunction g')
        (derivedPullbackCompIsoLeft g' f' f g sq)
        (derivedPullbackCompIsoCanonical g' f)).app K) := by
  rw [derivedBaseChangeMap_eq_baseChangeMap]
  exact Stacks.CategoryTheory.BaseChange.isIso_pushforward_map_iff (derivedAdjunction f)
    (derivedAdjunction f') (derivedAdjunction g) (derivedAdjunction g')
    (derivedPullbackCompIsoLeft g' f' f g sq) (derivedPullbackCompIsoCanonical g' f) K

end

end Stacks.Cohomology.DerivedBaseChange

end
