module

public import StacksFrontier.Topology.Sheaves.RingedSpace.Thickening
public import Mathlib.CategoryTheory.Functor.EpiMono
import StacksCore.Tactic.StacksAttribute

/-!
# Strict morphisms of thickenings of ringed spaces

In the situation of Stacks 08KZ — a commutative square

```
X  --i-->  X'
|          |
f          f'
v          v
S  --t-->  S'
```

of ringed spaces whose horizontal arrows are thickenings, with kernel ideal sheaves
`I = ker(i^♯)` on `X'` and `J = ker(t^♯)` on `S'` — the square carries a canonical map
`(f')^* J ⟶ I`, recorded as `MorphismOfThickenings.idealMap`. The square is called *strict*
when that map is surjective, which is `MorphismOfThickenings.IsStrict`.

For a strict square, the *reduced* form of the canonical ideal map, `f^* t^* J ⟶ i^* I`, is again
surjective.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.MorphismOfThickenings.baseToSourceIdeal`: the
  canonical ideal map read on the reduced source, `f^* t^* J ⟶ i^* I`.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.MorphismOfThickenings.epi_baseToSourceIdeal`: a
  strict square has surjective reduced canonical ideal map.

## References

* [Stacks Project, Tag 08L1](https://stacks.math.columbia.edu/tag/08L1)
* [Stacks Project, Tag 08KZ](https://stacks.math.columbia.edu/tag/08KZ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry.RingedSpaceThickening.MorphismOfThickenings

/-- A morphism of thickenings is strict if and only if its canonical ideal map `(f')^* J ⟶ I` is
an epimorphism. -/
lemma isStrict_iff (D : MorphismOfThickenings.{u}) :
    D.IsStrict ↔ Epi D.idealMap.1 :=
  Iff.rfl

/-- The canonical ideal map read on the reduced source: `f^* t^* J ⟶ i^* I`, obtained from
`MorphismOfThickenings.idealMap` by pulling back along `i` and undoing
`MorphismOfThickenings.reducedPullbackComparison`. -/
noncomputable def baseToSourceIdeal (D : MorphismOfThickenings.{u}) :
    (modulePullback D.f).obj ((modulePullback D.t).obj D.idealJ) ⟶
      (modulePullback D.i).obj D.idealI :=
  D.reducedPullbackComparison.inv ≫ (modulePullback D.i).map D.idealMap.1

/-- Module pullback along a morphism of ringed spaces is a left adjoint. -/
lemma isLeftAdjoint_modulePullback {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) :
    (modulePullback f).IsLeftAdjoint :=
  let _hadj : (SheafOfModules.pushforward (structureSheafHom f)).IsRightAdjoint :=
    modulePushforward_isRightAdjoint f
  (modulePullbackPushforwardAdjunction f).isLeftAdjoint

/-- For a strict morphism of thickenings the reduced canonical ideal map `f^* t^* J ⟶ i^* I` is
surjective. -/
@[stacks 08L1 "surjectivity of the reduced canonical ideal map"]
theorem epi_baseToSourceIdeal (D : MorphismOfThickenings.{u}) (hs : D.IsStrict) :
    Epi D.baseToSourceIdeal := by
  have : Epi D.idealMap.1 := hs
  have : (modulePullback D.i).IsLeftAdjoint := isLeftAdjoint_modulePullback D.i
  have : Epi ((modulePullback D.i).map D.idealMap.1) :=
    (modulePullback D.i).map_epi _
  exact epi_comp _ _

end AlgebraicGeometry.RingedSpaceThickening.MorphismOfThickenings

end
