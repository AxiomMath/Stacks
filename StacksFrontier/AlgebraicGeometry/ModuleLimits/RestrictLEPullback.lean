module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.MapDescentTransport
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.RestrictPullbackCoherence
/-!
# Restricting to a smaller open, read as a pullback

`StacksFrontier/AlgebraicGeometry/ModuleLimits/MapDescentTransport.lean` identifies
`Stacks.AlgebraicGeometry.ModuleLimits.restrictHomOfLE` as the conjugate of a morphism by
`Stacks.AlgebraicGeometry.ModuleLimits.restrictLEIso`, the comparison between restricting to `W`
and then to `V ≤ W` and restricting to `V` directly.  That comparison is built out of
`AlgebraicGeometry.Scheme.Modules.restrictFunctorComp`, which is on the *restriction* side of
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`.

Everything that has to be compared with it — `Stacks.Modules.restrictPullbackIso` above all — is
on the *pullback* side.  This file crosses over, using the coherence of
`StacksFrontier/AlgebraicGeometry/ModuleLimits/RestrictPullbackCoherence.lean`: `restrictLEIso`
is the pullback comparison `AlgebraicGeometry.Scheme.Modules.pullbackComp` for
`X.homOfLE e ≫ W.ι = V.ι`, conjugated by `restrictFunctorIsoPullback`.

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.restrictLEIso_hom_restrictFunctorIsoPullback_hom`:
  `restrictLEIso e` is `pullbackComp (X.homOfLE e) W.ι` together with the
  `AlgebraicGeometry.Scheme.Modules.pullbackCongr` for `X.homOfLE e ≫ W.ι = V.ι`, read through
  `restrictFunctorIsoPullback`.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ModuleLimits

open Scheme.Modules

/-- **`restrictLEIso` is the pullback composition comparison.**  For `V ≤ W` in `X`, the
comparison between restricting to `W` and then along `X.homOfLE e` and restricting to `V`
directly is, through `restrictFunctorIsoPullback`, the comparison
`AlgebraicGeometry.Scheme.Modules.pullbackComp (X.homOfLE e) W.ι` followed by the reindexing
along `AlgebraicGeometry.Scheme.homOfLE_ι`.

This is `restrictFunctorIsoPullback_hom_comp_of_eq` at `f := X.homOfLE e`, `g := W.ι` and
`k := V.ι`; it is what lets an equality of restrictions to a smaller open be compared with an
equality of pullbacks. -/
theorem restrictLEIso_hom_restrictFunctorIsoPullback_hom {X : Scheme.{u}} {V W : X.Opens}
    (e : V ≤ W) :
    (restrictLEIso e).hom ≫ (restrictFunctorIsoPullback V.ι).hom =
      Functor.whiskerRight (restrictFunctorIsoPullback W.ι).hom
          (restrictFunctor (X.homOfLE e)) ≫
        Functor.whiskerLeft (pullback W.ι) (restrictFunctorIsoPullback (X.homOfLE e)).hom ≫
          (pullbackComp (X.homOfLE e) W.ι).hom ≫ (pullbackCongr (X.homOfLE_ι e)).hom := by
  rw [restrictLEIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    restrictFunctorIsoPullback_hom_comp_of_eq]

end Stacks.AlgebraicGeometry.ModuleLimits
