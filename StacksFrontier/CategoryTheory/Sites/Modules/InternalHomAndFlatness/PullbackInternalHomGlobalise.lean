module

/-
Copyright (c) 2026 the Stacks in Lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.PullbackInternalHomLocal
public import StacksFrontier.AlgebraicGeometry.QcohRestrictEquiv.IsoLocality
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Globalising the internal Hom comparison from a covering

The canonical map of Stacks 0GMX is a morphism of sheaves of modules, so its invertibility is
local on the source site. Tag 03DL supplies a covering of the final object by the images of the
objects over which `F` admits a finite global presentation, so invertibility over each member of
that covering suffices.

This module records that last step and nothing else. The hypothesis is the invertibility of the
*restriction* of the canonical map to each member of the covering; it is deliberately left as a
hypothesis, so what is proved here is a reduction and not a carrier of Stacks 0GN2. The tag
belongs on whatever declaration eventually discharges that hypothesis, not here.

## Main results

* `Stacks.SheafOfModules.InternalHom.isIso_pullbackInternalHomMap_of_isIso_over`: the
  local-to-global step, under the source's own hypothesis `F.IsFinitePresentationOnSite`.

## References

* [Stacks Project, Tag 0GMX](https://stacks.math.columbia.edu/tag/0GMX)
* [Stacks Project, Tag 0GN2](https://stacks.math.columbia.edu/tag/0GN2)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace Stacks.SheafOfModules.InternalHom

universe u

section Globalise

variable {X Y : AlgebraicGeometry.RingedSite.{u, u, u}} (f : AlgebraicGeometry.RingedSite.Hom X Y)
  (F G : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))

/-- **The local-to-global step for Stacks 0GN2.** If the restriction of the canonical map of
Stacks 0GMX to the slice site over each `u(V)`, for `V` carrying a finite global presentation of
`F`, is invertible, then the canonical map is invertible.

The covering is `coversTop_obj_hasFiniteGlobalPresentation`, which is where the source's
hypothesis that `F` is of finite presentation in the sense of Tag 03DL is used, and locality of
invertibility for a morphism of sheaves of modules is
`Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_over`.

This is a **reduction**, not a carrier: the invertibility of the restrictions is a hypothesis
here, so this declaration carries no `@[stacks]` registration. -/
@[ega "0 6.7.6" "partial"]
public theorem isIso_pullbackInternalHomMap_of_isIso_over
    [F.IsFinitePresentationOnSite]
    (hres : ∀ V : {V : Y.C //
        _root_.SheafOfModules.HasFiniteGlobalPresentation (F.over V)},
      IsIso ((pullbackInternalHomMap f F G).over (f.u.obj V.val))) :
    IsIso (pullbackInternalHomMap f F G) :=
  Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_over
    (coversTop_obj_hasFiniteGlobalPresentation f F) _ hres

end Globalise

end Stacks.SheafOfModules.InternalHom

end
