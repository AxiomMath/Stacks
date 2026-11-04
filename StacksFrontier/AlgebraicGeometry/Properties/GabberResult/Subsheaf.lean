module

public import StacksFrontier.AlgebraicGeometry.CardinalGeneratedColimit.Basic

/-!
# The sections over an affine open of the subsheaf cut out by a compatible family

Let `N` be a compatible family of submodules of the sections of a quasi-coherent module `F` over
the affine opens of a scheme. Over an affine open `U`, the sections of `F` lying locally in `N`
are exactly `N U`.

## Main results

* `Stacks.AlgebraicGeometry.GabberColimit.localSections_eq`: for an affine open `U`, the sections
  of `F` over `U` lying locally in `N` are exactly `N U`.

## References

* [Stacks Project, Tag 077N](https://stacks.math.columbia.edu/tag/077N)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.GabberColimit

variable {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent]
  (N : ∀ U : X.affineOpens, Submodule Γ(X, U.1) Γ(F, U.1)) (hN : IsCompatible F N)

include hN in
/-- The sections of the subsheaf cut out by a compatible family over an affine open `U` are
exactly `N U`. -/
theorem localSections_eq (U : X.affineOpens) : localSections F N U.1 = N U :=
  obj_sheafSubmodule F N hN U

end Stacks.AlgebraicGeometry.GabberColimit

end
