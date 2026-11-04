module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcAffine
public import StacksFrontier.AlgebraicGeometry.Descent.ProperFpqcLocalAtTarget

/-!
# Integral and finite morphisms are fpqc local on the base

A morphism of schemes is integral precisely when its base changes along the members of an fpqc
covering of the target are integral, and likewise for finiteness.

## Main results

* `AlgebraicGeometry.isIntegralHom_isLocalAtTarget_fpqc`: being integral is fpqc local on the
  base.
* `AlgebraicGeometry.isFinite_isLocalAtTarget_fpqc`: being finite is fpqc local on the base.

## Implementation notes

Both statements are decompositions into properties already known to be fpqc local. An integral
morphism is one which is universally closed and affine
(`AlgebraicGeometry.IsIntegralHom.eq_universallyClosed_inf_isAffineHom`), and a finite morphism
is one which is integral and locally of finite type (`AlgebraicGeometry.IsFinite.eq_inf`); fpqc
locality is stable under infima of morphism properties.

## References

* [Stacks Project, Tag 02L9](https://stacks.math.columbia.edu/tag/02L9)
* [Stacks Project, Tag 02LA](https://stacks.math.columbia.edu/tag/02LA)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- **Stacks Project, Tag 02L9.** Integral morphisms of schemes are fpqc local on the
target. -/
@[ega "IV 2.7.1" "more general", sga "1 VIII 5.7" "more general", sga "4 IV 8.5.5"]
instance isIntegralHom_isLocalAtTarget_fpqc :
    MorphismProperty.IsLocalAtTarget
      (@IsIntegralHom : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage := by
  rw [IsIntegralHom.eq_universallyClosed_inf_isAffineHom]
  exact .inf _ _

/-- **Stacks Project, Tag 02LA.** Finite morphisms of schemes are fpqc local on the target. -/
@[ega "II 6.3.10" "more general", sga "4 IV 8.5.5"]
instance isFinite_isLocalAtTarget_fpqc :
    MorphismProperty.IsLocalAtTarget
      (@IsFinite : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage := by
  rw [IsFinite.eq_inf]
  exact .inf _ _

end AlgebraicGeometry

end
