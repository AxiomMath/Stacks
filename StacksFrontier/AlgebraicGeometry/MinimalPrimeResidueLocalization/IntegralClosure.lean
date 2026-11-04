module

public import Mathlib.RingTheory.Localization.Integral
public import StacksCore.Tactic.StacksAttribute

/-!
# The algebra structure that makes integral closure commute with localization

Given towers `IsScalarTower R S Sf` and `IsScalarTower R Rf Sf`, the restriction of
`algebraMap S Sf` makes `integralClosure Rf Sf` an algebra over `integralClosure R S`, compatible
with the inclusions into `Sf` and with the maps from `R`. When `Rf` is the localization of `R` at
a submonoid `M` and `Sf` that of `S` at the image of `M`, this presents `integralClosure Rf Sf` as
the localization of `integralClosure R S` at the image of `M`.

## Main definitions

* `Stacks.IntegralClosureLocalization.integralClosureMap`: the comparison ring homomorphism
  `integralClosure R S →+* integralClosure Rf Sf`, namely `algebraMap S Sf` restricted.
* `Stacks.IntegralClosureLocalization.integralClosureAlgebra`: the algebra structure it defines.

## Main results

* `Stacks.IntegralClosureLocalization.isScalarTower_integralClosure_right` and
  `Stacks.IntegralClosureLocalization.isScalarTower_integralClosure_left`: the comparison algebra
  structure is compatible with the inclusions into `Sf` and with the maps from `R`.
* `Stacks.IntegralClosureLocalization.isScalarTower_integralClosure_base`: the maps from `R` into
  `integralClosure Rf Sf` factor through `Rf`.
* `Stacks.IntegralClosureLocalization.isLocalization_integralClosure`: `integralClosure Rf Sf` is
  the localization of `integralClosure R S` at the image of `M`.

## References

* [Stacks Project, Tag 0307](https://stacks.math.columbia.edu/tag/0307)
* [Stacks Project, Tag 0C3B](https://stacks.math.columbia.edu/tag/0C3B)
-/

@[expose] public noncomputable section

universe u

namespace Stacks.IntegralClosureLocalization

variable (R : Type u) [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
variable (Rf : Type u) [CommRing Rf] [Algebra R Rf]
variable (Sf : Type u) [CommRing Sf] [Algebra S Sf] [Algebra Rf Sf] [Algebra R Sf]
variable [IsScalarTower R S Sf] [IsScalarTower R Rf Sf]

/-- The comparison map between the two integral closures: the restriction of `algebraMap S Sf`,
which carries elements integral over `R` to elements integral over `Rf`. -/
public noncomputable def integralClosureMap :
    ↥(integralClosure R S) →+* ↥(integralClosure Rf Sf) :=
  ((algebraMap S Sf).comp (integralClosure R S).val.toRingHom).codRestrict
    (integralClosure Rf Sf) fun y ↦
      (IsIntegral.map (IsScalarTower.toAlgHom R S Sf) y.2).tower_top

/-- The algebra structure of `integralClosure R S` on `integralClosure Rf Sf` given by
`integralClosureMap`. -/
@[instance_reducible]
public noncomputable def integralClosureAlgebra :
    Algebra ↥(integralClosure R S) ↥(integralClosure Rf Sf) :=
  (integralClosureMap R S Rf Sf).toAlgebra

/-- The comparison algebra structure is compatible with the inclusions into `Sf`. -/
public theorem isScalarTower_integralClosure_right :
    letI := integralClosureAlgebra R S Rf Sf
    IsScalarTower ↥(integralClosure R S) ↥(integralClosure Rf Sf) Sf :=
  let := integralClosureAlgebra R S Rf Sf
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- The comparison algebra structure is compatible with the maps from `R`. -/
public theorem isScalarTower_integralClosure_left :
    letI := integralClosureAlgebra R S Rf Sf
    IsScalarTower R ↥(integralClosure R S) ↥(integralClosure Rf Sf) :=
  let := integralClosureAlgebra R S Rf Sf
  IsScalarTower.of_algebraMap_eq fun a ↦
    Subtype.ext (IsScalarTower.algebraMap_apply R S Sf a)

/-- The maps from `R` into `integralClosure Rf Sf` factor through `Rf`. -/
public theorem isScalarTower_integralClosure_base :
    IsScalarTower R Rf ↥(integralClosure Rf Sf) :=
  IsScalarTower.of_algebraMap_eq fun a ↦
    Subtype.ext (IsScalarTower.algebraMap_apply R Rf Sf a)

/-- Integral closure commutes with localization: if `Rf` is the localization of `R` at `M` and
`Sf` the localization of `S` at the image of `M`, then `integralClosure Rf Sf` is the localization
of `integralClosure R S` at the image of `M`. -/
@[stacks 0307]
public theorem isLocalization_integralClosure (M : Submonoid R) [IsLocalization M Rf]
    [IsLocalization (Algebra.algebraMapSubmonoid S M) Sf] :
    letI := integralClosureAlgebra R S Rf Sf
    IsLocalization (Algebra.algebraMapSubmonoid ↥(integralClosure R S) M)
      ↥(integralClosure Rf Sf) :=
  let := integralClosureAlgebra R S Rf Sf
  let := isScalarTower_integralClosure_right R S Rf Sf
  let := isScalarTower_integralClosure_left R S Rf Sf
  IsLocalization.integralClosure M

end Stacks.IntegralClosureLocalization

end
