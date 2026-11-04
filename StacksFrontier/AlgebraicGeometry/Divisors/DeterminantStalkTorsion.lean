module

public import StacksFrontier.Algebra.Module.DoubleDualTorsionQuotient
public import StacksFrontier.AlgebraicGeometry.Divisors.DeterminantStalk

/-!
# The stalk of the determinant module as a torsion-free quotient

At a point whose local ring is a discrete valuation ring the double dual of a finite module is
its torsion-free quotient, so the stalk of the determinant module `(⋀^r F)^∨∨` is
`(⋀^r (F_x)) ⧸ tors`, and the stalk of the determinant comparison map `σ(f, r)` is the map that
`⋀^r (f_x)` induces on torsion-free quotients.

This is the form the determinant bound
`Stacks.OrderOfVanishing.length_quotient_range_torsionQuotientMap_exteriorPower_le_min_of_finrank`
is stated at, so it is what turns that bound into a bound on the cokernel of the stalk of
`σ(f, r)`.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.detStalkTorsionEquiv`: the stalk of `(⋀^r F)^∨∨` as
  `(⋀^r (F_x)) ⧸ tors`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.detStalkTorsionEquiv_stalkHom_detMap`: **the stalk of
  `σ(f, r)` is `Stacks.OrderOfVanishing.torsionQuotientMap (⋀^r (f_x))`.**

## Implementation notes

Both halves are already in the library: `detStalkEquiv_stalkHom_detMap` computes the stalk as a
double transpose and `Stacks.OrderOfVanishing.torsionQuotientDualEquiv_torsionQuotientMap` says
the identification of the double dual with the torsion-free quotient carries the induced map to
that double transpose. Only the composition is new.

## References

* [Stacks Project, Tag 0B3T](https://stacks.math.columbia.edu/tag/0B3T)
* [Stacks Project, Tag 0B36](https://stacks.math.columbia.edu/tag/0B36)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.SheafOfModules.SheafHomStalk

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {F F' : X.Modules}

section Equiv

variable (F) (r : ℕ) (x : X)
  [(exteriorPower F (r : ℤ)).IsFinitePresentation]
  [(dualSheaf (exteriorPower F (r : ℤ))).IsFinitePresentation]
  [IsDomain (ringStalk X.sheaf x)] [IsDedekindDomain (ringStalk X.sheaf x)]
  [Module.Finite (ringStalk X.sheaf x) (⋀[ringStalk X.sheaf x]^r (modStalk F x))]

/-- **The stalk of the determinant module `(⋀^r F)^∨∨` at a point whose local ring is a
Dedekind domain** is the torsion-free quotient of `⋀^r (F_x)`. -/
public def detStalkTorsionEquiv :
    modStalk (reflexiveHull (exteriorPower F (r : ℤ))) x ≃ₗ[ringStalk X.sheaf x]
      (⋀[ringStalk X.sheaf x]^r (modStalk F x) ⧸
        Submodule.torsion (ringStalk X.sheaf x) (⋀[ringStalk X.sheaf x]^r (modStalk F x))) :=
  (detStalkEquiv F r x).trans torsionQuotientDualEquiv.symm

/-- The identification is `detStalkEquiv` composed with the double-dual comparison. -/
public theorem torsionQuotientDualEquiv_detStalkTorsionEquiv
    (Phi : modStalk (reflexiveHull (exteriorPower F (r : ℤ))) x) :
    torsionQuotientDualEquiv (detStalkTorsionEquiv F r x Phi) = detStalkEquiv F r x Phi :=
  (torsionQuotientDualEquiv (R := ringStalk X.sheaf x)).apply_symm_apply _

end Equiv

section Naturality

variable (f : F ⟶ F') (r : ℕ) (x : X)
  [(exteriorPower F (r : ℤ)).IsFinitePresentation]
  [(dualSheaf (exteriorPower F (r : ℤ))).IsFinitePresentation]
  [(exteriorPower F' (r : ℤ)).IsFinitePresentation]
  [(dualSheaf (exteriorPower F' (r : ℤ))).IsFinitePresentation]
  [IsDomain (ringStalk X.sheaf x)] [IsLocalRing (ringStalk X.sheaf x)]
  [IsDiscreteValuationRing (ringStalk X.sheaf x)]
  [Module.Finite (ringStalk X.sheaf x) (⋀[ringStalk X.sheaf x]^r (modStalk F x))]
  [Module.Finite (ringStalk X.sheaf x) (⋀[ringStalk X.sheaf x]^r (modStalk F' x))]
  (Phi : modStalk (reflexiveHull (exteriorPower F (r : ℤ))) x)

/-- **The stalk of the determinant comparison map `σ(f, r)` of [Stacks, Tag 0B3T], read through
`detStalkTorsionEquiv`, is the map `⋀^r (f_x)` induces on torsion-free quotients.** -/
public theorem detStalkTorsionEquiv_stalkHom_detMap :
    detStalkTorsionEquiv F' r x (stalkHom (detMap f (r : ℤ)) x Phi)
      = Stacks.OrderOfVanishing.torsionQuotientMap
          (exteriorPower.map r (stalkHom f x)) (detStalkTorsionEquiv F r x Phi) := by
  refine (torsionQuotientDualEquiv (R := ringStalk X.sheaf x)).injective ?_
  rw [torsionQuotientDualEquiv_detStalkTorsionEquiv,
    Stacks.OrderOfVanishing.torsionQuotientDualEquiv_torsionQuotientMap,
    torsionQuotientDualEquiv_detStalkTorsionEquiv]
  exact detStalkEquiv_stalkHom_detMap f r x Phi

end Naturality

end AlgebraicGeometry.Scheme.Modules

end
