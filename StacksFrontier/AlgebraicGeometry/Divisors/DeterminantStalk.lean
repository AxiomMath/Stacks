module

public import StacksFrontier.AlgebraicGeometry.Modules.DualSheafStalk.Naturality
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerStalkNaturality
public import StacksFrontier.AlgebraicGeometry.Divisors.DeterminantComparison

/-!
# The stalk of the determinant comparison map

`StacksFrontier.AlgebraicGeometry.Divisors.DeterminantComparison` builds the comparison map

`σ(f, r) : (⋀^r F)^∨∨ ⟶ (⋀^r F')^∨∨`

of determinant modules attached to a morphism `f : F ⟶ F'`, as `doubleDualMap` of
`exteriorPowerMap`. This file computes its stalk: under the identification of the stalk of a
determinant module with the double `𝒪_{X,x}`-dual of `⋀^r (F_x)`, the stalk of `σ(f, r)` is the
double transpose of `⋀^r` of the stalk map of `f`.

Both halves were already in the library and are only composed here: the exterior-power half is
`Stacks.SheafOfModules.exteriorPowerStalkEquiv_naturality` and the reflexive-hull half is
`Stacks.AlgebraicGeometry.ReflexiveModules.dualEvalEquiv_stalkHom_doubleDualMap`.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.exteriorPowerModStalkEquiv`: Tag 01CH for the exterior power
  of a module on a scheme, at the `modStalk` spelling of the stalk.
* `AlgebraicGeometry.Scheme.Modules.detStalkEquiv`: the stalk of `(⋀^r F)^∨∨` as the double dual
  of `⋀^r (F_x)`.

## Main results

* `Stacks.AlgebraicGeometry.ReflexiveModules.stalkHom_eq_stalkMapL`: the two stalk-map
  constructions of the library agree.
* `AlgebraicGeometry.Scheme.Modules.detStalkEquiv_stalkHom_detMap`: **the stalk of `σ(f, r)` is
  the double transpose of `⋀^r (f_x)`.**

## Implementation notes

**Two stalk maps.** The reflexive-hull development induces a map of stalks as
`Stacks.AlgebraicGeometry.ReflexiveModules.stalkHom`, built from the slice-site
`SheafHomStalk.stalkLinearMap`; the exterior-power development uses
`PresheafOfModules.stalkMapL` applied to `SheafOfModules.SymPresentation.valHom`. The two are
not definitionally equal at the transparency `rfl` works at, because the colimit defining the
stalk is not exposed, but both send the germ of a section to the germ of its image, so
`stalkHom_eq_stalkMapL` identifies them by a germ chase.

**`congrArg`, not `rw`.** Rewriting with `stalkHom_eq_stalkMapL` or with
`dualEvalEquiv_stalkHom_doubleDualMap` underneath the stalk comparison exhausts the
heartbeat budget at `isDefEq` while `rw` unifies its motive; the same steps as `congrArg` and
`DFunLike.congr_fun`, which supply the motive, elaborate in seconds.

**No `@[stacks]` attribute.** This computes the stalk of `σ`; it asserts neither clause of Tag
0B3T. Identifying the divisor of `σ` with a bounded multiple of the given one is the clause this
is an input to, and it is not proved here.

## References

* [Stacks Project, Tag 01CH](https://stacks.math.columbia.edu/tag/01CH)
* [Stacks Project, Tag 01CP](https://stacks.math.columbia.edu/tag/01CP)
* [Stacks Project, Tag 0B3T](https://stacks.math.columbia.edu/tag/0B3T)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open SheafOfModules.SymPresentation (valHom)

universe u

namespace Stacks.AlgebraicGeometry.ReflexiveModules

open Stacks.SheafOfModules.SheafHomStalk

variable {X : Scheme.{u}} {F F' : X.Modules}

/-- **The library's two stalk maps of a morphism of modules agree.** `stalkHom` and
`PresheafOfModules.stalkMapL` of `valHom` both send a germ to the germ of its image. -/
public theorem stalkHom_eq_stalkMapL (f : F ⟶ F') (x : X) (m : modStalk F x) :
    stalkHom f x m = PresheafOfModules.stalkMapL x (valHom f) m := by
  obtain ⟨W, hxW, t, rfl⟩ := exists_germ_eq F m
  rw [stalkHom_germAt f x W hxW t]
  exact (PresheafOfModules.stalkMapL_germ x (valHom f) W hxW t).symm

end Stacks.AlgebraicGeometry.ReflexiveModules

namespace AlgebraicGeometry.Scheme.Modules

open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.SheafOfModules.SheafHomStalk

variable {X : Scheme.{u}} {F F' : X.Modules}

/-- **Tag 01CH for the exterior power of a module on a scheme**: the stalk at `x` of `⋀^r F` is
`⋀^r` of the stalk of `F`, at the `modStalk` spelling. -/
public def exteriorPowerModStalkEquiv (F : X.Modules) (r : ℕ) (x : X) :=
  SheafOfModules.exteriorPowerStalkEquiv (exteriorAlgebra F) (exteriorGenerator F)
    (isExteriorAlgebra_exteriorAlgebra F) r x

section Naturality

variable (f : F ⟶ F') (r : ℕ) (x : X) (q : modStalk (exteriorPower F (r : ℤ)) x)

/-- **The stalk of `⋀^r f` is `⋀^r` of the stalk map of `f`**, at the `stalkHom` spelling of the
stalk map. This is `Stacks.SheafOfModules.exteriorPowerStalkEquiv_naturality` read through
`stalkHom_eq_stalkMapL`. -/
public theorem exteriorPowerModStalkEquiv_stalkHom_exteriorPowerMap :
    exteriorPowerModStalkEquiv F' r x (stalkHom (exteriorPowerMap f (r : ℤ)) x q)
      = exteriorPower.map r (stalkHom f x) (exteriorPowerModStalkEquiv F r x q) := by
  refine Eq.trans (congrArg (exteriorPowerModStalkEquiv F' r x)
    (stalkHom_eq_stalkMapL (exteriorPowerMap f (r : ℤ)) x q)) ?_
  refine Eq.trans (SheafOfModules.exteriorPowerStalkEquiv_naturality
    (isExteriorAlgebra_exteriorAlgebra F) (isExteriorAlgebra_exteriorAlgebra F') f r x q) ?_
  exact congrArg (fun k => exteriorPower.map r k (exteriorPowerModStalkEquiv F r x q))
    (LinearMap.ext fun m => (stalkHom_eq_stalkMapL f x m).symm)

end Naturality

/-- **The stalk of the determinant module `(⋀^r F)^∨∨`** at `x` is the double `𝒪_{X,x}`-dual of
`⋀^r (F_x)`: Tag 01CP at `⋀^r F` and at its dual, composed with Tag 01CH. -/
public def detStalkEquiv (F : X.Modules) (r : ℕ) (x : X)
    [(exteriorPower F (r : ℤ)).IsFinitePresentation]
    [(dualSheaf (exteriorPower F (r : ℤ))).IsFinitePresentation] :
    modStalk (reflexiveHull (exteriorPower F (r : ℤ))) x ≃ₗ[ringStalk X.sheaf x]
      Module.Dual (ringStalk X.sheaf x) (Module.Dual (ringStalk X.sheaf x)
        (⋀[ringStalk X.sheaf x]^r (modStalk F x))) :=
  (dualEvalEquiv (exteriorPower F (r : ℤ)) x).trans
    (exteriorPowerModStalkEquiv F r x).dualMap.dualMap

section Det

variable (f : F ⟶ F') (r : ℕ) (x : X)
  [(exteriorPower F (r : ℤ)).IsFinitePresentation]
  [(dualSheaf (exteriorPower F (r : ℤ))).IsFinitePresentation]
  [(exteriorPower F' (r : ℤ)).IsFinitePresentation]
  [(dualSheaf (exteriorPower F' (r : ℤ))).IsFinitePresentation]
  (Phi : modStalk (reflexiveHull (exteriorPower F (r : ℤ))) x)

/-- **The stalk of the determinant comparison map `σ(f, r)` of [Stacks, Tag 0B3T] is the double
transpose of `⋀^r` of the stalk map of `f`.** Read through `detStalkEquiv` at `F` and at `F'`,
the stalk at `x` of `σ(f, r) : (⋀^r F)^∨∨ ⟶ (⋀^r F')^∨∨` is the double `𝒪_{X,x}`-linear
transpose of `⋀^r (f_x)`. -/
public theorem detStalkEquiv_stalkHom_detMap :
    detStalkEquiv F' r x (stalkHom (detMap f (r : ℤ)) x Phi)
      = Module.Dual.transpose (Module.Dual.transpose (exteriorPower.map r (stalkHom f x)))
          (detStalkEquiv F r x Phi) := by
  have key := dualEvalEquiv_stalkHom_doubleDualMap (exteriorPowerMap f (r : ℤ)) x Phi
  refine LinearMap.ext fun psi => ?_
  refine (DFunLike.congr_fun key ((exteriorPowerModStalkEquiv F' r x).dualMap psi)).trans ?_
  exact congrArg (dualEvalEquiv (exteriorPower F (r : ℤ)) x Phi)
    (LinearMap.ext fun q =>
      congrArg psi (exteriorPowerModStalkEquiv_stalkHom_exteriorPowerMap f r x q))

end Det

end AlgebraicGeometry.Scheme.Modules

end
