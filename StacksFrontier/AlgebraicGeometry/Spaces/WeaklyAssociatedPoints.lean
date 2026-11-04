module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.GeometricPoints
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.Defs

/-!
# Weakly associated points of a module on an algebraic space

Let `X` be an algebraic space and `F` an `𝒪_X`-module. A point `x` of `X` is *weakly
associated* to `F` when, at some geometric point `x̄` lying over `x`, the maximal ideal of the
étale local ring `𝒪_{X, x̄}` is a weakly associated prime of the geometric stalk `F_{x̄}`, that
is, when it is minimal among the primes containing the annihilator of some element of that
stalk. The weakly associated points of `X` itself are those of its structure sheaf.

## Main definitions

* `AlgebraicGeometry.Space.IsWeaklyAssociatedPoint` is the predicate that a point of an
  algebraic space is weakly associated to a module on it.
* `AlgebraicGeometry.Space.weaklyAssociatedPoints` is the set `WeakAss(F)` of weakly
  associated points of a module.
* `AlgebraicGeometry.Space.weaklyAssociatedPointsOfSpace` is the set `WeakAss(X)` of weakly
  associated points of the algebraic space `X`.

## Main results

* `AlgebraicGeometry.Space.mem_weaklyAssociatedPoints_iff` and
  `AlgebraicGeometry.Space.mem_weaklyAssociatedPointsOfSpace_iff` identify membership in the
  two sets with the corresponding pointwise predicate.

## Implementation notes

The ring-theoretic notion is `IsWeaklyAssociatedPrime` of Stacks 0547, which asks for an
element whose annihilator has the given prime as a *minimal* prime; it is therefore weaker
than the associated-prime notion. The scheme-level analogue of the definitions below is
`Stacks.Divisors.IsWeaklyAssociatedPoint` of Stacks 056L, with the Zariski local ring and
stalk replaced by `AlgebraicGeometry.Space.etaleLocalRing` and
`AlgebraicGeometry.Space.geometricModuleStalk`.

The existence of a geometric point above `x` is part of the condition, so a point admitting no
geometric lift is not declared weakly associated vacuously. Both notions are defined for every
`𝒪_X`-module: quasi-coherence is not used to form them, so this is more general than the
source, which states the definition for a quasi-coherent module.

The étale local ring is a local ring by
`AlgebraicGeometry.Space.isLocalRing_etaleLocalRing`, which is a theorem rather than an
instance, so it is supplied by hand; the module structure on the geometric stalk is the one
carried by the object of `ModuleCat`.

## References

* [Stacks Project, Tag 0CTX](https://stacks.math.columbia.edu/tag/0CTX)
* [Stacks Project, Tag 056L](https://stacks.math.columbia.edu/tag/056L)
-/

@[expose] public section

open CategoryTheory

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS)

/-- **Stacks 0CTX, part (1).** A point `x` of an algebraic space `X` is *weakly associated* to
an `𝒪_X`-module `F` when, at some geometric point above `x`, the maximal ideal of the étale
local ring is a weakly associated prime of the geometric stalk of `F`, that is, when it is
minimal among the primes containing the annihilator of some element of that stalk. -/
@[stacks 0CTX "weakly associated point"]
noncomputable def IsWeaklyAssociatedPoint (F : Modules.{u, m} B S hS X.1 X.2)
    (x : points B S hS X.1) : Prop :=
  ∃ xbar : GeometricPoint B S hS X.1,
    xbar.LiesOver x ∧
      let R := etaleLocalRing B S hS X.1 xbar
      let M := geometricModuleStalk B S hS X xbar F
      letI : IsLocalRing R := isLocalRing_etaleLocalRing B S hS X.1 X.2 xbar
      letI : Module R M := M.isModule
      IsWeaklyAssociatedPrime R M (IsLocalRing.maximalIdeal R)

/-- **Stacks 0CTX, part (2).** The set `WeakAss(F)` of points of an algebraic space weakly
associated to an `𝒪_X`-module `F`. -/
@[stacks 0CTX "set of weakly associated points"]
noncomputable abbrev weaklyAssociatedPoints (F : Modules.{u, m} B S hS X.1 X.2) :
    Set (points B S hS X.1) :=
  {x | IsWeaklyAssociatedPoint B S hS X F x}

/-- Membership in the weakly associated points of a module is the weakly associated point
predicate. -/
@[simp]
theorem mem_weaklyAssociatedPoints_iff (F : Modules.{u, m} B S hS X.1 X.2)
    (x : points B S hS X.1) :
    x ∈ weaklyAssociatedPoints B S hS X F ↔ IsWeaklyAssociatedPoint B S hS X F x :=
  Iff.rfl

/-- **Stacks 0CTX, part (3).** The weakly associated points `WeakAss(X)` of an algebraic space
`X` are the weakly associated points of its structure sheaf. -/
@[stacks 0CTX "weakly associated points of the space"]
noncomputable abbrev weaklyAssociatedPointsOfSpace : Set (points B S hS X.1) :=
  weaklyAssociatedPoints B S hS X
    (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)))

/-- A point is weakly associated to an algebraic space exactly when it is weakly associated to
its structure sheaf. -/
@[simp]
theorem mem_weaklyAssociatedPointsOfSpace_iff (x : points B S hS X.1) :
    x ∈ weaklyAssociatedPointsOfSpace B S hS X ↔
      IsWeaklyAssociatedPoint B S hS X
        (SheafOfModules.unit
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))) x :=
  Iff.rfl

end AlgebraicGeometry.Space

end
