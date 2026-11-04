module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finite
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Twist
public import StacksFrontier.AlgebraicGeometry.FiberRank.GenericPoint
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.HyperplaneTwistSequence
public import StacksFrontier.RingTheory.Depth.AssociatedPrime

/-!
# Depth, twisting, and the associated points of a coherent module

Let `X` be a scheme and let `F` be a coherent `𝒪_X`-module. A point at which the stalk `F_x`
has depth at least one along the maximal ideal `𝔪_x` is not an associated point of `F`. On a
quasi-compact locally Noetherian scheme a coherent module has only finitely many associated
points; if the stalk has depth at least two at every closed point then no associated point is
closed; and the associated points are unchanged by twisting by an integer tensor power of an
invertible module.

## Main results

* `Stacks.Divisors.notMem_associatedPoints_of_one_le_depth`: depth at least one at `x` rules
  out `x` being an associated point.
* `Stacks.Divisors.associatedPoints_finite`: a coherent module on a quasi-compact locally
  Noetherian scheme has finitely many associated points.
* `Stacks.Divisors.not_isClosed_singleton_of_mem_associatedPoints`: under depth at least two at
  every closed point, no associated point of `F` is a closed point.
* `Stacks.Divisors.associatedPoints_tensorPowModule_eq`: `Ass(ℱ(d)) = Ass(ℱ)` for the twists by
  the integer tensor powers of an invertible module.

## References

* [Stacks Project, Tag 00LI](https://stacks.math.columbia.edu/tag/00LI)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 02OJ](https://stacks.math.columbia.edu/tag/02OJ)
* [Stacks Project, Tag 05AF](https://stacks.math.columbia.edu/tag/05AF)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}}

/-- A point at which the stalk of a coherent module has depth at least one along the maximal
ideal of the local ring is not an associated point of that module. -/
theorem notMem_associatedPoints_of_one_le_depth (F : X.Modules) [F.IsCoherent] (x : X)
    (h : (1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x)) :
    x ∉ Stacks.Divisors.associatedPoints F := fun hx ↦
  have : Module.Finite (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
    AlgebraicGeometry.Scheme.Modules.finite_stalk_of_isCoherent F x
  maximalIdeal_not_isAssociatedPrimeStacks_of_one_le_depth h hx

/-- **`Ass(ℱ(d)) = Ass(ℱ)`.** Twisting by an integer tensor power of an invertible module does
not change the associated points. -/
theorem associatedPoints_tensorPowModule_eq (L F : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (d : ℤ) :
    Stacks.Divisors.associatedPoints
        (Stacks.AlgebraicGeometry.HyperplaneTwistSequence.twistModule X L F d) =
      Stacks.Divisors.associatedPoints F :=
  have : Stacks.Ample.IsInvertibleModule X (Stacks.Ample.tensorPowModule X L d) :=
    Stacks.Ample.isInvertibleModule_tensorPowModule X L d
  associatedPoints_tensorModules_eq_of_isInvertibleModule F
    (Stacks.Ample.tensorPowModule X L d)

/-- A coherent module on a quasi-compact locally Noetherian scheme has only finitely many
associated points. -/
theorem associatedPoints_finite (F : X.Modules) [IsLocallyNoetherian X] [F.IsCoherent]
    [CompactSpace X] : (Stacks.Divisors.associatedPoints F).Finite := by
  simpa using AlgebraicGeometry.associatedPoints_inter_finite F ⊤
    (by simpa using CompactSpace.isCompact_univ (X := X))

/-- If the stalk of a coherent module has depth at least two at every closed point of `X`, then
no associated point of that module is a closed point. -/
theorem not_isClosed_singleton_of_mem_associatedPoints (F : X.Modules) [IsLocallyNoetherian X]
    [F.IsCoherent]
    (hdepth : ∀ x : X, IsClosed ({x} : Set X) → (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x))
    {x : X} (hx : x ∈ Stacks.Divisors.associatedPoints F) :
    ¬ IsClosed ({x} : Set X) := fun hcl ↦
  notMem_associatedPoints_of_one_le_depth F x (le_trans (by norm_num) (hdepth x hcl)) hx

end Stacks.Divisors

end
