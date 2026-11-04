module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.GenericPoints
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Reduced
public import StacksFrontier.AlgebraicGeometry.Meromorphic.NoEmbeddedPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierPullbackCriteria

/-!
# Corollaries of the weakly associated point criterion for pullback of a divisor

Let `f : X ⟶ Y` be a morphism of schemes and `D ⊆ Y` an effective Cartier divisor.  The pullback
of `D` along `f` is defined as soon as `f` carries no weakly associated point of `X` into the
support of `D`.  Collected here are the four cases of the source which follow from that
criterion: a reduced source whose generic points avoid the support, a dominant morphism of
integral schemes, a locally Noetherian source read through its associated points, and a locally
Noetherian source without embedded points.

## Main results

* `Stacks.Divisors.isPullbackDefined_of_isReduced`: **Stacks 02OO (3)**, a reduced source.
* `Stacks.Divisors.isPullbackDefined_of_isDominant`: **Stacks 02OO (2)**, a dominant morphism of
  integral schemes.
* `Stacks.Divisors.isPullbackDefined_of_notMem_support_of_associated`: **Stacks 02OO (4)**, a
  locally Noetherian source, in terms of associated points.
* `Stacks.Divisors.isPullbackDefined_of_hasNoEmbeddedPoints`: **Stacks 02OO (5)**, a locally
  Noetherian source without embedded points.

## Implementation notes

Each case identifies the weakly associated points of `X` with a set of points that the hypothesis
controls: the generic points of the irreducible components when `X` is reduced (Tag 0EME), the
associated points when `X` is locally Noetherian (Tag 05AR), and again the generic points when
`X` has in addition no embedded points (Tag 05AH).  For a dominant morphism of integral schemes
the sole generic point of `X` maps to the generic point of `Y`, which misses the support of an
effective Cartier divisor because it is the generic point of an irreducible component.

## References

* [Stacks Project, Tag 02OO](https://stacks.math.columbia.edu/tag/02OO)
* [Stacks Project, Tag 0EME](https://stacks.math.columbia.edu/tag/0EME)
* [Stacks Project, Tag 05AR](https://stacks.math.columbia.edu/tag/05AR)
* [Stacks Project, Tag 05AH](https://stacks.math.columbia.edu/tag/05AH)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Divisors

/-- **Stacks 02OO (3).** The pullback of an effective Cartier divisor `D ⊆ Y` along a morphism
`f : X ⟶ Y` out of a reduced scheme is defined as soon as `f` carries no generic point of an
irreducible component of `X` into the support of `D`: on a reduced scheme those generic points
are exactly the weakly associated points. -/
@[stacks 02OO "part (3): a reduced source whose generic points avoid the support",
  ega "IV 21.10.1" "special case",
  ega "IV 21.4.5" "special case"]
theorem isPullbackDefined_of_isReduced {X Y : Scheme.{u}} (f : X ⟶ Y) [IsReduced X]
    (D : Y.IdealSheafData) (hD : IsEffectiveCartierDivisor D)
    (hf : ∀ ξ ∈ genericPoints X, f ξ ∉ D.supportSet) :
    IsPullbackDefined f D :=
  isPullbackDefined_of_notMem_support_of_weaklyAssociated f D hD <| by
    rwa [weaklyAssociatedPointsOfScheme_eq_genericPoints]

/-- **Stacks 02OO (2).** The pullback of an effective Cartier divisor is defined along a dominant
morphism of integral schemes: the generic point of the source is its only weakly associated
point, and dominance sends it to the generic point of the target, which an effective Cartier
divisor misses. -/
@[stacks 02OO "part (2): a dominant morphism of integral schemes",
  ega "IV 21.10.1" "special case",
  ega "IV 21.4.5" "special case"]
theorem isPullbackDefined_of_isDominant {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X]
    [IsIntegral Y] [IsDominant f] (D : Y.IdealSheafData) (hD : IsEffectiveCartierDivisor D) :
    IsPullbackDefined f D := by
  have h := (genericPoint_spec X).image f.continuous
  rw [Set.image_univ, f.denseRange.closure_range] at h
  refine isPullbackDefined_of_isReduced f D hD fun ξ hξ => ?_
  rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hξ
  subst hξ
  exact notMem_support_of_mem_genericPoints_of_isEffectiveCartierDivisor D hD
    (by rw [genericPoints_eq_singleton, Set.mem_singleton_iff]
        exact ((genericPoint_spec Y).eq h).symm)

/-- **Stacks 02OO (4).** The pullback of an effective Cartier divisor `D ⊆ Y` along a morphism
`f : X ⟶ Y` out of a locally Noetherian scheme is defined as soon as `f` carries no associated
point of `X` into the support of `D`: on a locally Noetherian scheme the associated points are
exactly the weakly associated points. -/
@[stacks 02OO "part (4): a locally Noetherian source whose associated points avoid the support",
  ega "IV 21.4.5" "special case"]
theorem isPullbackDefined_of_notMem_support_of_associated {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsLocallyNoetherian X] (D : Y.IdealSheafData) (hD : IsEffectiveCartierDivisor D)
    (hf : ∀ x ∈ schemeAssociatedPoints X, f x ∉ D.supportSet) :
    IsPullbackDefined f D :=
  isPullbackDefined_of_notMem_support_of_weaklyAssociated f D hD <| by
    simpa only [schemeAssociatedPoints, schemeWeaklyAssociatedPoints,
      ← associatedPoints_eq_weaklyAssociatedPoints X (SheafOfModules.unit X.ringCatSheaf)]
      using hf

/-- **Stacks 02OO (5).** The pullback of an effective Cartier divisor `D ⊆ Y` along a morphism
`f : X ⟶ Y` out of a locally Noetherian scheme without embedded points is defined as soon as `f`
carries no generic point of an irreducible component of `X` into the support of `D`: without
embedded points those generic points are exactly the weakly associated points. -/
@[stacks 02OO "part (5): no embedded points, generic points avoiding the support",
  ega "IV 21.10.1" "partial",
  ega "IV 21.4.5" "special case"]
theorem isPullbackDefined_of_hasNoEmbeddedPoints {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsLocallyNoetherian X] (hX : HasNoEmbeddedPoints X) (D : Y.IdealSheafData)
    (hD : IsEffectiveCartierDivisor D) (hf : ∀ ξ ∈ genericPoints X, f ξ ∉ D.supportSet) :
    IsPullbackDefined f D :=
  isPullbackDefined_of_notMem_support_of_weaklyAssociated f D hD <| by
    rwa [schemeWeaklyAssociatedPoints_eq_genericPoints_of_hasNoEmbeddedPoints X hX]

end Stacks.Divisors
