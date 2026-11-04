module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernComponent.ComponentRule
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.SectionTransport

/-!
# The divisor of a meromorphic section is an isomorphism invariant of the module

Let `X` be an integral scheme and let `f : L ≅ N` be an isomorphism of `𝒪_X`-modules. The stalk
map of `f` at the generic point carries a meromorphic section `s ∈ L_η` to one of `N`, and the
two have the same order of vanishing along every prime divisor: a basis of `L_x` is carried to a
basis of `N_x`, the specialization maps to the generic stalk commute with the stalk maps of `f`,
so a coordinate of `s` at `x` is also a coordinate of its image, and the order of vanishing is
read off any coordinate.

Consequently `div_L(s)` and `div_N(f s)` are the same Weil divisor, and the component cycles of
`StacksFrontier.AlgebraicGeometry.Chow.ChernComponent.ComponentRule` agree.

## Main results

* `Stacks.Divisors.IsStalkBasis.mapStalkLinearMap`,
  `Stacks.Divisors.IsTrivializedNear.mapStalkLinearMap` — bases and trivializations transport.
* `Stacks.Divisors.IsCoordinateAt.mapStalkLinearMap` — coordinates transport unchanged.
* `Stacks.Divisors.orderOfVanishing_mapStalkLinearMap` — the order of vanishing is unchanged.
* `Stacks.Divisors.weilDivisorOfMeromorphicSection_mapStalkLinearMap` — the Weil divisor is
  unchanged.
* `Stacks.Chow.chernComponentCycle_mapStalkLinearMap` — the component cycle of Stacks 02SO is
  unchanged.

## Implementation notes

The transport is along `AlgebraicGeometry.stalkLinearMap`, the stalk map of a morphism of
sheaves of modules read as a linear map over the local ring, and the only two facts used about
it are that it is bijective for an isomorphism
(`AlgebraicGeometry.bijective_stalkLinearMap`) and that it commutes with specialization
(`AlgebraicGeometry.stalkLinearMap_stalkSpecializes`). Both are already available, so nothing
here reopens the construction of the stalk map.

The companion statement for the `AlgebraicGeometry.MeromorphicSection` flavour of the order of
vanishing is `AlgebraicGeometry.orderOfVanishingMeromorphic_mapMeromorphicSection`; this file is
the same transport for the generic-stalk model that chapter 42 uses.

## References

* [Stacks Project, Tag 02SF](https://stacks.math.columbia.edu/tag/02SF)
* [Stacks Project, Tag 02SJ](https://stacks.math.columbia.edu/tag/02SJ)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}} (L N : X.Modules) (f : L ⟶ N)

/-- A stalk basis is carried to a stalk basis by the stalk map of an isomorphism: that map is
linear and bijective, so multiplication by the image is multiplication by the basis followed by
it. -/
theorem IsStalkBasis.mapStalkLinearMap [IsIso f] (x : X) {m : L.presheaf.stalk x}
    (hm : IsStalkBasis L x m) : IsStalkBasis N x (stalkLinearMap L N f x m) := by
  show Function.Bijective fun r : X.presheaf.stalk x ↦ r • stalkLinearMap L N f x m
  have hcomp : (fun r : X.presheaf.stalk x ↦ r • stalkLinearMap L N f x m) =
      (stalkLinearMap L N f x) ∘ fun r : X.presheaf.stalk x ↦ r • m :=
    funext fun r ↦ (map_smul (stalkLinearMap L N f x) r m).symm
  rw [hcomp]
  exact (bijective_stalkLinearMap L N f x).comp hm

/-- A module isomorphic to one trivialized near a point is trivialized near that point: the
image of a trivializing section is one, because the stalk map commutes with germs. -/
theorem IsTrivializedNear.mapStalkLinearMap [IsIso f] (x : X) (hL : IsTrivializedNear L x) :
    IsTrivializedNear N x := by
  obtain ⟨W, hxW, t, ht⟩ := hL
  refine ⟨W, hxW, f.val.app (op W) t, fun y hy ↦ ?_⟩
  rw [← stalkLinearMap_germ L N f W y hy t]
  exact (ht y hy).mapStalkLinearMap L N f y

variable [IsIntegral X]

/-- The stalk map of a morphism of modules commutes with the specialization to the generic
stalk. -/
theorem toGenericStalk_stalkLinearMap (x : X) (m : L.presheaf.stalk x) :
    toGenericStalk N x (stalkLinearMap L N f x m) =
      stalkLinearMap L N f (genericPoint X) (toGenericStalk L x m) :=
  (stalkLinearMap_stalkSpecializes L N f ((genericPoint_spec X).specializes trivial) m).symm

/-- A coordinate of a meromorphic section at a point is a coordinate of its image under the
stalk map of an isomorphism: the basis transports and the scalar is unchanged. -/
theorem IsCoordinateAt.mapStalkLinearMap [IsIso f] {x : X}
    {s : L.presheaf.stalk (genericPoint X)} {a : X.functionField}
    (ha : IsCoordinateAt L x s a) :
    IsCoordinateAt N x (stalkLinearMap L N f (genericPoint X) s) a := by
  obtain ⟨m, hm, hsa⟩ := ha
  refine ⟨stalkLinearMap L N f x m, hm.mapStalkLinearMap L N f x, ?_⟩
  rw [hsa, map_smul, toGenericStalk_stalkLinearMap L N f x m]

variable [IsLocallyNoetherian X]

/-- **The order of vanishing is an isomorphism invariant of the module.** An isomorphism
`L ≅ N` carries a meromorphic section of `L` to one of `N` with the same order of vanishing
along every prime divisor. -/
theorem orderOfVanishing_mapStalkLinearMap [IsIso f] {Z : PrimeDivisor X}
    (hL : IsTrivializedNear L Z.genericPoint) (s : L.presheaf.stalk (genericPoint X)) :
    orderOfVanishing N (stalkLinearMap L N f (genericPoint X) s) Z = orderOfVanishing L s Z := by
  obtain ⟨a, ha⟩ := exists_isCoordinateAt hL s
  rw [orderOfVanishing_eq hL ha,
    orderOfVanishing_eq (hL.mapStalkLinearMap L N f Z.genericPoint) (ha.mapStalkLinearMap L N f)]

/-- **The Weil divisor of a meromorphic section is an isomorphism invariant of the module.** -/
theorem weilDivisorOfMeromorphicSection_mapStalkLinearMap [IsIso f]
    (hL : ∀ x : X, IsTrivializedNear L x) (hN : ∀ x : X, IsTrivializedNear N x)
    (s : L.presheaf.stalk (genericPoint X)) :
    weilDivisorOfMeromorphicSection hN (stalkLinearMap L N f (genericPoint X) s) =
      weilDivisorOfMeromorphicSection hL s :=
  Subtype.ext (funext fun Z ↦ orderOfVanishing_mapStalkLinearMap L N f (hL Z.genericPoint) s)

end Stacks.Divisors

namespace Stacks.Chow

open Stacks.Divisors

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  [IsIntegral X] [IsLocallyNoetherian X] {k : ℤ}
  (hk : schemeDeltaDimension C p = ((k + 1 : ℤ) : EInt)) (L N : X.Modules) (f : L ⟶ N)

/-- **The component cycle of Stacks 02SO is an isomorphism invariant of the module.** The
divisor cycle of a meromorphic section of `L` is the divisor cycle of its image in an isomorphic
module `N`. -/
theorem chernComponentCycle_mapStalkLinearMap [IsIso f]
    (hL : ∀ x : X, IsTrivializedNear L x) (hN : ∀ x : X, IsTrivializedNear N x)
    (s : L.presheaf.stalk (genericPoint X)) :
    chernComponentCycle C p hk hN (stalkLinearMap L N f (genericPoint X) s) =
      chernComponentCycle C p hk hL s :=
  Subtype.ext (congrArg weilDivisorAlgebraicCycle
    (weilDivisorOfMeromorphicSection_mapStalkLinearMap L N f hL hN s))

end Stacks.Chow

end
