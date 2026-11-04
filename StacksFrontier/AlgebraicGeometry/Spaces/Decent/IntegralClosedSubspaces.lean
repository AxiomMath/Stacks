module

public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Sober
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.CodimensionZeroCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PropertyGammaPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Sober
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.Topology.Dimension.SpecializingSurjection

/-!
# Points, irreducible closed subsets and integral closed subspaces

Let `X` be a decent algebraic space over a scheme `S`. There are canonical bijections between

1. the points of `X`, that is `|X|`;
2. the irreducible closed subsets of `|X|`;
3. the integral closed subspaces of `X`,

the bijection from (1) to (2) sending a point to the closure of that point and the bijection
from (3) to (2) sending a closed subspace to its set of points. This is **Stacks 0ENF**.

Both bijections are stated as bijectivity of an explicitly given map rather than as the
existence of an abstract equivalence, because *which* map it is belongs to the statement.

The map from (1) to (2) is `TopologicalSpace.IrreducibleCloseds.closureSingleton`.

## Main definitions

* `AlgebraicGeometry.Space.IntegralClosedSubspace`: the integral closed subspaces of an
  algebraic space, that is (3).
* `AlgebraicGeometry.Space.integralClosedSubspaceSupport`: the set of points of an integral
  closed subspace, as an irreducible closed subset of `|X|`. This is the map from (3) to (2).

## Main results

* `AlgebraicGeometry.Space.injective_closureSingleton_points` and
  `AlgebraicGeometry.Space.bijective_closureSingleton_points`: the map from (1) to (2) is
  injective, and bijective.
* `AlgebraicGeometry.Space.injective_integralClosedSubspaceSupport`,
  `AlgebraicGeometry.Space.surjective_integralClosedSubspaceSupport` and
  `AlgebraicGeometry.Space.bijective_integralClosedSubspaceSupport`: the map from (3) to (2)
  is bijective.

## Implementation notes

The bijection from (1) to (2) is soberness of `|X|`, Stacks 03K6: injectivity is the Kolmogorov
property `AlgebraicGeometry.Space.t0Space_points_of_isDecentSpace`, which is Stacks 03K3, and
surjectivity is quasi-soberness `AlgebraicGeometry.Space.quasiSober_points_of_isDecentSpace`,
which goes through Stacks 086U.

Surjectivity of the map from (3) to (2) uses the reduced induced closed subspace structure of
Stacks 047X on an irreducible closed set of points, which is the subspace of Stacks 03IQ. The
existence clause of Stacks 03IQ uses Stacks 02W8 at the closed immersions,
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion`; injectivity
uses only the uniqueness clause.

The map from (1) to (2) is `TopologicalSpace.IrreducibleCloseds.closureSingleton` rather than the
inverse of Mathlib's `irreducibleSetEquivPoints`, which requires `QuasiSober` and `T0Space`
instances that the injectivity statement does not assume.

The topology on points is the local instance `AlgebraicGeometry.Space.pointTopology`.

## References

* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 03IQ](https://stacks.math.columbia.edu/tag/03IQ)
* [Stacks Project, Tag 03K3](https://stacks.math.columbia.edu/tag/03K3)
* [Stacks Project, Tag 03K6](https://stacks.math.columbia.edu/tag/03K6)
* [Stacks Project, Tag 03KF](https://stacks.math.columbia.edu/tag/03KF)
* [Stacks Project, Tag 047X](https://stacks.math.columbia.edu/tag/047X)
* [Stacks Project, Tag 04CD](https://stacks.math.columbia.edu/tag/04CD)
* [Stacks Project, Tag 0ABJ](https://stacks.math.columbia.edu/tag/0ABJ)
* [Stacks Project, Tag 0AD4](https://stacks.math.columbia.edu/tag/0AD4)
* [Stacks Project, Tag 0ENF](https://stacks.math.columbia.edu/tag/0ENF)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### Points and irreducible closed subsets -/

/-- Two points of a decent algebraic space over `S` with the same closure are equal: the map
from (1) to (2) is injective. -/
@[stacks 0ENF "the map from (1) to (2) is injective, unconditionally"]
theorem injective_closureSingleton_points (hX : IsAlgebraicSpace B S hS X)
    (hdecent : IsDecentSpace B S hS X) :
    Function.Injective (IrreducibleCloseds.closureSingleton (X := points B S hS X)) := by
  have : T0Space (points B S hS X) := t0Space_points_of_isDecentSpace B S hS hX hdecent
  intro x y h
  have hc : closure ({x} : Set (points B S hS X)) = closure {y} := by
    simpa using congrArg (fun T : IrreducibleCloseds (points B S hS X) =>
      (T : Set (points B S hS X))) h
  exact (inseparable_iff_closure_eq.2 hc).eq

/-- Taking the closure of a point is a bijection from the points of a decent algebraic space
`X` over `S` onto the irreducible closed subsets of `|X|`. -/
@[stacks 0ENF "the bijection from (1) to (2)"]
theorem bijective_closureSingleton_points (hX : IsAlgebraicSpace B S hS X)
    (hdecent : IsDecentSpace B S hS X) :
    Function.Bijective (IrreducibleCloseds.closureSingleton (X := points B S hS X)) := by
  have : QuasiSober (points B S hS X) := quasiSober_points_of_isDecentSpace B S hS hX hdecent
  refine ⟨injective_closureSingleton_points B S hS hX hdecent, fun T => ?_⟩
  obtain ⟨x, hx⟩ := QuasiSober.sober T.isIrreducible T.isClosed
  exact ⟨x, IrreducibleCloseds.ext (isGenericPoint_def.1 hx)⟩

/-! ### Integral closed subspaces -/

/-- An *integral closed subspace* of an algebraic space `X` over `S` is a closed subspace of
`X`, in the sense of Stacks 02YU, which is an integral algebraic space over `S`, in the sense of
Stacks 0AD4. -/
@[ext, stacks 0ENF "(3): the integral closed subspaces of an algebraic space"]
structure IntegralClosedSubspace (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) where
  /-- The underlying subfunctor of `X`. -/
  subspace : Subfunctor X
  /-- It is a closed subspace of `X`. -/
  isClosedSubspace : IsClosedSubspace B S hS subspace
  /-- It is an integral algebraic space over `S`. -/
  isIntegralSpace : IsIntegralSpace B S hS subspace.toFunctor

/-- The set of points of an integral closed subspace of `X` is closed in `|X|`. -/
theorem isClosed_range_pointsMap_integralClosedSubspace (hX : IsAlgebraicSpace B S hS X)
    (Z : IntegralClosedSubspace B S hS X) :
    IsClosed (Set.range (pointsMap B S hS Z.subspace.toFunctor Z.subspace.ι)) :=
  (isClosedImmersion_iff_isClosed_range_pointsMap B S hS hX Z.subspace.ι
    (isImmersion_of_isClosedImmersion B S hS Z.isClosedSubspace.2)).1 Z.isClosedSubspace.2

/-- The set of points of an integral closed subspace of `X` is irreducible in `|X|`. -/
theorem isIrreducible_range_pointsMap_integralClosedSubspace
    (Z : IntegralClosedSubspace B S hS X) :
    IsIrreducible (Set.range (pointsMap B S hS Z.subspace.toFunctor Z.subspace.ι)) := by
  have : IrreducibleSpace (points B S hS Z.subspace.toFunctor) := Z.isIntegralSpace.2.2
  have h := (IrreducibleSpace.isIrreducible_univ
      (points B S hS Z.subspace.toFunctor)).image
    (pointsMap B S hS Z.subspace.toFunctor Z.subspace.ι)
    (continuous_pointsMap B S hS Z.subspace.ι).continuousOn
  rwa [Set.image_univ] at h

/-- The set of points of an integral closed subspace of `X`, as an irreducible closed subset
of `|X|`. This is the map from (3) to (2). -/
@[stacks 0ENF "the map from (3) to (2): the point set of an integral closed subspace"]
def integralClosedSubspaceSupport (hX : IsAlgebraicSpace B S hS X)
    (Z : IntegralClosedSubspace B S hS X) : IrreducibleCloseds (points B S hS X) where
  carrier := Set.range (pointsMap B S hS Z.subspace.toFunctor Z.subspace.ι)
  isIrreducible' := isIrreducible_range_pointsMap_integralClosedSubspace B S hS Z
  isClosed' := isClosed_range_pointsMap_integralClosedSubspace B S hS hX Z

/-- The underlying set of `AlgebraicGeometry.Space.integralClosedSubspaceSupport` is the range
of the map on points induced by the inclusion of the subspace. -/
@[simp]
theorem coe_integralClosedSubspaceSupport (hX : IsAlgebraicSpace B S hS X)
    (Z : IntegralClosedSubspace B S hS X) :
    (integralClosedSubspaceSupport B S hS hX Z : Set (points B S hS X)) =
      Set.range (pointsMap B S hS Z.subspace.toFunctor Z.subspace.ι) :=
  rfl

/-- An integral closed subspace of an algebraic space over `S` is determined by its set of
points: the map from (3) to (2) is injective. -/
@[stacks 0ENF "the map from (3) to (2) is injective, unconditionally"]
theorem injective_integralClosedSubspaceSupport (hX : IsAlgebraicSpace B S hS X) :
    Function.Injective (integralClosedSubspaceSupport B S hS hX) := by
  intro Z W h
  have key (V : IntegralClosedSubspace B S hS X)
      (hV : integralClosedSubspaceSupport B S hS hX V = integralClosedSubspaceSupport B S hS hX Z) :
      V.subspace = reducedClosedSubspace B S hS X hX _
        (isClosed_range_pointsMap_integralClosedSubspace B S hS hX Z) :=
    eq_reducedClosedSubspace B S hS X hX _ _ V.subspace V.isClosedSubspace
      (congrArg IrreducibleCloseds.carrier hV) V.isIntegralSpace.1
  exact IntegralClosedSubspace.ext ((key Z rfl).trans (key W h.symm).symm)

/-- Every irreducible closed subset of `|X|`, for `X` a decent algebraic space over `S`, is the
set of points of an integral closed subspace: the map from (3) to (2) is surjective. -/
@[stacks 0ENF "the map from (3) to (2) is surjective"]
theorem surjective_integralClosedSubspaceSupport (hX : IsAlgebraicSpace B S hS X)
    (hdecent : IsDecentSpace B S hS X) :
    Function.Surjective (integralClosedSubspaceSupport B S hS hX) := by
  intro T
  have hRclosed : IsClosedSubspace B S hS
      (reducedClosedSubspace B S hS X hX (T : Set (points B S hS X)) T.isClosed) :=
    isClosedSubspace_reducedClosedSubspace B S hS X hX _ T.isClosed
  have hRpoints : Set.range (pointsMap B S hS
        (reducedClosedSubspace B S hS X hX (T : Set (points B S hS X)) T.isClosed).toFunctor
        (reducedClosedSubspace B S hS X hX (T : Set (points B S hS X)) T.isClosed).ι) =
      (T : Set (points B S hS X)) :=
    range_pointsMap_ι_reducedClosedSubspace B S hS X hX _ T.isClosed
  have hRirreducible : IrreducibleSpace (points B S hS
      (reducedClosedSubspace B S hS X hX (T : Set (points B S hS X)) T.isClosed).toFunctor) :=
    ((isEmbedding_pointsMap_of_isImmersion B S hS hX
        (reducedClosedSubspace B S hS X hX (T : Set (points B S hS X)) T.isClosed).ι
        (isImmersion_of_isClosedImmersion B S hS hRclosed.2)).toHomeomorph.trans
      (Homeomorph.setCongr hRpoints)).irreducibleSpace_iff.2
      (Subtype.irreducibleSpace T.isIrreducible)
  exact ⟨⟨_, hRclosed,
    hasEtaleLocalProperty_isReduced_reducedClosedSubspace B S hS X hX _ T.isClosed,
    isDecentSpace_of_relativelyRepresentable B S hS hRclosed.1 _ hRclosed.2.1 hdecent,
    hRirreducible⟩, IrreducibleCloseds.ext hRpoints⟩

/-- Taking the set of points is a bijection from the integral closed subspaces of a decent
algebraic space `X` over `S` onto the irreducible closed subsets of `|X|`. -/
@[stacks 0ENF "the bijection from (3) to (2)"]
theorem bijective_integralClosedSubspaceSupport (hX : IsAlgebraicSpace B S hS X)
    (hdecent : IsDecentSpace B S hS X) :
    Function.Bijective (integralClosedSubspaceSupport B S hS hX) :=
  ⟨injective_integralClosedSubspaceSupport B S hS hX,
    surjective_integralClosedSubspaceSupport B S hS hX hdecent⟩

end AlgebraicGeometry.Space

end
