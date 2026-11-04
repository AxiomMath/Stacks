module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ClosedPoint
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen

/-!
# The cotangent space at a nonsingular closed point of a variety

A variety is nonsingular at a point when the local ring there is regular, and then the dimension
of the cotangent space `𝔪_x / 𝔪_x²` at a closed point equals the dimension of the variety. For a
regular local ring the cotangent space has dimension the Krull dimension of the ring, and at a
closed point of a variety that Krull dimension is the dimension of the variety, the variety being
irreducible.

## Main results

* `AlgebraicGeometry.finrank_cotangentSpace_eq_topologicalKrullDim`: the cotangent space at a
  nonsingular closed point of a variety has dimension the dimension of the variety.
* `AlgebraicGeometry.ringKrullDim_stalk_eq_of_topologicalKrullDim_eq`: two irreducible schemes
  locally of finite type over a field and of the same dimension have local rings of the same
  Krull dimension at any pair of closed points.

## Implementation notes

Nonsingularity at the point is membership in `AlgebraicGeometry.regularLocus`. The Krull
dimension of the local ring is reached in two steps, both instances of Tag 0A21: the dimension of
an irreducible scheme equals its dimension at any point, and the dimension at a closed point is
the Krull dimension of the local ring there. Irreducibility comes from integrality, which
`AlgebraicGeometry.IsVariety` provides. The Noetherian hypothesis of the regularity criterion is
supplied by local finite type over a field, which is not an instance and so is introduced
explicitly.

## References

* [Stacks Project, Tag 00KU](https://stacks.math.columbia.edu/tag/00KU)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
* [Stacks Project, Tag 07R1](https://stacks.math.columbia.edu/tag/07R1)
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry

/-- **The cotangent space at a nonsingular closed point of a variety has dimension the dimension
of the variety.** The local ring at the point is regular, so its cotangent space has dimension
its Krull dimension, and at a closed point of an irreducible scheme locally of finite type over a
field that Krull dimension is the dimension of the scheme. -/
public theorem finrank_cotangentSpace_eq_topologicalKrullDim (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsVariety k f] (x : X)
    (hx : IsClosed ({x} : Set X)) (hreg : x ∈ regularLocus X) :
    (Module.finrank (ResidueField (X.presheaf.stalk x))
        (CotangentSpace (X.presheaf.stalk x)) : WithBot ℕ∞) = topologicalKrullDim X := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherianRing (X.presheaf.stalk x) := inferInstance
  have hrank := (IsRegularLocalRing.iff_finrank_cotangentSpace
    (ToType (X.presheaf.stalk x))).mp hreg
  rw [hrank]
  exact ((topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k X f x).trans
    (topologicalKrullDimAt_eq_krullDimOfRing_stalk k X f x hx)).symm

/-- **Irreducible schemes of equal dimension have local rings of equal Krull dimension at closed
points.** At a closed point of a scheme locally of finite type over a field the Krull dimension
of the local ring is the dimension at that point, and for an irreducible scheme that is the
dimension of the whole scheme. -/
public theorem ringKrullDim_stalk_eq_of_topologicalKrullDim_eq (k : Type u) [Field k]
    {X Y : Scheme.{u}} (fX : X ⟶ Spec (.of k)) (fY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType fX] [LocallyOfFiniteType fY]
    [IrreducibleSpace X] [IrreducibleSpace Y] (x : X) (y : Y)
    (hx : IsClosed ({x} : Set X)) (hy : IsClosed ({y} : Set Y))
    (hdim : topologicalKrullDim X = topologicalKrullDim Y) :
    ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk y) := by
  rwa [← topologicalKrullDimAt_eq_krullDimOfRing_stalk k X fX x hx,
    ← topologicalKrullDimAt_eq_krullDimOfRing_stalk k Y fY y hy,
    ← topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k X fX x,
    ← topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k Y fY y]

end AlgebraicGeometry

end
