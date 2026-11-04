module

public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorOfPoints

/-!
# The ideal of the graph of a relative point

Let `X` and `T` be schemes over `S` and let `x : T ⟶ X` be a morphism over `S`. Its graph is the
morphism `T ⟶ X ×_S T` with components `x` and the identity, and it is a section of the
projection `X ×_S T ⟶ T`. The *point ideal* of `x` is the ideal sheaf on `X ×_S T` cutting out
the image of that graph.

When `X ⟶ S` is smooth of relative dimension one the point ideal is an effective Cartier
divisor of degree one, and multiplying by it is the operation `D ↦ D + x` that adds a point to
a degree-`d` Hilbert family; this is the content of Stacks Tag 0B9G.

## Main definitions

* `Stacks.Hilbert.pointIdeal` — the ideal sheaf of the graph of a relative point.

## Main results

* `Stacks.Hilbert.pointGraph_comp_snd` — the graph of a relative point is a section of the
  base-change projection.

## Implementation notes

The graph is `pullback.lift x.left (𝟙 T.left) _`; its ideal sheaf is the kernel ideal sheaf
`Scheme.Hom.ker` of that morphism, which is the ideal sheaf of its scheme-theoretic image.

Tag 0B9G is the statement that point addition between Hilbert schemes is finite locally free of
degree `d + 1`; that morphism is not constructed here, and no declaration in this file carries a
`@[stacks]` attribute.

## References

* [Stacks Project, Tag 0B9G](https://stacks.math.columbia.edu/tag/0B9G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Hilbert

variable {S : Scheme.{u}} (X T : Over S)

/-- The graph `T ⟶ X ×_S T` of a morphism `x : T ⟶ X` over `S`. -/
def pointGraph (x : T ⟶ X) : T.left ⟶ ((Over.pullback T.hom).obj X).left :=
  pullback.lift x.left (𝟙 T.left) (by simp)

/-- The graph of a relative point is a section of the base-change projection. -/
@[simp]
theorem pointGraph_comp_snd (x : T ⟶ X) :
    pointGraph X T x ≫ pullback.snd X.hom T.hom = 𝟙 T.left :=
  pullback.lift_snd _ _ _

/-- The ideal of the graph of a relative point of `X` over `T`, an ideal sheaf on `X ×_S T`. -/
def pointIdeal (x : T ⟶ X) : ((Over.pullback T.hom).obj X).left.IdealSheafData :=
  (pointGraph X T x).ker

end Stacks.Hilbert

end
