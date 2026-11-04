module

public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ClosedPoint
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
public import StacksFrontier.RingTheory.RegularLocalRing.DepthBound

/-!
# Depth at least two on a smooth scheme of dimension at least two

Hypothesis (2) of [Stacks, Tag 0FD9] — the connectedness of the zero scheme of a regular section
of an ample invertible module — is that `depth(𝒪_{X,x}) ≥ 2` at every closed point `x` of `X`.
This file discharges it for a scheme smooth over a field of dimension at least two.

A scheme smooth over a field is regular ([Stacks, Tag 056S]), so each of its local rings is a
regular local ring, and a regular local ring is Cohen–Macaulay: its depth is its Krull dimension
(`IsRegularLocalRing.two_le_depth_of_two_le_ringKrullDim`). At a closed point of a scheme locally
of finite type over a field the Krull dimension of the local ring is the local dimension of the
space, and on an irreducible such scheme the local dimension is the dimension of the whole space.
So dimension at least two for the scheme gives depth at least two at each closed point.

## Main results

* `AlgebraicGeometry.two_le_depth_stalk_of_smooth_of_two_le_ringKrullDim`: the bound from
  regularity of the local ring, at a point where the local ring has dimension at least two.
* `AlgebraicGeometry.two_le_depth_stalk_of_smooth_of_isClosed`: the bound at a closed point,
  with the dimension hypothesis read on the space at that point.
* `AlgebraicGeometry.two_le_depth_stalk_of_smooth_of_irreducible`: the bound at every closed
  point of an irreducible smooth scheme of dimension at least two — hypothesis (2) of
  [Stacks, Tag 0FD9] in the form its consumers have it.

## Implementation notes

`AlgebraicGeometry.two_le_depth_stalk_of_smooth` of
`StacksFrontier.AlgebraicGeometry.FundamentalGroup.PuritySmoothEquivalence` is a *relative*
statement: it transports `depth ≥ 2` from the base along a smooth morphism. Over a field the
base local ring is a field, of depth zero, so that lemma gives nothing here and the bound has to
come from the absolute regularity of the source.

Irreducibility is used only to identify the local dimension at a point with the dimension of the
space; the statements before the last one do not assume it, and take the dimension hypothesis
locally.

## References

* [Stacks Project, Tag 0FD9](https://stacks.math.columbia.edu/tag/0FD9)
* [Stacks Project, Tag 056S](https://stacks.math.columbia.edu/tag/056S)
* [Stacks Project, Tag 00NQ](https://stacks.math.columbia.edu/tag/00NQ)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- **At a point of a scheme smooth over a field whose local ring has Krull dimension at least
two, the local ring has depth at least two.** The local ring is regular by [Stacks, Tag 056S],
and a regular local ring is Cohen–Macaulay. -/
theorem two_le_depth_stalk_of_smooth_of_two_le_ringKrullDim {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Smooth f] (x : X)
    (hdim : (2 : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x)) :
    (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) := by
  have hreg : IsLocallyNoetherian X ∧ ∀ y : X, IsRegularLocalRing (X.presheaf.stalk y) :=
    ((isRegular_tfae X).out 1 2).mp (isRegular_of_smooth_over_field f)
  have : IsRegularLocalRing (X.presheaf.stalk x) := hreg.2 x
  exact IsRegularLocalRing.two_le_depth_of_two_le_ringKrullDim _ hdim

/-- **At a closed point of a scheme smooth over a field whose local dimension there is at least
two, the local ring has depth at least two.** At a closed point of a scheme locally of finite
type over a field the local dimension of the space is the Krull dimension of the local ring. -/
theorem two_le_depth_stalk_of_smooth_of_isClosed (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Smooth f] (x : X)
    (hx : IsClosed ({x} : Set X)) (hdim : (2 : WithBot ℕ∞) ≤ topologicalKrullDimAt X x) :
    (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) :=
  two_le_depth_stalk_of_smooth_of_two_le_ringKrullDim f x
    ((topologicalKrullDimAt_eq_krullDimOfRing_stalk k X f x hx) ▸ hdim)

/-- **Hypothesis (2) of [Stacks, Tag 0FD9] for an irreducible scheme smooth over a field of
dimension at least two**: the local ring at every closed point has depth at least two.

On an irreducible scheme locally of finite type over a field the local dimension at any point is
the dimension of the whole space, so the dimension hypothesis is read once, on `X`. -/
theorem two_le_depth_stalk_of_smooth_of_irreducible (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Smooth f] [IrreducibleSpace X]
    (hdim : (2 : WithBot ℕ∞) ≤ topologicalKrullDim X) (x : X)
    (hx : IsClosed ({x} : Set X)) :
    (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) :=
  two_le_depth_stalk_of_smooth_of_isClosed k f x hx
    ((topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k X f x) ▸ hdim)

end AlgebraicGeometry

end
