module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksFrontier.RingTheory.IntegrallyClosed.Defs
public import StacksCore.Tactic.StacksAttribute

/-!
# Geometrically normal schemes over a field

A scheme over a field is geometrically normal at a point if, after every field extension,
the local ring at every point above it is normal. It is geometrically normal if this holds at
every point.

## Main definitions

* `AlgebraicGeometry.IsGeometricallyNormalAt` expresses geometric normality at a point.
* `AlgebraicGeometry.IsGeometricallyNormal` expresses geometric normality at every point.

## Main results

The characterizing lemmas unfold the two predicates into their defining conditions.

## Implementation notes

The base change along `k → K` is represented by the canonical pullback of the structure morphism
and `Spec K ⟶ Spec k`. A point lies over `x` when its image under the first pullback projection is
`x`. As in the algebraic definition of geometric normality, extension fields live in the universe
of the base field.

## References

* [Stacks Project, Tag 038M](https://stacks.math.columbia.edu/tag/038M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}}

/- `AlgebraicGeometry.IsRationalPoint`, in
`StacksFrontier/AlgebraicGeometry/Variety/Projective/RationalPointHyperplane.lean`, has the same
signature `(f : X ⟶ Spec (.of k)) (x : X) : Prop` and an unrelated body: it asserts that the
canonical map `k → κ(x)` to the residue field is an isomorphism, a condition on `x` alone, with
no quantification over extensions of `k` and no normality of any local ring. -/
/-- A scheme `X ⟶ Spec k` is geometrically normal at `x` if, after every field extension
`K / k`, the local ring at every point of the base change lying over `x` is normal. -/
@[stacks 038M "part (1)", ega "IV 6.7.6", ega "IV 6.7.8"]
public def IsGeometricallyNormalAt (f : X ⟶ Spec (.of k)) (x : X) : Prop :=
  ∀ (K : Type u) [Field K] [Algebra k K]
    (x' : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u})),
    (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base x' = x →
      IsNormalRing
        ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).presheaf.stalk x')

/-- A scheme over `k` is geometrically normal if it is geometrically normal at every point. -/
@[stacks 038M "part (2)", ega "IV 6.7.6"]
public def IsGeometricallyNormal (f : X ⟶ Spec (.of k)) : Prop :=
  ∀ x : X, IsGeometricallyNormalAt f x

/-- The defining condition for geometric normality at a point. -/
@[simp]
public theorem isGeometricallyNormalAt_iff (f : X ⟶ Spec (.of k)) (x : X) :
    IsGeometricallyNormalAt f x ↔
      ∀ (K : Type u) [Field K] [Algebra k K]
        (x' : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u})),
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base x' = x →
          IsNormalRing
            ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).presheaf.stalk x') :=
  Iff.rfl

/-- A scheme is geometrically normal exactly when it is geometrically normal at every point. -/
@[simp]
public theorem isGeometricallyNormal_iff (f : X ⟶ Spec (.of k)) :
    IsGeometricallyNormal f ↔ ∀ x : X, IsGeometricallyNormalAt f x :=
  Iff.rfl

/-- Geometric normality implies geometric normality at each point. -/
public theorem IsGeometricallyNormal.at {f : X ⟶ Spec (.of k)}
    (hf : IsGeometricallyNormal f) (x : X) : IsGeometricallyNormalAt f x :=
  hf x

end AlgebraicGeometry
