module

public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import StacksFrontier.RingTheory.Unramified.Defs
public import StacksCore.Tactic.StacksAttribute

/-!
# Unramified morphisms of schemes

A morphism of schemes is unramified (respectively G-unramified) at a point when suitable affine
neighbourhoods of that point and its image induce an unramified (respectively G-unramified) map
on rings of sections. It is unramified (respectively G-unramified) when this holds at every point
of its source.

## Main definitions

* `AlgebraicGeometry.UnramifiedAt` is unramifiedness of a scheme morphism at a point.
* `AlgebraicGeometry.GUnramifiedAt` is G-unramifiedness of a scheme morphism at a point.
* `AlgebraicGeometry.Unramified` is unramifiedness of a scheme morphism.
* `AlgebraicGeometry.GUnramified` is G-unramifiedness of a scheme morphism.

## Main results

* `AlgebraicGeometry.unramified_iff` characterizes the global unramifiedness class pointwise.
* `AlgebraicGeometry.gUnramified_iff` characterizes the global G-unramifiedness class pointwise.

## Implementation notes

The affine neighbourhoods are represented by open subsets together with `IsAffineOpen`
witnesses. The containment of the source neighbourhood in the inverse image of the target
neighbourhood supplies the canonical map on sections through `Scheme.Hom.appLE`. Its underlying
ring homomorphism determines the algebra structure used by `Algebra.Unramified` or
`Algebra.GUnramified`.

The two global notions are classes, following Mathlib's convention for properties of scheme
morphisms. Their fields directly expose the corresponding pointwise predicates.

## References

* [Stacks Project, Tag 02G4](https://stacks.math.columbia.edu/tag/02G4)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

open CategoryTheory

/-- A morphism of schemes `f : X ⟶ S` is unramified at `x : X` if there are affine open
neighbourhoods `U` of `x` and `V` of its image, with `U ≤ f ⁻¹ᵁ V`, such that the induced map on
rings of sections is unramified. -/
@[stacks 02G4 "part (1)", sga "3 XI 1.3", sga "3 XI 1.5"]
public def UnramifiedAt {X S : Scheme.{u}} (f : X ⟶ S) (x : X) : Prop :=
  ∃ (U : X.Opens), IsAffineOpen U ∧ x ∈ U ∧
    ∃ (V : S.Opens) (_ : IsAffineOpen V) (e : U ≤ f ⁻¹ᵁ V),
      letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
      Algebra.Unramified Γ(S, V) Γ(X, U)

/-- A morphism of schemes `f : X ⟶ S` is G-unramified at `x : X` if there are affine open
neighbourhoods `U` of `x` and `V` of its image, with `U ≤ f ⁻¹ᵁ V`, such that the induced map on
rings of sections is G-unramified. -/
@[stacks 02G4 "part (2)", ega "IV 17.3.7" "unramified case"]
public def GUnramifiedAt {X S : Scheme.{u}} (f : X ⟶ S) (x : X) : Prop :=
  ∃ (U : X.Opens), IsAffineOpen U ∧ x ∈ U ∧
    ∃ (V : S.Opens) (_ : IsAffineOpen V) (e : U ≤ f ⁻¹ᵁ V),
      letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
      Algebra.GUnramified Γ(S, V) Γ(X, U)

/-- A morphism of schemes is unramified if it is unramified at every point of its source. -/
@[mk_iff, stacks 02G4 "part (3)"]
public class Unramified {X S : Scheme.{u}} (f : X ⟶ S) : Prop where
  /-- The morphism is unramified at every point `x` of its source. -/
  unramifiedAt (x : X) : UnramifiedAt f x

/-- A morphism of schemes is G-unramified if it is G-unramified at every point of its source. -/
@[mk_iff, stacks 02G4 "part (4)"]
public class GUnramified {X S : Scheme.{u}} (f : X ⟶ S) : Prop where
  /-- The morphism is G-unramified at every point `x` of its source. -/
  gUnramifiedAt (x : X) : GUnramifiedAt f x

end AlgebraicGeometry
