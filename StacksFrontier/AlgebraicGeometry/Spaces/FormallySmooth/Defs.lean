module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# Formally smooth, étale and unramified transformations

A transformation of set-valued functors on the big fppf site of a scheme is formally
smooth, formally étale, or formally unramified according as its lifts across affine
square-zero closed immersions exist, exist uniquely, or are unique when they exist.

## Main definitions

* `AlgebraicGeometry.Space.IsSquareZeroClosedImmersion` is the property of a morphism of
  the big fppf site over `S` that its underlying morphism of schemes is a closed immersion
  defined by a square-zero ideal.
* `AlgebraicGeometry.Space.IsLift` is the property of a section over the larger test object
  that it solves a given infinitesimal lifting problem.
* `AlgebraicGeometry.Space.FormallySmooth` is existence of infinitesimal lifts.
* `AlgebraicGeometry.Space.FormallyEtale` is existence and uniqueness of infinitesimal
  lifts.
* `AlgebraicGeometry.Space.FormallyUnramified` is uniqueness of infinitesimal lifts.

## Implementation notes

The affine test objects are objects of the big fppf slice whose underlying schemes
are affine. The square-zero ideal defining a closed immersion is the kernel ideal
sheaf of its underlying scheme morphism. A lifting problem includes the equality
expressing commutativity of its solid square. The three predicates use exactly
the same lifting problem, so composition and base change can be stated directly
in these terms.

## References

* [Stacks Project, Tag 049S](https://stacks.math.columbia.edu/tag/049S)
-/

@[expose] public section

open CategoryTheory Opposite

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A closed immersion of objects over `S` defined by a square-zero ideal. -/
public abbrev IsSquareZeroClosedImmersion {T T' : BigFppfOver B S hS} (i : T ⟶ T') : Prop :=
  let f := (BigFppfOver.toScheme B S hS).map i
  IsClosedImmersion f ∧ f.ker ^ 2 = ⊥

variable {B S hS}

/-- A section over `T'` lifting a commutative solid square for a transformation. -/
public abbrev IsLift {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v} (a : F ⟶ G)
    {T T' : BigFppfOver B S hS} (i : T ⟶ T') (x : F.obj (op T)) (y : G.obj (op T'))
    (z : F.obj (op T')) : Prop :=
  F.map i.op z = x ∧ a.app (op T') z = y

/-- **Stacks 049S, part (1).** Every commutative affine square against a
square-zero closed immersion admits a lift. -/
@[stacks 049S "part (1)",
  stacks 060G "formal smoothness of a morphism of algebraic spaces",
  sga "3 XI 1.6" "formally smooth"]
public abbrev FormallySmooth {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v} (a : F ⟶ G) : Prop :=
  ∀ (T T' : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
    IsAffine ((BigFppfOver.toScheme B S hS).obj T') → ∀ (i : T ⟶ T'),
      IsSquareZeroClosedImmersion B S hS i → ∀ (x : F.obj (op T)) (y : G.obj (op T')),
        a.app (op T) x = G.map i.op y → ∃ z : F.obj (op T'), IsLift a i x y z

/-- **Stacks 049S, part (2).** Every commutative affine square against a
square-zero closed immersion admits exactly one lift. -/
@[stacks 049S "part (2)",
  stacks 04GC "formally étale for a morphism of algebraic spaces",
  sga "3 XI 1.6" "formally étale"]
public abbrev FormallyEtale {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v} (a : F ⟶ G) : Prop :=
  ∀ (T T' : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
    IsAffine ((BigFppfOver.toScheme B S hS).obj T') → ∀ (i : T ⟶ T'),
      IsSquareZeroClosedImmersion B S hS i → ∀ (x : F.obj (op T)) (y : G.obj (op T')),
        a.app (op T) x = G.map i.op y → ∃! z : F.obj (op T'), IsLift a i x y z

/-- **Stacks 049S, part (3).** Every commutative affine square against a
square-zero closed immersion admits at most one lift. -/
@[stacks 049S "part (3)",
  stacks 04G7 "formally unramified morphism of algebraic spaces",
  sga "3 XI 1.6" "formally unramified"]
public abbrev FormallyUnramified {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v} (a : F ⟶ G) :
    Prop :=
  ∀ (T T' : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
    IsAffine ((BigFppfOver.toScheme B S hS).obj T') → ∀ (i : T ⟶ T'),
      IsSquareZeroClosedImmersion B S hS i → ∀ (x : F.obj (op T)) (y : G.obj (op T')),
        a.app (op T) x = G.map i.op y → ∀ z₁ z₂ : F.obj (op T'),
          IsLift a i x y z₁ → IsLift a i x y z₂ → z₁ = z₂

end AlgebraicGeometry.Space

end
