module

public import Mathlib.RingTheory.Noetherian.Defs
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.McQuillan
public import StacksFrontier.Topology.Algebra.AdicTopology.AdmissibleRings
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdic
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissible

/-!
# Types of affine formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`. An affine formal algebraic space `X`
over `S` is *McQuillan* when it satisfies the equivalent conditions of Stacks 0AIC, and it
then carries an associated weakly admissible topological ring `A`, namely the one whose
quotients by its weak ideals of definition present `X`. Stacks 0AID singles out five types of
McQuillan affine formal algebraic space by a condition on `A`: it is *classical* when `A` is
admissible, *weakly adic* when `A` is weakly adic, *adic* when `A` is adic, *adic\** when `A`
is adic with a finitely generated ideal of definition, and *Noetherian* when `A` is Noetherian
and adic.

## Main definitions

* `AlgebraicGeometry.FormalSpace.IsPresentingRing`: a weakly admissible topological ring
  together with a presentation of the sheaf by the spectra of its quotients, which is the
  associated ring of a McQuillan affine formal algebraic space.
* `AlgebraicGeometry.FormalSpace.IsClassical`,
  `AlgebraicGeometry.FormalSpace.IsWeaklyAdic`, `AlgebraicGeometry.FormalSpace.IsAdic`,
  `AlgebraicGeometry.FormalSpace.IsAdicStar` and
  `AlgebraicGeometry.FormalSpace.IsNoetherian`: the five types of Stacks 0AID.

## Implementation notes

The McQuillan condition is condition (4) of Stacks 0AIC,
`AlgebraicGeometry.FormalSpace.HasSomeSurjectivePresentation`, which already contains
affineness. The equivalence of the five conditions of 0AIC is proved in this library, but above
this file in the import order, and it does not in any case make the associated ring a function
of `X`: what it gives is that the ring exists and is unique up to isomorphism of topological
rings, not a choice of one. Each type is therefore stated
by quantifying existentially over a topological ring presenting `X` in the sense of condition
(1) of 0AIC, that is over a ring `A` carrying an
`AlgebraicGeometry.FormalSpace.WeakIdealColimitPresentation` of `X`. This is faithful,
because by 0AIC a McQuillan space has such a ring and it is determined by `X` up to
isomorphism of topological rings, under which all five ring-theoretic conditions are
invariant.

The ring and its topological structure are bound by ordinary existential quantifiers rather
than by instance binders, since `Exists` takes no instance arguments; the bound variables
are nevertheless available as local instances in the body. The predicates are abbreviations,
so a consumer may use their conjunction and existential structure directly. Adic\* keeps the
finitely generated ideal of definition explicit, and the Noetherian condition asks for
`IsNoetherianRing` together with adicness, as in the source.

## References

* [Stacks Project, Tag 0AID](https://stacks.math.columbia.edu/tag/0AID)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

add_to_stacks 0AID "McQuillan" AlgebraicGeometry.FormalSpace.HasSomeSurjectivePresentation

/-- A weakly admissible topological ring `A` *presents* an fppf sheaf `X` when `X` is the
colimit of the spectra of the quotients of `A` by its weak ideals of definition. By Stacks
0AIC such a ring exists exactly for a McQuillan affine formal algebraic space, and it is then
the associated ring of `X`. -/
abbrev IsPresentingRing (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] (X : FppfSheaf B S hS) : Prop :=
  TopologicalRing.IsWeaklyAdmissible A ∧
    Nonempty (WeakIdealColimitPresentation B S hS A X)

/-- **Stacks 0AID (1).** A McQuillan affine formal algebraic space is *classical* when its
associated weakly admissible topological ring is admissible, that is has an ideal of
definition and is complete. -/
@[stacks 0AID "classical"]
abbrev IsClassical (X : FppfSheaf B S hS) : Prop :=
  HasSomeSurjectivePresentation B S hS X ∧
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
      (_ : IsLinearTopology A A),
      IsPresentingRing B S hS A X ∧ TopologicalRing.IsAdmissible A

/-- **Stacks 0AID (2).** A McQuillan affine formal algebraic space is *weakly adic* when its
associated weakly admissible topological ring is weakly adic, that is the closed powers of a
single ideal form a fundamental system of open ideals. -/
@[stacks 0AID "weakly adic"]
abbrev IsWeaklyAdic (X : FppfSheaf B S hS) : Prop :=
  HasSomeSurjectivePresentation B S hS X ∧
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
      (_ : IsLinearTopology A A),
      IsPresentingRing B S hS A X ∧ TopologicalRing.IsWeaklyAdic A

/-- **Stacks 0AID (3).** A McQuillan affine formal algebraic space is *adic* when its
associated weakly admissible topological ring is adic, that is its topology is the adic
topology of an ideal of definition and it is complete. -/
@[stacks 0AID "adic"]
abbrev IsAdic (X : FppfSheaf B S hS) : Prop :=
  HasSomeSurjectivePresentation B S hS X ∧
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
      (_ : IsLinearTopology A A),
      IsPresentingRing B S hS A X ∧ TopologicalRing.IsAdic A

/-- **Stacks 0AID (4).** A McQuillan affine formal algebraic space is *adic\** when its
associated weakly admissible topological ring is adic and moreover has a finitely generated
ideal of definition. -/
@[stacks 0AID "adic star"]
abbrev IsAdicStar (X : FppfSheaf B S hS) : Prop :=
  HasSomeSurjectivePresentation B S hS X ∧
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
      (_ : IsLinearTopology A A),
      IsPresentingRing B S hS A X ∧ TopologicalRing.IsAdic A ∧
        ∃ I : Ideal A, TopologicalRing.IsIdealOfDefinition I ∧ I.FG

/-- **Stacks 0AID (5).** A McQuillan affine formal algebraic space is *Noetherian* when its
associated weakly admissible topological ring is both a Noetherian ring and adic. -/
@[stacks 0AID "Noetherian"]
abbrev IsNoetherian (X : FppfSheaf B S hS) : Prop :=
  HasSomeSurjectivePresentation B S hS X ∧
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
      (_ : IsLinearTopology A A),
      IsPresentingRing B S hS A X ∧ IsNoetherianRing A ∧ TopologicalRing.IsAdic A

end AlgebraicGeometry.FormalSpace

end
