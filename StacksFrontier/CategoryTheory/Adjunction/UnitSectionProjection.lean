module

public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Transporting a unit under a projection of sections

An adjunction built by `CategoryTheory.Adjunction.ofNatIsoRight` — one adjunction read through
an isomorphism of its right adjoint — has a unit which differs from the original one by that
isomorphism.  When the two right adjoints are two *descriptions* of one and the same functor,
and the thing one wants to say about the unit is visible through a projection that both
descriptions share, the difference is invisible: the projection of the two units agree.  Such a
statement is an application of `congrArg`, and a consumer has the equality of the two units on
sections already.

What this file supplies is the *shape* in which that application can be made.  Written directly,
`congrArg pr h` with the goal known elaborates `pr` against a metavariable and then matches
`?pr ?w = ?pr ?w'` against the goal; `Stacks.CategoryTheory.proj_congr` takes the equality
`h` **first**, with the type its two sides live in implicit, so the type of sections is read off
`h` and the projection is checked against it by first-order unification.  The caller never asks
the elaborator to compare two spellings of a type of sections while a metavariable stands in the
projection's place.

## Main results

* `Stacks.CategoryTheory.proj_congr`: an arbitrary projection, applied to an equality of
  sections.

## Implementation notes

The intended consumer is
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleBaseChangeChartUnitTransport.lean`, where the
two right adjoints are the two descriptions of the direct image of modules along an étale
morphism of algebraic spaces, the projection is the chart projection of a section of a direct
image, and the transport of the unit along their comparison is the step whose direct form does
not elaborate.

Two further abstractions **do not fit** the heartbeat budget there, so
neither is stated here.  Transporting the unit along the isomorphism of right adjoints *inside*
the abstract statement — an adjunction, an isomorphism of its right adjoint, a family of types of
sections with an action of the morphisms, and two projections agreeing once the isomorphism is
inserted — is provable in general but cannot be instantiated at the adjunction of Stacks 03D7:
supplying the concrete action of morphisms on sections and the concrete projections exceeds the
budget before the conclusion is reached.  And holding only the module and the two sections
variable, with the equality as a hypothesis, does not help either: the instantiation is then
driven by matching the hypothesis against a binder whose type is written in a different spelling
of the direct image, and it is that match which is expensive.  What does fit is this file's
statement, in which the type of sections is a variable fixed by the hypothesis.
-/

@[expose] public section

namespace Stacks.CategoryTheory

universe t t'

/-- **An arbitrary projection of sections applied to an equality of sections.**  The equality is
the first explicit argument and the type of sections is implicit, so that a consumer supplies a
hypothesis it already has and the projection is then checked against the type that hypothesis
fixes, rather than the other way round. -/
theorem proj_congr {T : Sort t} {T' : Sort t'} {w w' : T} (h : w = w') (pr : T → T') :
    pr w = pr w' :=
  congrArg pr h

end Stacks.CategoryTheory

end
