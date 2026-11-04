module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablePresentingRing

/-!
# Adic\* affine formal algebraic spaces are countably indexed

An adic\* affine formal algebraic space over `S` is countably indexed: the powers of an ideal of
definition of its presenting ring form a countable fundamental system of neighbourhoods of zero.
These results are stated next to `StacksFrontier.AlgebraicGeometry.FormalSpace.CountablePresentingRing`
but kept in a module of their own, so that that module stays as it is on the base.

## Main definitions

* `AlgebraicGeometry.FormalSpace.IsCountablyIndexedOfIsAdicStar'`: The statement that every
  adic\* affine formal algebraic space over `S` is countably indexed.

## Main results

* `AlgebraicGeometry.FormalSpace.isCountablyIndexedOfIsAdicStar'`: Every adic\* affine formal
  algebraic space over `S` is countably indexed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Filter

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The affine implication from adic\* to countably indexed of the list of **Stacks 0AKY**: every
adic\* affine formal algebraic space over `S` is countably indexed. It is proved by
`AlgebraicGeometry.FormalSpace.isCountablyIndexedOfIsAdicStar'` below and so is a hypothesis of
nothing. -/
abbrev IsCountablyIndexedOfIsAdicStar' : Prop :=
  ∀ U : FppfSheaf B S hS, IsAdicStar B S hS U → IsCountablyIndexed B S hS U

/-- **An adic\* affine formal algebraic space is countably indexed.** The powers of an ideal of
definition of an adic topological ring are a countable fundamental system of neighbourhoods of
zero, so the presenting ring of an adic\* affine formal algebraic space has countably generated
`nhds 0`, and Stacks 0AN1 turns that into countable indexing of the space.

Untagged: Stacks 0AKY is a list of definitions, whose covering set is the five predicates of
`StacksFrontier/AlgebraicGeometry/FormalSpace/Types.lean`; this is the implication between two of
them that the source records in passing. -/
theorem isCountablyIndexedOfIsAdicStar' : IsCountablyIndexedOfIsAdicStar' B S hS := by
  rintro U ⟨-, A, instCR, instTS, instTR, instLT, hApres, hAadic, -⟩
  let : CommRing A := instCR
  let : TopologicalSpace A := instTS
  let : IsTopologicalRing A := instTR
  let : IsLinearTopology A A := instLT
  exact isCountablyIndexed_of_isPresentingRing B S hS U A hApres
    (Rig.countablyGenerated_nhds_of_isAdicRing hAadic)

end AlgebraicGeometry.FormalSpace

end
