module

public import Mathlib.Algebra.Colimit.Ring
public import StacksCore.Tactic.StacksAttribute

/-!
# Directed sets and systems of rings

A directed set is a nonempty preorder in which every pair of elements has a common upper bound.
A system of rings over such an index consists of rings and compatible transition homomorphisms.

## Main definitions

* `IsDirected` expresses the common-upper-bound condition.
* `DirectedSystem` expresses the identity and composition laws for transition maps.

## Implementation notes

The source's directed sets are represented by a type `I` with instances `Preorder I`,
`Nonempty I` and `IsDirectedOrder I`, the last being Mathlib's specialization of `IsDirected`.
A system of rings is represented by a family `A : I → Type*` with ring instances, ring
homomorphisms `φ i j h : A i →+* A j`, and a `DirectedSystem A` instance for their underlying
maps. The general Mathlib notions are therefore adopted directly rather than wrapped in
ring-specific aliases.

## References

* [Stacks Project, Tag 078I](https://stacks.math.columbia.edu/tag/078I)
-/

@[expose] public section

add_to_stacks 078I "directed sets" IsDirected
add_to_stacks 078I "systems of rings" DirectedSystem
