module

public import StacksFrontier.Topology.Constructible.NormalForm
import StacksCore.Tactic.StacksAttribute

/-!
# Boolean operations on constructible sets in Stacks' normal form

Stacks 005G(1) defines a subset of a topological space `X` to be constructible when it is a
finite union of sets `U ∩ Vᶜ` with `U, V ⊆ X` open and retrocompact; this is the predicate
`IsConstructibleStratified`. Stacks 005H states that this collection of subsets is closed under
finite intersections, finite unions and complements.

The proof transports the closure properties of Mathlib's `Topology.IsConstructible` along
`Topology.isConstructible_iff_isConstructibleStratified`. The substance is in that equivalence:
it uses that the open retrocompact subsets of `X` form a sublattice of `Set X`
(`isSublattice_isOpen_and_isRetrocompact`), which is the content of the Stacks proof.

## Main results

* `IsConstructibleStratified.iUnion`: a finite union of sets in normal form is in normal form.
* `IsConstructibleStratified.iInter`: a finite intersection of sets in normal form is in normal
  form.
* `IsConstructibleStratified.compl`: the complement of a set in normal form is in normal form.

## References

* [Stacks Project, Tag 005H](https://stacks.math.columbia.edu/tag/005H)
-/

@[expose] public section

variable {X : Type*} [TopologicalSpace X] {ι : Type*}

/-- **Stacks 005H** (finite unions).
A finite union of subsets of `X` that are each a finite union of sets `U ∩ Vᶜ` with `U, V`
open and retrocompact in `X` is again such a finite union. -/
@[stacks 005H "finite unions of constructible sets, in the normal form of 005G(1)"]
theorem IsConstructibleStratified.iUnion [Finite ι] {f : ι → Set X}
    (hf : ∀ i, IsConstructibleStratified (f i)) :
    IsConstructibleStratified (⋃ i, f i) :=
  Topology.isConstructible_iff_isConstructibleStratified.mp <|
    Topology.IsConstructible.iUnion fun i ↦
      Topology.isConstructible_iff_isConstructibleStratified.mpr (hf i)

/-- **Stacks 005H** (finite intersections).
A finite intersection of subsets of `X` that are each a finite union of sets `U ∩ Vᶜ` with
`U, V` open and retrocompact in `X` is again such a finite union. -/
@[stacks 005H "finite intersections of constructible sets, in the normal form of 005G(1)"]
theorem IsConstructibleStratified.iInter [Finite ι] {f : ι → Set X}
    (hf : ∀ i, IsConstructibleStratified (f i)) :
    IsConstructibleStratified (⋂ i, f i) :=
  Topology.isConstructible_iff_isConstructibleStratified.mp <|
    Topology.IsConstructible.iInter fun i ↦
      Topology.isConstructible_iff_isConstructibleStratified.mpr (hf i)

/-- **Stacks 005H** (complements).
The complement of a finite union of sets `U ∩ Vᶜ` with `U, V` open and retrocompact in `X` is
again such a finite union. -/
@[stacks 005H "complements of constructible sets, in the normal form of 005G(1)"]
theorem IsConstructibleStratified.compl {s : Set X} (hs : IsConstructibleStratified s) :
    IsConstructibleStratified sᶜ :=
  Topology.isConstructible_iff_isConstructibleStratified.mp <|
    (Topology.isConstructible_iff_isConstructibleStratified.mpr hs).compl
