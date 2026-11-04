module

public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Algebra.Module
public import StacksFrontier.Topology.Algebra.Ring

@[expose] public section

/-!
# Ideals of definition, admissible and adic topological rings

Stacks Project, Chapter 15 "More on Algebra". The tags treated here are

07E8.

## Tag 07E8 — Topological rings and modules

This file records topological modules and their continuous homomorphisms, linear topologies,
ideals of definition, and the pre-admissible, admissible, pre-adic, and adic conditions on a
topological ring.

### Main definitions

* `TopModuleCat`: Mathlib's category of topological modules, whose objects are the modules over a
  topological ring whose addition and scalar multiplication are continuous.
* `ContinuousLinearMap` and `StacksTopologicalRingHom`: continuous module and ring homomorphisms.
* `IsIdealOfDefinition`: an open ideal whose powers are cofinal among the neighborhoods
  of zero.
* `IsPreAdmissible` and `IsAdmissible`: existence of an ideal of definition,
  without and with completeness.
* `IsPreAdic` and `IsAdic`: an adic topology defined by an ideal of definition,
  without and with completeness.

### Main results

* `preAdic_and_adic_iff_admissible_and_open_powers`: the source's equivalent
  description in terms of an ideal of definition all of whose positive powers are open.

### Implementation notes

Mathlib's `IsTopologicalRing`, `IsLinearTopology`, and root-level `IsAdic` express respectively
topological rings, linear topologies, and equality with the topology defined by the powers of a
fixed ideal. Completeness is expressed using the canonical right uniformity of the additive
topological group, together with the Hausdorff condition required by the source. For a commutative
ring, `IsLinearTopology R R` gives the source's basis of ideals.

### References

* [EGA I, Chapter 0, Sections 7.1 and 7.2]
* [Stacks Project, Tag 07E8](https://stacks.math.columbia.edu/tag/07E8)

-/

namespace TopologicalRing

/-! ### Stacks Tag 07E8 -/

section

section

@[expose] public section

open Filter
open scoped Topology

universe u v w

add_to_stacks 07E8 "(1), topological rings" IsTopologicalRing
add_to_stacks 07E8 "(1), topological modules" TopModuleCat
add_to_stacks 07E8 "(2), homomorphisms of topological modules" ContinuousLinearMap
add_to_sga "3 VIIB 0.2" ContinuousLinearMap
add_to_sga "3 VIIB 0.2.2" ContinuousLinearMap
add_to_sga "3 VIIB 0.3.6" ContinuousLinearMap
add_to_sga "3 VIIB 0.5.B" ContinuousLinearMap
add_to_sga "3 VIIB 1.3.5.A" ContinuousLinearMap
add_to_sga "6 II AppII.3.0.2" ContinuousLinearMap
add_to_ega "0 18.5.3" "partial" ContinuousLinearMap
add_to_ega "0 19.1.1" ContinuousLinearMap
add_to_stacks 07E8 "(2), homomorphisms of topological rings" StacksTopologicalRingHom
add_to_stacks 07E8 "(3), linear topologies" IsLinearTopology
add_to_ega "0 20.3.1" IsLinearTopology
add_to_ega "0 7.1.1" IsLinearTopology

/-- An ideal of definition is open and its powers are cofinal among the neighborhoods of zero. -/
@[stacks 07E8 "(4)"]
public def IsIdealOfDefinition {R : Type u} [CommRing R] [TopologicalSpace R]
    (I : Ideal R) : Prop :=
  IsOpen (I : Set R) ∧
    ∀ U ∈ 𝓝 (0 : R), ∃ n : ℕ, ((I ^ n : Ideal R) : Set R) ⊆ U

/-- A topological ring is pre-admissible if it has an ideal of definition. -/
@[stacks 07E8 "(5)"]
public def IsPreAdmissible (R : Type u) [CommRing R] [TopologicalSpace R] : Prop :=
  ∃ I : Ideal R, IsIdealOfDefinition I

/-- Completeness for an additive topological group, including the Hausdorff condition. -/
public def IsComplete (R : Type u) [Ring R] [TopologicalSpace R] [IsTopologicalRing R] : Prop :=
  T2Space R ∧ @CompleteSpace R (IsTopologicalAddGroup.rightUniformSpace R)

/-- A topological ring is admissible if it is pre-admissible and complete. -/
@[stacks 07E8 "(6)", ega "0 7.1.2" "admissible"]
public def IsAdmissible (R : Type u) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] : Prop :=
  IsPreAdmissible R ∧ IsComplete R

/-- A topological ring is pre-adic if an ideal of definition defines its topology through its
powers. -/
@[stacks 07E8 "(7)"]
public def IsPreAdic (R : Type u) [CommRing R] [TopologicalSpace R] : Prop :=
  ∃ I : Ideal R, IsIdealOfDefinition I ∧ _root_.IsAdic I

/-- A topological ring is adic if it is pre-adic and complete. -/
@[stacks 07E8 "(8)", ega "0 7.1.9" "preadic (J^n a basis)"]
public def IsAdic (R : Type u) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] : Prop :=
  IsPreAdic R ∧ IsComplete R

end

end

section

open Filter
open scoped Topology

universe u

/-- A (pre-)adic topological ring is equivalently a (pre-)admissible topological ring possessing
an ideal of definition all of whose positive powers are open. -/
@[stacks 07E8 "equivalent characterization"]
public theorem preAdic_and_adic_iff_admissible_and_open_powers
    {R : Type u} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsLinearTopology R R] :
    (IsPreAdic R ↔ IsPreAdmissible R ∧
      ∃ I : Ideal R, IsIdealOfDefinition I ∧
        ∀ n : ℕ, 1 ≤ n → IsOpen ((I ^ n : Ideal R) : Set R)) ∧
    (IsAdic R ↔ IsAdmissible R ∧
      ∃ I : Ideal R, IsIdealOfDefinition I ∧
        ∀ n : ℕ, 1 ≤ n → IsOpen ((I ^ n : Ideal R) : Set R)) := by
  have hpre : IsPreAdic R ↔ IsPreAdmissible R ∧
      ∃ I : Ideal R, IsIdealOfDefinition I ∧
        ∀ n : ℕ, 1 ≤ n → IsOpen ((I ^ n : Ideal R) : Set R) := by
    constructor
    · rintro ⟨I, hIdef, hIadic⟩
      exact ⟨⟨I, hIdef⟩, I, hIdef, fun n _ ↦ (isAdic_iff.mp hIadic).1 n⟩
    · rintro ⟨_, I, hIdef, hopen⟩
      refine ⟨I, hIdef, isAdic_iff.mpr ⟨fun n ↦ ?_, hIdef.2⟩⟩
      rcases n with _ | n
      · simp
      · exact hopen (n + 1) (by omega)
  refine ⟨hpre, ?_⟩
  rw [IsAdic, IsAdmissible, hpre]
  tauto

end

end

end TopologicalRing

end
