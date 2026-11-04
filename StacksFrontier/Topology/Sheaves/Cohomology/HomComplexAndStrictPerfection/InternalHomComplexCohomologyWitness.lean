module

public import Mathlib.Topology.Sheaves.Skyscraper
public import StacksFrontier.Topology.Sheaves.Cohomology.HomComplexAndStrictPerfection.InternalHomComplexCohomology

/-!
# A non-degenerate instance of the data of Stacks 0A8L

[Stacks, Tag 0A8L] is a statement about a ringed space `(X, O_X)`, two complexes `L` and `M` of
`O_X`-modules, an open `U ⊆ X` and an integer `n`; after
`Stacks.SheafOfModules.sheafHomComplexHomologyEquiv` it carries no further hypothesis. This file
exhibits that data concretely, at an arbitrary universe `u`, and records that the instance is not
degenerate: the open is nonempty and proper, the structure sheaf has a nonzero ring of sections
over it, and the complexes are the unit module in degree zero rather than the zero complex.

The space is a two-point discrete space, the sheaf of rings is the skyscraper sheaf at one of the
two points with value `ULift ℤ`, and the open is the singleton on which the skyscraper is
supported. Nothing below is used elsewhere; it exists so that the statement of
[Stacks, Tag 0A8L] can be seen to be about a situation that occurs.

## Main definitions

* `Stacks.SheafOfModules.SheafHomComplexWitness.space`,
  `Stacks.SheafOfModules.SheafHomComplexWitness.ringSheaf`,
  `Stacks.SheafOfModules.SheafHomComplexWitness.openSet` and
  `Stacks.SheafOfModules.SheafHomComplexWitness.complex`: the data.
* `Stacks.SheafOfModules.SheafHomComplexWitness.equiv`: [Stacks, Tag 0A8L] at that data.

## Main results

* `Stacks.SheafOfModules.SheafHomComplexWitness.mem_openSet` and
  `Stacks.SheafOfModules.SheafHomComplexWitness.openSet_ne_top`: the open is nonempty and proper.
* `Stacks.SheafOfModules.SheafHomComplexWitness.sections_nontrivial`: the ring of sections of the
  structure sheaf over the open is nonzero.

## References

* [Stacks Project, Tag 0A8L](https://stacks.math.columbia.edu/tag/0A8L)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.SheafOfModules.SheafHomComplexWitness

/-- A two-point discrete space, at an arbitrary universe. -/
def space : TopCat.{u} := @TopCat.of (ULift.{u} Bool) ⊥

/-- Membership of the base point in an open is decided classically; the choice is named so that
the skyscraper sheaf below and the computation of its sections use the same instance. -/
noncomputable def decBasePoint : (U : Opens space.{u}) →
    Decidable ((ULift.up false : space.{u}) ∈ U) := fun _ ↦ Classical.dec _

/-- A sheaf of commutative rings on `space` whose sections over any open containing the base point
are `ULift ℤ`: the skyscraper sheaf at the base point. -/
noncomputable def ringSheaf : TopCat.Sheaf CommRingCat.{u} space.{u} :=
  @skyscraperSheaf space.{u} (ULift.up false) decBasePoint.{u}
    CommRingCat.{u} _ (CommRingCat.of (ULift.{u} ℤ)) _

/-- The open on which the skyscraper sheaf is supported: the singleton of the base point. Every
subset of `space` is open. -/
def openSet : Opens space.{u} := ⟨{ULift.up false}, trivial⟩

/-- A complex of modules over the structure sheaf which is the unit module in degree `0` and zero
elsewhere. -/
noncomputable def complex : CochainComplex (StructureSheafModules ringSheaf.{u}) ℤ :=
  (HomologicalComplex.single (StructureSheafModules ringSheaf.{u}) (ComplexShape.up ℤ) 0).obj
    (SheafOfModules.unit _)

/-- The base point lies in `openSet`, so `openSet` is nonempty. -/
theorem mem_openSet : (ULift.up false : space.{u}) ∈ openSet.{u} := rfl

/-- `openSet` is a proper open: the other point of `space` is not in it. -/
theorem openSet_ne_top : openSet.{u} ≠ ⊤ := by
  intro h
  have hmem : (ULift.up true : space.{u}) ∈ openSet.{u} := h ▸ trivial
  exact Bool.noConfusion (congrArg ULift.down (Set.mem_singleton_iff.mp hmem))

/-- The ring of sections of the structure sheaf over `openSet` is nonzero: it is `ULift ℤ`. -/
theorem sections_nontrivial :
    Nontrivial ((structureSheaf ringSheaf.{u}).obj.obj (op openSet.{u})) := by
  have key : ringSheaf.{u}.obj.obj (op openSet.{u}) = CommRingCat.of (ULift.{u} ℤ) :=
    ite_eq_left mem_openSet.{u}
  have key' : (structureSheaf ringSheaf.{u}).obj.obj (op openSet.{u}) =
      RingCat.of (ULift.{u} ℤ) :=
    congrArg (fun A : CommRingCat.{u} ↦ (forget₂ CommRingCat RingCat).obj A) key
  exact key' ▸ (inferInstance : Nontrivial (ULift.{u} ℤ))

/-- Degree `0` of `complex` is the unit module, which by `sections_nontrivial` has a nonzero group
of sections over `openSet`; so `complex` is not the zero complex. -/
noncomputable def complexXZero :
    complex.{u}.X 0 ≅ SheafOfModules.unit (structureSheaf ringSheaf.{u}) :=
  HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _

/-- [Stacks, Tag 0A8L] at the data above: the statement is instantiable at a concrete ringed space,
a concrete nonempty proper open and concrete nonzero complexes, at an arbitrary universe `u`. -/
noncomputable def equiv :=
  sheafHomComplexHomologyEquiv ringSheaf.{u} openSet complex complex 0

end Stacks.SheafOfModules.SheafHomComplexWitness

end
