module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentWeakSerre
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import StacksCore.Tactic.StacksAttribute

/-!
# Kernels and cokernels of coherent sheaves of modules

On a ringed space, both the kernel and the cokernel of a morphism between coherent sheaves of
modules are coherent.

## Main results

* `SheafOfModules.kernel_isCoherent` states closure of coherent modules under kernels.
* `SheafOfModules.cokernel_isCoherent` states closure of coherent modules under cokernels.
* `SheafOfModules.coherentModules_isWeakSerreClass`: coherent modules form a weak Serre
  subcategory.

## Implementation notes

Kernels and cokernels are the categorical ones in the category of sheaves of modules, and
coherence is the predicate `SheafOfModules.IsCoherent`.

Two definitionally identical coherence predicates on sheaves of modules are in scope:
`SheafOfModules.IsCoherent` and `Stacks.SheafOfModules.IsCoherent`. They are declared
independently and so are distinct constants, but they have the same two fields, hence
`SheafOfModules.isCoherent_iff`, which lets the closure results proved for the second be read as
results about the first.

## References

* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
-/

public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace SheafOfModules

variable {X : Type u} [TopologicalSpace X]
  {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}

/-- The two coherence predicates on sheaves of modules over a ringed space have the same two
fields, so they agree. -/
theorem isCoherent_iff (M : SheafOfModules.{u} R) :
    M.IsCoherent ↔ Stacks.SheafOfModules.IsCoherent M :=
  ⟨fun h => ⟨h.isFiniteType, h.kernel_isFiniteType⟩,
    fun h => ⟨h.isFiniteType, h.kernel_isFiniteType⟩⟩

/-- A kernel of a morphism of coherent sheaves of modules is coherent. -/
@[stacks 01BY "kernel_coherent", ega "0 5.3.4" "Ker(u) coherent"]
instance kernel_isCoherent {F G : SheafOfModules.{u} R} [F.IsCoherent] [G.IsCoherent]
    (f : F ⟶ G) : (kernel f).IsCoherent := by
  have hF := (isCoherent_iff F).mp ‹F.IsCoherent›
  have hG := (isCoherent_iff G).mp ‹G.IsCoherent›
  exact (isCoherent_iff _).mpr (Stacks.SheafOfModules.isCoherent_kernel f)

/-- The cokernel of a morphism of coherent sheaves of modules is coherent. -/
@[stacks 01BY "cokernel_coherent", instance, ega "0 5.3.4" "Coker(u) coherent"]
theorem cokernel_isCoherent {F G : SheafOfModules.{u} R} [F.IsCoherent] [G.IsCoherent]
    (f : F ⟶ G) : (cokernel f).IsCoherent := by
  have hF := (isCoherent_iff F).mp ‹F.IsCoherent›
  have hG := (isCoherent_iff G).mp ‹G.IsCoherent›
  exact (isCoherent_iff _).mpr
    (ObjectProperty.prop_cokernel (P := fun M => Stacks.SheafOfModules.IsCoherent M) f hF hG)

/-- The two coherence predicates are equal as object properties. -/
theorem coherentModules_eq :
    (fun M : SheafOfModules.{u} R => M.IsCoherent) =
      (fun M : SheafOfModules.{u} R => Stacks.SheafOfModules.IsCoherent M) := by
  funext M
  exact propext (isCoherent_iff M)

/-- **Stacks Project, Tag 01BY (5).** Coherent sheaves of modules on a ringed space form a weak
Serre subcategory of all sheaves of modules. -/
instance coherentModules_isWeakSerreClass :
    ObjectProperty.IsWeakSerreClass (fun M : SheafOfModules.{u} R => M.IsCoherent) :=
  (coherentModules_eq (X := X) (R := R)) ▸
    (Stacks.SheafOfModules.coherentModules_isWeakSerreClass (X := X) (R := R))

end SheafOfModules
