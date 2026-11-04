module

public import Mathlib.CategoryTheory.Action.Continuous
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.Topology.Algebra.OpenSubgroup
public import StacksCore.Tactic.StacksAttribute

/-!
# Continuity of a representation on a finite module

Deformations of a *continuous* representation of a topological group are deformations of the
underlying representation whose associated action on the discrete deformed module is
continuous. For a finitely generated module this is the same as continuity of the representation
itself into the general linear group with the discrete topology: continuity of the action makes
the stabilizer of each of finitely many generators open, hence the kernel of the representation
open, which is continuity at the identity.

## Main results

* `Deformation.Examples.continuous_representation_iff_continuousSMul`: for a finitely generated
  module, a representation is continuous into the discrete general linear group if and only if
  the induced action on the discrete module is continuous.

## Implementation notes

The action associated with the representation is the canonical action of the general linear
group restricted along the representation. Both the general linear group and the module are
explicitly given the discrete topology in the statement. The argument needs nothing about
Artinian local algebras and is stated for modules over an arbitrary semiring.

## References

* [Stacks Project, Tag 0D3K](https://stacks.math.columbia.edu/tag/0D3K)
-/

@[expose] public section

namespace Deformation.Examples

/-- For a finitely generated module over a semiring, a representation is continuous into the
discrete general linear group if and only if the induced action on the discrete module is
continuous. -/
@[stacks 0D3K "continuity_equivalence"]
public theorem continuous_representation_iff_continuousSMul
    (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M] [Module.Finite R M]
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (ρ : Γ →* LinearMap.GeneralLinearGroup R M) :
    letI : TopologicalSpace (LinearMap.GeneralLinearGroup R M) := ⊥
    letI : TopologicalSpace M := ⊥
    letI : MulAction Γ M := MulAction.compHom M ρ
    Continuous ρ ↔ ContinuousSMul Γ M := by
  let : TopologicalSpace (LinearMap.GeneralLinearGroup R M) := ⊥
  let : TopologicalSpace M := ⊥
  let : MulAction Γ M := MulAction.compHom M ρ
  have : DiscreteTopology (LinearMap.GeneralLinearGroup R M) := discreteTopology_bot _
  have : DiscreteTopology M := discreteTopology_bot _
  refine ⟨fun hρ => ?_, fun hact => ?_⟩
  · have : ContinuousSMul (LinearMap.GeneralLinearGroup R M) M :=
      ⟨continuous_of_discreteTopology⟩
    exact MulAction.continuousSMul_compHom hρ
  · obtain ⟨S, hSfinite, hSspan⟩ := Submodule.fg_def.mp (Module.Finite.fg_top (R := R) (M := M))
    have hUopen : IsOpen (⋂ m ∈ S, (MulAction.stabilizer Γ m : Set Γ)) :=
      hSfinite.isOpen_biInter fun m _ =>
        (continuousSMul_iff_stabilizer_isOpen (M := Γ) (X := M)).mp hact m
    have hkeropen : IsOpen (ρ.ker : Set Γ) :=
      Subgroup.isOpen_of_mem_nhds ρ.ker <|
        Filter.mem_of_superset (hUopen.mem_nhds (x := 1) (by simp)) fun g hg =>
          Units.ext <| LinearMap.ext_on hSspan fun x hx => Set.mem_iInter₂.mp hg x hx
    apply continuous_of_continuousAt_one ρ
    rw [ContinuousAt, nhds_discrete (LinearMap.GeneralLinearGroup R M), Filter.tendsto_pure,
      map_one]
    exact hkeropen.mem_nhds (by simp)

end Deformation.Examples
