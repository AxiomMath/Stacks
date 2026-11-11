module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalScheme.WeakIdealOfDefinitionColimit
public import StacksFrontier.AlgebraicGeometry.FormalScheme.WeakIdealOfDefinitionColimitConverse
public import StacksFrontier.AlgebraicGeometry.FormalScheme.WeakIdealOfDefinitionColimitFppf
public import StacksFrontier.AlgebraicGeometry.FormalScheme.WeakIdealOfDefinitionInf

/-!
# Colimits along thickenings and fundamental systems of weak ideals of definition

**Stacks 0AIV** concludes that the formal algebraic space `h_𝔛` attached to a formal scheme `𝔛` in
the sense of McQuillan is a colimit of schemes along thickenings, as in Stacks 0AIU, if and only if
there exists a fundamental system of weak ideals of definition for `𝔛`. This file assembles the two
directions, the weak ideals of definition being those that correspond to thickenings (cut out by
their sections over the affine formal opens, `IdealSheaf.IsCutOutOn`).

## Main results

* `AlgebraicGeometry.McQuillanFormalScheme.isColimitOfThickenings_iff`: the equivalence.

## Implementation notes

The source's fundamental system is a family of weak ideals of definition `ℐ_λ`, each of which it
turns into the scheme `(𝔛, 𝒪_𝔛/ℐ_λ)`; that scheme exists, and is a thickening of `h_𝔛`, exactly for
the weak ideals of definition cut out by their sections over the affine formal opens
(`StacksFrontier.AlgebraicGeometry.FormalScheme.WeakIdealOfDefinitionCorrespondence`), and the
fundamental systems are taken among those. No directedness is assumed: a fundamental system is
closed up under finite intersections, which preserve both conditions
(`AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf.isCutOutOn_inf`).

## References

* [Stacks Project, Tag 0AIV](https://stacks.math.columbia.edu/tag/0AIV)
* [Stacks Project, Tag 0AIU](https://stacks.math.columbia.edu/tag/0AIU)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf

variable {X : LTRS.{u}}

/-- The closure of a family of ideal sheaves under binary intersections. -/
inductive InfClosure (𝒮 : Set (IdealSheaf X)) : IdealSheaf X → Prop
  | mem {I : IdealSheaf X} : I ∈ 𝒮 → InfClosure 𝒮 I
  | inf {I J : IdealSheaf X} : InfClosure 𝒮 I → InfClosure 𝒮 J → InfClosure 𝒮 (I.inf J)

/-- Every member of the closure under binary intersections of a family of weak ideals of
definition on `𝒜` is a weak ideal of definition on `𝒜`. -/
theorem InfClosure.isWeakIdealOfDefinitionOn {𝒮 : Set (IdealSheaf X)} {𝒜 : Opens X → Prop}
    (h𝒮 : ∀ I ∈ 𝒮, I.IsWeakIdealOfDefinitionOn 𝒜) {I : IdealSheaf X} (hI : InfClosure 𝒮 I) :
    I.IsWeakIdealOfDefinitionOn 𝒜 := by
  induction hI with
  | mem h => exact h𝒮 _ h
  | inf _ _ h₁ h₂ => exact isWeakIdealOfDefinitionOn_inf h₁ h₂

/-- Every member of the closure under binary intersections of a family of weak ideals of
definition cut out by their sections over the weakly affine formal opens is again cut out by its
sections over the weakly affine formal opens. -/
theorem InfClosure.isCutOutOn {𝒮 : Set (IdealSheaf X)}
    (h𝒮 : ∀ I ∈ 𝒮, I.IsWeakIdealOfDefinitionOn (IsWeakAffineFormalOpen X))
    (hC : ∀ I ∈ 𝒮, I.IsCutOutOn (IsWeakAffineFormalOpen X)) {I : IdealSheaf X}
    (hI : InfClosure 𝒮 I) : I.IsCutOutOn (IsWeakAffineFormalOpen X) := by
  induction hI with
  | mem h => exact hC _ h
  | inf h₁ h₂ c₁ c₂ =>
    exact isCutOutOn_inf (h₁.isWeakIdealOfDefinitionOn h𝒮) (h₂.isWeakIdealOfDefinitionOn h𝒮) c₁ c₂

/-- The closure under binary intersections of a fundamental system of weak ideals of definition is
one. -/
theorem isFundamentalSystem_infClosure {𝒮 : Set (IdealSheaf X)} {𝒜 : Opens X → Prop}
    (h : IsFundamentalSystemOfWeakIdealsOfDefinitionOn 𝒮 𝒜) :
    IsFundamentalSystemOfWeakIdealsOfDefinitionOn {I | InfClosure 𝒮 I} 𝒜 := by
  refine ⟨fun I hI => InfClosure.isWeakIdealOfDefinitionOn h.1 hI, fun U hU => ⟨fun N => ?_⟩⟩
  refine ⟨fun hN => ?_, fun ⟨I, hI, hIN⟩ => ?_⟩
  · obtain ⟨I, hI, hIN⟩ := (h.2 U hU).mem_iff.mp hN
    exact ⟨I, InfClosure.mem hI, hIN⟩
  · exact Filter.mem_of_superset
      (((InfClosure.isWeakIdealOfDefinitionOn h.1 hI) U hU).1.mem_nhds (Ideal.zero_mem _)) hIN

end AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf

namespace AlgebraicGeometry.McQuillanFormalScheme

open LocallyTopologicallyRingedSpace

/-- A McQuillan formal scheme `𝔛` satisfies `McQuillanFormalScheme.IsColimitOfThickenings` if and
only if `𝔛` has a fundamental system of weak ideals of definition cut out by their sections over
the weakly affine formal opens: the Zariski form of
`isFppfColimitOfThickenings_iff_exists_isFundamentalSystem`. -/
theorem isColimitOfThickenings_iff (𝔛 : McQuillanFormalScheme.{u}) :
    𝔛.IsColimitOfThickenings ↔ ∃ 𝒮 : Set (IdealSheaf 𝔛.obj),
      (∀ I ∈ 𝒮, I.IsCutOutOn (IsWeakAffineFormalOpen 𝔛.obj)) ∧
        IsFundamentalSystemOfWeakIdealsOfDefinitionOn 𝒮 (IsWeakAffineFormalOpen 𝔛.obj) := by
  refine ⟨fun h => ?_, fun ⟨𝒮, hC, hfund⟩ => ?_⟩
  · obtain ⟨𝒮, -, -, hC, hfund⟩ := IdealSheaf.exists_isFundamentalSystem_of_isColimitOfThickenings h
    exact ⟨𝒮, hC, hfund⟩
  · by_cases hne : 𝒮.Nonempty
    · have hfund' := IdealSheaf.isFundamentalSystem_infClosure hfund
      refine IdealSheaf.isColimitOfThickenings_of_isFundamentalSystem 𝔛.property
        (𝒮 := {I | IdealSheaf.InfClosure 𝒮 I}) (fun I hI => hfund'.1 I hI)
        (fun I hI => IdealSheaf.InfClosure.isCutOutOn hfund.1 hC hI)
        ⟨hne.some, IdealSheaf.InfClosure.mem hne.some_mem⟩
        (fun I hI J hJ => ⟨I.inf J, IdealSheaf.InfClosure.inf hI hJ, fun W => by
          rw [IdealSheaf.inf_ideal]; exact ⟨inf_le_left, inf_le_right⟩⟩) hfund'
    · have hnone : ∀ U : Opens 𝔛.obj, ¬ IsWeakAffineFormalOpen 𝔛.obj U := fun U hU => by
        obtain ⟨I, hI, -⟩ := (hfund.2 U hU).mem_iff.mp Filter.univ_mem
        exact hne ⟨I, hI⟩
      refine IdealSheaf.isColimitOfThickenings_of_isFundamentalSystem 𝔛.property
        (𝒮 := {default}) (fun _ _ U hU => (hnone U hU).elim)
        (fun _ _ U hU => (hnone U hU).elim) ⟨default, rfl⟩
        (fun I hI J hJ => ⟨default, rfl, fun W => by
          rw [Set.mem_singleton_iff.mp hI, Set.mem_singleton_iff.mp hJ]
          exact ⟨le_rfl, le_rfl⟩⟩)
        ⟨fun _ _ U hU => (hnone U hU).elim, fun U hU => (hnone U hU).elim⟩

/-- The functor of points `h_𝔛` of a McQuillan formal scheme is a colimit of schemes along
thickenings, as in Stacks 0AIU, in fppf sheaves if and only if `𝔛` has a fundamental system of
weak ideals of definition cut out by their sections over the weakly affine formal opens. -/
@[stacks 0AIV "h_𝔛 is a colimit of schemes along thickenings as in Lemma 0AIU (colimit in fppf \
sheaves) exactly when there exists a fundamental system of weak ideals of definition, \
CORRECTED: the weak ideals of definition are those cut out by their sections over the affine \
formal opens, the ones to which the correspondence ℐ ↦ (𝔛, 𝒪_𝔛/ℐ) applies (it fails for an \
arbitrary ideal sheaf)"]
theorem isFppfColimitOfThickenings_iff_exists_isFundamentalSystem (𝔛 : McQuillanFormalScheme.{u}) :
    𝔛.IsFppfColimitOfThickenings ↔ ∃ 𝒮 : Set (IdealSheaf 𝔛.obj),
      (∀ I ∈ 𝒮, I.IsCutOutOn (IsWeakAffineFormalOpen 𝔛.obj)) ∧
        IsFundamentalSystemOfWeakIdealsOfDefinitionOn 𝒮 (IsWeakAffineFormalOpen 𝔛.obj) := by
  rw [isFppfColimitOfThickenings_iff]
  exact isColimitOfThickenings_iff 𝔛

end AlgebraicGeometry.McQuillanFormalScheme

end
