module

public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.RingedSiteComparisonConverse

/-!
# Pseudo-coherence on a ringed space and on its site of opens

`AlgebraicGeometry.RingedSpace.PseudoCoherence.isPseudoCoherentFrom_ringedSite_iff` identifies
`m`-pseudo-coherence of an object of `D(O_X)` on the ringed space and on its site of opens. Taking
all `m` at once, the two notions of pseudo-coherence agree: Stacks 08FT (3) on the site of opens is
Stacks 08CB (3).

## Main results

* `AlgebraicGeometry.RingedSpace.PseudoCoherence.isPseudoCoherent_ringedSite_iff`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open StrictlyPerfect

universe u d

namespace AlgebraicGeometry.RingedSpace.PseudoCoherence

variable (X : RingedSpace.{u, u}) [HasDerivedCategory.{d} (OXMod.{u} X)]

attribute [local instance] hasDerivedCategoryRingedSite

/-- **Stacks 08FT (3) on the site of opens is Stacks 08CB (3).** -/
theorem isPseudoCoherent_ringedSite_iff (E : DerivedCategory (OXMod.{u} X)) :
    (Stacks.SheafOfModules.ringedSite X.sheaf).IsPseudoCoherent E ↔ IsPseudoCoherent E := by
  refine ⟨fun h => ?_, isPseudoCoherent_ringedSite X E⟩
  obtain ⟨K, hK, ⟨e⟩⟩ := h
  exact ⟨K, fun m => isPseudoCoherentComplexFrom_of_ringedSite X K m (hK m), ⟨e⟩⟩

end AlgebraicGeometry.RingedSpace.PseudoCoherence

end
