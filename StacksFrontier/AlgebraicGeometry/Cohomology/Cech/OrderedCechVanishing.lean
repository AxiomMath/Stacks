module

public import StacksFrontier.AlgebraicGeometry.ProjectiveCohomology.CechCohomologyIso
public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfSheavesOfModules.ModuleValuedAlternatingComparison

/-!
# Vanishing of cohomology from exactness of the ordered Čech complex

Let `X` be a scheme covered by opens `U i`, indexed by a linearly ordered type, all of whose finite
intersections are affine, and let `F` be a quasi-coherent `𝒪_X`-module. By [Stacks, Tag 01XD] the
cohomology of `F` is the cohomology of the Čech complex of the covering, and by [Stacks, Tag 01FM]
that is the cohomology of the ordered Čech complex, indexed by the strictly increasing tuples of
indices. This file records the consequence in the form a computation produces it: **if every
ordered Čech cocycle of `F` in degree `q + 1` is a coboundary, then `H^{q+1}(X, F) = 0`**.

## Main results

* `Stacks.Cohomology.OrderedCech.isZero_rightDerived_sections_of_exact`: the statement above.

## References

* [Stacks Project, Tag 01XD](https://stacks.math.columbia.edu/tag/01XD)
* [Stacks Project, Tag 01FM](https://stacks.math.columbia.edu/tag/01FM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.Cohomology.CechSheaf

universe u

namespace Stacks.Cohomology.OrderedCech

/-- **If every ordered Čech cocycle of degree `q + 1` is a coboundary, `H^{q+1}(X, F)` vanishes**,
for a quasi-coherent module on a scheme covered by opens with affine finite intersections. -/
theorem isZero_rightDerived_sections_of_exact (X : Scheme.{u}) {ι : Type u} [LinearOrder ι]
    (U : ι → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i)
    (haffine : ∀ (r : ℕ) (s : Fin (r + 1) → ι), IsAffineOpen (⨅ k, U (s k)))
    (F : X.Modules) [F.IsQuasicoherent] (q : ℕ)
    (hex : ∀ c : CechCochains.OrdCochain (X := TopCat.of X) U (abSections F) (q + 1),
      CechCochains.ordD (X := TopCat.of X) U (abSections F) (q + 1) c = 0 →
        ∃ b, CechCochains.ordD (X := TopCat.of X) U (abSections F) q b = c) :
    IsZero (((Stacks.Cohomology.sectionsFunctor X ⊤).rightDerived (q + 1)).obj F) := by
  refine IsZero.of_iso ?_ ((Stacks.Cohomology.CechIso.cechHomologyIsoRightDerived X ⊤ U hU
    haffine F (q + 1)).trans (orderedCechHomologyModuleIso ⊤ U hU F (q + 1)).symm)
  refine ((orderedModuleComplex ⊤ U hU F).exactAt_iff_isZero_homology (q + 1)).1 ?_
  rw [(orderedModuleComplex ⊤ U hU F).exactAt_iff' q (q + 1) (q + 1 + 1) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  intro c hc
  have hg : ((orderedModuleComplex ⊤ U hU F).sc' q (q + 1) (q + 1 + 1)).g =
      ordModuleDiff ⊤ U hU F (q + 1) := orderedModuleComplex_d ⊤ U hU F (q + 1)
  have hf : ((orderedModuleComplex ⊤ U hU F).sc' q (q + 1) (q + 1 + 1)).f =
      ordModuleDiff ⊤ U hU F q := orderedModuleComplex_d ⊤ U hU F q
  rw [hg] at hc
  obtain ⟨b, hb⟩ := hex c hc
  exact ⟨b, by rw [hf]; exact hb⟩

end Stacks.Cohomology.OrderedCech

end
