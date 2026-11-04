module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyBrutalDuality
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyCechTransferCup

/-!
# The pairings of the graded pieces through the top degree

Let `K` be a bounded below complex of `𝒪_X`-modules vanishing above degree `d` and `γ` a pairing
of `K` with itself into itself. For `a + b = d` the pairing of the graded pieces
`Kᵃ[-a] ⊗ Kᵇ[-b] ⟶ K` (`Stacks.Cech.Hypercohomology.gradedPairing`) lands in the top degree: read
in `σ^{≤d}K = K`, it is the pairing `Kᵃ[-a] ⊗ Kᵇ[-b] ⟶ Kᵈ[-d]` attached to the bidegree `(a, b)`
component of `γ`, followed by the inclusion `Kᵈ[-d] ⟶ σ^{≤d}K` of the top term.

## Main results

* `Stacks.Cech.Hypercohomology.gradedPairing_comp_truncLEπ`: the comparison of pairings.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.CechSheaf (SectionRing sectionsPresheafFunctor)
open Stacks.Cech.LinearCupProduct (ComplexPairing tensorPresheafModules)

universe u

namespace Stacks.Cech.Hypercohomology

attribute [local instance] ModuleCat.hasLimitsOfSize ModuleCat.hasColimitsOfSize
attribute [local instance high] Stacks.Cech.Refinement.sectionCommRing

variable {X : TopCat.{u}} {O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  (K : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))) (γ : Pairing O K K K) (d : ℤ)
  (hd : ∀ n, d < n → IsZero (K.obj.X n))

/-- **The pairing of the graded pieces in bidegree `(a, b)`, `a + b = d`, through the top
degree**: read in `σ^{≤d}K`, it is the pairing `Kᵃ[-a] ⊗ Kᵇ[-b] ⟶ Kᵈ[-d]` attached to the
bidegree `(a, b)` component `μ₀` of `γ`, followed by the inclusion of the top term. -/
theorem gradedPairing_comp_truncLEπ (a b : ℤ) (hab : a + b = d)
    (μ₀ : Stacks.Cech.LinearCupProduct.Pairing (SectionRing (ringSheaf O) ⊤)
      (sectionsP O (K.obj.X a)) (sectionsP O (K.obj.X b)) (sectionsP O (K.obj.X d)))
    (hγ : γ.μ a b d hab = μ₀) :
    ComplexPairing.comp (gradedPairing K γ d hd a b hab)
        ((Stacks.Cech.Refinement.sectionsComplex O).map (truncLEπ O K d).hom) =
      ComplexPairing.comp (singlePairingAtTo O a b d hab μ₀)
        ((Stacks.Cech.Refinement.sectionsComplex O).map (truncLEι O K d).hom) := by
  subst hab
  refine ComplexPairing.ext' fun a' b' n hn => ?_
  rw [ComplexPairing.comp_μ, ComplexPairing.comp_μ]
  by_cases h : a' = a ∧ b' = b
  · obtain ⟨rfl, rfl⟩ := h
    subst hn
    rw [gradedPairing_μ, singlePairingAtTo_rfl, singlePairingAt_μ, hγ,
      sectionsComplex_truncLEπ_f K (a' + b') (a' + b') le_rfl]
    simp only [Category.assoc]
    congr 3
    rw [← cancel_mono (truncLESectionsXIso K (a' + b') (a' + b') le_rfl).hom, Category.assoc,
      sectionsComplex_truncLEι_f K (a' + b'), Iso.inv_hom_id, Iso.inv_hom_id]
  · rw [gradedPairing_μ_of_ne K γ (a + b) hd a b rfl a' b' n hn h, singlePairingAtTo_rfl,
      singlePairingAt_μ_of_ne _ _ _ a' b' n hn h, Limits.zero_comp, Limits.zero_comp]

end Stacks.Cech.Hypercohomology

end
