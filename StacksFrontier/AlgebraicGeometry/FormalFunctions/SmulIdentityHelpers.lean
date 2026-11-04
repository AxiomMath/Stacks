module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedRealizationModule

/-!
# A hypothesis-free step of the sheaf-level identity of [Stacks, Tag 0897]

The `B`-linearity of [Stacks, Tag 0897]'s comparison `⨁ₙ Hᵖ(X, Mₙ) ≅ Hᵖ(X', F')` reduces to one
identity of morphisms of sheaves in each degree, and the proof of that identity has two steps
which mention neither the graded algebra the development is about nor the graded module: the
compatibility of the degree-`i` inclusion into the ungraded realization with restriction, and the
re-association that assembles the identity out of its two halves. **This file collects them**, so
that the assembly can be run both for the Rees algebra `⨁ₙ ℐⁿ` of [Stacks, Tag 02O8] and for the
`𝓑 = f^* B̃` of [Stacks, Tag 0897] without either development depending on the other.

## Main results

* `Stacks.Cohomology.FormalFunctions.gradedAlgebra_ungradedSheaf_map_ungradedIncl_eval`:
  **the degree-`i` inclusion of a global section of a homogeneous piece commutes with restriction**
  — the section it names in the ungraded realization over a smaller open is the inclusion of its
  restriction.

The re-association that assembles the identity out of its two halves is the base's
`Stacks.Cohomology.FormalFunctions.rees_assemble` (`ReesSmulCompatible.lean`), used as it is.
The degree-`i` lemma is stated for an arbitrary commutative graded algebra `𝓑`; the base's
`Stacks.Cohomology.FormalFunctions.ungradedSheaf_map_ungradedIncl_eval` is its instance at the
Rees algebra, hence the distinct name.

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.Cohomology.FormalFunctions

/-- **The degree-`i` inclusion of a global section of a homogeneous piece commutes with
restriction**: the section it names in the ungraded realization over a smaller open is the
inclusion of its restriction. -/
public theorem gradedAlgebra_ungradedSheaf_map_ungradedIncl_eval {Y : Scheme.{u}}
    (𝓑 : SheafOfModules.GradedAlgebra.{u, u} Y.ringCatSheaf) [𝓑.IsCommutative]
    (i : ℤ) (s : (𝓑.piece i).val.sections) {U V : (Opens ↥Y)ᵒᵖ} (f : U ⟶ V) :
    (𝓑.ungradedSheaf.obj.map f).hom (𝓑.ungradedIncl i (s.eval U)) =
      𝓑.ungradedIncl i (s.eval V) := by
  refine Eq.trans (𝓑.toPresheafGradedAlgebra.totalSheafRestrict_inclSheaf
    (J := Opens.grothendieckTopology ↥Y) f i (s.eval U)) ?_
  exact congrArg (𝓑.ungradedIncl i) (PresheafOfModules.sections_property s f)

end Stacks.Cohomology.FormalFunctions

end
