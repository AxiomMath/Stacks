module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAssociatedChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedFiniteTypeOnCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteDirectImageCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentFinitePresentation

/-!
# The associated module of a coherent module is coherent

For an object `Z` of the big fppf site whose algebraic space `h_Z` is étale-locally locally
Noetherian, the associated module `𝒢ᵃ` on the small étale site of `h_Z`
(`AlgebraicGeometry.Space.representedModuleOf`) of a quasi-coherent `𝒪_{Z₀}`-module of finite
type is coherent: it is quasi-coherent, of finite type on the site
(`AlgebraicGeometry.Space.isFiniteTypeOnSite_representedQuasicoherentSchemeEquivalence`), and on
a locally Noetherian algebraic space such a module is coherent ([Stacks, Tag 07UB]).

## Main results

* `AlgebraicGeometry.Space.isCoherent_representedModuleOf`: the statement above.

## References

* [Stacks Project, Tag 07UB](https://stacks.math.columbia.edu/tag/07UB)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The associated module of a quasi-coherent module of finite type is coherent** on a
represented algebraic space which is étale-locally locally Noetherian. -/
theorem isCoherent_representedModuleOf (Z : BigFppfOver B S hS)
    (hZ : HasEtaleLocalProperty B S hS (yoneda.obj Z) (fun V : Scheme.{u} => IsLocallyNoetherian V))
    (G : ((BigFppfOver.toScheme B S hS).obj Z).Modules) (hG : G.IsQuasicoherent)
    (hft : SheafOfModules.IsFiniteType G) :
    IsCoherent B S hS (yoneda.obj Z) (isAlgebraicSpace_yoneda B S hS Z)
      (representedModuleOf B S hS Z G) := by
  have : Fact (HasEtaleLocalProperty B S hS (yoneda.obj Z)
      (fun V : Scheme.{u} => IsLocallyNoetherian V)) := ⟨hZ⟩
  have h1 := isFiniteTypeOnSite_representedQuasicoherentSchemeEquivalence B S hS Z G hG hft
  exact (isCoherent_iff_isQuasicoherentOnSite_and_isFiniteType B S hS _ _ _).2
    ⟨isQuasicoherentOnSite_representedModuleOf B S hS Z G hG,
      Stacks.SheafOfModules.presheafIsFiniteType_of_isFiniteTypeOnSite _ h1⟩

end AlgebraicGeometry.Space

end
