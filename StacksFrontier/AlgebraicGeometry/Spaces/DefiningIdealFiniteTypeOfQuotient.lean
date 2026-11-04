module

public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.GlobalGenerators
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraDegreeZero
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBinaryProducts
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeOnSiteKernel
public import StacksCore.Tactic.StacksAttribute

/-!
# The ideal sheaf of a closed subspace whose structure-sheaf quotient is finitely presented

Let `X` be an algebraic space over a scheme `S` of a big fppf site and let `Z ⊆ X` be a closed
subspace with inclusion `i` and defining ideal sheaf `𝓘`.  Then `𝓘` is of finite type as soon as
the quotient `i_*𝒪_Z = 𝒪_X/𝓘` is of finite presentation: `𝓘` is the kernel in the short exact
sequence

`0 ⟶ 𝓘 ⟶ 𝒪_X ⟶ i_*𝒪_Z ⟶ 0`

of Stacks 09RP, the structure sheaf is of finite type, and Stacks 082T applies.

## Main results

* `AlgebraicGeometry.Space.isFiniteTypeOnSite_unit_structureRingSheaf`: the structure sheaf is of
  finite type on the small étale site.
* `AlgebraicGeometry.Space.isFiniteTypeOnSite_definingIdealSheaf_of_isFinitePresentationOnSite`:
  **finite presentation of `i_*𝒪_Z` gives finite type of `𝓘`.**

## References

* [Stacks Project, Tag 082T](https://stacks.math.columbia.edu/tag/082T)
* [Stacks Project, Tag 09RP](https://stacks.math.columbia.edu/tag/09RP)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS) (Z : ClosedSubspaces B S hS X.1)

/-- **The structure sheaf of an algebraic space is of finite type on its small étale site.** -/
theorem isFiniteTypeOnSite_unit_structureRingSheaf :
    SheafOfModules.IsFiniteTypeOnSite
      (SheafOfModules.unit (structureRingSheaf B S hS X) : Modules.{u, u} B S hS X.1 X.2) :=
  Stacks.SheafOfModules.isFiniteTypeOnSite_of_isFiniteType
    (SheafOfModules.unit (structureRingSheaf B S hS X) : Modules.{u, u} B S hS X.1 X.2)
    inferInstance

/-- **The defining ideal sheaf of a closed subspace is of finite type as soon as the quotient of
the structure sheaf it determines is of finite presentation.** For a closed subspace `Z ⊆ X` with
inclusion `i`, if `i_*𝒪_Z` is of finite presentation on the small étale site of `X`, then the
defining ideal sheaf `𝓘` of `Z` is of finite type. -/
theorem isFiniteTypeOnSite_definingIdealSheaf_of_isFinitePresentationOnSite
    (h : (pushforwardStructureSheaf B S hS X Z).IsFinitePresentationOnSite) :
    SheafOfModules.IsFiniteTypeOnSite (definingIdealSheaf B S hS X Z).toSheafOfModules := by
  have : ∀ (U : (smallEtaleRingedSite B S hS X.1 X.2).C)
      (N : _root_.SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).over U)),
      Small.{u, u + 1} N.sections :=
    fun _ N => _root_.SheafOfModules.small_sections_of_isTerminal Over.mkIdTerminal N
  exact Stacks.SheafOfModules.isFiniteTypeOnSite_X₁_of_shortExact_of_small
    (S := definingIdealShortComplex B S hS X Z)
    (definingIdealShortComplex_shortExact B S hS X Z)
    (isFiniteTypeOnSite_unit_structureRingSheaf B S hS X) h

end AlgebraicGeometry.Space

end
