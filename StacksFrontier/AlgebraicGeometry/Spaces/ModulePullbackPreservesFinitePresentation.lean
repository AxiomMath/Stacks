module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ModuleNoetherianModel
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams

/-!
# Inverse image of modules preserves quasi-coherence and finite presentation

Let `g : Z ⟶ W` be a morphism of algebraic spaces over a scheme `S`.  The inverse image
`g^*` of `𝒪_W`-modules carries quasi-coherent modules to quasi-coherent modules and modules of
finite presentation to modules of finite presentation.

## Main results

* `AlgebraicGeometry.Space.isFinitePresentation_modulePullback`: the inverse image of a module
  of finite presentation is of finite presentation.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_and_isFinitePresentation_modulePullback`: both
  preservation statements together.

## Implementation notes

Finite presentation of the inverse image is a statement about the inverse image of modules
along a morphism of ringed topoi, which is how `AlgebraicGeometry.Space.modulePullback` is
built; the module is read in the structure-ring-sheaf vocabulary of the ringed topos of the
small étale site, where `Stacks.Sheaves.FinitePresentation.isFinitePresentation_pullbackModules`
applies.  Quasi-coherence is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite`.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The inverse image of `𝒪`-modules along a morphism of algebraic spaces preserves
quasi-coherence and finite presentation. -/
theorem isQuasicoherentOnSite_and_isFinitePresentation_modulePullback
    (Z W : AlgebraicSpaces B S hS) (g : Z ⟶ W) (N : Modules.{u, u} B S hS W.1 W.2) :
    (N.IsQuasicoherentOnSite → ((modulePullback B S hS g).obj N).IsQuasicoherentOnSite) ∧
      (N.IsFinitePresentation → ((modulePullback B S hS g).obj N).IsFinitePresentation) :=
  ⟨isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS g N,
    isFinitePresentation_modulePullback g N⟩

end AlgebraicGeometry.Space

end
