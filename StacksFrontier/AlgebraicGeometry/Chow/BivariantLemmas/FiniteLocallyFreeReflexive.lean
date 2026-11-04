module

public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Sheaf
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.FiniteLocallyFree

/-!
# A finite locally free module on a locally Noetherian scheme is reflexive

`Stacks.Chow.isIso_toDoubleDual_of_isFiniteLocallyFree`: for a finite locally free module `ℱ` on
a locally Noetherian scheme, the canonical map `ℱ ⟶ ℱ^∨∨` is an isomorphism. `ℱ` is coherent
(Stacks 01XZ), and a coherent finite locally free module on a locally Noetherian scheme is
reflexive (`Stacks.FundamentalGroup.ExtendedEtale.isReflexive_of_isFiniteLocallyFree`).

The same statement without the Noetherian hypothesis is
`Stacks.AlgebraicGeometry.ReflexiveModules.isIso_toDoubleDual_of_isFiniteLocallyFree`.

## References

* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 0AY3](https://stacks.math.columbia.edu/tag/0AY3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.Chow

/-- A finite locally free module on a locally Noetherian scheme is reflexive. -/
theorem isIso_toDoubleDual_of_isFiniteLocallyFree {W : Scheme.{u}} [IsLocallyNoetherian W]
    (F : W.Modules)
    (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F) :
    IsIso (toDoubleDual F) := by
  have := hF
  have : F.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isFiniteLocallyFree W F
  exact Stacks.FundamentalGroup.ExtendedEtale.isReflexive_of_isFiniteLocallyFree F
    ((Scheme.Modules.isFiniteLocallyFree_iff F).2 hF)

end Stacks.Chow

end
