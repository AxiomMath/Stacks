module

public import StacksFrontier.AlgebraicGeometry.Modules.DualFiniteLocallyFree

/-!
# The rank of the dual of a finite locally free module, as an instance

`Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFreeOfRank_dualSheaf` says that the dual
`ℰ^∨` of a finite locally free module `ℰ` of constant rank `r` on a scheme is finite locally free
of rank `r`. This file registers it as an instance,
`Stacks.AlgebraicGeometry.ReflexiveModules.instIsFiniteLocallyFreeOfRankDualSheaf`, so that the
rank of a dual (and of a dual of a dual) is found by instance search, as the Chern classes of
`ℰ^∨` require.
-/

@[expose] public section

universe u

open AlgebraicGeometry

namespace Stacks.AlgebraicGeometry.ReflexiveModules

/-- **The dual of a finite locally free module of rank `r` is finite locally free of rank `r`**,
as an instance: `Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFreeOfRank_dualSheaf`
with its hypothesis found by instance search. -/
instance instIsFiniteLocallyFreeOfRankDualSheaf {X : Scheme.{u}} (E : X.Modules) (r : ℕ)
    [hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (R := X.ringCatSheaf) E r] :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (R := X.ringCatSheaf) (dualSheaf E) r :=
  isFiniteLocallyFreeOfRank_dualSheaf E r hE

end Stacks.AlgebraicGeometry.ReflexiveModules

end
