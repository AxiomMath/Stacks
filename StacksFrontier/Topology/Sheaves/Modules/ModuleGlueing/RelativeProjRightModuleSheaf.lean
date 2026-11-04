module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedModuleLeftRight
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjQuasicoherent

/-!
# The sheaf on a relative projective spectrum attached to a right graded module

`Stacks.RelativeProj.Situation.moduleSheaf` attaches the sheaf `ℳ̃` to a *left* graded module over
the graded algebra of a relative `Proj` situation, whereas the quadruple side of Section 01NS and
the module `ℳ̃_T` of Tag 01O6 are stated for a *right* graded module. The algebra of a situation is
commutative, so the two notions agree, and this file reads `ℳ̃` on the right-module spelling by
exchanging the arguments of the action.

The quasi-coherence of the homogeneous pieces is the same requirement on both spellings, since the
pieces are literally the same sheaves; it is restated as an instance so that `ℳ̃` elaborates for a
right graded module without a `letI`.

## Main definitions

* `Stacks.RelativeProj.Situation.rightModuleSheaf`: **`ℳ̃` for a right graded module** over the
  algebra of a situation.

## References

* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01O6](https://stacks.math.columbia.edu/tag/01O6)
* [Stacks Project, Tag 0FQZ](https://stacks.math.columbia.edu/tag/0FQZ)

## Not done here

No Stacks tag is carried. Nothing is proved about `ℳ̃` here beyond what the left-module spelling
already carries; in particular no comparison is made with `ℳ̃_T` of Tag 01O6, which is property (1)
of Tag 01O7.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.SheafOfModules
open scoped Stacks.GradedLocalization

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local instance] Stacks.RelativeProj.Situation.sectionModuleDecomposition

namespace Stacks.RelativeProj.Situation

variable {s : Situation.{u}} (M : SheafOfModules.GradedModule.{u, u, u} s.algebra)

/-- The homogeneous pieces of the left graded module read off a right one are the pieces of the
right one, so they are quasi-coherent as soon as those are. -/
public instance isQuasicoherent_piece_toLeftGradedModule
    [∀ n : ℤ, (M.piece n).IsQuasicoherent] (n : ℤ) :
    ((SheafOfModules.GradedModule.toLeftGradedModule M s.mul_comm).piece n).IsQuasicoherent :=
  inferInstanceAs ((M.piece n).IsQuasicoherent)

variable [∀ n : ℤ, (M.piece n).IsQuasicoherent]

/-- **The sheaf `ℳ̃` attached to a right graded module on a relative projective spectrum**: the
sheaf attached to the left graded module it defines, the algebra of a situation being
commutative. -/
public noncomputable abbrev rightModuleSheaf : (relativeProj s).Modules :=
  moduleSheaf (SheafOfModules.GradedModule.toLeftGradedModule M s.mul_comm)

end Stacks.RelativeProj.Situation

end
