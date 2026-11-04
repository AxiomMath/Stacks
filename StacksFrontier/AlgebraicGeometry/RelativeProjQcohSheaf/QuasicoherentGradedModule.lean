module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.Basic

/-!
# Quasi-coherent sheaves of graded algebras and of graded modules on a scheme

Situation 01NN fixes a scheme `S` and a **quasi-coherent** graded `𝒪_S`-algebra `𝒜`, and the
statements attached to it quantify over the **quasi-coherent** sheaves of graded `𝒜`-modules `ℳ` on
`S`. A sheaf of graded algebras over the structure sheaf of a scheme is a family of sheaves of
modules with a multiplication (Tag 0FQW), and a sheaf of graded modules over it is again a family
of sheaves of modules with an action (Tag 0FQZ); quasi-coherence of either is quasi-coherence of
every homogeneous piece, in the sense of `SheafOfModules.IsQuasicoherent`.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.IsQuasicoherentGradedAlgebra`: **a quasi-coherent
  graded `𝒪_S`-algebra**, the algebra of Situation 01NN.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.IsQuasicoherentGradedModule`: **a quasi-coherent
  sheaf of graded `𝒜`-modules on `S`**, as in Tag 01O7.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.IsQuasicoherentGradedAlgebra.veronese` and
  `IsQuasicoherentGradedModule.veronese`: the homogeneous pieces of the `d`-th Veronese regradings
  `𝒜^{(d)}` and `ℳ^{(d)}` of a quasi-coherent graded algebra, respectively module, are
  quasi-coherent.

## Implementation notes

Quasi-coherence is stated as a predicate on the homogeneous pieces, in the sense of Mathlib's
site-level `SheafOfModules.IsQuasicoherent`, rather than as a field of a bundled structure. The
Veronese regradings are not bundled: only their homogeneous pieces `𝒜_{nd}` and `ℳ_{nd}` occur, and
they are indexed directly.

## References

* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 0FQZ](https://stacks.math.columbia.edu/tag/0FQZ)
-/

@[expose] public section

open CategoryTheory

open AlgebraicGeometry Stacks.RingedSpace

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

variable {S : Scheme.{u}}

/-- **A quasi-coherent graded `𝒪_S`-algebra**, as in Situation 01NN: a sheaf of graded algebras
over the structure sheaf of `S` each of whose homogeneous pieces is a quasi-coherent sheaf of
modules. -/
def IsQuasicoherentGradedAlgebra
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)) : Prop :=
  ∀ n : ℤ, (A.piece n).IsQuasicoherent

/-- **A quasi-coherent sheaf of graded `𝒜`-modules on `S`**, as in Tag 01O7: a sheaf of graded
modules over `𝒜` each of whose homogeneous pieces is a quasi-coherent sheaf of modules. -/
def IsQuasicoherentGradedModule
    {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)}
    (M : SheafOfModules.GradedModule.{u, u, u} A) : Prop :=
  ∀ n : ℤ, (M.piece n).IsQuasicoherent

/-- The homogeneous pieces `𝒜_{nd}` of the `d`-th Veronese regrading `𝒜^{(d)}` of a quasi-coherent
graded algebra are quasi-coherent. -/
theorem IsQuasicoherentGradedAlgebra.veronese
    {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)}
    (hA : IsQuasicoherentGradedAlgebra A) (d n : ℤ) : (A.piece (n * d)).IsQuasicoherent :=
  hA (n * d)

/-- The homogeneous pieces `ℳ_{nd}` of the `d`-th Veronese regrading `ℳ^{(d)}` of a quasi-coherent
sheaf of graded modules are quasi-coherent. -/
theorem IsQuasicoherentGradedModule.veronese
    {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)}
    {M : SheafOfModules.GradedModule.{u, u, u} A} (hM : IsQuasicoherentGradedModule M) (d n : ℤ) :
    (M.piece (n * d)).IsQuasicoherent :=
  hM (n * d)

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
