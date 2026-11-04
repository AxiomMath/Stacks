module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedHomotopyCategory

/-!
# K-injective differential graded modules

Let `R` be a sheaf of rings on a site and let `A` be a sheaf of differential graded
`R`-algebras. A right differential graded `A`-module `I` is *K-injective* when every acyclic
right differential graded `A`-module has only the zero morphism into `I` in the homotopy
category.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.IsKInjective` is K-injectivity of a right
  differential graded module.

## Implementation notes

Acyclicity is exactness of the underlying cochain complex of sheaves of modules. The vanishing
of the group of morphisms in the homotopy category is expressed as `Subsingleton` of the
morphism type, which is the correct formulation here because the morphism types of the homotopy
category are not known to carry an additive structure at this point.

The condition is stated through the quotient functor of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedHomotopyCategory.lean`, so it
concerns homotopy classes of morphisms of right differential graded modules, not morphisms of
the underlying cochain complexes.

The base is an arbitrary sheaf of rings on an arbitrary site rather than the structure sheaf of
a ringed site, and the universes of the site, the ring, the algebra pieces and the module
pieces are independent; a ringed site `X` is the case `R := X.ringSheaf`.

## References

* [Stacks Project, Tag 0FSU](https://stacks.math.columbia.edu/tag/0FSU)
-/

@[expose] public section

open CategoryTheory

universe t a m v u

namespace SheafOfModules

namespace DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A : DifferentialGradedAlgebra.{t, a} R}

/-- A right differential graded module is K-injective when the homotopy classes of morphisms
into it from every acyclic right differential graded module vanish. -/
@[stacks 0FSU]
abbrev IsKInjective (I : DifferentialGradedModule.{t, a, m} A) : Prop :=
  ∀ M : DifferentialGradedModule.{t, a, m} A, M.complex.Acyclic →
    Subsingleton ((HomotopyCategory.quotient A).obj M ⟶ (HomotopyCategory.quotient A).obj I)

end DifferentialGradedModule

end SheafOfModules
