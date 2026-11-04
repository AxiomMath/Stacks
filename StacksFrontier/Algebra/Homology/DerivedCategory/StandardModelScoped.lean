module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# The standard model of the derived category, as a scoped instance

Opening the scope `Stacks.StandardDerivedModel` makes `HasDerivedCategory.standard C` the
derived category of every abelian category `C`, above the locally small models of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean` where a file also activates those.
Under this scope the instance terms of
the different spellings of one category of modules (`X.Modules`,
`SheafOfModules (structureSheafRing X.toRingedSpace)`, `OXMod X.toRingedSpace`) share one head
and are compared argument by argument.

## Main definitions

* `Stacks.StandardDerivedModel.hasDerivedCategory`: the scoped instance.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Stacks.StandardDerivedModel

/-- The standard model of the derived category of an abelian category, as a scoped instance. -/
scoped instance (priority := 1100) hasDerivedCategory (C : Type*) [Category* C] [Abelian C] :
    HasDerivedCategory C :=
  HasDerivedCategory.standard C

end Stacks.StandardDerivedModel

end
