module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitUnboundedIsIso

/-!
# The regular module is a separating family of one object

A homomorphism of `B`-modules out of `B` is determined by the image of `1`, so the regular module
alone separates the category of `B`-modules.  The fact is
`Stacks.ChaoticSite.isSeparating_regularModule`, proved in the module that uses it for
Stacks 08QA; this file records it under a second name for a dévissage of a natural transformation
of functors on derived categories of diagrams of `B`-modules along the free diagrams with
coefficients `B`.

## Main results

* `Stacks.ChaoticSite.isSeparating_ofObj_regularModule`: the regular module is a separating
  family of one object.
-/

@[expose] public section

open CategoryTheory

namespace Stacks.ChaoticSite

universe u

variable {B : Type u} [Ring B]

/-- **The regular module is a separating family of one object**: two morphisms of `B`-modules
agreeing after composition with every `B ⟶ X` are equal. -/
alias isSeparating_ofObj_regularModule := isSeparating_regularModule

end Stacks.ChaoticSite

end
