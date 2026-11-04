module
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.CohomologyAtTheTerminalObject
import all StacksFrontier.CategoryTheory.Sites.GlobalSections.CohomologyAtTheTerminalObject

public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.GroupTheory.FreeAbelianGroup

/-!
# Naturality of cohomology at a terminal object

For a site with a terminal object `U`, the identification `h'IsoH` of the cohomology presheaf of
an abelian sheaf evaluated at `U` with the sheaf cohomology `Sheaf.H` is natural in the sheaf.

## Main results

* `h'IsoH_hom_naturality`: the isomorphisms `h'IsoH` commute with the maps induced by a morphism
  of abelian sheaves.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite TopologicalSpace

universe w' v u

namespace Stacks.Cohomology.TerminalCohomology

variable {C : Type u} [Category.{v} C]

variable (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{v}]

variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]

/-- **`h'IsoH` is natural in the sheaf**: it is a component of a natural isomorphism of functors
on abelian sheaves, `CategoryTheory.Abelian.extFunctor` applied to
`freeOfTerminalIsoConstantSheaf`. -/
theorem h'IsoH_hom_naturality {F G : Sheaf J AddCommGrpCat.{v}} (ψ : F ⟶ G) (n : ℕ) (U : C)
    (hU : IsTerminal U) :
    ((Sheaf.cohomologyPresheafFunctor J n).map ψ).app (op U) ≫ (h'IsoH J G n U hU).hom =
      (h'IsoH J F n U hU).hom ≫ AddCommGrpCat.ofHom (Sheaf.H.map ψ n) :=
  ((extFunctor.{w'} n).map (freeOfTerminalIsoConstantSheaf J U hU).symm.op.hom).naturality ψ

section Opens

variable {X : Type u} [TopologicalSpace X]

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

end Opens

end Stacks.Cohomology.TerminalCohomology

end
