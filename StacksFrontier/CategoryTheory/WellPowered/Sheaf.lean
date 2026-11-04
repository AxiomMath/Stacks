module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Subobject.Comma
public import Mathlib.Topology.Sheaves.Limits
public import StacksFrontier.CategoryTheory.WellPowered.CommRing
public import StacksFrontier.CategoryTheory.WellPowered.Functor
public import StacksFrontier.CategoryTheory.WellPowered.FullyFaithful
public import StacksFrontier.CategoryTheory.WellPowered.Under
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A category of sheaves is well-powered

A category of sheaves with values in a category with pullbacks is well-powered whenever the
corresponding presheaf category is. In particular sheaves of commutative rings on a small site or
on a topological space, and sheaves of algebras on a scheme, form well-powered categories.

## Main results

* `Stacks.SheafWellPowered.wellPowered`: `CategoryTheory.Sheaf J A` is `WellPowered.{w}`.
* `Stacks.SheafWellPowered.wellPoweredTopCatSheaf`: `TopCat.Sheaf A X` is `WellPowered.{w}`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe v₁ v₂ w u₁ u₂

namespace Stacks.SheafWellPowered

section Site

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  (A : Type u₂) [Category.{v₂} A] [HasPullbacks A]

/-- **A category of sheaves is well-powered whenever the presheaf category is.** -/
@[sga "4 II 4.12" "special case"]
instance wellPowered [LocallySmall.{w} (Cᵒᵖ ⥤ A)] [WellPowered.{w} (Cᵒᵖ ⥤ A)]
    [LocallySmall.{w} (Sheaf J A)] : WellPowered.{w} (Sheaf J A) :=
  WellPoweredTransfer.wellPowered_of_fullyFaithful (sheafToPresheaf J A)

end Site

section Space

variable (A : Type u₂) [Category.{v₂} A] (X : TopCat.{u₁})

/-- **A category of sheaves on a topological space is well-powered** whenever the corresponding
category of sheaves on its opens is. -/
instance wellPoweredTopCatSheaf [LocallySmall.{w} (Sheaf (Opens.grothendieckTopology X) A)]
    [WellPowered.{w} (Sheaf (Opens.grothendieckTopology X) A)]
    [LocallySmall.{w} (TopCat.Sheaf A X)] : WellPowered.{w} (TopCat.Sheaf A X) :=
  show WellPowered.{w} (Sheaf (Opens.grothendieckTopology X) A) from inferInstance

end Space

end Stacks.SheafWellPowered
