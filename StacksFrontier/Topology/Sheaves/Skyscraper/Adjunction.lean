module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Sites.LocalSite
public import Mathlib.Topology.Sheaves.Skyscraper
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks Project, Tag 009C — Lemma 6.27.2

For a topological space `X` and a point `x : X`, the stalk functor `ℱ ↦ ℱ.stalk x` is
left adjoint to the skyscraper-sheaf functor `A ↦ i_{x,*} A`. In particular for any
sheaf `ℱ` on `X` and any object `A` of the target category,
`Mor(ℱ.stalk x, A) ≃ Mor(ℱ, skyscraperSheaf x A)`.

`Mathlib.Topology.Sheaves.Skyscraper` proves this for any value category with colimits, in
both the presheaf and the sheaf form. The target categories the Stacks lemma names -- sets,
abelian groups, and modules over a fixed ring, which subsumes sheaves of `O_X`-modules once
`O_X` is fixed -- are instances of it, so this module states nothing of its own: it registers
the tag on Mathlib's two declarations.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

add_to_stacks 009C stalkSkyscraperSheafAdjunction

add_to_stacks 009C skyscraperPresheafStalkAdjunction
