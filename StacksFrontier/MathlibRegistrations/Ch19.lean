module

public import Mathlib.Algebra.Module.Injective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Presentable.Type
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks tags of chapter 19 (Injectives) covered by Mathlib

Each tag registered here is stated in Mathlib; this file only records the correspondence.

The map (05NN) is `CategoryTheory.Limits.colimit.post F (coyoneda.obj (op A))`, for any index
category in place of the ordinal. Lemma 05NR is `HasCardinalLT.isCardinalPresentable` at
`κ = ℵ₀`: a finite type (`hasCardinalLT_aleph0_iff`) is `ℵ₀`-presentable, i.e. `Hom(A, -)`
preserves colimits indexed by any filtered category, which includes every nonzero ordinal.
-/

add_to_stacks 05NN CategoryTheory.Limits.colimit.post

add_to_stacks 05NR HasCardinalLT.isCardinalPresentable

add_to_stacks 0F5S "the left adjoint `- ⊗ G` of `Hom(G, -)` into right `End(G)`-modules"
  CategoryTheory.IsGrothendieckAbelian.tensorObjPreadditiveCoyonedaObjAdjunction

add_to_stacks 05NU Module.Baer.iff_injective
