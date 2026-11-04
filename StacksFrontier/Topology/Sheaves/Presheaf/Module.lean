module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf

import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 006Q — Presheaves of modules over a presheaf of rings

Let `X` be a topological space and `O` a presheaf of rings on `X`. Stacks 006Q defines (1) a
presheaf of `O`-modules as an abelian presheaf `F` together with a map of presheaves of sets
`O × F → F` making each `O(U) × F(U) → F(U)` an `O(U)`-module structure on the abelian group
`F(U)`; (2) a morphism of presheaves of `O`-modules as a morphism of abelian presheaves
commuting with those actions; (3) the hom-set $\Hom_\mathcal{O}(F, G)$; and (4) the category
$\mathit{PMod}(\mathcal{O})$.

All four clauses are Mathlib's `PresheafOfModules O`, for `O : (Opens X)ᵒᵖ ⥤ RingCat`. The
structure carries the underlying abelian presheaf and, for each open `U`, the `O(U)`-module
structure on `F(U)` of clause (1); `PresheafOfModules.Hom` is clause (2), whose components are
`O(U)`-linear and whose `naturality` field is the compatibility square of the tag (stated using
restriction of scalars along `O(U) → O(V)`); the hom-set of clause (3) is that same type, which
is the hom-type of the category `PresheafOfModules.instCategory` of clause (4).
-/

@[expose] public section

-- The former @[stacks 006Q] declarations were abbreviations for the Mathlib notions, together
-- with lemmas re-extracting the module structures and the compatibility square from them.
add_to_stacks 006Q "a presheaf of `O`-modules: an abelian presheaf with an `O(U)`-module
  structure on each `F(U)`, compatible with restriction" PresheafOfModules
add_to_sga "3 I 4.7.1.1" PresheafOfModules
add_to_sga "4 II 6.7" PresheafOfModules
add_to_sga "3 I 3.1" "O-module definition" PresheafOfModules
add_to_stacks 006Q "the `O(U)`-module structure on the sections over `U`"
  PresheafOfModules.instModuleCarrierObjOppositeRingCatCarrierAbPresheaf
add_to_sga "3 I 3.1" "F(S) is an O(S)-module"
  PresheafOfModules.instModuleCarrierObjOppositeRingCatCarrierAbPresheaf
add_to_stacks 006Q "a morphism of presheaves of `O`-modules; also the hom-set
  `Hom_O(F, G)`, which is the hom-type of `PMod(O)`" PresheafOfModules.Hom
add_to_sga "3 I 3.1" "Hom_O(F,F')" PresheafOfModules.Hom
add_to_stacks 006Q "the compatibility square of a morphism with the actions, via restriction of
  scalars along `O(U) → O(V)`" PresheafOfModules.Hom.naturality
add_to_sga "3 I 3.1" "morphism compatibility" PresheafOfModules.Hom.naturality
add_to_stacks 006Q "the category `PMod(O)`" PresheafOfModules.instCategory
add_to_sga "3 I 3.1" "category (O-Mod.)" PresheafOfModules.instCategory
