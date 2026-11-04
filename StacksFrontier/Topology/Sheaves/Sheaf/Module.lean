module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.Spaces

import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0077 — Sheaves of modules

Let `X` be a topological space and `𝒪` a sheaf of rings on `X`. Stacks 0077 defines (1) a sheaf
of `𝒪`-modules as a presheaf of `𝒪`-modules whose underlying presheaf of abelian groups is a
sheaf; (2) a morphism of sheaves of `𝒪`-modules as a morphism of the underlying presheaves of
`𝒪`-modules; (3) the hom-set `Hom_𝒪(ℱ, 𝒢)`; and (4) the category `Mod(𝒪)`.

All four clauses are Mathlib's `SheafOfModules 𝒪`, a structure bundling a
`PresheafOfModules 𝒪.obj` (its `val`) with the sheaf condition on the underlying presheaf (its
`isSheaf`) — clause (1). `SheafOfModules.Hom` is the morphism type, a one-field structure
holding a morphism of the underlying presheaves of modules — clauses (2) and (3), with
`SheafOfModules.hom_ext` saying that field determines the morphism. Clause (4) is
`SheafOfModules.instCategory`.

Mathlib states this for a general site `(C, J)`; a sheaf of rings on the space `X` is the case
`C = Opens X` with `Opens.grothendieckTopology X`.

## Main definitions

* `ModuleCategory`: notation for the category `Mod(𝒪)` over a space, i.e. `SheafOfModules 𝒪`
  with the structure sheaf's site spelled out.
-/

@[expose] public section

-- The former @[stacks 0077] declarations restated these Mathlib ones as equivalences with the
-- explicit subtype of presheaves of modules and with the presheaf-level hom types.
add_to_stacks 0077 "a sheaf of `𝒪`-modules" SheafOfModules
add_to_sga "2 I 1.7" "partial" SheafOfModules
add_to_sga "3 I 4.7.1.1" SheafOfModules
add_to_sga "4 II 6.7" SheafOfModules
add_to_sga "4 II 6.9" SheafOfModules
add_to_sga "4 IV 14.2" SheafOfModules
add_to_sga "4 V 3.5" SheafOfModules
add_to_sga "4 V 6.13" SheafOfModules
add_to_sga "4 VI 8.7.1" SheafOfModules
add_to_sga "4 Vbis 2.4.0" "partial" SheafOfModules
add_to_sga "4 Vbis 4.1.0" "fiber G_X = Mod(Z_X)" SheafOfModules
add_to_sga "4 Vbis 4.3.0" "fiber category F_{n_X}" SheafOfModules
add_to_sga "4 XVII 7.0.1" "more general" SheafOfModules
add_to_sga "5 I App.1.1" SheafOfModules
add_to_sga "6 I 1.3" "partial" SheafOfModules
add_to_sga "6 I 4.8" "ambient S-category C" SheafOfModules
add_to_sga "6 II 2.0" SheafOfModules
add_to_sga "6 II 2.3.2" SheafOfModules
add_to_sga "6 III 1.1" SheafOfModules
add_to_sga "6 III 5.1" SheafOfModules
add_to_sga "6 VI 2.2" "more general" SheafOfModules
add_to_sga "7 IX 9.4" SheafOfModules
add_to_ega "0 4.1.3" "more general" SheafOfModules
add_to_sga "4 IV 11.1.2" "definition of _A E" SheafOfModules
add_to_stacks 0077 "the sheaf condition on the underlying presheaf of abelian groups"
  SheafOfModules.isSheaf
add_to_stacks 0077 "a morphism of sheaves of `𝒪`-modules; also the hom-set `Hom_𝒪(ℱ, 𝒢)`"
  SheafOfModules.Hom
add_to_ega "0 4.4.1" "special case" SheafOfModules.Hom
add_to_sga "4 IV 11.1.2" "Hom_A(M,N)" SheafOfModules.Hom
add_to_stacks 0077 "a morphism is determined by the underlying morphism of presheaves of
  modules" SheafOfModules.hom_ext
add_to_stacks 0077 "the category `Mod(𝒪)`" SheafOfModules.instCategory
add_to_sga "4 IV 11.1.2" "_A E is a category" SheafOfModules.instCategory

open CategoryTheory TopologicalSpace

universe u

-- `TopCat.Sheaf RingCat X` is definitionally `Sheaf (Opens.grothendieckTopology X) RingCat`, but
-- instance resolution does not unfold the `TopCat.Sheaf` def while searching for
-- `Category (SheafOfModules 𝒪)`; the type is spelled out unfolded so the instance is found.
variable (X : TopCat.{u})
  (𝒪 : CategoryTheory.Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/-- Clause (4) of Stacks 0077, the category `Mod(𝒪)` of sheaves of `𝒪`-modules on a
topological space `X`.

This is *only* an abbreviation: it is reducibly `SheafOfModules 𝒪`, carries no data of its
own, and adds nothing to Mathlib's definition. Its purpose is to name the site — it fixes
`𝒪` to be a sheaf of rings on `Opens X` for the open-cover topology, which is the Stacks
setting, and in that spelling the `Category` instance is found by unification. -/
@[ega "0 4.1.3",
  sga "3 I 4.7.1.1",
  sga "4 II 6.7" "special case",
  sga "4 IV 11.1.2" "special case",
  sga "4 Vbis 2.4.0" "partial",
  sga "4 Vbis 4.1.0" "fiber G_X = Mod(Z_X)",
  sga "6 I 4.8" "ambient S-category C",
  sga "6 II 2.0" "Mod for a spatial topos",
  sga "6 II 2.3.2",
  sga "6 III 5.1" "special case"]
abbrev ModuleCategory := SheafOfModules 𝒪

example : Category (ModuleCategory X 𝒪) := inferInstance
