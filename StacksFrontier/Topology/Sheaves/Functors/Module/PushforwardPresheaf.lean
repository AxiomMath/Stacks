module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Topology.Category.TopCat.Opens

import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 008S — pushforward of a presheaf of modules along a continuous map

Let `f : X → Y` be a continuous map of topological spaces, `𝒪` a presheaf of rings on `X` and
`ℱ` a presheaf of `𝒪`-modules. Stacks 008S says that the pushforward presheaf
`(f_*ℱ)(V) = ℱ(f^{-1}V)` carries a natural map of underlying presheaves of sets
`f_*𝒪 × f_*ℱ → f_*ℱ` making it a presheaf of `f_*𝒪`-modules, and that this is functorial
in `ℱ`.

Mathlib states this at the level of sites, for restriction along any functor: with
`F = Opens.map f : Opens Y ⥤ Opens X`, the presheaf of rings `f_*𝒪` is `F.op ⋙ 𝒪` and
`PresheafOfModules.pushforward₀ F 𝒪 : PresheafOfModules 𝒪 ⥤ PresheafOfModules (F.op ⋙ 𝒪)` is
the functor of the tag; `PresheafOfModules.pushforward₀Obj` is its value on `ℱ`. The scalar
action is the module structure carried by a `PresheafOfModules`, and its compatibility with
restriction — the naturality of the tag's map of presheaves of sets — is
`PresheafOfModules.map_smul`.
-/

@[expose] public section

-- The former @[stacks 008S] functor was `pushforward₀` at `Opens.map f`, and the surrounding
-- declarations spelled out the scalar action and functoriality that it already carries.
add_to_stacks 008S "the pushforward `f_*ℱ` as a presheaf of `f_*𝒪`-modules"
  PresheafOfModules.pushforward₀Obj
add_to_stacks 008S "pushforward as a functor `PMod(𝒪) ⥤ PMod(f_*𝒪)`"
  PresheafOfModules.pushforward₀
add_to_stacks 008S "the scalar action is compatible with restriction, which is the naturality of
  the map `f_*𝒪 × f_*ℱ ⟶ f_*ℱ`" PresheafOfModules.map_smul
add_to_sga "3 I 6.4" "more general" PresheafOfModules.map_smul
