module

public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import StacksCore.Tactic.StacksAttribute

/-!
# The sheaf associated to a presheaf, for a topology

For a category `C` with a topology `J` and a presheaf of sets `F` on `C`, Stacks 00ZL calls
`F^# := L L F` — the twofold iterate of the plus construction `L` — the *sheaf associated to* `F`,
and equips it with the canonical map `F → F^#`, the composite of `ℓ_F : F → L F` with
`ℓ_{L F} : L F → L L F`.

This is exactly Mathlib's `CategoryTheory.GrothendieckTopology.sheafify`, which is *defined* as
`J.plusObj (J.plusObj F)`, together with `CategoryTheory.GrothendieckTopology.toSheafify` and
`CategoryTheory.GrothendieckTopology.sheafify_isSheaf`. Mathlib spells the canonical map as
`J.toPlus F ≫ J.plusMap (J.toPlus F)` rather than as `J.toPlus F ≫ J.toPlus (J.plusObj F)`; that
the two agree is the naturality square `CategoryTheory.GrothendieckTopology.toPlus_naturality`
instantiated at `J.toPlus F`.
-/

@[expose] public section

/- The object `F^# = L L F`, the canonical map into it and the fact that it is a sheaf are all
in Mathlib, the first two by definition. -/
add_to_stacks 00ZL "the sheaf F^# = L L F"
  CategoryTheory.GrothendieckTopology.sheafify
add_to_sga "3 IV 4.3.14" CategoryTheory.GrothendieckTopology.sheafify
add_to_sga "3 IV 4.3.15" CategoryTheory.GrothendieckTopology.sheafify
add_to_sga "3 VIB 8.1" CategoryTheory.GrothendieckTopology.sheafify
add_to_sga "4 II 3.5" "the sheaf F^# = LLF" CategoryTheory.GrothendieckTopology.sheafify
add_to_stacks 00ZL "the canonical map F → F^#"
  CategoryTheory.GrothendieckTopology.toSheafify
add_to_sga "4 II 3.5" "canonical map F → aF" CategoryTheory.GrothendieckTopology.toSheafify
add_to_stacks 00ZL "F^# is a sheaf"
  CategoryTheory.GrothendieckTopology.sheafify_isSheaf
add_to_sga "3 IV 4.3.14" "more general" CategoryTheory.GrothendieckTopology.sheafify_isSheaf
add_to_sga "4 II 3.5" "aF is a sheaf" CategoryTheory.GrothendieckTopology.sheafify_isSheaf
-- The former @[stacks 00ZL] theorem was this naturality square instantiated at `J.toPlus F`,
-- which is what identifies Mathlib's canonical map `F → F^#` with the source's composite
-- `ℓ_{L F} ∘ ℓ_F`.
add_to_stacks 00ZL "the canonical map F → F^# is the composite of the two units ℓ_F and ℓ_{L F}
  of the plus construction: naturality of `toPlus` at `toPlus F` turns Mathlib's
  `toPlus F ≫ plusMap (toPlus F)` into `toPlus F ≫ toPlus (plusObj F)`"
  CategoryTheory.GrothendieckTopology.toPlus_naturality
