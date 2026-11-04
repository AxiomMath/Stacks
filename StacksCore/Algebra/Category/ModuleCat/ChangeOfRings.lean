module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import StacksCore.Tactic.StacksAttribute

/-! # Change of rings: the two adjunctions around restriction of scalars

Restriction of scalars along `R → S` has adjoints on both sides, and the Stacks project records
them as two consecutive lemmas of section 10.14.

**Tag 05DQ** (categorical half): base change `Mod_R → Mod_S`, `M ↦ M ⊗_R S`, is *left* adjoint
to restriction `Mod_S → Mod_R`, `N ↦ N_R`. The Hom-set formula the tag also states,
`Hom_R(M, N_R) = Hom_S(M ⊗_R S, N)`, is `LinearMap.liftBaseChangeEquiv`, tagged in
`StacksCore.RingTheory.TensorProduct.Basic`.

**Tag 08YP**: restriction is in turn left adjoint to coextension of scalars
`M ↦ Hom_R(S, M)`, which Mathlib spells `ModuleCat.coextendScalars`. Both halves live here:
the adjunction is `ModuleCat.restrictCoextendScalarsAdj`, and the tag's formula
`Hom_R(N_R, M) = Hom_S(N, Hom_R(S, M))` is the pair of mutually inverse maps
`RestrictionCoextensionAdj.HomEquiv.fromRestriction` and `.toRestriction` — Mathlib gives the
bijection as two directions rather than one bundled `Equiv`, so both carry the tag.

Throughout, Mathlib writes the base change as `S ⊗_R M` where the tag writes `M ⊗_R S`; the two
agree by `TensorProduct.comm`, and nothing here depends on the choice.
-/

@[expose] public section

add_to_stacks 05DQ "Base change `M ↦ S ⊗_R M` is left adjoint to restriction of scalars
  `N ↦ N_R`. The tag writes the tensor product in the other order."
  ModuleCat.extendRestrictScalarsAdj

add_to_stacks 08YP "Restriction of scalars `N ↦ N_R` is left adjoint to coextension of scalars
  `M ↦ Hom_R(S, M)`." ModuleCat.restrictCoextendScalarsAdj
add_to_stacks 08YP "`Hom_R(N_R, M) → Hom_S(N, Hom_R(S, M))`, one direction of the tag's
  Hom-set formula." ModuleCat.RestrictionCoextensionAdj.HomEquiv.fromRestriction
add_to_stacks 08YP "`Hom_S(N, Hom_R(S, M)) → Hom_R(N_R, M)`, the other direction of the tag's
  Hom-set formula." ModuleCat.RestrictionCoextensionAdj.HomEquiv.toRestriction
