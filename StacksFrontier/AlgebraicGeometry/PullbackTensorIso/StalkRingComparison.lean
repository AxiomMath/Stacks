module

public import StacksFrontier.AlgebraicGeometry.PullbackTensorIso.Basic

/-!
# The stalk of the structure sheaf, in `CommRingCat` and in `RingCat`

The stalk of a tensor product of Stacks 01CB is a tensor product over
`Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X x`, the stalk of the structure sheaf
taken in `CommRingCat`. The module-level stalk of a pullback
(`Stacks.ModuleSkyscraper.pullbackStalkIsoOfAdjunction`) is stated over
`Stacks.ModuleSkyscraper.stalkRingMap`, a map between stalks taken in `RingCat`. The two rings
are not the same: the two colimits are built in two different categories, and the carriers are
not equal by `rfl`. This file compares them.

## Main definitions and results

* `Stacks.PullbackTensorIso.ringCatStalk`: the stalk of the structure sheaf taken in
  `RingCat`, spelled through `Stacks.SheafOfModules.TensorStalkRingedSpace.O` so that both the
  module structure of Stacks 01CB and Mathlib's module structure on a stalk resolve against it.
* `Stacks.PullbackTensorIso.stalkRingIso` and `stalkRingEquiv`: the comparison, as an
  isomorphism in `RingCat` and as a `RingEquiv`. It is
  `CategoryTheory.Limits.preservesColimitIso` for the forgetful functor
  `CommRingCat ⥤ RingCat`, which preserves filtered colimits; no colimit comparison is
  built by hand here.
* `Stacks.PullbackTensorIso.stalkRingEquiv_germ`: the comparison carries a germ to the
  corresponding germ. This is `CategoryTheory.Limits.ι_preservesColimitIso_hom`, the germ
  maps being the colimit inclusions.
* `Stacks.PullbackTensorIso.smul_stalkRingEquiv`: **the two scalar actions on the stalk of a
  sheaf of modules agree under the comparison.** The stalk of a sheaf of modules carries the
  action of Stacks 01CB over the `CommRingCat` stalk and Mathlib's action over the `RingCat`
  stalk; both are pinned by `germ (r • m) = germ r • germ m`, so they correspond under the
  comparison. Consequently a map of stalks that is linear for one is linear for the other
  (`smul_stalkRingEquiv_symm` gives the direction needed for that).
* `Stacks.PullbackTensorIso.stalkRestrictEquiv`: the two module structures are identified by
  the identity map, as a linear equivalence. The two are different instance terms with the
  same scalar action, so a tensor product taken over one is not the tensor product taken
  over the other; this is the honest comparison between them — `AddEquiv.refl` carrying only
  the linearity datum, in the shape of Mathlib's `ModuleCat.restrictScalarsId'App` — rather
  than a transport along an equality of instances.

## Universes

A single universe `u`, over `AlgebraicGeometry.RingedSpace.{u, u}`.

## Transparency notes

* `ringCatStalk` is spelled
  `TopCat.Presheaf.stalk (Stacks.SheafOfModules.TensorStalkRingedSpace.O Z) z` rather than
  `Stacks.ModuleSkyscraper.Stalk (structureSheafRing Z) z`. The two are definitionally equal,
  but instance search runs at reducible transparency and `structureSheafRing` is a
  semireducible definition, so with the second spelling neither module structure on a stalk is
  found. Sheaves of modules are taken over `structureSheafRing`, a reducible definition, for the
  same reason.
* The germ compatibility is proved by `ConcreteCategory.congr_hom` applied to the colimit
  identity, with no intervening rewrite: the identity is about a composite of morphisms and
  the goal about an iterated application, and the two are interchangeable only by
  definitional unfolding, which `rewrite` will not do.

## References

* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat

universe u

namespace Stacks.PullbackTensorIso

variable (Z : RingedSpace.{u, u}) (z : Z.carrier)

/-- The stalk at `z` of the structure sheaf of `Z`, read as a sheaf of not necessarily
commutative rings and so taken as a colimit in `RingCat`. -/
abbrev ringCatStalk : RingCat.{u} :=
  TopCat.Presheaf.stalk (C := RingCat.{u}) (X := Z.carrier)
    (Stacks.SheafOfModules.TensorStalkRingedSpace.O Z) z

/-- **The stalk of the structure sheaf taken in `CommRingCat`, compared with the stalk taken
in `RingCat`.** The forgetful functor `CommRingCat ⥤ RingCat` preserves filtered colimits and
a stalk is a filtered colimit, so the comparison is an isomorphism. -/
def stalkRingIso : (forget₂ CommRingCat.{u} RingCat.{u}).obj
  (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk Z z) ≅
    ringCatStalk Z z :=
  preservesColimitIso (forget₂ CommRingCat.{u} RingCat.{u})
    ((OpenNhds.inclusion z).op ⋙ Z.presheaf)

/-- `stalkRingIso` carries the germ of a section in the `CommRingCat` stalk to its germ in the
`RingCat` stalk. -/
lemma stalkRingIso_hom_germ (U : Opens Z.carrier) (h : z ∈ U) (r : Z.presheaf.obj (op U)) :
    (stalkRingIso Z z).hom.hom (TopCat.Presheaf.germ Z.presheaf U z h r) =
      TopCat.Presheaf.germ (C := RingCat.{u}) (Stacks.SheafOfModules.TensorStalkRingedSpace.O Z) U z
        h r :=
  ConcreteCategory.congr_hom
    (ι_preservesColimitIso_hom (forget₂ CommRingCat.{u} RingCat.{u})
      ((OpenNhds.inclusion z).op ⋙ Z.presheaf) (op ⟨U, h⟩)) r

/-- `stalkRingIso` as an isomorphism of rings. -/
def stalkRingEquiv : Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk Z z ≃+* ringCatStalk Z z
  :=
  CategoryTheory.Iso.ringCatIsoToRingEquiv (stalkRingIso Z z)

/-- `stalkRingEquiv` carries the germ of a section in the `CommRingCat` stalk to its germ in the
`RingCat` stalk. -/
@[simp]
lemma stalkRingEquiv_germ (U : Opens Z.carrier) (h : z ∈ U) (r : Z.presheaf.obj (op U)) :
    stalkRingEquiv Z z (TopCat.Presheaf.germ Z.presheaf U z h r) =
      TopCat.Presheaf.germ (C := RingCat.{u}) (Stacks.SheafOfModules.TensorStalkRingedSpace.O Z) U z
        h r :=
  stalkRingIso_hom_germ Z z U h r

variable {Z z}

/-- **The two scalar actions on the stalk of a sheaf of modules agree.** The action of
Stacks 01CB over the stalk of the structure sheaf taken in `CommRingCat` and Mathlib's action
over the stalk taken in `RingCat` correspond under `stalkRingEquiv`. -/
lemma smul_stalkRingEquiv (M : SheafOfModules.{u}
  (structureSheafRing Z))
    (r : Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk Z z) (m :
      Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk Z M.val z) :
    stalkRingEquiv Z z r • m = r • m := by
  obtain ⟨U, hU, r₀, hr⟩ := TopCat.Presheaf.exists_germ_eq Z.presheaf r
  obtain ⟨W, hWU, hW, m₀, hm⟩ :=
    TopCat.Presheaf.exists_le_germ_eq (C := AddCommGrpCat.{u}) M.val.presheaf m hU
  have hrW : TopCat.Presheaf.germ Z.presheaf W z hW (Z.presheaf.map (homOfLE hWU).op r₀) = r :=
    (TopCat.Presheaf.germ_res_apply Z.presheaf (homOfLE hWU) z hW r₀).trans hr
  rw [← hrW, ← hm, stalkRingEquiv_germ]
  exact (AlgebraicGeometry.SheafOfModules.germ_hom_smul
    (structureSheafRing Z) z M.val W hW _ m₀).symm.trans
    (Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule_germ_smul Z M.val z W hW _ m₀)

/-- `smul_stalkRingEquiv` read in the other direction: Mathlib's action of the `RingCat`
stalk is the action of Stacks 01CB of the corresponding element of the `CommRingCat` stalk. -/
lemma smul_stalkRingEquiv_symm (M : SheafOfModules.{u}
  (structureSheafRing Z))
    (r : ringCatStalk Z z) (m : Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk Z M.val z) :
    r • m = (stalkRingEquiv Z z).symm r • m :=
  ((congrArg (· • m) ((stalkRingEquiv Z z).apply_symm_apply r)).symm).trans
    (smul_stalkRingEquiv M ((stalkRingEquiv Z z).symm r) m)

/-- **The two module structures on the stalk of a sheaf of modules are identified by the
identity map.** On the left is the stalk as a module over the `RingCat` stalk, with scalars
restricted along `stalkRingEquiv` — the module
`Stacks.ModuleSkyscraper.pullbackStalkIsoOfAdjunction` hands over; on the right is the stalk as
a module over the `CommRingCat` stalk, the module
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso` is stated for. The underlying
groups are the same and the two actions agree by `smul_stalkRingEquiv`, so this is the identity
map carrying only the linearity datum — no transport along an equality of instances. It is
built exactly as Mathlib's `ModuleCat.restrictScalarsId'App` is. -/
def stalkRestrictEquiv (M : SheafOfModules.{u}
  (structureSheafRing Z)) :
    (ModuleCat.restrictScalars (stalkRingEquiv Z z).toRingHom).obj
        (Stacks.ModuleSkyscraper.stalkMod (structureSheafRing Z) z M) ≃ₗ[
      Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk Z z]
        Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk Z M.val z :=
  AddEquiv.toLinearEquiv (AddEquiv.refl _) fun r m => smul_stalkRingEquiv M r m

/-- `stalkRestrictEquiv` is the identity on underlying elements. -/
@[simp]
lemma stalkRestrictEquiv_apply (M : SheafOfModules.{u}
  (structureSheafRing Z))
    (m : Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk Z M.val z) : stalkRestrictEquiv M m =
      m := rfl

end Stacks.PullbackTensorIso
