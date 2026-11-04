module

public import Mathlib.Geometry.RingedSpace.Basic
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalk
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks 0095 (2) — the pullback `f^*G = O_X ⊗_{f^{-1}O_Y} f^{-1}G`

Let `(f, f^\sharp) : (X, O_X) → (Y, O_Y)` be a morphism of ringed spaces and let `G` be a
sheaf of `O_Y`-modules.  Stacks 0095 (2) *defines* the pullback of `G` by the formula
$$
  f^*G = O_X \otimes_{f^{-1}O_Y} f^{-1}G ,
$$
"where the ring map `f^{-1}O_Y → O_X` is the map corresponding to `f^\sharp`", and where the
module structure on `f^{-1}G` is the one supplied by Stacks 008X.

Both ingredients are already in the draft, but the definition was not: the object appears only
as an inline term in the *type* of `PullbackStalkTensor.stalkPullbackTensorIso` (Stacks 0098),
and there the structure morphism `alpha : f^{-1}O_Y ⟶ O_X` is a free variable, unrelated to any
`f^\sharp`.  This file supplies the two missing pieces.

## Main definitions

* `PullbackStalkTensor.sharpTranspose`: the ring map `f^{-1}O_Y ⟶ O_X` *corresponding to*
  `f^\sharp : O_Y ⟶ f_*O_X`, namely its transpose under the adjunction
  `TopCat.Sheaf.pullbackPushforwardAdjunction` at `CommRingCat`, transported along
  `TopCat.Sheaf.pullbackIso` to the sheafification-of-`f_p` model `invRing` of `f^{-1}` used in
  the draft.  Characterised by `PullbackStalkTensor.homEquiv_sharpTranspose`: applying the
  adjunction bijection to it returns `f^\sharp`.
* `PullbackStalkTensor.modulePullbackTensor`: **Stacks 0095 (2)**, the sheaf of `O_X`-modules
  `f^*G = O_X ⊗_{f^{-1}O_Y} f^{-1}G`.  It is `Stacks.Sheafify.ModuleStalkTensor.tensorSheaf` — the
    sheafification
  of the sectionwise tensor product presheaf — applied to `invMod f O_Y G = f^{-1}G` along
  `sharpTranspose`, so it really is the tensor product the tag names, not an abstract left
  adjoint.
* `PullbackStalkTensor.sharpOfRingedSpace` and
  `PullbackStalkTensor.ringedSpacePullbackTensor`: the same definitions packaged for an actual
  morphism `g : X ⟶ Y` of `AlgebraicGeometry.RingedSpace`, whose `g.hom.c` is `f^\sharp`.

## Notes on interpretation

* Everything is stated for a ringed space whose carrier and whose structure sheaf live in the
  same universe, as in `StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace`.
* `stalkPullbackTensorIso` (Stacks 0098) applies verbatim to `modulePullbackTensor`, since the
  latter is by definition an instance of the term occurring there with
  `alpha := sharpTranspose f OY OX sharp`.
* Stacks 0095 (2) defines the *object* `f^*G` for a fixed `G`; the sentence "thus we have
  defined functors" that follows the definition is a separate claim.  The action of `f^*` on
  morphisms of sheaves of modules is not constructed here: it would require the sectionwise
  tensor product `Stacks.Sheafify.ModuleStalkTensor.tensorPresheafOfModules` and the inverse image
  `InverseImageModules.inverseImageSheafOfModules` to be made functorial in the module
  variable, and neither is at present.

## Implementation notes

**Universes.** Everything is stated at a single universe `u` carrying the space, the rings and
the module sections together, so Stacks 0095 (2) applies to a morphism of ringed spaces over
`TopCat.{u}` — in particular to a morphism of `Scheme.{u}`.  That single universe is forced, not
chosen, and the two constraints forcing it both come from Mathlib and are inherited through
`StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalk`:
`TopCat.Presheaf.pullback` asks for the hom universe of the target category to be the universe of
the space, so `CommRingCat.{v}` on a space in `TopCat.{u}` forces `v = u`; and
`PresheafOfModules.ModuleColimit` (which computes the pullback module structure upstream) ties the
module universe and the smallness universe to the ring universe.  Full independence of the space
and ring universes is therefore not available here; the coincidence is also what makes
`HasSheafify` resolve for `RingCat` and `AddCommGrpCat` in this area.  Every `TopCat`,
`CommRingCat` and `SheafOfModules` argument is written `.{u}` explicitly: left implicit they
default to `0` and silently pin the whole file there.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Stacks.Sheafify.ModuleStalkTensor

universe u

namespace PullbackStalkTensor

section Spaces

variable {X Y : TopCat.{u}} (f : X ⟶ Y)
  (OY : TopCat.Sheaf CommRingCat.{u} Y) (OX : TopCat.Sheaf CommRingCat.{u} X)
  (sharp : OY ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f).obj OX)

/-- **The ring map `f^{-1}O_Y ⟶ O_X` corresponding to `f^\sharp : O_Y ⟶ f_*O_X`.**

This is the transpose of `f^\sharp` under the adjunction between `f^{-1}` and `f_*` on sheaves
of commutative rings, moved along `TopCat.Sheaf.pullbackIso` from Mathlib's `f^{-1}` (defined
as a left adjoint) to the sheafification-of-`f_p` description `invRing` used throughout the
draft.  It is exactly the morphism Stacks 0095 (2) asks for, and it is what turns the free
variable `alpha` of Stacks 0098 into data determined by the morphism of ringed spaces. -/
noncomputable def sharpTranspose : invRing f OY ⟶ OX :=
  ((TopCat.Sheaf.pullbackIso CommRingCat.{u} f).app OY).inv ≫
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).homEquiv OY OX).symm sharp

/-- Transported back to Mathlib's `f^{-1}`, `sharpTranspose` is the adjoint transpose of
`f^\sharp`. -/
theorem pullbackIso_hom_comp_sharpTranspose :
    ((TopCat.Sheaf.pullbackIso CommRingCat.{u} f).app OY).hom ≫ sharpTranspose f OY OX sharp
      = ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).homEquiv OY OX).symm
          sharp :=
  Iso.hom_inv_id_assoc _ _

/-- `sharpTranspose` *corresponds to* `f^\sharp`: applying the `(f^{-1}, f_*)` hom-set bijection
to it recovers `f^\sharp`.  This is the clause "where the ring map `f^{-1}O_Y → O_X` is the map
corresponding to `f^\sharp`" of Stacks 0095 (2). -/
theorem homEquiv_sharpTranspose :
    (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).homEquiv OY OX
        (((TopCat.Sheaf.pullbackIso CommRingCat.{u} f).app OY).hom ≫ sharpTranspose f OY OX sharp)
      = sharp := by
  rw [pullbackIso_hom_comp_sharpTranspose, Equiv.apply_symm_apply]

variable (G : SheafOfModules.{u} (ringSheaf OY))

/-- **Stacks 0095 (2).**  The pullback of a sheaf of `O_Y`-modules `G` along a morphism of
ringed spaces `(f, f^\sharp)`:
`f^*G = O_X ⊗_{f^{-1}O_Y} f^{-1}G`,
a sheaf of `O_X`-modules.  The tensor product is `Stacks.Sheafify.ModuleStalkTensor.tensorSheaf`,
  i.e. the
sheafification of the sectionwise tensor product presheaf
`U ↦ O_X(U) ⊗_{(f^{-1}O_Y)(U)} (f^{-1}G)(U)`; the `f^{-1}O_Y`-module `f^{-1}G` is
`invMod f OY G`, the inverse image of Stacks 008X; and the ring map `f^{-1}O_Y → O_X` is
`sharpTranspose f OY OX sharp`, the map corresponding to `f^\sharp`. -/
@[stacks 0095 "(2)",
  ega "0 4.3.1" "Ψ*(G) definition",
  sga "4 IV 13.2.2" "ringed space, comm O",
  sga "4 Vbis 1.3.6" "ringed spaces, φ^*"]
noncomputable def modulePullbackTensor : SheafOfModules.{u} (ringSheaf OX) :=
  tensorSheaf (invRing f OY) OX (sharpTranspose f OY OX sharp) (invMod f OY G)

end Spaces

section RingedSpace

variable {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (g : X ⟶ Y)

/-- The structure morphism `f^\sharp : O_Y ⟶ g_*O_X` of a morphism of ringed spaces, read as a
morphism of sheaves of commutative rings on `Y`.  Underlying it is `g.hom.c`. -/
noncomputable def sharpOfRingedSpace :
    Y.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).obj X.sheaf :=
  ⟨g.hom.c⟩

/-- **Stacks 0095 (2)** for a morphism of ringed spaces: the pullback
`g^*G = O_X ⊗_{g^{-1}O_Y} g^{-1}G` of a sheaf of `O_Y`-modules `G`, with the ring map
`g^{-1}O_Y → O_X` the one corresponding to the structure morphism `g^\sharp = g.hom.c`. -/
@[stacks 0095 "(2)",
  ega "0 4.3.1" "Ψ*(G) definition",
  sga "4 IV 13.2.2" "ringed space, comm O",
  sga "4 Vbis 1.3.6" "ringed spaces, φ^*"]
noncomputable def ringedSpacePullbackTensor (G : SheafOfModules.{u} (ringSheaf Y.sheaf)) :
    SheafOfModules.{u} (ringSheaf X.sheaf) :=
  modulePullbackTensor g.hom.base Y.sheaf X.sheaf (sharpOfRingedSpace g) G

end RingedSpace

end PullbackStalkTensor
