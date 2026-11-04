module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.AlgebraicGeometry.PicardGroup.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Picard group of a scheme

The Picard group of a scheme `X` is the Picard group of its structure sheaf, viewed as a sheaf
of rings on the site of opens of `X`. This file names it `X.picardGroup`, together with the
class `X.picardClass L hL` of an invertible module.

## Main definitions

* `AlgebraicGeometry.Scheme.ringCatIsSheaf`: the sheaf condition for the `RingCat`-valued
  structure sheaf, in the spelling the Picard group is stated at.
* `AlgebraicGeometry.Scheme.picardGroup`: `Pic(X)`.
* `AlgebraicGeometry.Scheme.picardClass`: the class of an invertible `𝒪_X`-module.

## Main results

* `AlgebraicGeometry.Scheme.picardClass_eq_iff` and
  `AlgebraicGeometry.Scheme.picardClass_eq_zero_iff`: equality of classes is isomorphism of
  modules, and a class vanishes exactly when the module is trivial.
* `AlgebraicGeometry.Scheme.subsingleton_picardGroup`: `Pic(X)` is trivial as soon as every
  invertible `𝒪_X`-module is trivial. This is the shape in which the triviality statements of
  [Stacks, Tag 0BDA](https://stacks.math.columbia.edu/tag/0BDA) are to be proved.

## Implementation notes

**Why this file exists at all.** `Stacks.SheafOfModules.PicardGroup` takes the sheaf condition
of the `RingCat`-valued structure sheaf as an argument, and a scheme offers that proof in at
least three defeq but *not syntactically equal* spellings: `X.ringCatSheaf.2`,
`(structureSheaf X.sheaf).property`, and
`Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) X.IsSheaf`. Elaboration
accepts all three, because it unfolds at default transparency. **Instance search does not**: it
runs at reducible transparency, and `Scheme.ringCatSheaf` is a plain `def`, so for the first two
spellings the search for `AddCommGroup (PicardGroup X.presheaf _)` fails even though the
instance applies. Concretely, with `X.ringCatSheaf.2` the group structure is not found by
`inferInstance` while `instAddCommGroupPicardGroup _ _` supplied by hand typechecks.

`ringCatIsSheaf` fixes one spelling — the third, which is the one that works — and `picardGroup`
is an `abbrev` over it, so instance search reduces through it and always finds the group. Every
scheme-level consumer should write `X.picardGroup`; `X.picardClass` accepts an invertibility
hypothesis in any of the three spellings, since that is only elaboration.

## References

* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- The sheaf condition for the `RingCat`-valued structure sheaf of a scheme, in the one
spelling that instance search can see through. -/
noncomputable abbrev ringCatIsSheaf (X : Scheme.{u}) :
    Presheaf.IsSheaf (Opens.grothendieckTopology ↥X)
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf X.presheaf) :=
  Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) X.IsSheaf

/-- **Stacks Project, Tag 01CX.** The Picard group `Pic(X)` of a scheme: the abelian group of
isomorphism classes of invertible `𝒪_X`-modules under tensor product. -/
@[sga "4 IX 3.3", sga "4½ Arcata 2.2.3"]
noncomputable abbrev picardGroup (X : Scheme.{u}) :=
  Stacks.SheafOfModules.PicardGroup X.presheaf X.ringCatIsSheaf

/-- The class in `Pic(X)` of an invertible `𝒪_X`-module. -/
noncomputable def picardClass (X : Scheme.{u}) (L : X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf L) : X.picardGroup :=
  Stacks.SheafOfModules.picardClass X.presheaf X.ringCatIsSheaf L hL

/-- Two invertible `𝒪_X`-modules have the same class in `Pic(X)` exactly when they are
isomorphic. -/
theorem picardClass_eq_iff (X : Scheme.{u}) (L N : X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf L)
    (hN : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf N) :
    X.picardClass L hL = X.picardClass N hN ↔ Nonempty (L ≅ N) :=
  Stacks.SheafOfModules.picardClass_eq_iff X.presheaf X.ringCatIsSheaf L N hL hN

/-- The class of an invertible `𝒪_X`-module in `Pic(X)` vanishes exactly when the module is
trivial. -/
theorem picardClass_eq_zero_iff (X : Scheme.{u}) (L : X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf L) :
    X.picardClass L hL = 0 ↔ Stacks.SheafOfModules.IsTrivial X.presheaf X.ringCatIsSheaf L :=
  Stacks.SheafOfModules.picardClass_eq_zero_iff X.presheaf X.ringCatIsSheaf L hL

/-- Addition in `Pic(X)` is the tensor product of invertible `𝒪_X`-modules. -/
theorem picardClass_tensorSheaf (X : Scheme.{u}) (L N : X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf L)
    (hN : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf N)
    (hLN : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
          (X.ringCatIsSheaf)⟩).obj (L)).obj (N)))) :
    X.picardClass L hL + X.picardClass N hN =
      X.picardClass ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
          (X.ringCatIsSheaf)⟩).obj (L)).obj (N))) hLN :=
  Stacks.SheafOfModules.picardClass_tensorSheaf X.presheaf X.ringCatIsSheaf L N hL hN hLN

/-- **`Pic(X)` is trivial as soon as every invertible `𝒪_X`-module is trivial.** -/
theorem subsingleton_picardGroup (X : Scheme.{u})
    (h : ∀ L : X.Modules, Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf L →
      Stacks.SheafOfModules.IsTrivial X.presheaf X.ringCatIsSheaf L) :
    Subsingleton X.picardGroup :=
  Stacks.SheafOfModules.subsingleton_picardGroup X.presheaf X.ringCatIsSheaf h

end AlgebraicGeometry.Scheme

end
