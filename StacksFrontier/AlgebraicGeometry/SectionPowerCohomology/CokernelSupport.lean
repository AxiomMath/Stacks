module

public import StacksFrontier.AlgebraicGeometry.Meromorphic.DenominatorSupport
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs
public import StacksFrontier.AlgebraicGeometry.TwistedCohomologyLocalization.Untwisting
public import StacksFrontier.AlgebraicGeometry.TwistedCohomologyLocalization.MayerVietorisStep

/-!
# The cokernel of multiplication by `sⁿ` lives off `X_s`

Let `X` be a scheme, `ℒ` an invertible `𝒪_X`-module, `s` a global section of `ℒ` and `ℱ` an
arbitrary `𝒪_X`-module. Multiplication by `sⁿ` is the morphism
`Stacks.Cohomology.TwistedLocalizationMap.twistHom X L s F n : ℱ ⟶ ℱ ⊗ ℒ^{⊗ n}`, and over every
open inside the nonvanishing open `X_s` it is bijective on sections
([Stacks, Tag 01CY], the trivialization clause). This file reads that off its cokernel: the
support of `cokernel (twistHom … n)` misses `X_s` entirely.

## Main results

* `Stacks.Cohomology.TwistedLocalizationMap.bijective_twistHom_app`: multiplication by `sⁿ` is
  bijective on the sections over any open inside `X_s`.
* `Stacks.Cohomology.TwistedLocalizationMap.supp_cokernel_twistHom_subset_compl`: **the
  conclusion** — `supp (cokernel (twistHom X L s F n)) ⊆ (X_s)ᶜ`.

## The argument

`AlgebraicGeometry.supp_cokernel_subset` of
`../Meromorphic/DenominatorSupport.lean` already says that the support of `cokernel φ` is
contained in any set outside which `φ` is surjective on the sections over every open of some
neighbourhood; the whole content of this file is to feed it the trivialization.

The section-level input at `twistHom` is
`Stacks.InverseSection.bijective_sectionPowerAction_app`, which is stated for the ringed-space
spelling of the structure sheaf and for `Stacks.NonvanishingTrivialize.nonvanishingOpen`. The
comparison of the two nonvanishing opens is
`Stacks.Cohomology.Untwisting.nonvanishingOpen_eq_trivialize`, and the three instance bridges to
that spelling are introduced inside the proof that needs them rather than as declarations of
this file, since `../TwistedCohomologyLocalization/Untwisting.lean` already carries them as
`local instance`s.

## References

* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 056J](https://stacks.math.columbia.edu/tag/056J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.SheafOfModules

universe u

namespace Stacks.Cohomology.TwistedLocalizationMap

attribute [local implicit_reducible] _root_.SheafOfModules.forget
  PresheafOfModules.restrictScalars TensorSheafification.structureSheaf

variable (X : Scheme.{u})
  (L : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  [IsInvertible X.presheaf
    (structureSheafRing X.toRingedSpace).property L]

attribute [local instance] Stacks.SheafOfModules.tensorRightEquiv

/-- **Multiplication by `sⁿ` is bijective on the sections over an open inside `X_s`.** This is
the trivialization clause of [Stacks, Tag 01CY] for an arbitrary module and an arbitrary power,
`Stacks.InverseSection.bijective_sectionPowerAction_app`, read at the morphism `twistHom`.

The three instance bridges to the ringed-space spelling of the structure sheaf are introduced
inside the proof rather than as `local instance`s of this file, so that no declaration here
repeats the ones `../TwistedCohomologyLocalization/Untwisting.lean` already has. -/
public theorem bijective_twistHom_app (s : L.sections) (F : X.Modules) (n : ℕ) {W : X.Opens}
    (hW : W ≤ nonvanishingOpen L s) :
    Function.Bijective fun t : F.val.obj (op W) => (twistHom X L s F n).val.app (op W) t := by
  have hsheafObj : IsInvertible (SheafedSpace.sheaf X.toRingedSpace).obj
      (_root_.structureSheaf X.toRingedSpace.sheaf).property L := ‹_›
  have : AlgebraicGeometry.SheafOfModules.IsInvertible
      (SheafedSpace.sheaf X.toRingedSpace).obj
      (_root_.structureSheaf X.toRingedSpace.sheaf).property L :=
    IsInvertible.toAlgebraicGeometry _ _ L hsheafObj
  have : (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u}
      ⟨(SheafedSpace.sheaf X.toRingedSpace).obj,
        Presheaf.isSheaf_of_isSheaf_comp _ ((SheafedSpace.sheaf X.toRingedSpace).obj)
          (forget₂ CommRingCat RingCat)
          ((_root_.structureSheaf X.toRingedSpace.sheaf).property)⟩).flip.obj (L))).IsEquivalence :=
    TensorPower.isEquivalence_tensorRightFunctor
      (SheafedSpace.sheaf X.toRingedSpace).obj
      (_root_.structureSheaf X.toRingedSpace.sheaf).property L
  exact Stacks.InverseSection.bijective_sectionPowerAction_app X.toRingedSpace L s
    (Stacks.Cohomology.Untwisting.nonvanishingOpen_eq_trivialize X L s ▸ hW) F n

/-- **The cokernel of multiplication by `sⁿ` is supported off `X_s`.** Over every open inside
`X_s` the morphism is bijective on sections, so in particular surjective, and
`AlgebraicGeometry.supp_cokernel_subset` applies with the complement of `X_s` as the ambient
closed set. -/
public theorem supp_cokernel_twistHom_subset_compl (s : L.sections) (F : X.Modules) (n : ℕ) :
    _root_.SheafOfModules.supp (cokernel (twistHom X L s F n)) ⊆
      (↑(nonvanishingOpen L s) : Set X)ᶜ :=
  AlgebraicGeometry.supp_cokernel_subset X (twistHom X L s F n)
    ((↑(nonvanishingOpen L s) : Set X)ᶜ) fun _ hx =>
    ⟨nonvanishingOpen L s, not_not.mp hx, fun _ hV => (bijective_twistHom_app X L s F n hV).2⟩

end Stacks.Cohomology.TwistedLocalizationMap

end
