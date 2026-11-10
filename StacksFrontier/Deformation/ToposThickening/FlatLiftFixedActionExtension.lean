module

public import StacksFrontier.Deformation.ToposThickening.FlatLiftFlatnessEquivalence
public import StacksFrontier.Deformation.ToposThickening.FlatLiftObstruction
public import StacksFrontier.Deformation.ToposThickening.ModulesOnThickening.ActionMapUnique

/-!
# An ideal-product sequence with invertible second factor is an extension with action map one

Let `i : (Sh(C), O) ⟶ (Sh(D), O')` be a first order thickening of ringed topoi with square-zero
ideal `I`, let `ℱ` be an `O`-module presented on the thickened topos as an `i_*O`-module, and
let `ℱ'` be an `O'`-module presented by a short exact sequence

`0 ⟶ I·ℱ' ⟶ ℱ' ⟶ i_*ℱ ⟶ 0`,

that is, with `i^*ℱ' ≅ ℱ`. When the second factor `I ⊗_O ℱ ⟶ I·ℱ'` of the canonical map of
Stacks 08MQ is an isomorphism, pushing that sequence out along its inverse exhibits `ℱ'` as an
extension of `ℱ` by `I ⊗_O ℱ` in the sense of Stacks 08MB whose canonical action of the
square-zero ideal is the **identity**.

This is the direction of the bookkeeping of Section 08MN opposite to the one
`StacksFrontier.Deformation.ToposThickening.FixedActionFlatness` carries: there an extension with
action map the identity is read as an ideal-product sequence, here an ideal-product sequence
whose second factor is invertible is read as such an extension.

## Main results

* `Deformation.ToposThickening.exists_fixedAction_of_isIso_canonicalSecondFactor`: **the
  extension with action map the identity attached to `ℱ'`.**

## Implementation notes

No pushout is formed. Replacing the kernel term `I·ℱ'` of the sequence by `I ⊗_O ℱ` along the
inverse of the second factor is an isomorphism of short complexes, so short exactness transports
(`CategoryTheory.ShortComplex.shortExact_of_iso`), and the resulting extension's inclusion is
the second factor followed by the inclusion of the ideal product. That its action map is the
identity is then the characterisation of the second factor,
`Deformation.ToposThickening.reductionTensorMap_comp_canonicalSecondFactor`, read on pure
tensors through the uniqueness of the action map,
`Deformation.ToposThickening.extensionActionMap_unique`.

## References

* [Stacks Project, Tag 08MB](https://stacks.math.columbia.edu/tag/08MB)
* [Stacks Project, Tag 08MP](https://stacks.math.columbia.edu/tag/08MP)
* [Stacks Project, Tag 08MQ](https://stacks.math.columbia.edu/tag/08MQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.SheafOfModules.FlatSquareZero (ringMap multiplicationMap reductionTensorMap
  multiplicationMap_tmul reductionTensorMap_tmul)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor)

universe v u w v' u'

namespace Deformation.ToposThickening

variable {X : RingedTopos.{v, u, w}} {X' : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [X'.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X'.J AddCommGrpCat.{w}]
  [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X'.J AddCommGrpCat.{w}]
  (i : RingedToposHom X X') (hi : FirstOrderThickening i)
  (F : SheafOfModules.{w}
    (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))
  (F' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))
  (q : F' ⟶ (SheafOfModules.restrictScalars (ringMap i.fSharp)).obj F)
  (hq : (idealProductSubmodule hi F').ι ≫ q = 0)
  (hqex : (ShortComplex.mk (idealProductSubmodule hi F').ι q hq).ShortExact)

include hqex

/-- The ideal-product sequence with its kernel term replaced by `I ⊗_O ℱ` is a complex. -/
theorem canonicalSecondFactor_comp_ι_comp_eq_zero :
    (canonicalSecondFactor i hi F F' q hq hqex ≫ (idealProductSubmodule hi F').ι) ≫ q = 0 := by
  rw [Category.assoc, hq, comp_zero]

/-- **The ideal-product sequence with its kernel term replaced by `I ⊗_O ℱ` is short exact**,
when the second factor is invertible. -/
theorem shortExact_canonicalSecondFactor_comp_ι
    (hcsf : IsIso (canonicalSecondFactor i hi F F' q hq hqex)) :
    (ShortComplex.mk
      (canonicalSecondFactor i hi F F' q hq hqex ≫ (idealProductSubmodule hi F').ι) q
      (canonicalSecondFactor_comp_ι_comp_eq_zero i hi F F' q hq hqex)).ShortExact := by
  have := hcsf
  refine ShortComplex.shortExact_of_iso ?_ hqex
  refine ShortComplex.isoMk (asIso (canonicalSecondFactor i hi F F' q hq hqex)).symm
    (Iso.refl _) (Iso.refl _) ?_ ?_
  · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom, asIso_inv, ← Category.assoc,
      IsIso.inv_hom_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

/-- **The canonical action of the square-zero ideal on the ideal-product sequence read through
the inverse of an invertible second factor is the identity.** The extension is the
ideal-product sequence of `ℱ'` with its kernel term `I·ℱ'` replaced by `I ⊗_O ℱ` along the
inverse of the second factor, and the action map is the identity because the second factor is
characterised by carrying `α ⊗ q(x)` to `α·x`.

This names the extension rather than merely asserting that one exists, which is what a
consumer comparing *which* extension a given flat lift gives needs;
`Deformation.ToposThickening.exists_fixedAction_of_isIso_canonicalSecondFactor` is the
existential reading of it. -/
theorem extensionActionMap_shortExactYonedaExtension_canonicalSecondFactor
    (hcsf : IsIso (canonicalSecondFactor i hi F F' q hq hqex)) :
    (extensionActionMap hi (Abelian.shortExactYonedaExtension
        (shortExact_canonicalSecondFactor_comp_ι i hi F F' q hq hqex hcsf))).1 =
      𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor ((pushforwardCommRingFunctor i.toToposHom).obj
          X.O)).flip.obj F).obj hi.I) := by
  refine extensionActionMap_unique hi _ _ ?_
  intro U a x
  have h2 := reductionTensorMap_tmul i.fSharp hi.I F' F q U a (show F'.val.obj U from x)
  have h3 := multiplicationMap_tmul i.fSharp hi.I F' hi.incl U a (show F'.val.obj U from x)
  have h4 := congrArg (fun m ↦ m.val.app U
      (((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf X'.O) (𝟙
              (Stacks.SheafOfModules.Tensor.ringSheaf X'.O).obj)).unit.app
          (PresheafOfModules.tensorObj ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj
              hi.I).val F'.val)).app U
          (a ⊗ₜ[X'.O.obj.obj U] (show F'.val.obj U from x))))
    (reductionTensorMap_comp_canonicalSecondFactor i hi F F' q hq hqex)
  exact Eq.trans (congrArg (fun y ↦ (canonicalSecondFactor i hi F F' q hq hqex ≫
    (idealProductSubmodule hi F').ι).val.app U y) h2.symm) (h4.trans h3)

/-- **`ℱ'` is an extension of `ℱ` by `I ⊗_O ℱ` whose canonical action of the square-zero ideal
is the identity**, as soon as the second factor `I ⊗_O ℱ ⟶ I·ℱ'` of the canonical map of
Stacks 08MQ is an isomorphism.

The sequence is the ideal-product sequence of `ℱ'` with its kernel term read through the inverse
of that factor, and the action map is the identity because the second factor is characterised by
carrying `α ⊗ q(x)` to `α·x`. -/
theorem exists_fixedAction_of_isIso_canonicalSecondFactor
    (hcsf : IsIso (canonicalSecondFactor i hi F F' q hq hqex)) :
    ∃ E : Abelian.YonedaExtension
        ((SheafOfModules.restrictScalars
          ((sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map i.fSharp)).obj F)
        ((SheafOfModules.restrictScalars
          ((sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map i.fSharp)).obj
          (((Stacks.SheafOfModules.Tensor.sheafTensor ((pushforwardCommRingFunctor
              i.toToposHom).obj X.O)).flip.obj F).obj
            hi.I)) 0,
      (extensionActionMap hi E).1 =
        𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor ((pushforwardCommRingFunctor
            i.toToposHom).obj X.O)).flip.obj F).obj hi.I) :=
  ⟨_, extensionActionMap_shortExactYonedaExtension_canonicalSecondFactor i hi F F' q hq hqex hcsf⟩

end Deformation.ToposThickening

end
