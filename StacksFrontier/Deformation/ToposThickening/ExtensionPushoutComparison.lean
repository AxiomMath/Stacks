module

public import StacksFrontier.Deformation.ToposThickening.ExtensionPushout

/-!
# The canonical map from an extension to its pushout along a morphism of thickenings

In the situation of `StacksFrontier/Deformation/ToposThickening/ExtensionPushout.lean` — a morphism
`h^♯ : O'₂ ⟶ O'₁` of first order thickenings of `(Sh(C), O)` presented on one site, and an
extension `0 ⟶ K₂ ⟶ F'₂ ⟶ F ⟶ 0` over `O'₂` — Stacks 08MJ produces an extension
`0 ⟶ K₁ ⟶ F'₁ ⟶ F ⟶ 0` over `O'₁` whose middle term is the pushout `F'₂ ⊔_{K₂} K₁` with the
descended `O'₁`-module structure. This file constructs the canonical map `F'₂ ⟶ F'₁`, read as a
map of `O'₂`-modules along `h^♯`, and records that it is `κ` on kernel modules and the identity on
`F`: the map of extensions of the pushout square of Stacks 08MJ.

## Main definitions

* `Deformation.ToposThickening.MorphismOfFirstOrderThickenings.PushoutExtensionData`
  `.comparisonMap`: the canonical map `F'₂ ⟶ F'₁` of Stacks 08MJ.

## Main results

* `...PushoutExtensionData.comparisonSection_f`: it is `κ` on kernel modules.
* `...PushoutExtensionData.extQuotOne_comparisonSection`: it is the identity on `F`.

## References

* [Stacks Project, Tag 08MJ](https://stacks.math.columbia.edu/tag/08MJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TensorProduct
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor)

universe v u w v₂ u₂

attribute [local implicit_reducible] SheafOfModules.unit PresheafOfModules.unit
  CategoryTheory.ConcreteCategory.hom CategoryTheory.sheafCompose SheafOfModules.forget
  SheafOfModules.restrictScalars PresheafOfModules.restrictScalars ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj' PresheafOfModules.restrictScalarsObj

attribute [local instance] PresheafOfModules.moduleMulOpposite
  PresheafOfModules.isCentralScalar_of_commRing

namespace Deformation.ToposThickening

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v₂, u₂, max v₂ u₂}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{max v₂ u₂})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{max v₂ u₂} RingCat.{max v₂ u₂})]

namespace MorphismOfFirstOrderThickenings

variable {i : RingedToposHom X Y} (D : MorphismOfFirstOrderThickenings i)

/-- The section of `T` with ring component `a` and zero ideal component is carried by `q` to the
image `h^♯(a)` of `a` in `O'₁`. -/
lemma sqZeroProj_mk_zero (U : Y.Cᵒᵖ) (a : D.O₂.obj.obj U) :
    D.sqZeroProj.hom.app U (D.sqZeroMk a 0) = D.ringMapH.hom.app U a := by
  rw [D.sqZeroProj_hom_app, D.sqZeroFst_mk, D.sqZeroSnd_mk,
    show D.inclOne U 0 = 0 from map_zero (D.first.incl.val.app U).hom, sub_zero]

end MorphismOfFirstOrderThickenings

section PushoutExtension

variable [Y.J.WEqualsLocallyBijective AddCommGrpCat.{max v₂ u₂}]
  [HasSheafify Y.J AddCommGrpCat.{max v₂ u₂}]
  [HasWeakSheafify Y.J AddCommGrpCat.{max v₂ u₂}]

attribute [local instance] sectionsModuleOfCommRing

namespace MorphismOfFirstOrderThickenings

attribute [local instance] sectionsModuleOverTwo

variable {i : RingedToposHom X Y}

attribute [local instance] sectionsModuleOverSqZero sectionsModuleOfSqZeroExt

namespace PushoutExtensionData

variable {D : MorphismOfFirstOrderThickenings i} (dat : D.PushoutExtensionData)
  (E₂ : Abelian.YonedaExtension ((SheafOfModules.restrictScalars D.ringMap₂).obj dat.F)
    ((SheafOfModules.restrictScalars D.ringMap₂).obj dat.K₂) 0)

variable (hE₂ : (extensionActionMap D.second E₂).1 = dat.c₂)

/-! ### The canonical map from the given extension to the pushed-out one -/

/-- Equal morphisms of sheaves of modules agree on local sections. -/
private lemma val_app_congr {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat} {M N : SheafOfModules R} {f g : M ⟶ N} (h : f = g) (U : Cᵒᵖ)
    (x : M.val.obj U) : f.val.app U x = g.val.app U x := by
  rw [h]

/-- The twisted action of the section `(a, 0)` of `T = O'₂ ⋉ I₁` on the pushout is the action of
its ring component `a`: the twisting term vanishes on the zero section of `I₁`. -/
lemma twistedSmul_mk_zero (U : Y.Cᵒᵖ) (a : D.O₂.obj.obj U)
    (p : (dat.pushoutModule E₂).val.obj U) :
    dat.twistedSmul E₂ U (D.sqZeroMk a 0) p = a • p := by
  rw [dat.twistedSmul_eq, D.sqZeroFst_mk, D.sqZeroSnd_mk, dat.twist_zero_left, sub_zero]

/-- The comparison with the pushout is bijective on local sections, read in the direction
opposite to `middleIso_inv_hom`. -/
lemma middleIso_hom_inv (U : Y.Cᵒᵖ) (p : (dat.twistedSheaf E₂).val.obj U) :
    (dat.middleIso E₂ hE₂).hom.val.app U ((dat.middleIso E₂ hE₂).inv.val.app U p) = p :=
  val_app_congr (dat.middleIso E₂ hE₂).inv_hom_id U p

/-- A local section of the middle term of the given extension, read through the pushout
comparison in the pushout with its twisted `T`-action. The pushout and the twisted module have
the same local sections; naming this reading lets the `T`-linearity of `middleIso` be applied to
the image of a section under the pushout comparison. -/
noncomputable def twistedComparisonSection (U : Y.Cᵒᵖ) (x : E₂.Z.left.val.obj U) :
    (dat.twistedSheaf E₂).val.obj U :=
  (dat.pushoutLift E₂).val.app U x

/-- That reading is semilinear for the section `(a, 0)` of `T`: the pushout comparison is
`O'₂`-linear, and `(a, 0)` acts on the twisted module as its ring component `a`. -/
lemma twistedComparisonSection_smul (U : Y.Cᵒᵖ) (a : D.O₂.obj.obj U)
    (x : E₂.Z.left.val.obj U) :
    dat.twistedComparisonSection E₂ U (a • x) =
      D.sqZeroMk a 0 • dat.twistedComparisonSection E₂ U x :=
  ((dat.twistedSmul_mk_zero E₂ U a ((dat.pushoutLift E₂).val.app U x)).trans
    (map_smul ((dat.pushoutLift E₂).val.app U).hom a x).symm).symm

/-- The image in the middle term of the extension of Stacks 08MJ of a local section of the
middle term of the given extension: the pushout comparison followed by the identification of the
descended module with the pushout. -/
noncomputable def comparisonSection (U : Y.Cᵒᵖ) (x : E₂.Z.left.val.obj U) :
    (dat.middle E₂ hE₂).val.obj U :=
  (dat.middleIso E₂ hE₂).inv.val.app U (dat.twistedComparisonSection E₂ U x)

/-- The comparison on local sections is semilinear over `h^♯`: a section `a` of `O'₂` acts on
the twisted module as the section `(a, 0)` of `T`, whose image under `q` is `h^♯(a)`. -/
lemma comparisonSection_smul (U : Y.Cᵒᵖ) (a : D.O₂.obj.obj U) (x : E₂.Z.left.val.obj U) :
    dat.comparisonSection E₂ hE₂ U (a • x) =
      D.ringMapH.hom.app U a • dat.comparisonSection E₂ hE₂ U x := by
  have hsmul : (dat.middleIso E₂ hE₂).inv.val.app U
        (D.sqZeroMk a 0 • dat.twistedComparisonSection E₂ U x) =
      D.sqZeroProj.hom.app U (D.sqZeroMk a 0) • dat.comparisonSection E₂ hE₂ U x :=
    map_smul ((dat.middleIso E₂ hE₂).inv.val.app U).hom (D.sqZeroMk a 0)
      (dat.twistedComparisonSection E₂ U x)
  calc dat.comparisonSection E₂ hE₂ U (a • x)
      = (dat.middleIso E₂ hE₂).inv.val.app U
          (D.sqZeroMk a 0 • dat.twistedComparisonSection E₂ U x) :=
        congrArg ((dat.middleIso E₂ hE₂).inv.val.app U)
          (dat.twistedComparisonSection_smul E₂ U a x)
    _ = D.sqZeroProj.hom.app U (D.sqZeroMk a 0) • dat.comparisonSection E₂ hE₂ U x := hsmul
    _ = D.ringMapH.hom.app U a • dat.comparisonSection E₂ hE₂ U x :=
        congrArg (fun z : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U =>
          z • dat.comparisonSection E₂ hE₂ U x) (D.sqZeroProj_mk_zero U a)

/-- The comparison on underlying presheaves of abelian groups: the pushout comparison followed
by the identification of the descended module with the pushout. -/
noncomputable def comparisonPresheafHom :
    E₂.Z.left.val.presheaf ⟶ (dat.middle E₂ hE₂).val.presheaf :=
  (PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf D.O₂).obj).map
      (dat.pushoutLift E₂).val ≫
    (show (dat.pushoutModule E₂).val.presheaf ⟶ (dat.middle E₂ hE₂).val.presheaf from
      (PresheafOfModules.toPresheaf D.sqZeroExt.obj).map (dat.middleIso E₂ hE₂).inv.val)

/-- **The canonical map of Stacks 08MJ on middle terms.** The map `F'₂ ⟶ F'₁` from the middle
term of the given extension over the second thickening to the middle term of the extension that
Stacks 08MJ produces over the first, read as a map of `O'₂`-modules along `h^♯`. It is the
pushout comparison, which the `O'₁`-module structure on the pushout descends. -/
noncomputable def comparisonMap :
    E₂.Z.left ⟶ (SheafOfModules.restrictScalars D.ringMapH).obj (dat.middle E₂ hE₂) :=
  ⟨PresheafOfModules.homMk (dat.comparisonPresheafHom E₂ hE₂)
    (fun U a x => dat.comparisonSection_smul E₂ hE₂ U a x)⟩

/-- The canonical map on local sections. -/
lemma comparisonMap_app (U : Y.Cᵒᵖ) (x : E₂.Z.left.val.obj U) :
    (dat.comparisonMap E₂ hE₂).val.app U x = dat.comparisonSection E₂ hE₂ U x := rfl

/-- **The canonical map of Stacks 08MJ is the identity on `F`**, on local sections: composing it
with the quotient map onto `F` of the extension over the first thickening gives the quotient map
of the given extension. -/
lemma extQuotOne_comparisonSection (U : Y.Cᵒᵖ) (x : E₂.Z.left.val.obj U) :
    (dat.extQuotOne E₂ hE₂).val.app U (dat.comparisonSection E₂ hE₂ U x) =
      E₂.g.val.app U x := by
  have hinv : (dat.middleIso E₂ hE₂).hom.val.app U (dat.comparisonSection E₂ hE₂ U x) =
      (dat.pushoutLift E₂).val.app U x :=
    dat.middleIso_hom_inv E₂ hE₂ U (dat.twistedComparisonSection E₂ U x)
  calc (dat.extQuotOne E₂ hE₂).val.app U (dat.comparisonSection E₂ hE₂ U x)
      = dat.quotSection E₂ U
          ((dat.middleIso E₂ hE₂).hom.val.app U (dat.comparisonSection E₂ hE₂ U x)) :=
        dat.extQuotOne_app E₂ hE₂ U _
    _ = dat.quotSection E₂ U ((dat.pushoutLift E₂).val.app U x) :=
        congrArg (dat.quotSection E₂ U) hinv
    _ = E₂.g.val.app U x :=
        val_app_congr (dat.pushoutLift_quot E₂) U x

/-- **The canonical map of Stacks 08MJ is `κ` on kernel modules**, on local sections: the image
of a section of `K₂` is the image under the inclusion of `K₁` of its image under `κ`. -/
lemma comparisonSection_f (U : Y.Cᵒᵖ) (k : dat.K₂.val.obj U) :
    dat.comparisonSection E₂ hE₂ U (E₂.f.val.app U k) =
      (dat.extInclOne E₂ hE₂).val.app U (dat.kernelMap.val.app U k) := by
  have hcomm : (dat.pushoutLift E₂).val.app U (E₂.f.val.app U k) =
      dat.inclSection E₂ U (dat.kernelMap.val.app U k) :=
    val_app_congr (dat.pushout_comm E₂) U k
  calc dat.comparisonSection E₂ hE₂ U (E₂.f.val.app U k)
      = (dat.middleIso E₂ hE₂).inv.val.app U
          (dat.inclSection E₂ U (dat.kernelMap.val.app U k)) :=
        congrArg ((dat.middleIso E₂ hE₂).inv.val.app U) hcomm
    _ = (dat.extInclOne E₂ hE₂).val.app U (dat.kernelMap.val.app U k) :=
        (dat.extInclOne_app E₂ hE₂ U (dat.kernelMap.val.app U k)).symm

end PushoutExtensionData

end MorphismOfFirstOrderThickenings

end PushoutExtension

end Deformation.ToposThickening

end
