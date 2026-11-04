module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import StacksFrontier.Deformation.ToposThickening.ExtensionPushout
public import StacksFrontier.Deformation.ToposThickening.Helpers.ObstructionCompatibilityRestriction
public import StacksFrontier.Deformation.ToposThickening.ModulesOnThickening.FixedAction

/-!
# Compatibility of the existence obstructions under a morphism of first order thickenings

Let `(Sh(C), O)` be a ringed topos with two first order thickenings `O'₁` and `O'₂` presented on
one site and a morphism `h^♯ : O'₂ ⟶ O'₁` of thickenings over it, as in Stacks 08MJ, and let
`ℐ₂ ⟶ ℐ₁` be the induced map of defining ideals. Let `F` be an `O`-module, let `(Kₖ, cₖ)` be a
module with a prescribed action `cₖ : ℐₖ ⊗_O F ⟶ Kₖ` for `k = 1, 2`, and let `κ : K₂ ⟶ K₁` make
the square with `ℐ₂ ⊗ F ⟶ ℐ₁ ⊗ F` commute. Then the map
`Ext²_O(F, K₂) ⟶ Ext²_O(F, K₁)` induced by `κ` carries `o(F, K₂, c₂)` to `o(F, K₁, c₁)`.

## Main results

* `Deformation.ToposThickening.MorphismOfFirstOrderThickenings.existenceObstructionClass_first`:
  the obstruction class of the first thickening is the obstruction class of the second pushed
  forward along `κ`.

## References

* [Stacks Project, Tag 0CYC](https://stacks.math.columbia.edu/tag/0CYC)
* [Stacks Project, Tag 08MJ](https://stacks.math.columbia.edu/tag/08MJ)
* [Stacks Project, Tag 08MF](https://stacks.math.columbia.edu/tag/08MF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TensorProduct
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor)

universe v u w v₂ u₂ w₂ e

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
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{max v₂ u₂}]
  [HasSheafify Y.J AddCommGrpCat.{max v₂ u₂}]
  [HasWeakSheafify Y.J AddCommGrpCat.{max v₂ u₂}]
  {i : RingedToposHom X Y}

attribute [local instance] sectionsModuleOfCommRing

namespace MorphismOfFirstOrderThickenings

attribute [local instance] sectionsModuleOverTwo sectionsModuleOverSqZero
  sectionsModuleOfSqZeroExt

variable {D : MorphismOfFirstOrderThickenings i}

namespace PushoutExtensionData

variable (dat : D.PushoutExtensionData)
  (E₂ : Abelian.YonedaExtension ((SheafOfModules.restrictScalars D.ringMap₂).obj dat.F)
    ((SheafOfModules.restrictScalars D.ringMap₂).obj dat.K₂) 0)
  {N : SheafOfModules.{max v₂ u₂} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i))}
  (cmp₂ : E₂.Z.left ⟶ (SheafOfModules.restrictScalars D.ringMap₂).obj N) (n : dat.K₁ ⟶ N)
  (hn : E₂.f ≫ cmp₂ =
    dat.kernelMapTwo ≫ (SheafOfModules.restrictScalars D.ringMap₂).map n)

/-- The comparison from the pushout `F'₂ ⊔_{K₂} K₁` to a module over the base, out of a
comparison on the middle term of the given extension and a map out of the new kernel module
agreeing with it. -/
noncomputable def pushoutCompare :
    dat.pushoutModule E₂ ⟶ (SheafOfModules.restrictScalars D.ringMap₂).obj N :=
  pushout.desc cmp₂ ((SheafOfModules.restrictScalars D.ringMap₂).map n) hn

/-- On the new kernel module the comparison is the prescribed map. -/
lemma pushoutIncl_pushoutCompare :
    dat.pushoutIncl E₂ ≫ dat.pushoutCompare E₂ cmp₂ n hn =
      (SheafOfModules.restrictScalars D.ringMap₂).map n :=
  pushout.inr_desc _ _ _

/-- On the middle term of the given extension the comparison is the prescribed comparison. -/
lemma pushoutLift_pushoutCompare :
    dat.pushoutLift E₂ ≫ dat.pushoutCompare E₂ cmp₂ n hn = cmp₂ :=
  pushout.inl_desc _ _ _

/-- The comparison kills the twisting term when the prescribed action map of the first
thickening followed by the prescribed map out of the new kernel module vanishes. -/
lemma pushoutCompare_twist (hc : dat.c₁ ≫ n = 0) (U : Y.Cᵒᵖ) (m : D.first.I.val.obj U)
    (p : (dat.pushoutModule E₂).val.obj U) :
    (dat.pushoutCompare E₂ cmp₂ n hn).val.app U (dat.twist E₂ U m p) = 0 := by
  have hz : (SheafOfModules.restrictScalars D.ringMap₂).map dat.c₁ ≫
      dat.pushoutIncl E₂ ≫ dat.pushoutCompare E₂ cmp₂ n hn = 0 := by
    rw [dat.pushoutIncl_pushoutCompare E₂ cmp₂ n hn, ← Functor.map_comp, hc,
      CategoryTheory.Functor.map_zero]
  exact congrArg (fun z : (SheafOfModules.restrictScalars D.ringMap₂).obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u₂, v₂, max v₂ u₂, max v₂ u₂, max v₂ u₂}
          (baseRing i)).obj D.first.I).obj dat.F) ⟶
      (SheafOfModules.restrictScalars D.ringMap₂).obj N ↦
    z.val.app U (dat.tensorMk U m (dat.quotSection E₂ U p))) hz

/-- The comparison from the pushout, on local sections, with values in the sections of the
module over the base. -/
noncomputable def compareSection (U : Y.Cᵒᵖ) (p : (dat.pushoutModule E₂).val.obj U) :
    N.val.obj U :=
  (dat.pushoutCompare E₂ cmp₂ n hn).val.app U p

/-- The comparison respects differences of sections. -/
lemma compareSection_sub (U : Y.Cᵒᵖ) (p p' : (dat.pushoutModule E₂).val.obj U) :
    dat.compareSection E₂ cmp₂ n hn U (p - p') =
      dat.compareSection E₂ cmp₂ n hn U p - dat.compareSection E₂ cmp₂ n hn U p' :=
  map_sub ((dat.pushoutCompare E₂ cmp₂ n hn).val.app U).hom p p'

/-- The comparison is linear over the structure sheaf of the second thickening. -/
lemma compareSection_smul (U : Y.Cᵒᵖ) (a : D.O₂.obj.obj U)
    (p : (dat.pushoutModule E₂).val.obj U) :
    dat.compareSection E₂ cmp₂ n hn U (a • p) =
      D.fSharp₂.hom.app U a • dat.compareSection E₂ cmp₂ n hn U p :=
  map_smul ((dat.pushoutCompare E₂ cmp₂ n hn).val.app U).hom a p

/-- The comparison kills the twisting term. -/
lemma compareSection_twist (hc : dat.c₁ ≫ n = 0) (U : Y.Cᵒᵖ) (m : D.first.I.val.obj U)
    (p : (dat.pushoutModule E₂).val.obj U) :
    dat.compareSection E₂ cmp₂ n hn U (dat.twist E₂ U m p) = 0 :=
  dat.pushoutCompare_twist E₂ cmp₂ n hn hc U m p

/-- The comparison from the pushout is linear for the twisted action. -/
lemma compareSection_smul_sqZero (hc : dat.c₁ ≫ n = 0) (U : Y.Cᵒᵖ) (r : D.sqZeroSections U)
    (p : (dat.pushoutModule E₂).val.obj U) :
    dat.compareSection E₂ cmp₂ n hn U (dat.twistedSmul E₂ U r p) =
      (structureRingMap i).hom.app U (D.sqZeroProj.hom.app U r) •
        dat.compareSection E₂ cmp₂ n hn U p := by
  rw [D.structureRingMap_sqZeroProj, dat.twistedSmul_eq, dat.compareSection_sub,
    dat.compareSection_smul, dat.compareSection_twist E₂ cmp₂ n hn hc]
  exact sub_zero _

/-- Two maps of sheaves of modules are equal as soon as they agree on all local sections. -/
private theorem hom_ext_of_app_eq {C' : Type*} [Category C'] {J' : GrothendieckTopology C'}
    {R : Sheaf J' RingCat.{w₂}} {A B : SheafOfModules.{e} R} (f g : A ⟶ B)
    (h : ∀ (U : C'ᵒᵖ) (x : A.val.obj U), f.val.app U x = g.val.app U x) : f = g :=
  SheafOfModules.hom_ext <| PresheafOfModules.hom_ext fun U ↦ ModuleCat.hom_ext <|
    LinearMap.ext (h U)

/-- The comparison from the pushout, as a map of modules over `T = O'₂ ⋉ ℐ₁`. -/
noncomputable def twistedCompare (hc : dat.c₁ ≫ n = 0) :
    dat.twistedSheaf E₂ ⟶
      (SheafOfModules.restrictScalars D.sqZeroProj).obj
        ((SheafOfModules.restrictScalars (structureRingMap i)).obj N) :=
  ⟨PresheafOfModules.homMk
    ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf D.O₂).obj).map
      (dat.pushoutCompare E₂ cmp₂ n hn).val)
    (fun U r p ↦ dat.compareSection_smul_sqZero E₂ cmp₂ n hn hc U r p)⟩

variable (hE₂ : (extensionActionMap D.second E₂).1 = dat.c₂)

/-- The comparison from the middle term of the extension over the first thickening to a module
over the base: the descent along `q : T ⟶ O'₁` of the comparison from the pushout. -/
noncomputable def middleCompare (hc : dat.c₁ ≫ n = 0) :
    dat.middle E₂ hE₂ ⟶ (SheafOfModules.restrictScalars (structureRingMap i)).obj N :=
  D.sqZeroRestrictFullyFaithful.preimage
    ((dat.middleIso E₂ hE₂).hom ≫ dat.twistedCompare E₂ cmp₂ n hn hc)

/-- Restricting the comparison on the middle term along `q` gives the comparison from the
pushout. -/
lemma restrictScalars_middleCompare (hc : dat.c₁ ≫ n = 0) :
    (SheafOfModules.restrictScalars D.sqZeroProj).map
        (dat.middleCompare E₂ cmp₂ n hn hE₂ hc) =
      (dat.middleIso E₂ hE₂).hom ≫ dat.twistedCompare E₂ cmp₂ n hn hc :=
  D.sqZeroRestrictFullyFaithful.map_preimage _

/-- On the new kernel module the comparison on the middle term is the prescribed map. -/
lemma extInclOne_middleCompare (hc : dat.c₁ ≫ n = 0) :
    dat.extInclOne E₂ hE₂ ≫ dat.middleCompare E₂ cmp₂ n hn hE₂ hc =
      (SheafOfModules.restrictScalars (structureRingMap i)).map n := by
  apply D.sqZeroRestrictFullyFaithful.map_injective
  rw [Functor.map_comp, dat.restrictScalars_extInclOne E₂ hE₂,
    dat.restrictScalars_middleCompare E₂ cmp₂ n hn hE₂ hc, Category.assoc,
    Iso.inv_hom_id_assoc]
  exact hom_ext_of_app_eq _ _ fun U k ↦
    congrArg (fun z : (SheafOfModules.restrictScalars D.ringMap₂).obj dat.K₁ ⟶
      (SheafOfModules.restrictScalars D.ringMap₂).obj N ↦ z.val.app U k)
    (dat.pushoutIncl_pushoutCompare E₂ cmp₂ n hn)

/-- The comparison on the middle term is compatible with the two surjections onto `F`, as soon
as the two maps it is built from are. -/
lemma middleCompare_extQuotOne (hc : dat.c₁ ≫ n = 0) (ng : N ⟶ dat.F)
    (hcmpg : cmp₂ ≫ (SheafOfModules.restrictScalars D.ringMap₂).map ng = E₂.g)
    (hng : n ≫ ng = 0) :
    dat.middleCompare E₂ cmp₂ n hn hE₂ hc ≫
        (SheafOfModules.restrictScalars (structureRingMap i)).map ng =
      dat.extQuotOne E₂ hE₂ := by
  have hpq : dat.pushoutCompare E₂ cmp₂ n hn ≫
      (SheafOfModules.restrictScalars D.ringMap₂).map ng = dat.pushoutQuot E₂ := by
    apply pushout.hom_ext
    · refine (Category.assoc _ _ _).symm.trans ?_
      erw [dat.pushoutLift_pushoutCompare, hcmpg, dat.pushoutLift_quot]
    · refine (Category.assoc _ _ _).symm.trans ?_
      erw [dat.pushoutIncl_pushoutCompare, ← Functor.map_comp, hng, Functor.map_zero,
        dat.pushoutIncl_quot]
  apply D.sqZeroRestrictFullyFaithful.map_injective
  rw [Functor.map_comp, dat.restrictScalars_middleCompare E₂ cmp₂ n hn hE₂ hc,
    dat.restrictScalars_extQuotOne E₂ hE₂, Category.assoc]
  refine congrArg (fun z ↦ (dat.middleIso E₂ hE₂).hom ≫ z) ?_
  exact hom_ext_of_app_eq _ _ fun U p ↦ congrArg (fun z : dat.pushoutModule E₂ ⟶
      (SheafOfModules.restrictScalars D.ringMap₂).obj dat.F ↦ z.val.app U p) hpq

/-! ### The presentation for the first thickening -/

/-- The action map of the extension over the first thickening is killed by the projection. -/
lemma extensionOne_actionMap_comp (P₂ : MonoActionPresentation D.second E₂)
    (proj₁ : dat.K₁ ⟶ P₂.C)
    (hz₁ : dat.c₁ ≫ proj₁ = 0) :
    (extensionActionMap D.first (dat.extensionOne E₂ hE₂)).1 ≫ proj₁ = 0 :=
  (congrArg (fun z ↦ z ≫ proj₁) (dat.extensionOne_actionMap E₂ hE₂)).trans hz₁

/-- The defining sequence of the presentation for the first thickening is short exact. -/
lemma extensionOne_shortExact (P₂ : MonoActionPresentation D.second E₂)
    (proj₁ : dat.K₁ ⟶ P₂.C)
    (hz₁ : dat.c₁ ≫ proj₁ = 0) (hSE₁ : (ShortComplex.mk dat.c₁ proj₁ hz₁).ShortExact) :
    (ShortComplex.mk (extensionActionMap D.first (dat.extensionOne E₂ hE₂)).1 proj₁
      (dat.extensionOne_actionMap_comp E₂ hE₂ P₂ proj₁ hz₁)).ShortExact :=
  ShortComplex.shortExact_of_iso
    (show ShortComplex.mk dat.c₁ proj₁ hz₁ ≅
        ShortComplex.mk (extensionActionMap D.first (dat.extensionOne E₂ hE₂)).1 proj₁
          (dat.extensionOne_actionMap_comp E₂ hE₂ P₂ proj₁ hz₁) from
      ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        ((Category.id_comp _).trans
          ((dat.extensionOne_actionMap E₂ hE₂).trans (Category.comp_id dat.c₁).symm))
        ((Category.id_comp proj₁).trans (Category.comp_id proj₁).symm))
    hSE₁

/-- The prescribed action map of the first thickening is killed by the projection followed by
the kernel map of the descended extension. -/
lemma c₁_comp_proj_descent (P₂ : MonoActionPresentation D.second E₂)
    (proj₁ : dat.K₁ ⟶ P₂.C)
    (hz₁ : dat.c₁ ≫ proj₁ = 0) : dat.c₁ ≫ (proj₁ ≫ P₂.descent.f) = 0 :=
  (Category.assoc _ _ _).symm.trans ((congrArg (fun z ↦ z ≫ P₂.descent.f) hz₁).trans zero_comp)

/-- The comparison of the presentation for the second thickening is compatible with the map of
kernel modules and the projection. -/
lemma comparison_left_proj (P₂ : MonoActionPresentation D.second E₂)
    (proj₁ : dat.K₁ ⟶ P₂.C)
    (hpj : dat.kernelMap ≫ proj₁ = P₂.proj) :
    E₂.f ≫ P₂.comparison = dat.kernelMapTwo ≫
      (SheafOfModules.restrictScalars D.ringMap₂).map (proj₁ ≫ P₂.descent.f) :=
  P₂.comparison_left.trans
    ((congrArg (fun z ↦ (SheafOfModules.restrictScalars D.ringMap₂).map z ≫
          (SheafOfModules.restrictScalars D.ringMap₂).map P₂.descent.f) hpj.symm).trans
      ((congrArg
          (fun z ↦ z ≫ (SheafOfModules.restrictScalars D.ringMap₂).map P₂.descent.f)
          ((SheafOfModules.restrictScalars D.ringMap₂).map_comp dat.kernelMap proj₁)).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun z ↦ dat.kernelMapTwo ≫ z)
            ((SheafOfModules.restrictScalars D.ringMap₂).map_comp proj₁
              P₂.descent.f).symm))))

/-- The kernel map of the descended extension composed with its quotient map vanishes. -/
lemma proj_descent_comp_descent_g (P₂ : MonoActionPresentation D.second E₂)
    (proj₁ : dat.K₁ ⟶ P₂.C) :
    (proj₁ ≫ P₂.descent.f) ≫ P₂.descent.g = 0 := by
  rw [Category.assoc, yonedaExtension_comp_zero, comp_zero]

/-- **The presentation of the obstruction class for the first thickening attached to one for the
second.** Its quotient module and its extension of `F` over the base are those of the given
presentation; its kernel module is the one prescribed by the data, its extension is the one
Stacks 08MJ produces by pushout, and its comparison is the descent along `q` of the comparison
from the pushout. -/
noncomputable def firstPresentation (P₂ : MonoActionPresentation D.second E₂)
    (proj₁ : dat.K₁ ⟶ P₂.C)
    (hz₁ : dat.c₁ ≫ proj₁ = 0) (hSE₁ : (ShortComplex.mk dat.c₁ proj₁ hz₁).ShortExact)
    (hpj : dat.kernelMap ≫ proj₁ = P₂.proj) :
    MonoActionPresentation D.first (dat.extensionOne E₂ hE₂) where
  C := P₂.C
  proj := proj₁
  zero := dat.extensionOne_actionMap_comp E₂ hE₂ P₂ proj₁ hz₁
  shortExact := dat.extensionOne_shortExact E₂ hE₂ P₂ proj₁ hz₁ hSE₁
  descent := P₂.descent
  comparison := dat.middleCompare E₂ P₂.comparison (proj₁ ≫ P₂.descent.f)
    (dat.comparison_left_proj E₂ P₂ proj₁ hpj) hE₂
    (dat.c₁_comp_proj_descent E₂ P₂ proj₁ hz₁)
  comparison_left :=
    (dat.extInclOne_middleCompare E₂ P₂.comparison (proj₁ ≫ P₂.descent.f)
      (dat.comparison_left_proj E₂ P₂ proj₁ hpj) hE₂
      (dat.c₁_comp_proj_descent E₂ P₂ proj₁ hz₁)).trans (Functor.map_comp _ _ _)
  comparison_right :=
    dat.middleCompare_extQuotOne E₂ P₂.comparison (proj₁ ≫ P₂.descent.f)
      (dat.comparison_left_proj E₂ P₂ proj₁ hpj) hE₂
      (dat.c₁_comp_proj_descent E₂ P₂ proj₁ hz₁) P₂.descent.g P₂.comparison_right
      (dat.proj_descent_comp_descent_g E₂ P₂ proj₁)

/-- The map of defining ideals compares the two action maps. -/
lemma firstPresentation_comm₁₂
    (hkm : dat.c₂ ≫ dat.kernelMap =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u₂, v₂, max v₂ u₂, max v₂ u₂, max v₂ u₂}
        (baseRing i)).map D.idealMap).app dat.F ≫ dat.c₁) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u₂, v₂, max v₂ u₂, max v₂ u₂, max v₂ u₂}
      (baseRing i)).map D.idealMap).app dat.F ≫
        (extensionActionMap D.first (dat.extensionOne E₂ hE₂)).1 =
      (extensionActionMap D.second E₂).1 ≫ dat.kernelMap := by
  rw [dat.extensionOne_actionMap E₂ hE₂, hE₂]
  exact hkm.symm

variable
  [HasExt.{e} (SheafOfModules.{max v₂ u₂} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)))]
  [HasExt.{e} (SheafOfModules.{max v₂ u₂} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]

omit [HasExt.{e} (SheafOfModules.{max v₂ u₂} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))] in
/-- **The universal obstruction classes of the two presentations differ by the induced map of
defining ideals.** -/
lemma firstPresentation_universalClass (P₂ : MonoActionPresentation D.second E₂)
    (proj₁ : dat.K₁ ⟶ P₂.C)
    (hz₁ : dat.c₁ ≫ proj₁ = 0) (hSE₁ : (ShortComplex.mk dat.c₁ proj₁ hz₁).ShortExact)
    (hpj : dat.kernelMap ≫ proj₁ = P₂.proj)
    (hkm : dat.c₂ ≫ dat.kernelMap =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u₂, v₂, max v₂ u₂, max v₂ u₂, max v₂ u₂}
        (baseRing i)).map D.idealMap).app dat.F ≫ dat.c₁) :
    (dat.firstPresentation E₂ hE₂ P₂ proj₁ hz₁ hSE₁ hpj).universalClass =
      P₂.universalClass.comp
        (Abelian.Ext.mk₀
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u₂, v₂, max v₂ u₂, max v₂ u₂, max v₂ u₂}
            (baseRing i)).map D.idealMap).app dat.F))
        (add_zero 2) :=
  Abelian.comp_extClass_naturality
    (dat.firstPresentation E₂ hE₂ P₂ proj₁ hz₁ hSE₁ hpj).shortExact P₂.shortExact
    { τ₁ := ((Stacks.SheafOfModules.Tensor.sheafTensor.{u₂, v₂, max v₂ u₂, max v₂ u₂, max v₂ u₂}
        (baseRing i)).map D.idealMap).app dat.F
      τ₂ := dat.kernelMap
      τ₃ := 𝟙 _
      comm₁₂ := dat.firstPresentation_comm₁₂ E₂ hE₂ hkm
      comm₂₃ := hpj.trans (Category.comp_id _).symm }
    (yonedaExtension_shortExact P₂.descent).extClass
    (yonedaExtension_shortExact P₂.descent).extClass
    (Abelian.Ext.comp_mk₀_id _).symm

end PushoutExtensionData

/-! ### The data attached to a presentation for the second thickening -/

/-- The data of Stacks 08MJ attached to a short exact sequence `0 → ℐ₂ ⊗ F → Q₂ → C → 0` and its
pushout along the induced map of defining ideals: the kernel modules are `Q₂` and the pushout,
and the two action maps are the two maps out of the tensor products. -/
noncomputable def pushoutDataOfPushout
    {F Q₂ K₁ : SheafOfModules.{max v₂ u₂} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i))}
    (d₂ : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u₂, v₂, max v₂ u₂, max v₂ u₂, max v₂ u₂}
      (baseRing i)).obj D.second.I).obj F ⟶ Q₂)
    (c₁ : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u₂, v₂, max v₂ u₂, max v₂ u₂, max v₂ u₂}
      (baseRing i)).obj D.first.I).obj F ⟶ K₁) (γ : Q₂ ⟶ K₁)
    (hγ : d₂ ≫ γ =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u₂, v₂, max v₂ u₂, max v₂ u₂, max v₂ u₂}
        (baseRing i)).map D.idealMap).app F ≫ c₁) :
    D.PushoutExtensionData where
  F := F
  K₁ := K₁
  K₂ := Q₂
  c₁ := c₁
  c₂ := d₂
  kernelMap := γ
  comm := fun U b y ↦ by
    have ht := tensorSheaf_map_unit_tmul (baseRing i) (H := F) D.idealMap U b y
    have h := congrArg (fun z :
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u₂, v₂, max v₂ u₂, max v₂ u₂, max v₂ u₂}
          (baseRing i)).obj D.second.I).obj F ⟶ K₁ ↦
      z.val.app U (((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i))
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)).obj)).unit.app
        (PresheafOfModules.tensorObj D.second.I.val F.val)).app U
        (b ⊗ₜ[(baseRing i).obj.obj U] y))) hγ
    exact h.trans (congrArg (fun z ↦ c₁.val.app U z) ht)

end MorphismOfFirstOrderThickenings

end Deformation.ToposThickening

/-! ### The compatibility of the obstruction classes -/

namespace Deformation.ToposThickening

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v₂, u₂, w₂}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w₂})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w₂} RingCat.{w₂})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w₂}]
  [HasSheafify Y.J AddCommGrpCat.{w₂}] [HasWeakSheafify Y.J AddCommGrpCat.{w₂}]
  {i : RingedToposHom X Y}

namespace MorphismOfFirstOrderThickenings

variable (D : MorphismOfFirstOrderThickenings i)
  [HasExt.{e} (SheafOfModules.{w₂} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)))]
  [HasExt.{e} (SheafOfModules.{w₂} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]

/-- The obstruction classes of the two thickenings are compatible: the map
`Ext²_O(F, K₂) ⟶ Ext²_O(F, K₁)` induced by `κ` carries `o(F, K₂, c₂)` to `o(F, K₁, c₁)`. -/
@[stacks 0CYC]
theorem existenceObstructionClass_first
    [HasExt.{e} (SheafOfModules.{w₂} (Stacks.SheafOfModules.Tensor.ringSheaf D.O₂))]
    (F K₁ K₂ : SheafOfModules.{w₂} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)))
    (c₁ : ((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).obj D.first.I).obj F ⟶ K₁)
    (c₂ : ((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).obj D.second.I).obj F ⟶ K₂)
    (κ : K₂ ⟶ K₁)
    (hκ : c₂ ≫ κ =
      ((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).map D.idealMap).app F ≫ c₁) :
    existenceObstructionClass D.first F K₁ c₁ =
      (existenceObstructionClass D.second F K₂ c₂).comp (Abelian.Ext.mk₀ κ) (add_zero 2) := by
  classical
  obtain ⟨Q₁, E₁, ⟨P₁⟩⟩ := exists_extension_monoActionPresentation D.first F
  obtain ⟨Q₂, E₂, ⟨P₂⟩⟩ := exists_extension_monoActionPresentation D.second F
  obtain ⟨E₃, u₂, u₁, ⟨hu₂, hg₂⟩, hu₁, hg₁⟩ :=
    exists_extension_hom_pair_of_extensions E₂ (D.restrictedExtension E₁)
  have hd₂ : (extensionActionMap D.second E₃).1 ≫ biprod.fst = (extensionActionMap D.second E₂).1 :=
    extensionActionMap_comp_of_hom D.second E₃ E₂ biprod.fst u₂ hu₂ hg₂
  have : Mono (extensionActionMap D.second E₂).1 := P₂.shortExact.mono_f
  obtain ⟨P₃⟩ := exists_monoActionPresentation D.second E₃ (mono_of_mono_fac hd₂)
  have huniv := D.universalClass_first_eq_comp_of_hom P₃ P₁ biprod.snd u₁ hu₁ hg₁
  rw [existenceObstructionClass_eq_obstruction D.first F K₁ c₁ P₁,
    existenceObstructionClass_eq_obstruction D.second F K₂ c₂ P₃]
  show P₁.universalClass.comp (Abelian.Ext.mk₀ c₁) (add_zero 2) =
    (P₃.universalClass.comp (Abelian.Ext.mk₀ c₂) (add_zero 2)).comp
      (Abelian.Ext.mk₀ κ) (add_zero 2)
  rw [huniv, Abelian.Ext.comp_assoc_of_third_deg_zero,
    Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀,
    Abelian.Ext.mk₀_comp_mk₀, hκ]
  rfl

end MorphismOfFirstOrderThickenings

end Deformation.ToposThickening

end
