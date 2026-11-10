module

public import StacksFrontier.Deformation.ToposThickening.FlatThickeningComplexPushout

/-!
# The flat lift `h^*ℱ'₂` of Stacks 08VY

In Situation **Stacks 08VX**, presented on one site as
`Deformation.ToposThickening.FlatThickeningComplexSituation`, the `O'₁`-module `h^*ℱ'₂` is a lift
of `ℱ` flat over `O_{ℬ'₁}`. This file builds it as a `Deformation.ToposThickening.FlatLift`
across the first column, out of the identification of `h^*ℱ'₂` with the descended pushout
`ℱ'₂ ⊔_{I₂ ⊗ ℱ} (I₁ ⊗ ℱ)`, an extension of `ℱ` by `I₁ ⊗ ℱ` whose canonical action of `I₁` is the
identity.

## Main definitions

* `Deformation.ToposThickening.yonedaExtensionOfIso`: an extension with its middle term replaced
  by an isomorphic object.
* `Deformation.ToposThickening.flatLiftOfIso`: the flat lift of Stacks 08MQ attached to an
  extension with action map the identity, on a module isomorphic to its middle term.
* `Deformation.ToposThickening.FlatThickeningComplexSituation.pulledLift`: `h^*ℱ'₂` as a flat
  lift of `ℱ` across the first column.

## Main results

* `Deformation.ToposThickening.fixedActionExtensionClass_flatLiftOfIso`: the class attached to
  `flatLiftOfIso` is the class of the extension.
* `Deformation.ToposThickening.FlatThickeningComplexSituation.pulledLift_π`: the map
  `h^*ℱ'₂ ⟶ i₁_*ℱ` of the lift is the transpose under `h^* ⊣ h_*` of the reduction
  `ℱ'₂ ⟶ i₂_*ℱ`, i.e. the identification `i₁^*h^*ℱ'₂ = i₂^*ℱ'₂ = ℱ`.

## References

* [Stacks Project, Tag 08VY](https://stacks.math.columbia.edu/tag/08VY)
* [Stacks Project, Tag 08MQ](https://stacks.math.columbia.edu/tag/08MQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardModuleFunctor)
open Stacks.Sheaves.RingedToposModules.RingedToposHom (pullbackModules)

universe v u v₂ u₂ w vB uB wB vB' uB' wB' e

namespace Deformation.ToposThickening

section Transport

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]

/-- **An extension with its middle term replaced by an isomorphic object**: for
`0 ⟶ A ⟶ E ⟶ B ⟶ 0` and `κ : M ≅ E`, the extension `0 ⟶ A ⟶ M ⟶ B ⟶ 0` with maps `E.f ≫ κ⁻¹`
and `κ ≫ E.g`. -/
noncomputable def yonedaExtensionOfIso {A B : 𝒜} (E : Abelian.YonedaExtension B A 0) {M : 𝒜}
    (κ : M ≅ E.Z.left) : Abelian.YonedaExtension B A 0 :=
  Abelian.shortExactYonedaExtension (S := ShortComplex.mk (E.f ≫ κ.inv) (κ.hom ≫ E.g) (by
      rw [Category.assoc, κ.inv_hom_id_assoc, yonedaExtension_comp_zero]))
    (ShortComplex.shortExact_of_iso
      (S₁ := ShortComplex.mk E.f E.g (yonedaExtension_comp_zero E))
      (ShortComplex.isoMk (Iso.refl _) κ.symm (Iso.refl _) (by simp) (by simp))
      (yonedaExtension_shortExact E))

end Transport

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v₂, u₂, w}}
  {B : RingedTopos.{vB, uB, wB}} {B' : RingedTopos.{vB', uB', wB'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [B.J.HasSheafCompose (forget RingCat.{wB})] [B'.J.HasSheafCompose (forget RingCat.{wB'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{wB} RingCat.{wB})]
  [B'.J.HasSheafCompose (forget₂ CommRingCat.{wB'} RingCat.{wB'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [B.J.HasSheafCompose (forget AddCommGrpCat.{wB})]
  [B'.J.HasSheafCompose (forget AddCommGrpCat.{wB'})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w}] [HasWeakSheafify Y.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify X.J AddCommGrpCat.{w}]

section FlatLiftOfIso

variable (i : RingedToposHom X Y) (t : RingedToposHom B B') (f : RingedToposHom X B)
  (f' : RingedToposHom Y B') (hi : FirstOrderThickening i) (ht : FirstOrderThickening t)
  (comm : f'.comp i = t.comp f)
  (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)))

omit [B'.J.HasSheafCompose (forget RingCat.{wB'})]
  [B'.J.HasSheafCompose (forget₂ CommRingCat.{wB'} RingCat.{wB'})]
  [B.J.HasSheafCompose (forget AddCommGrpCat.{wB})]
  [B'.J.HasSheafCompose (forget AddCommGrpCat.{wB'})]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [B.J.HasSheafCompose (forget RingCat.{wB})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{wB} RingCat.{wB})] in
/-- Replacing the middle term of an extension by an isomorphic object does not change its
canonical action map. -/
theorem extensionActionMap_yonedaExtensionOfIso
    (E : Abelian.YonedaExtension ((structureRestrict i).obj F)
      ((structureRestrict i).obj (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj
          F).obj hi.I)) 0)
    {M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)} (κ : M ≅ E.Z.left) :
    (extensionActionMap hi (yonedaExtensionOfIso E κ)).1 = (extensionActionMap hi E).1 :=
  (extensionActionMap_comp_of_hom hi E (yonedaExtensionOfIso E κ)
    (𝟙 _) κ.inv ((Category.id_comp _).symm.trans (congrArg (· ≫ (E.f ≫ κ.inv))
      (CategoryTheory.Functor.map_id (structureRestrict i) _).symm))
    (κ.inv_hom_id_assoc E.g)).symm.trans (Category.comp_id _)

variable (hstrict : IsStrictPullbackIdealMap i t f f' hi ht comm)
  (hF : AlgebraicGeometry.SheafOfModules.IsFlat (reducedBaseModule i t f f' comm F))
  (hcff : IsIso (canonicalFirstFactor i t f f' hi ht comm F))

/-- **The flat lift attached to an extension with action map the identity, on a module isomorphic
to its middle term** (Stacks 08MQ): the module `M`, with the map `M ≅ E ⟶ i_*ℱ`. -/
noncomputable def flatLiftOfIso
    (E : Abelian.YonedaExtension ((structureRestrict i).obj F)
      ((structureRestrict i).obj (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj
          F).obj hi.I)) 0)
    (hE : (extensionActionMap hi E).1 = 𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing
        i)).flip.obj F).obj hi.I))
    {M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)} (κ : M ≅ E.Z.left) :
    FlatLift i f' hi F :=
  flatLiftOfFixedActionIdentity i t f f' hi ht comm F hstrict hF hcff (yonedaExtensionOfIso E κ)
    ((extensionActionMap_yonedaExtensionOfIso i hi F E κ).trans hE)

omit [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [B.J.HasSheafCompose (forget AddCommGrpCat.{wB})] in
/-- The module of `flatLiftOfIso` is the given module. -/
theorem flatLiftOfIso_module'
    (E : Abelian.YonedaExtension ((structureRestrict i).obj F)
      ((structureRestrict i).obj (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj
          F).obj hi.I)) 0)
    (hE : (extensionActionMap hi E).1 = 𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing
        i)).flip.obj F).obj hi.I))
    {M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)} (κ : M ≅ E.Z.left) :
    (flatLiftOfIso i t f f' hi ht comm F hstrict hF hcff E hE κ).module' = M := rfl

omit [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [B.J.HasSheafCompose (forget AddCommGrpCat.{wB})] in
/-- The map to `i_*ℱ` of `flatLiftOfIso` is `M ≅ E ⟶ i_*ℱ`. -/
theorem flatLiftOfIso_π
    (E : Abelian.YonedaExtension ((structureRestrict i).obj F)
      ((structureRestrict i).obj (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj
          F).obj hi.I)) 0)
    (hE : (extensionActionMap hi E).1 = 𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing
        i)).flip.obj F).obj hi.I))
    {M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)} (κ : M ≅ E.Z.left) :
    (flatLiftOfIso i t f f' hi ht comm F hstrict hF hcff E hE κ).π = κ.hom ≫ E.g := rfl

omit [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [B.J.HasSheafCompose (forget AddCommGrpCat.{wB})] in
/-- **The class attached to `flatLiftOfIso` is the class of the extension**: the middle terms are
isomorphic over `ℱ`, and both action maps are the identity. -/
theorem fixedActionExtensionClass_flatLiftOfIso
    [HasExt.{e} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
    (E : Abelian.YonedaExtension ((structureRestrict i).obj F)
      ((structureRestrict i).obj (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj
          F).obj hi.I)) 0)
    (hE : (extensionActionMap hi E).1 = 𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing
        i)).flip.obj F).obj hi.I))
    {M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)} (κ : M ≅ E.Z.left) :
    ((flatLiftOfIso i t f f' hi ht comm F hstrict hF hcff E hE κ).fixedActionExtensionClass
        i t f f' hi ht comm F hstrict hF).1 =
      extensionClass F (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj
          hi.I) E := by
  have h := (extensionActionMap_yonedaExtensionOfIso i hi F E κ).trans hE
  exact (fixedActionExtensionClass_flatLiftOfFixedActionIdentity i t f f' hi ht comm F hstrict hF
    hcff (yonedaExtensionOfIso E κ) h).trans
    ((extensionClass_eq_iff_exists_iso_of_fixedActionIdentity i hi F _ E h hE).2 ⟨κ, rfl⟩)

end FlatLiftOfIso

namespace FlatThickeningComplexSituation

variable {i : RingedToposHom X Y} {t : RingedToposHom B B'} (D : FlatThickeningComplexSituation i t)

omit [HasSheafify Y.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] in
/-- The strictness of the first column, in the form of Stacks 08MQ's hypotheses. -/
theorem isStrictPullbackIdealMap₁ :
    IsStrictPullbackIdealMap i t D.f D.f₁ D.upper.lower.first D.lower.lower.first D.restrict₁ :=
  (isStrictPullbackIdealMap_iff_isStrict _ _ _ _ _ _ _).mpr D.strict₁

/-- `ℱ` is flat over `O_ℬ` in the reduced presentation of the first column. -/
theorem isFlat_reducedBaseModule₁ :
    AlgebraicGeometry.SheafOfModules.IsFlat
      (reducedBaseModule i t D.f D.f₁ D.restrict₁ D.F) :=
  isFlat_reducedBaseModule_of_isFlatOverBase i t D.f D.f₁ D.upper.lower.first D.lower.lower.first
    D.restrict₁ D.F D.isFlatOverBase

/-- The first factor `f^*𝒥₁ ⊗_O ℱ ⟶ I₁ ⊗_O ℱ` of Stacks 08MQ is invertible for the first
column. -/
theorem isIso_canonicalFirstFactor₁ :
    IsIso (canonicalFirstFactor i t D.f D.f₁ D.upper.lower.first D.lower.lower.first D.restrict₁
      D.F) :=
  isIso_canonicalFirstFactor_of_isFlat i t D.f D.f₁ D.upper.lower.first D.lower.lower.first
    D.restrict₁ D.F D.flat₁ D.strict₁

/-- The identification `h^*ℱ'₂ ≅ P` of `h^*ℱ'₂` with the descended pushout. -/
noncomputable def pulledModuleIso : D.pulledModule ≅ D.pushoutDescent.Z.left :=
  asIso D.pulledToPushoutDescent

/-- **`h^*ℱ'₂` as a flat lift of `ℱ` across the first column**: the `O'₁`-module `h^*ℱ'₂`, flat
over `O_{ℬ'₁}`, with its identification `i₁^*h^*ℱ'₂ = i₂^*ℱ'₂ = ℱ` (`pulledLift_π`). Flatness
and the short exactness of `0 ⟶ I₁·h^*ℱ'₂ ⟶ h^*ℱ'₂ ⟶ i₁_*ℱ ⟶ 0` come from Stacks 08MQ: through
the identification of `h^*ℱ'₂` with the descended pushout, an extension of `ℱ` by `I₁ ⊗ ℱ` with
action map the identity. -/
noncomputable def pulledLift : FlatLift i D.f₁ D.upper.lower.first D.F :=
  flatLiftOfIso i t D.f D.f₁ D.upper.lower.first D.lower.lower.first D.restrict₁ D.F
    D.isStrictPullbackIdealMap₁ D.isFlat_reducedBaseModule₁ D.isIso_canonicalFirstFactor₁
    D.pushoutDescent D.pushoutDescent_actionMap D.pulledModuleIso

/-- The module of `pulledLift` is `h^*ℱ'₂`. -/
theorem pulledLift_module' : D.pulledLift.module' = D.pulledModule := rfl

/-- **The map `h^*ℱ'₂ ⟶ i₁_*ℱ` of `pulledLift` is the canonical one**: the transpose under
`h^* ⊣ h_*` of the reduction `ℱ'₂ ⟶ i₂_*i₂^*ℱ'₂ = i₂_*ℱ = h_*i₁_*ℱ` of `ℱ'₂`, the unit of
`i₂^* ⊣ i₂_*`. -/
theorem pulledLift_π :
    D.pulledLift.π = (D.adjH.homEquiv _ _).symm
      (D.i₂.pullbackAdjPushforwardModulesViaComparison.unit.app D.F' ≫
        (D.upper.lower.restrictHIso D.F).inv) := by
  refine (flatLiftOfIso_π i t D.f D.f₁ D.upper.lower.first D.lower.lower.first D.restrict₁ D.F
    D.isStrictPullbackIdealMap₁ D.isFlat_reducedBaseModule₁ D.isIso_canonicalFirstFactor₁
    D.pushoutDescent D.pushoutDescent_actionMap D.pulledModuleIso).trans ?_
  refine (D.adjH.homEquiv_naturality_right_symm _ _).symm.trans ?_
  exact congrArg (D.adjH.homEquiv _ _).symm D.pushoutInclusion_comp_g

/-- The class attached to `pulledLift` is the class of the descended pushout. -/
theorem fixedActionExtensionClass_pulledLift
    [HasExt.{e} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))] :
    (D.pulledLift.fixedActionExtensionClass i t D.f D.f₁
        D.upper.lower.first D.lower.lower.first D.restrict₁ D.F D.isStrictPullbackIdealMap₁
        D.isFlat_reducedBaseModule₁).1 =
      extensionClass D.F (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).obj
          D.upper.lower.first.I) D.pushoutDescent :=
  fixedActionExtensionClass_flatLiftOfIso i t D.f D.f₁ D.upper.lower.first D.lower.lower.first
    D.restrict₁ D.F D.isStrictPullbackIdealMap₁ D.isFlat_reducedBaseModule₁
    D.isIso_canonicalFirstFactor₁ D.pushoutDescent D.pushoutDescent_actionMap D.pulledModuleIso

end FlatThickeningComplexSituation

end Deformation.ToposThickening

end
