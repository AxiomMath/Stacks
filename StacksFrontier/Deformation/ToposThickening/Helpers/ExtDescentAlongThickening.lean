module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardEssentialSurjectivity
public import StacksFrontier.Deformation.ToposThickening.FlatPushforwardEquivalence
public import StacksFrontier.Deformation.ToposThickening.ModulesOnThickening.ClosedImmersion
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardTensorRowComplex
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective

/-!
# Descent of modules and their Ext groups along a first order thickening

Let `i : (Sh(C), O) ⟶ (Sh(D), O')` be a first order thickening of ringed topoi. Its underlying
morphism of topoi is an equivalence, so the direct image `i_* : Mod(O) ⥤ Mod(i_*O)` is an
equivalence of categories. This is how the deformation theory of modules over thickenings of
ringed topoi, which is developed on the thickened topos with modules over `i_*O` (Remark Stacks
08MM, Stacks 08VW), is read back on the reduced topos.

## Main results

* `Deformation.ToposThickening.isEquivalence_pushforwardModuleFunctor_of_firstOrderThickening`:
  `i_*` is an equivalence of categories of modules.
* `Deformation.ToposThickening.pushforwardModuleTensorIso`: `i_*J ⊗_{i_*O} i_*F ≅ i_*(J ⊗_O F)`,
  natural in `J` (`Deformation.ToposThickening.pushforwardModuleTensorIso_hom_naturality`).
* `Deformation.ToposThickening.extDescentAddEquiv`:
  `Ext^n_O(F, J ⊗ F) ≃ Ext^n_{i_*O}(i_*F, i_*J ⊗ i_*F)`, natural in `J`
  (`Deformation.ToposThickening.extDescentAddEquiv_comp_mk₀`).

## References

* [Stacks Project, Tag 08MM](https://stacks.math.columbia.edu/tag/08MM)
* [Stacks Project, Tag 08M3](https://stacks.math.columbia.edu/tag/08M3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardModuleFunctor)

universe v u v' u' w w' w''

namespace Deformation.ToposThickening

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w})]

/-- **The direct image of modules along a first order thickening is an equivalence.** The
underlying morphism of topoi of a first order thickening `i` is an equivalence, hence a closed
immersion of topoi (`Deformation.ToposThickening.FirstOrderThickening.isClosedImmersion`), so
`i_* : Mod(O) ⥤ Mod(i_*O)` is fully faithful and essentially surjective
(`Stacks.Sheaves.PushforwardEssentialImage.essSurj_pushforwardModuleFunctor`). -/
theorem isEquivalence_pushforwardModuleFunctor_of_firstOrderThickening
    [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
    [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
    {i : RingedToposHom X Y} (hi : FirstOrderThickening i) :
    (pushforwardModuleFunctor i.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).IsEquivalence := by
  have : i.toToposHom.pushforward.IsEquivalence := hi.equiv
  have : (pushforwardModuleFunctor i.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).EssSurj :=
    ⟨fun M => Stacks.Sheaves.PushforwardEssentialImage.essSurj_pushforwardModuleFunctor
      i.toToposHom _ hi.isClosedImmersion M⟩
  exact { }

section Tensor

variable [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [HasWeakSheafify Y.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {i : RingedToposHom X Y} (hi : FirstOrderThickening i)

/-- The morphism `(Sh(C), O) ⟶ (Sh(D), i_*O)` with identity structure map, in the form of the
modules development. -/
noncomputable abbrev pushforwardModulesHom (i : RingedToposHom X Y) :=
  (pushforwardRingToposHom i X.O).toModulesHom

/-- The direct image of modules of `pushforwardModulesHom` is `i_*`. -/
noncomputable def pushforwardModulesHomIso (i : RingedToposHom X Y) :
    Stacks.Sheaves.RingedToposModules.pushforwardModules (pushforwardModulesHom i) ≅
      pushforwardModuleFunctor i.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  (pushforwardRingToposHom i X.O).toModulesPushforwardIso

omit [HasWeakSheafify X.J AddCommGrpCat] [HasWeakSheafify Y.J AddCommGrpCat]
  [X.J.WEqualsLocallyBijective AddCommGrpCat] [Y.J.WEqualsLocallyBijective AddCommGrpCat] in
include hi in
/-- For a first order thickening `i`, the direct image of modules along `pushforwardModulesHom i`
is an equivalence of categories. -/
theorem isEquivalence_pushforwardModules_pushforwardModulesHom :
    (Stacks.Sheaves.RingedToposModules.pushforwardModules
      (pushforwardModulesHom i)).IsEquivalence := by
  have h := isEquivalence_pushforwardModuleFunctor_of_firstOrderThickening hi
  exact Functor.isEquivalence_of_iso (F := pushforwardModuleFunctor i.toToposHom
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (pushforwardModulesHomIso i).symm

/-- The pullback along `pushforwardModulesHom` of the direct image is the identity, as a natural
isomorphism. -/
noncomputable def pullbackPushforwardModuleNatIso :
    pushforwardModuleFunctor i.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
        (pushforwardModulesHom i).pullbackModules ≅ 𝟭 _ :=
  haveI := isEquivalence_pushforwardModules_pushforwardModulesHom hi
  Functor.isoWhiskerRight (pushforwardModulesHomIso i).symm
      (pushforwardModulesHom i).pullbackModules ≪≫
    asIso (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
      (pushforwardModulesHom i)).counit

/-- **`i_*J ⊗_{i_*O} i_*F ≅ i_*(J ⊗_O F)`, naturally in `J`**, for a first order thickening `i`:
the projection formula of `(Sh(C), O) ⟶ (Sh(D), i_*O)`, an equivalence. -/
noncomputable def pushforwardModuleTensorNatIso
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    pushforwardModuleFunctor i.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
        (Stacks.SheafOfModules.Tensor.sheafTensor
            ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).flip.obj
          ((pushforwardModuleFunctor i.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj F) ≅
      (Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj F ⋙
        pushforwardModuleFunctor i.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  haveI := isEquivalence_pushforwardModules_pushforwardModulesHom hi
  haveI := (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
    (pushforwardModulesHom i)).isEquivalence_left_of_isEquivalence_right
  Functor.isoWhiskerLeft _ ((Stacks.SheafOfModules.Tensor.sheafTensor
      ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).flip.mapIso
        ((pushforwardModulesHomIso i).app F).symm) ≪≫
    Functor.isoWhiskerLeft _
      (Stacks.SheafOfModules.pushforwardTensorNatIso (pushforwardModulesHom i) F
        (fun G => Stacks.SheafOfModules.isIso_pushforwardTensorMap (pushforwardModulesHom i) G F
          inferInstance inferInstance)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (pullbackPushforwardModuleNatIso hi)
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj F ⋙
        Stacks.Sheaves.RingedToposModules.pushforwardModules (pushforwardModulesHom i)) ≪≫
    Functor.leftUnitor _ ≪≫
    Functor.isoWhiskerLeft _ (pushforwardModulesHomIso i)

/-- **`i_*J ⊗_{i_*O} i_*F ≅ i_*(J ⊗_O F)`** for a first order thickening `i`. -/
noncomputable abbrev pushforwardModuleTensorIso
    (F J : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor
          ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).flip.obj
        ((pushforwardModuleFunctor i.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj F)).obj
        ((pushforwardModuleFunctor i.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj J) ≅
      (pushforwardModuleFunctor i.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj F).obj J) :=
  (pushforwardModuleTensorNatIso hi F).app J

/-- The identification `i_*J ⊗ i_*F ≅ i_*(J ⊗ F)` is natural in `J`. -/
theorem pushforwardModuleTensorIso_hom_naturality
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    {J J' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (k : J ⟶ J') :
    ((Stacks.SheafOfModules.Tensor.sheafTensor
          ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).flip.obj
        ((pushforwardModuleFunctor i.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj F)).map
        ((pushforwardModuleFunctor i.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map k) ≫
      (pushforwardModuleTensorIso hi F J').hom =
    (pushforwardModuleTensorIso hi F J).hom ≫
      (pushforwardModuleFunctor i.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj F).map k) :=
  (pushforwardModuleTensorNatIso hi F).hom.naturality k

end Tensor

section Ext

attribute [local instance 5000] SheafOfModules.instAbelian

variable [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [HasWeakSheafify Y.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {i : RingedToposHom X Y} (hi : FirstOrderThickening i)

/-- The direct image of modules along `i`, with target the modules over `i_*O` as they occur in
the deformation theory of thickenings. -/
noncomputable abbrev thickenedModulesFunctor (i : RingedToposHom X Y) :
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O)) :=
  pushforwardModuleFunctor i.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)

omit [HasWeakSheafify X.J AddCommGrpCat] [HasWeakSheafify Y.J AddCommGrpCat]
  [X.J.WEqualsLocallyBijective AddCommGrpCat] [Y.J.WEqualsLocallyBijective AddCommGrpCat] in
include hi in
/-- For a first order thickening `i`, `thickenedModulesFunctor i` is an equivalence of
categories. -/
theorem isEquivalence_thickenedModulesFunctor : (thickenedModulesFunctor i).IsEquivalence :=
  isEquivalence_pushforwardModuleFunctor_of_firstOrderThickening hi

variable [HasExt.{w'} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [HasExt.{w''} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf
    ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))]
  [EnoughInjectives (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

/-- Composition with `Ext.mk₀` of an isomorphism, as an additive equivalence. -/
noncomputable def extCompIsoAddEquiv {C : Type*} [Category C] [Abelian C] [HasExt.{w'} C]
    {A B B' : C} (e : B ≅ B') (n : ℕ) : Abelian.Ext.{w'} A B n ≃+ Abelian.Ext.{w'} A B' n where
  toFun α := α.comp (Abelian.Ext.mk₀ e.hom) (add_zero n)
  invFun β := β.comp (Abelian.Ext.mk₀ e.inv) (add_zero n)
  left_inv α := by
    simp only [Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀, Iso.hom_inv_id,
      Abelian.Ext.comp_mk₀_id]
  right_inv β := by
    simp only [Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀, Iso.inv_hom_id,
      Abelian.Ext.comp_mk₀_id]
  map_add' α β := by simp only [Abelian.Ext.add_comp]

/-- **`Ext^n_O(F, J ⊗ F) ≃ Ext^n_{i_*O}(i_*F, i_*J ⊗ i_*F)`** for a first order thickening `i`:
the direct image of modules is an exact equivalence, and it carries `J ⊗ F` to `i_*J ⊗ i_*F`. -/
noncomputable def extDescentAddEquiv
    (F J : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (n : ℕ) :
    Abelian.Ext.{w'} F (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj F).obj J) n ≃+
      Abelian.Ext.{w''} ((thickenedModulesFunctor i).obj F)
        (((Stacks.SheafOfModules.Tensor.sheafTensor
          ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).flip.obj
            ((thickenedModulesFunctor i).obj F)).obj ((thickenedModulesFunctor i).obj J)) n :=
  haveI := isEquivalence_thickenedModulesFunctor hi
  haveI : (thickenedModulesFunctor i).Additive := Functor.additive_of_preserves_binary_products _
  (AddEquiv.ofBijective _
      (CategoryTheory.Functor.mapExt_bijective_of_preservesInjectiveObjects
        (thickenedModulesFunctor i) F
        (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj F).obj J) n)).trans
    (extCompIsoAddEquiv (pushforwardModuleTensorIso hi F J).symm n)

/-- `extDescentAddEquiv` sends `α` to its image under the direct image `i_*`, composed with the
inverse of `i_*J ⊗ i_*F ≅ i_*(J ⊗ F)`. -/
theorem extDescentAddEquiv_apply
    (F J : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (n : ℕ)
    (α : Abelian.Ext.{w'} F
      (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj F).obj J) n) :
    extDescentAddEquiv hi F J n α = haveI := isEquivalence_thickenedModulesFunctor hi
      haveI : (thickenedModulesFunctor i).Additive :=
        Functor.additive_of_preserves_binary_products _
      (α.mapExactFunctor (thickenedModulesFunctor i)).comp
        (Abelian.Ext.mk₀ (pushforwardModuleTensorIso hi F J).inv) (add_zero n) := rfl

/-- **The descent of `Ext` is natural in `J`.** -/
theorem extDescentAddEquiv_comp_mk₀
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    {J J' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (k : J ⟶ J') (n : ℕ)
    (α : Abelian.Ext.{w'} F
      (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj F).obj J) n) :
    extDescentAddEquiv hi F J' n
        (α.comp
          (Abelian.Ext.mk₀ (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj F).map k))
          (add_zero n)) =
      (extDescentAddEquiv hi F J n α).comp (Abelian.Ext.mk₀
        (((Stacks.SheafOfModules.Tensor.sheafTensor
          ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).flip.obj
            ((thickenedModulesFunctor i).obj F)).map ((thickenedModulesFunctor i).map k)))
        (add_zero n) := by
  have := isEquivalence_thickenedModulesFunctor hi
  have : (thickenedModulesFunctor i).Additive := Functor.additive_of_preserves_binary_products _
  rw [extDescentAddEquiv_apply, extDescentAddEquiv_apply, Abelian.Ext.mapExactFunctor_comp,
    Abelian.Ext.mapExactFunctor_mk₀, Abelian.Ext.comp_assoc_of_third_deg_zero,
    Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀, Abelian.Ext.mk₀_comp_mk₀]
  congr 2
  refine (Iso.comp_inv_eq _).mpr ?_
  exact ((Iso.inv_comp_eq _).mpr (pushforwardModuleTensorIso_hom_naturality hi F k)).symm.trans
    (Category.assoc _ _ _).symm

end Ext

end Deformation.ToposThickening

end
