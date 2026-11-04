module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackToposRightUnitorTransport
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorRightUnitor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposUnitStructureMap
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalSheafTensorUnitors
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPushforwardIsoSections

/-! # The right-unitor coherence of Stacks 03EL, unconditionally

Let `f : (Sh(C), 𝒪_C) ⟶ (Sh(D), 𝒪_D)` be a morphism of ringed topoi presented by a functor of the
underlying sites which is a morphism of sites. This file proves the module-level right-unitor
coherence `Stacks.Sheaves.DerivedPullback.fourFieldRightUnitorCoherence` of the comparison of
Stacks 03EL for the site-presented pullback, with no hypothesis beyond the morphism of sites.

The coherence `Stacks.SheafOfModules.pullbackTensorIso_hom_app_comp_rightUnitor` holds for a unit
comparison `ν : f^*𝒪_D ⟶ 𝒪_C` whose composite with the unit of extension of scalars of Stacks 03CZ
is, on local sections, the inverse-image form `f♯ : f⁻¹𝒪_D ⟶ 𝒪_C` of the structure map. The unit
comparison defined here, the adjunct of `f♯` across the adjunction of Stacks 03CZ, satisfies this
by construction, and it agrees with the comparison
`Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso` of Stacks 03LU and with the
comparison `AlgebraicGeometry.RingedToposHom.pullbackUnitStructureMap` of a two-field morphism of
ringed topoi.

## Main definitions

* `Stacks.Sheaves.RingedToposModules.fSharpModulesHom`: the inverse-image form
  `f♯ : f⁻¹𝒪_D ⟶ 𝒪_C` of the structure map, read as a morphism of `f⁻¹𝒪_D`-modules out of the
  inverse image of `𝒪_D`.
* `Stacks.Sheaves.RingedToposModules.pullbackModulesUnitComparison`: the unit comparison
  `ν : f^*𝒪_D ⟶ 𝒪_C`, the adjunct of `f♯` across the adjunction of Stacks 03CZ.

## Main results

* `Stacks.Sheaves.RingedToposModules.pullbackModulesUnitComparison_val_app_extendUnit`: the unit
  comparison carries the image of a local section `s` of `f⁻¹𝒪_D` under the unit of extension of
  scalars to `f♯(s)`.
* `Stacks.Sheaves.RingedToposModules.pullbackTensorIso_hom_app_comp_rightUnitor_unitComparison`:
  the four-field right-unitor coherence of Stacks 03EL at `pullbackModulesUnitComparison`.
* `moduleSheafFunctor_map_homEquiv_pullbackModulesUnitComparison`: the adjunct of the unit
  comparison across the adjunction of Stacks 03D7 is the direct-image form `f♯ : 𝒪_D ⟶ f_*𝒪_C` of
  the structure map, on underlying sheaves of sets.
* `Stacks.Sheaves.RingedToposModules.pullbackModulesUnitComparison_eq_inv`: the unit comparison is
  the inverse of the comparison of Stacks 03LU, for an arbitrary morphism of ringed topoi.
* `Stacks.Sheaves.DerivedPullback.pullbackModulesUnitComparison_eq`: the same for a morphism
  presented by a morphism of sites.
* `AlgebraicGeometry.RingedToposHom.pullbackUnitStructureMap_eq`: the comparison
  `AlgebraicGeometry.RingedToposHom.pullbackUnitStructureMap` of a two-field morphism of ringed
  topoi of Stacks 01D3 is the unit comparison.
* `AlgebraicGeometry.RingedToposHom.pullbackUnitStructureMap_val_app_extendUnit`: the Stacks 03CZ
  formula on local sections, for that two-field comparison.
* `Stacks.Sheaves.DerivedPullback.fourFieldRightUnitorCoherence`: the four-field right-unitor
  coherence of Stacks 03EL, with the comparison of Stacks 03LU and with
  `Stacks.SheafOfModules.sheafTensorUnitNatIso` as the unitor.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf AlgebraicGeometry
open Stacks.Sheaves.RingedToposModules Stacks.Sheaves.ToposPullback
open Stacks.Sheaves.ToposPushforward Stacks.PresheafOfModules.ChangeOfRings
open Stacks.SheafOfModules.ChangeOfRings

namespace Stacks.Sheaves.RingedToposModules

/-! ## Morphisms of sheaves of modules on local sections -/

section Bookkeeping

universe t uu vv

variable {C : Type uu} [Category.{vv} C] {J : GrothendieckTopology C}
  {R R' : Sheaf J RingCat.{t}}

/-- A composite of morphisms of sheaves of modules, read on a local section. -/
private lemma comp_val_app {A B D : SheafOfModules.{t} R} (a : A ⟶ B) (b : B ⟶ D) (V : Cᵒᵖ)
    (x : A.val.obj V) :
    PresheafOfModules.Hom.app (a ≫ b).val V x =
      PresheafOfModules.Hom.app b.val V (PresheafOfModules.Hom.app a.val V x) := rfl

/-- An equality of morphisms of sheaves of modules, read on a local section. -/
private lemma val_app_congr {A B : SheafOfModules.{t} R} {a b : A ⟶ B} (h : a = b) (V : Cᵒᵖ)
    (x : A.val.obj V) :
    PresheafOfModules.Hom.app a.val V x = PresheafOfModules.Hom.app b.val V x := by
  rw [h]

/-- The adjunct of a morphism across extension of scalars, read on a local section. -/
private lemma restrict_comp_val_app (α : R ⟶ R')
    {A : SheafOfModules.{t} R} {B D : SheafOfModules.{t} R'}
    (a : A ⟶ (SheafOfModules.restrictScalars α).obj B) (b : B ⟶ D) (V : Cᵒᵖ)
    (x : A.val.obj V) :
    PresheafOfModules.Hom.app (a ≫ (SheafOfModules.restrictScalars α).map b).val V x =
      PresheafOfModules.Hom.app b.val V (PresheafOfModules.Hom.app a.val V x) := rfl

end Bookkeeping

section AbstractAdjunction

universe v₁ u₁ v₂ u₂ v₃ u₃

/-- The hom-set bijection of a composite of adjunctions, at one morphism. -/
private lemma comp_homEquiv_apply {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂}
    [Category.{v₂} C₂] {C₃ : Type u₃} [Category.{v₃} C₃]
    {F : C₁ ⥤ C₂} {G : C₂ ⥤ C₁} {H : C₂ ⥤ C₃} {I : C₃ ⥤ C₂}
    (adj₁ : F ⊣ G) (adj₂ : H ⊣ I) (A : C₁) (B : C₃) (k : (F ⋙ H).obj A ⟶ B) :
    (adj₁.comp adj₂).homEquiv A B k =
      adj₁.homEquiv A (I.obj B) (adj₂.homEquiv (F.obj A) B k) := by
  rw [Adjunction.comp_homEquiv]
  rfl

end AbstractAdjunction

/-! ## The unit comparison of a morphism of ringed topoi -/

universe w w' v u v' u'

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (g : RingedToposHom X Y)

/-- The inverse image of the structure sheaf of the target, read as a module over the
inverse-image sheaf of rings. This is `SheafOfModules.unit` of that sheaf of rings on the nose
(`Stacks.Sheaves.FinitePresentation.inverseImageModulesUnitIso` is `Iso.refl`). -/
abbrev inverseImageStructureUnit : SheafOfModules.{w}
    (inverseImageRingSheaf g.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :=
  (inverseImageModules g.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))

/-- Extension of scalars along the inverse-image form of the structure map is left adjoint to
restriction of scalars: the adjunction of Stacks 03CZ, at `f♯`. -/
abbrev extendRestrictScalarsFSharpAdjunction :
    extendScalarsFSharp g ⊣ SheafOfModules.restrictScalars g.fSharpInverseImage :=
  g.extendRestrictScalarsFSharpAdjunction

/-- **The inverse-image form `f⁻¹O_D ⟶ O_C` of the structure map, read as a morphism of
`f⁻¹O_D`-modules** out of the inverse image of `O_D` and into the restriction of scalars of
`O_C`. This is `Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit` with its source
written as `inverseImageStructureUnit`. -/
def fSharpModulesHom : inverseImageStructureUnit g ⟶
    (SheafOfModules.restrictScalars g.fSharpInverseImage).obj
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  unitToRestrictScalarsUnit g.fSharpInverseImage

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- `Stacks.Sheaves.RingedToposModules.fSharpModulesHom` is `f♯` on local sections. -/
theorem fSharpModulesHom_val_app (V : X.Cᵒᵖ)
    (s : (inverseImageStructureUnit g).val.obj V) :
    (fSharpModulesHom g).val.app V s = g.fSharpInverseImage.hom.app V s :=
  Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit_val_app
    g.fSharpInverseImage V s

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- The underlying morphism of sheaves of sets of
`Stacks.Sheaves.RingedToposModules.fSharpModulesHom` is `f♯`. -/
theorem moduleSheafFunctor_map_fSharpModulesHom :
    (Sheaf.moduleSheafFunctor
          (inverseImageRingSheaf g.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map (fSharpModulesHom g) =
      (sheafCompose X.J (forget RingCat.{w})).map g.fSharpInverseImage :=
  Stacks.SheafOfModules.ChangeOfRings.moduleSheafFunctor_map_unitToRestrictScalarsUnit
    g.fSharpInverseImage

/-- **The unit comparison `ν : f^*O_D ⟶ O_C` of a morphism of ringed topoi**: the adjunct, across
the adjunction of Stacks 03CZ, of the inverse-image form of the structure map read as a morphism
of `f⁻¹O_D`-modules. -/
def pullbackModulesUnitComparison :
    (g.pullbackModules).obj (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  ((extendRestrictScalarsFSharpAdjunction g).homEquiv (inverseImageStructureUnit g)
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).symm (fSharpModulesHom g)

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- The adjunct of the unit comparison across the adjunction of Stacks 03CZ is `f♯`. -/
theorem homEquiv_pullbackModulesUnitComparison :
    (extendRestrictScalarsFSharpAdjunction g).homEquiv (inverseImageStructureUnit g)
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (pullbackModulesUnitComparison g) =
      fSharpModulesHom g :=
  ((extendRestrictScalarsFSharpAdjunction g).homEquiv (inverseImageStructureUnit g)
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).apply_symm_apply _

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- **The unit comparison on local sections**: it carries the image of a local section `s` of
`f⁻¹O_D` under the unit of extension of scalars of Stacks 03CZ to `f♯(s)`. -/
theorem pullbackModulesUnitComparison_val_app_extendUnit (V : X.Cᵒᵖ)
    (s : (inverseImageStructureUnit g).val.obj V) :
    (pullbackModulesUnitComparison g).val.app V
        (((extendRestrictScalarsAdjunction X.J (fSharpCommRing g)
            (inverseImageRingSheaf g.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).unit.app
          ((inverseImageModules g.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))).val.app V s) =
      g.fSharpInverseImage.hom.app V s := by
  have h : ((extendRestrictScalarsFSharpAdjunction g).unit.app
          (inverseImageStructureUnit g) ≫
        (SheafOfModules.restrictScalars g.fSharpInverseImage).map
          (pullbackModulesUnitComparison g)) =
      fSharpModulesHom g :=
    (Adjunction.homEquiv_unit (extendRestrictScalarsFSharpAdjunction g)
      (inverseImageStructureUnit g)
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (pullbackModulesUnitComparison g)).symm.trans
      (homEquiv_pullbackModulesUnitComparison g)
  refine Eq.trans ?_ (fSharpModulesHom_val_app g V s)
  refine Eq.trans ?_
    (congrArg (fun m ↦ PresheafOfModules.Hom.app (SheafOfModules.Hom.val m) V s) h)
  exact (restrict_comp_val_app g.fSharpInverseImage
    ((extendRestrictScalarsFSharpAdjunction g).unit.app (inverseImageStructureUnit g))
    (pullbackModulesUnitComparison g) V s).symm

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- **The adjunct of the unit comparison across the adjunction of Stacks 03D7 is the
direct-image form `f♯ : O_D ⟶ f_*O_C` of the structure map**, on underlying sheaves of sets. -/
theorem moduleSheafFunctor_map_homEquiv_pullbackModulesUnitComparison :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        ((pullbackAdjPushforwardModules g).homEquiv
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (pullbackModulesUnitComparison g)) =
      (sheafCompose Y.J (forget RingCat.{w'})).map g.fSharp := by
  have h1 : (pullbackAdjPushforwardModules g).homEquiv
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (pullbackModulesUnitComparison g) =
      (inverseImageAdjDirectImageModules g.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).homEquiv
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        ((SheafOfModules.restrictScalars g.fSharpInverseImage).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
        (fSharpModulesHom g) :=
    (comp_homEquiv_apply
        (inverseImageAdjDirectImageModules g.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (extendRestrictScalarsFSharpAdjunction g)
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (pullbackModulesUnitComparison g)).trans
      (congrArg ((inverseImageAdjDirectImageModules g.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).homEquiv
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          ((SheafOfModules.restrictScalars g.fSharpInverseImage).obj
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
        (homEquiv_pullbackModulesUnitComparison g))
  refine Eq.trans
    (congrArg (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map h1) ?_
  refine Eq.trans
    (congrArg (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
    (Adjunction.homEquiv_unit
      (inverseImageAdjDirectImageModules g.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      ((SheafOfModules.restrictScalars g.fSharpInverseImage).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
      (fSharpModulesHom g))) ?_
  refine Eq.trans ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map_comp
    ((inverseImageAdjDirectImageModules g.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).unit.app
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    ((directImageModules g.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
      (fSharpModulesHom g))) ?_
  refine Eq.trans (congrArg (fun m ↦ m ≫
      (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        ((directImageModules g.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
          (fSharpModulesHom g)))
    (moduleSheafFunctor_map_inverseImageAdjDirectImageModules_unit_app' g.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))) ?_
  refine Eq.trans (congrArg (fun m ↦ g.toToposHom.adj.unit.app
      (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ≫ m)
    (moduleSheafFunctor_map_directImageModules_map g.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) (fSharpModulesHom g))) ?_
  refine Eq.trans (congrArg (fun m ↦ g.toToposHom.adj.unit.app
      (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ≫
        g.toToposHom.pushforward.map m)
    (moduleSheafFunctor_map_fSharpModulesHom g)) ?_
  refine Eq.trans (congrArg (fun m ↦ m ≫ g.toToposHom.pushforward.map
      ((sheafCompose X.J (forget RingCat.{w})).map g.fSharpInverseImage))
    (ringSheafMap_ringUnit g.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).symm) ?_
  exact (fSharp_underlying g).symm

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- `moduleSheafFunctor_map_homEquiv_pullbackModulesUnitComparison` read on a local section. -/
theorem homEquiv_pullbackModulesUnitComparison_val_app (W : Y.Cᵒᵖ)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj W) :
    ((pullbackAdjPushforwardModules g).homEquiv
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (pullbackModulesUnitComparison g)).val.app W r =
      g.fSharp.hom.app W r :=
  congrArg (fun m ↦ (Sheaf.sectionsFunctor Y.J W).map m r)
    (moduleSheafFunctor_map_homEquiv_pullbackModulesUnitComparison g)

/-- **The right-unitor coherence of Stacks 03EL for an arbitrary morphism of ringed topoi, at the
unit comparison `pullbackModulesUnitComparison`.** -/
theorem pullbackTensorIso_hom_app_comp_rightUnitor_unitComparison
    (A : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    (Stacks.SheafOfModules.pullbackTensorIso g).hom.app
          (A, SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj ((g.pullbackModules).obj A)).map
            (pullbackModulesUnitComparison g) ≫
          (Stacks.SheafOfModules.tensorSheafUnitRightIso X.O.obj
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property ((g.pullbackModules).obj A)).hom =
      (g.pullbackModules).map
        (Stacks.SheafOfModules.tensorSheafUnitRightIso Y.O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property A).hom := by
  have h := Stacks.SheafOfModules.pullbackTensorIso_hom_app_comp_rightUnitor g A
    (pullbackModulesUnitComparison g) (pullbackModulesUnitComparison_val_app_extendUnit g)
  dsimp only [Functor.uncurry_obj_map, Functor.prod_obj] at h
  rw [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp] at h
  exact h

/-! ## The two unit comparisons agree, for an arbitrary morphism of ringed topoi -/

section UnitComparisonEq

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (g : RingedToposHom X Y)

omit [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The direct image of the unit section of `O_C` is the unit section of `f_*O_C`.** The
constant-`1` global section of `O_C`, pushed forward and evaluated on the image of the unique
section of the terminal sheaf under `MorphismOfTopoi.pushforwardTerminalSection`, is
`f♯(1) = 1`. -/
theorem pushforward_unitTerminal_val_app_terminalSection (W : Y.Cᵒᵖ) :
    (g.toToposHom.pushforward.map
          (unitTerminalHomEquiv (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (𝟙 _))).hom.app W
        ((MorphismOfTopoi.pushforwardTerminalSection g.toToposHom).hom.app W
          (terminalSheafSection Y.J W)) =
      g.fSharp.hom.app W (1 : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj W) := by
  have h : (MorphismOfTopoi.pushforwardTerminalSection g.toToposHom).hom.app W
        (terminalSheafSection Y.J W) =
      (default : (g.toToposHom.pushforward ⋙ Sheaf.sectionsFunctor Y.J W).obj
        (⊤_ (Sheaf X.J (Type u)))) :=
    Subsingleton.elim (α := (g.toToposHom.pushforward ⋙ Sheaf.sectionsFunctor Y.J W).obj
      (⊤_ (Sheaf X.J (Type u)))) _ _
  rw [map_one]
  exact congrArg ((g.toToposHom.pushforward ⋙ Sheaf.sectionsFunctor Y.J W).map
      (unitTerminalHomEquiv (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (𝟙 _))) h

omit [HasWeakSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The unit comparison of Stacks 03CZ is the comparison of Stacks 03LU, for an arbitrary
morphism of ringed topoi:** `pullbackModulesUnitComparison` is the inverse of
`pullbackModulesObjUnitIso`. -/
theorem pullbackModulesUnitComparison_eq_inv :
    pullbackModulesUnitComparison g = (pullbackModulesObjUnitIso g).inv := by
  refine ((pullbackAdjPushforwardModules g).homEquiv
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).injective ?_
  refine CategoryTheory.Sheaf.unit_hom_ext_val_app_one _ _ (fun W ↦ ?_)
  refine Eq.trans (homEquiv_pullbackModulesUnitComparison_val_app g W
    (1 : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj W)) ?_
  exact Eq.trans (pushforward_unitTerminal_val_app_terminalSection g W).symm
    (pullbackModulesObjUnitIso_inv_adjunct_val_app_one g W).symm

end UnitComparisonEq

end Stacks.Sheaves.RingedToposModules

/-! ## The two-field comparison of Stacks 01D3 is the same morphism

`AlgebraicGeometry.RingedToposHom.pullbackUnitStructureMap`, the comparison `f^*𝒪_D ⟶ 𝒪_C` of a
two-field morphism of ringed topoi of Stacks 01D3, is the transpose across the adjunction of
Stacks 03D7 of the structure map read on unit modules. It is the same morphism as
`pullbackModulesUnitComparison` at `AlgebraicGeometry.RingedToposHom.toModulesHom`. -/

namespace AlgebraicGeometry.RingedToposHom

universe wb wb' vb ub vb' ub'

variable {X : RingedTopos.{vb, ub, wb}} {Y : RingedTopos.{vb', ub', wb'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{wb} RingCat.{wb})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{wb'} RingCat.{wb'})]
  [X.J.HasSheafCompose (forget RingCat.{wb})] [Y.J.HasSheafCompose (forget RingCat.{wb'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{wb})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{wb'})]
  [HasWeakSheafify X.J AddCommGrpCat.{wb}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{wb}]
  [HasWeakSheafify Y.J AddCommGrpCat.{wb'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{wb'}]
  (f : AlgebraicGeometry.RingedToposHom X Y)

omit [HasWeakSheafify Y.J AddCommGrpCat.{wb'}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{wb'}] in
/-- **The two canonical comparisons `f^*𝒪_D ⟶ 𝒪_C` of a morphism of ringed topoi agree:**
`AlgebraicGeometry.RingedToposHom.pullbackUnitStructureMap` is
`Stacks.Sheaves.RingedToposModules.pullbackModulesUnitComparison` at `toModulesHom`. -/
theorem pullbackUnitStructureMap_eq :
    AlgebraicGeometry.RingedToposHom.pullbackUnitStructureMap f =
      Stacks.Sheaves.RingedToposModules.pullbackModulesUnitComparison f.toModulesHom := by
  have h0 : (AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModules f).homEquiv
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (AlgebraicGeometry.RingedToposHom.pullbackUnitStructureMap f) =
      (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules f.toModulesHom).homEquiv
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (AlgebraicGeometry.RingedToposHom.pullbackUnitStructureMap f) ≫
        f.toModulesPushforwardIso.hom.app
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    Adjunction.homEquiv_ofNatIsoRight_apply
      (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules f.toModulesHom)
      f.toModulesPushforwardIso
      (AlgebraicGeometry.RingedToposHom.pullbackUnitStructureMap f)
  have h1 : (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
          f.toModulesHom).homEquiv
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (AlgebraicGeometry.RingedToposHom.pullbackUnitStructureMap f) ≫
        f.toModulesPushforwardIso.hom.app
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) =
      AlgebraicGeometry.RingedToposHom.unitStructureMap f :=
    h0.symm.trans (AlgebraicGeometry.RingedToposHom.homEquiv_pullbackUnitStructureMap f)
  refine ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
    f.toModulesHom).homEquiv (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).injective ?_
  refine hom_ext_moduleSheafFunctor (Sheaf.hom_ext_sections fun W r ↦ ?_)
  refine Eq.trans ?_ (homEquiv_pullbackModulesUnitComparison_val_app f.toModulesHom W r).symm
  refine Eq.trans ?_ (AlgebraicGeometry.RingedToposHom.unitStructureMap_val_app f W r)
  refine Eq.trans ?_ (val_app_congr h1 W r)
  refine Eq.trans ?_ (comp_val_app
    ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules f.toModulesHom).homEquiv
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (AlgebraicGeometry.RingedToposHom.pullbackUnitStructureMap f))
    (f.toModulesPushforwardIso.hom.app
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) W r).symm
  exact (AlgebraicGeometry.RingedToposHom.toModulesPushforwardIso_hom_app_val_app f
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) W _).symm

omit [HasWeakSheafify Y.J AddCommGrpCat.{wb'}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{wb'}] in
/-- **The two-field comparison `f^*𝒪_D ⟶ 𝒪_C` on local sections**: it carries the image of a
local section `s` of `f⁻¹𝒪_D` under the unit of extension of scalars of Stacks 03CZ to `f♯(s)`. -/
theorem pullbackUnitStructureMap_val_app_extendUnit (V : X.Cᵒᵖ)
    (s : (inverseImageStructureUnit f.toModulesHom).val.obj V) :
    (AlgebraicGeometry.RingedToposHom.pullbackUnitStructureMap f).val.app V
        (((extendRestrictScalarsFSharpAdjunction f.toModulesHom).unit.app
          (inverseImageStructureUnit f.toModulesHom)).val.app V s) =
      f.fSharpInverseImageRing.hom.app V s :=
  (val_app_congr (pullbackUnitStructureMap_eq f) V _).trans
    (pullbackModulesUnitComparison_val_app_extendUnit f.toModulesHom V s)

end AlgebraicGeometry.RingedToposHom

/-! ## The coherence, for the site-presented pullback -/

namespace Stacks.Sheaves.DerivedPullback

section Substitute

universe v₄ u₄

end Substitute

section SiteMorphism

universe u

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : RingedToposSiteHom X Y)

/-- The right unitor `sheafTensorUnitNatIso` is `tensorSheafUnitRightIso`. -/
private lemma sheafTensorUnitNatIso_hom_app_eq (R : RingedTopos.{u, u, u})
    (A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R.O)) :
    (Stacks.SheafOfModules.sheafTensorUnitNatIso R.O).hom.app A =
      (Stacks.SheafOfModules.tensorSheafUnitRightIso R.O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf R.O).property A).hom := by
  rw [← _root_.SheafOfModules.rightUnitor_sheafTensor_eq R.O A]
  rfl

omit [HasSheafify X.J AddCommGrpCat.{u}] [HasSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The unit comparison of Stacks 03CZ is the comparison of Stacks 03LU**, for a morphism of
ringed topoi presented by a morphism of sites. -/
theorem pullbackModulesUnitComparison_eq (hmos : f.u.IsMorphismOfSites Y.J X.J) :
    pullbackModulesUnitComparison (modulesHomOfSiteHom f hmos) =
      (pullbackModulesObjUnitIso (modulesHomOfSiteHom f hmos)).inv :=
  pullbackModulesUnitComparison_eq_inv (modulesHomOfSiteHom f hmos)

omit [HasSheafify X.J AddCommGrpCat.{u}] [HasSheafify Y.J AddCommGrpCat.{u}] in
/-- **The four-field right-unitor coherence of Stacks 03EL at the comparison of Stacks 03LU**,
with `Stacks.SheafOfModules.sheafTensorUnitNatIso` as the right unitor. -/
theorem fourFieldRightUnitorCoherence (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    (Stacks.SheafOfModules.pullbackTensorIso (modulesHomOfSiteHom f hmos)).hom.app
          (A, SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
            (((modulesHomOfSiteHom f hmos).pullbackModules).obj A)).map
            (pullbackModulesObjUnitIso (modulesHomOfSiteHom f hmos)).inv ≫
          (Stacks.SheafOfModules.sheafTensorUnitNatIso X.O).hom.app
            (((modulesHomOfSiteHom f hmos).pullbackModules).obj A) =
      ((modulesHomOfSiteHom f hmos).pullbackModules).map
        ((Stacks.SheafOfModules.sheafTensorUnitNatIso Y.O).hom.app A) := by
  rw [sheafTensorUnitNatIso_hom_app_eq, sheafTensorUnitNatIso_hom_app_eq,
    ← pullbackModulesUnitComparison_eq f hmos]
  exact pullbackTensorIso_hom_app_comp_rightUnitor_unitComparison (modulesHomOfSiteHom f hmos) A

end SiteMorphism

end Stacks.Sheaves.DerivedPullback

end
