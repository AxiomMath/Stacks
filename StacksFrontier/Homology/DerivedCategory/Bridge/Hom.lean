module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedInternalHom
public import StacksFrontier.Homology.DerivedCategory.Bridge.Pushforward
public import StacksFrontier.Topology.Sheaves.Cohomology.HomComplexAndStrictPerfection.InternalHomComplexQuasiIso

/-!
# Derived Hom and `Ext` across two models of the derived category

Two choices `H₁ H₂ : HasDerivedCategory C` are compared by the triangulated equivalence
`e = StacksDraft.DerivedModel.modelEquiv H₁ H₂` of
`StacksFrontier/Homology/DerivedCategory/Bridge/Basic.lean`, with
`modelCompQIso H₁ H₂ : Q₁ ⋙ e.functor ≅ Q₂`. This file transports along it the `Ext` groups and
the derived internal Hom.

Morphisms need nothing new: `e.fullyFaithfulFunctor.homEquiv` compares `K ⟶ L` with
`e K ⟶ e L`, and on classes of complexes Mathlib's `Localization.homEquiv` compares
`Q₁ K ⟶ Q₁ L` with `Q₂ K ⟶ Q₂ L`, which `Localization.homEquiv_eq` identifies with conjugation by
`modelCompQIso`. Shifted morphisms are compared by `Stacks.Injectives.shiftedHomMapAddEquiv`.

## Main results

* `StacksDraft.DerivedModel.ext_homEquiv_modelEquiv`: `Ext.homEquiv` at the second model is
  `Ext.homEquiv` at the first one carried across by the comparison.
* `StacksDraft.DerivedModel.bifunctorModelEquivIso`: two bifunctors on the two models,
  contravariant in the first variable and induced by the same bifunctor of complexes, correspond
  under the comparison.
* `AlgebraicGeometry.RingedSite.derivedSheafHomBifunctorModelEquivIso`: the derived internal Hom
  `RSheafHom(-, -)` of a ringed site at two models, with the vanishing and invertibility
  corollaries `isZero_derivedSheafHomBifunctor_modelEquiv_iff`,
  `isIso_derivedSheafHomBifunctor_obj_map_modelEquiv_iff` and
  `isIso_derivedSheafHomBifunctor_map_app_modelEquiv_iff`.
* `AlgebraicGeometry.RingedSite.derivedSheafHomBifunctorStandardIso` and
  `AlgebraicGeometry.Scheme.derivedSheafHomBifunctorStandardIso`: the standard model against the
  locally small one, for sheaves of modules on a ringed site and for `𝒪_X`-modules on a scheme.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite

universe u v w z w'

namespace StacksDraft.DerivedModel

section Ext

variable {C : Type u} [Category.{v} C] [Abelian C]
  (H₁ : HasDerivedCategory.{w} C) (H₂ : HasDerivedCategory.{z} C)

/-- A shifted morphism between the classes of two complexes, shrunk to a small type, is read at
the second model as its reading at the first model carried across by the comparison. -/
theorem smallShiftedHom_equiv_modelEquiv {K L : CochainComplex C ℤ} {m : ℤ}
    [Localization.HasSmallLocalizedShiftedHom.{w'}
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) ℤ K L]
    (β : Localization.SmallShiftedHom.{w'} (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      K L m) :
    Localization.SmallShiftedHom.equiv _ (@DerivedCategory.Q C _ _ H₂) β =
      (ShiftedHom.mk₀ 0 rfl ((modelCompQIso H₁ H₂).inv.app K)).comp
        (((Localization.SmallShiftedHom.equiv _ (@DerivedCategory.Q C _ _ H₁) β).map
          (modelEquiv H₁ H₂).functor).comp
            (ShiftedHom.mk₀ 0 rfl ((modelCompQIso H₁ H₂).hom.app L)) (zero_add _))
        (add_zero _) := by
  let W := HomologicalComplex.quasiIso C (ComplexShape.up ℤ)
  have h : Localization.SmallHom.equiv W (@DerivedCategory.Q C _ _ H₂) β =
      (modelCompQIso H₁ H₂).inv.app _ ≫
        (modelEquiv H₁ H₂).functor.map
          (Localization.SmallHom.equiv W (@DerivedCategory.Q C _ _ H₁) β) ≫
          (modelCompQIso H₁ H₂).hom.app _ := by
    rw [← Localization.homEquiv_eq W _ _ (modelEquiv H₁ H₂).functor (modelCompQIso H₁ H₂)]
    exact (Localization.homEquiv_trans _ _ _ _ _).symm
  rw [Localization.SmallShiftedHom.equiv_apply, Localization.SmallShiftedHom.equiv_apply, h]
  simp only [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp, ShiftedHom.map, Functor.map_comp,
    Category.assoc, Iso.app_hom]
  rw [← NatTrans.shift_app_comm (modelCompQIso H₁ H₂).hom m L, Functor.commShiftIso_comp_hom_app,
    Category.assoc]

/-- **`Ext` at the two models.** The identification of `Ext X Y n` with shifted morphisms of the
derived category at the second model is the one at the first model, carried across by the
comparison equivalence. -/
theorem ext_homEquiv_modelEquiv [HasExt.{w'} C] {X Y : C} {n : ℕ} (α : Abelian.Ext.{w'} X Y n) :
    @Abelian.Ext.homEquiv C _ _ _ X Y H₂ n α =
      (ShiftedHom.mk₀ 0 rfl ((modelCompQIso H₁ H₂).inv.app _)).comp
        (((@Abelian.Ext.homEquiv C _ _ _ X Y H₁ n α).map (modelEquiv H₁ H₂).functor).comp
          (ShiftedHom.mk₀ 0 rfl ((modelCompQIso H₁ H₂).hom.app _)) (zero_add _)) (add_zero _) :=
  smallShiftedHom_equiv_modelEquiv H₁ H₂ α

end Ext

section DerivedHom

variable {C : Type u} [Category.{v} C] [Abelian C]
  (H₁ : HasDerivedCategory.{w} C) (H₂ : HasDerivedCategory.{z} C)
  (G : (CochainComplex C ℤ)ᵒᵖ ⥤ CochainComplex C ℤ ⥤ CochainComplex C ℤ)

/-- A bifunctor of the second model induced by `G` followed by `Q` is, after precomposition with
the comparison, induced by the same along the localizations of the first model. -/
@[instance_reducible]
def liftingWhiskeringLeft₂ModelEquiv
    (F₂ : (@DerivedCategory C _ _ H₂)ᵒᵖ ⥤ @DerivedCategory C _ _ H₂ ⥤ @DerivedCategory C _ _ H₂)
    [Localization.Lifting₂ (@DerivedCategory.Q C _ _ H₂).op (@DerivedCategory.Q C _ _ H₂)
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)).op
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (G ⋙ (whiskeringRight _ _ _).obj (@DerivedCategory.Q C _ _ H₂)) F₂] :
    Localization.Lifting₂ (@DerivedCategory.Q C _ _ H₁).op (@DerivedCategory.Q C _ _ H₁)
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)).op
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (G ⋙ (whiskeringRight _ _ _).obj (@DerivedCategory.Q C _ _ H₂))
      ((((whiskeringLeft₂ _).obj (modelEquiv H₁ H₂).functor.op).obj
        (modelEquiv H₁ H₂).functor).obj F₂) :=
  ⟨show (((whiskeringLeft₂ _).obj
      (@DerivedCategory.Q C _ _ H₁ ⋙ (modelEquiv H₁ H₂).functor).op).obj
        (@DerivedCategory.Q C _ _ H₁ ⋙ (modelEquiv H₁ H₂).functor)).obj F₂ ≅ _ from
    (((whiskeringLeft₂ _).mapIso (NatIso.op (modelCompQIso H₁ H₂)).symm).app _).app F₂ ≪≫
    (((whiskeringLeft₂ _).obj _).mapIso (modelCompQIso H₁ H₂)).app F₂ ≪≫
      Localization.Lifting₂.iso _ _ (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)).op
        (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) _ _⟩

/-- **Transport of a derived bifunctor.** Let `F₁` and `F₂` be the bifunctors of the two models
induced by the same bifunctor `G` of complexes followed by `Q`, contravariant in the first
variable. Then the comparison carries `F₁` to `F₂`. -/
def bifunctorModelEquivIso
    (F₁ : (@DerivedCategory C _ _ H₁)ᵒᵖ ⥤ @DerivedCategory C _ _ H₁ ⥤ @DerivedCategory C _ _ H₁)
    (F₂ : (@DerivedCategory C _ _ H₂)ᵒᵖ ⥤ @DerivedCategory C _ _ H₂ ⥤ @DerivedCategory C _ _ H₂)
    [Localization.Lifting₂ (@DerivedCategory.Q C _ _ H₁).op (@DerivedCategory.Q C _ _ H₁)
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)).op
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (G ⋙ (whiskeringRight _ _ _).obj (@DerivedCategory.Q C _ _ H₁)) F₁]
    [Localization.Lifting₂ (@DerivedCategory.Q C _ _ H₂).op (@DerivedCategory.Q C _ _ H₂)
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)).op
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (G ⋙ (whiskeringRight _ _ _).obj (@DerivedCategory.Q C _ _ H₂)) F₂] :
    F₁ ⋙ (whiskeringRight _ _ _).obj (modelEquiv H₁ H₂).functor ≅
      (((whiskeringLeft₂ _).obj (modelEquiv H₁ H₂).functor.op).obj
        (modelEquiv H₁ H₂).functor).obj F₂ :=
  letI := liftingWhiskeringLeft₂ModelEquiv H₁ H₂ G F₂
  Localization.lift₂NatIso (@DerivedCategory.Q C _ _ H₁).op (@DerivedCategory.Q C _ _ H₁)
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)).op
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    ((G ⋙ (whiskeringRight _ _ _).obj (@DerivedCategory.Q C _ _ H₁)) ⋙
      (whiskeringRight _ _ _).obj (modelEquiv H₁ H₂).functor)
    (G ⋙ (whiskeringRight _ _ _).obj (@DerivedCategory.Q C _ _ H₂)) _ _
    (isoWhiskerLeft G ((whiskeringRight _ _ _).mapIso (modelCompQIso H₁ H₂)))

end DerivedHom

end StacksDraft.DerivedModel

namespace AlgebraicGeometry.RingedSite

open StacksDraft.DerivedModel

section Models

variable (X : RingedSite.{u, u, u})
  (H₁ : HasDerivedCategory.{w} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
  (H₂ : HasDerivedCategory.{z} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))

/-- **The derived internal Hom at two models.** The comparison of two models of `D(𝒪)` carries
`RSheafHom(-, -)` of the first model to `RSheafHom(-, -)` of the second. -/
def derivedSheafHomBifunctorModelEquivIso :
    @derivedSheafHomBifunctor X H₁ ⋙ (whiskeringRight _ _ _).obj (modelEquiv H₁ H₂).functor ≅
      (((whiskeringLeft₂ _).obj (modelEquiv H₁ H₂).functor.op).obj
        (modelEquiv H₁ H₂).functor).obj (@derivedSheafHomBifunctor X H₂) :=
  @bifunctorModelEquivIso _ _ _ H₁ H₂
    (sheafHomComplexBifunctor X ⋙ (whiskeringLeft _ _ _).obj (kInjectiveResolution X)) _ _
    (@derivedSheafHomBifunctorLifting X H₁) (@derivedSheafHomBifunctorLifting X H₂)

variable {X}

/-- `RSheafHom(K, L)` vanishes at the first model if and only if `RSheafHom` of the images of
`K` and `L` vanishes at the second. -/
theorem isZero_derivedSheafHomBifunctor_modelEquiv_iff (K L : @DerivedCategory _ _ _ H₁) :
    IsZero (((@derivedSheafHomBifunctor X H₁).obj (op K)).obj L) ↔
      IsZero (((@derivedSheafHomBifunctor X H₂).obj
        (op ((modelEquiv H₁ H₂).functor.obj K))).obj ((modelEquiv H₁ H₂).functor.obj L)) :=
  isZero_obj_iff_of_iso (RF₁ := (@derivedSheafHomBifunctor X H₁).obj (op K))
    (J := (modelEquiv H₁ H₂).functor) (G := (modelEquiv H₁ H₂).functor)
    (RF₂ := (@derivedSheafHomBifunctor X H₂).obj (op ((modelEquiv H₁ H₂).functor.obj K)))
    ((derivedSheafHomBifunctorModelEquivIso X H₁ H₂).app (op K)) L

/-- A map in the target variable of `RSheafHom` is invertible at the first model if and only if
the corresponding map is invertible at the second. -/
theorem isIso_derivedSheafHomBifunctor_obj_map_modelEquiv_iff (K : @DerivedCategory _ _ _ H₁)
    {L L' : @DerivedCategory _ _ _ H₁} (g : L ⟶ L') :
    IsIso (((@derivedSheafHomBifunctor X H₁).obj (op K)).map g) ↔
      IsIso (((@derivedSheafHomBifunctor X H₂).obj
        (op ((modelEquiv H₁ H₂).functor.obj K))).map ((modelEquiv H₁ H₂).functor.map g)) :=
  isIso_map_iff_of_iso (RF₁ := (@derivedSheafHomBifunctor X H₁).obj (op K))
    (J := (modelEquiv H₁ H₂).functor) (G := (modelEquiv H₁ H₂).functor)
    (RF₂ := (@derivedSheafHomBifunctor X H₂).obj (op ((modelEquiv H₁ H₂).functor.obj K)))
    ((derivedSheafHomBifunctorModelEquivIso X H₁ H₂).app (op K)) g

/-- A map in the source variable of `RSheafHom` is invertible at the first model if and only if
the corresponding map is invertible at the second. -/
theorem isIso_derivedSheafHomBifunctor_map_app_modelEquiv_iff {K K' : @DerivedCategory _ _ _ H₁}
    (f : K' ⟶ K) (L : @DerivedCategory _ _ _ H₁) :
    IsIso (((@derivedSheafHomBifunctor X H₁).map f.op).app L) ↔
      IsIso (((@derivedSheafHomBifunctor X H₂).map ((modelEquiv H₁ H₂).functor.map f).op).app
        ((modelEquiv H₁ H₂).functor.obj L)) :=
  isIso_map_iff_of_iso (RF₁ := (@derivedSheafHomBifunctor X H₁).flip.obj L)
    (J := (modelEquiv H₁ H₂).functor) (G := (modelEquiv H₁ H₂).functor.op)
    (RF₂ := (@derivedSheafHomBifunctor X H₂).flip.obj ((modelEquiv H₁ H₂).functor.obj L))
    (((flipFunctor _ _ _).mapIso (derivedSheafHomBifunctorModelEquivIso X H₁ H₂)).app L) f.op

end Models

/-- `RSheafHom(-, -)` at the standard model of `D(𝒪)` and at the locally small model
`SheafOfModules.hasDerivedCategory`, compared by `SheafOfModules.derivedModelEquiv`. -/
def derivedSheafHomBifunctorStandardIso (X : RingedSite.{u, u, u}) :
    @derivedSheafHomBifunctor X (HasDerivedCategory.standard _) ⋙
        (whiskeringRight _ _ _).obj
          (SheafOfModules.derivedModelEquiv (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).functor ≅
      (((whiskeringLeft₂ _).obj (SheafOfModules.derivedModelEquiv
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).functor.op).obj
        (SheafOfModules.derivedModelEquiv (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).functor).obj
          (derivedSheafHomBifunctor X) :=
  derivedSheafHomBifunctorModelEquivIso X _ _

end AlgebraicGeometry.RingedSite

namespace AlgebraicGeometry.Scheme

open StacksDraft.DerivedModel

/-- `RSheafHom(-, -)` on `D(𝒪_X)` for a scheme `X`, at the standard model and at the locally
small model `Scheme.Modules.hasDerivedCategory`, compared by `Scheme.Modules.derivedModelEquiv`. -/
def derivedSheafHomBifunctorStandardIso (X : Scheme.{u}) :=
  RingedSite.derivedSheafHomBifunctorModelEquivIso (Stacks.SheafOfModules.ringedSite X.sheaf)
    (HasDerivedCategory.standard X.Modules) (Modules.hasDerivedCategory X)

end AlgebraicGeometry.Scheme
