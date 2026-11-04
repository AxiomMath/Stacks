module

public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.SingleObj
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence

/-!
# Modules as abelian groups with scalar operations

For a ring `R`, an `R`-module is an abelian group `M` together with, for each `a : R`, an
endomorphism of `M`, additively and multiplicatively in `a`. That is, it is an *additive*
functor from the one-object preadditive category `CategoryTheory.SingleObj R` to
`AddCommGrpCat`. The same description holds for sheaves of `R`-modules on a site: a sheaf of
`R`-modules is an additive functor from `SingleObj R` to the abelian sheaves.

This is the device by which a statement about abelian sheaves is upgraded to a statement about
sheaves of modules: an equivalence of additive categories induces an equivalence of the
categories of additive functors out of `SingleObj R`, and under the two identifications below
that is an equivalence of the categories of modules.

## Main definitions

* `CategoryTheory.moduleScalarActionEquivalence`: `ModuleCat R ≌ (SingleObj R ⥤+ AddCommGrpCat)`.
* `CategoryTheory.scalarActionCongrRight`: an additive equivalence `C ≌ D` induces
  `(SingleObj R ⥤+ C) ≌ (SingleObj R ⥤+ D)`.
* `CategoryTheory.moduleSheafScalarActionEquivalence`:
  `Sheaf J (ModuleCat R) ≌ (SingleObj R ⥤+ Sheaf J AddCommGrpCat)`.

## Implementation notes

Both equivalences are *strict* on underlying objects: the unit is the identity and the counit is
the identity on the value at the unique object of `SingleObj R`. That is recorded by the
`underlyingIso` lemmas, which hold by `Iso.refl`, and it is what makes the composite
identifications below computable with the forgetful functors.

The module structure attached to an additive functor `F : SingleObj R ⥤+ AddCommGrpCat` is
`CategoryTheory.scalarActionModule`: scalar multiplication by `a` is `F.obj.map a`. The ring
axioms are the functor laws (`map_id`, `map_comp`) and additivity (`map_add`).

## References

* [Stacks Project, Tag 0DV5](https://stacks.math.columbia.edu/tag/0DV5), part (3), where the
  source upgrades part (2) to sheaves of `Λ`-modules "in exactly the same way".
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ v₃ u₁ u₂ u₃ u r

namespace CategoryTheory

/-! ### Modules as additive functors out of `SingleObj R` -/

/-- Scalar multiplication on a module, as a functor from the one-object category on `R`. -/
public def moduleScalarFunctor (R : Type r) [Ring R] (M : ModuleCat.{u} R) :
    SingleObj R ⥤ AddCommGrpCat.{u} where
  obj _ := AddCommGrpCat.of M
  map a := AddCommGrpCat.ofHom
    { toFun := fun x ↦ a • x
      map_zero' := smul_zero a
      map_add' := smul_add a }
  map_id _ := by ext x; exact one_smul R x
  map_comp a b := by ext x; exact mul_smul b a x

public instance moduleScalarFunctor_additive (R : Type r) [Ring R] (M : ModuleCat.{u} R) :
    (moduleScalarFunctor R M).Additive where
  map_add := by
    rintro ⟨⟩ ⟨⟩ a b
    ext x
    exact add_smul (show R from a) (show R from b) (show M from x)

/-- A module, read as an abelian group with additive scalar operations. -/
public def moduleToScalarAction (R : Type r) [Ring R] :
    ModuleCat.{u} R ⥤ (SingleObj R ⥤+ AddCommGrpCat.{u}) where
  obj M := AdditiveFunctor.of (moduleScalarFunctor R M)
  map f := ObjectProperty.homMk
    { app := fun _ ↦ AddCommGrpCat.ofHom f.hom.toAddMonoidHom
      naturality := fun _ _ a ↦ by ext x; exact f.hom.map_smul a x }
  map_id _ := by ext x; rfl
  map_comp _ _ := by ext x; rfl

/-- The module structure on the value of an additive functor out of `SingleObj R`: scalar
multiplication by `a` is the image of `a`. -/
@[instance_reducible]
public def scalarActionModule (R : Type r) [Ring R]
    (F : SingleObj R ⥤+ AddCommGrpCat.{u}) :
    Module R (F.obj.obj (SingleObj.star R)) where
  smul a x := (F.obj.map a).hom x
  one_smul x := by
    change (F.obj.map (𝟙 (SingleObj.star R))).hom x = x
    simp
  mul_smul a b x :=
    ConcreteCategory.congr_hom
      (F.obj.map_comp (X := SingleObj.star R) (Y := SingleObj.star R)
        (Z := SingleObj.star R) b a) x
  smul_zero a := (F.obj.map a).hom.map_zero
  smul_add a := (F.obj.map a).hom.map_add
  add_smul a b x := by
    change (F.obj.map (a + b : SingleObj.star R ⟶ SingleObj.star R)).hom x = _
    rw [F.obj.map_add]
    rfl
  zero_smul x := by
    change (F.obj.map (0 : SingleObj.star R ⟶ SingleObj.star R)).hom x = 0
    simp

/-- An abelian group with additive scalar operations, read as a module. -/
public def scalarActionToModule (R : Type r) [Ring R] :
    (SingleObj R ⥤+ AddCommGrpCat.{u}) ⥤ ModuleCat.{u} R where
  obj F := @ModuleCat.of R _ (F.obj.obj (SingleObj.star R)) _ (scalarActionModule R F)
  map {F G} f := by
    letI := scalarActionModule R F
    letI := scalarActionModule R G
    exact ModuleCat.ofHom
      { (f.hom.app (SingleObj.star R)).hom with
        map_smul' := fun a x ↦ ConcreteCategory.congr_hom (f.hom.naturality a) x }
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

/-- **A module is an abelian group with additive scalar operations.** -/
public def moduleScalarActionEquivalence (R : Type r) [Ring R] :
    ModuleCat.{u} R ≌ (SingleObj R ⥤+ AddCommGrpCat.{u}) where
  functor := moduleToScalarAction R
  inverse := scalarActionToModule R
  unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)
  counitIso := NatIso.ofComponents (fun _ ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun ⟨⟩ ↦ Iso.refl _) (by rintro ⟨⟩ ⟨⟩ a; ext; rfl)))
    (by intros; rfl)

/-- Evaluation of the scalar-action presentation of a module is its underlying abelian group. -/
public def moduleScalarActionEquivalence_underlyingIso (R : Type r) [Ring R] :
    (moduleScalarActionEquivalence.{u} R).functor ⋙ AdditiveFunctor.forget _ _ ⋙
        (CategoryTheory.evaluation _ _).obj (SingleObj.star R) ≅
      forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u} :=
  Iso.refl _

/-! ### Transporting scalar operations along an additive equivalence -/

/-- **Scalar operations transport along an additive equivalence.** -/
public def scalarActionCongrRight
    {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    {D : Type u₂} [Category.{v₂} D] [Preadditive D]
    (R : Type r) [Ring R] (e : C ≌ D) [e.functor.Additive] :
    (SingleObj R ⥤+ C) ≌ (SingleObj R ⥤+ D) := by
  letI : (additiveFunctor (SingleObj R) D).IsClosedUnderIsomorphisms :=
    { of_iso := fun {F H} i h ↦ by
        let : F.Additive := h
        exact Functor.additive_of_iso i }
  exact e.congrRight.congrFullSubcategory (by
    funext F
    apply propext
    change (F ⋙ e.functor).Additive ↔ F.Additive
    exact ⟨fun _ ↦ Functor.additive_of_comp_faithful F e.functor, fun _ ↦ inferInstance⟩)

/-- Transporting scalar operations commutes with evaluation of the underlying object. -/
public def scalarActionCongrRight_evaluationIso
    {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    {D : Type u₂} [Category.{v₂} D] [Preadditive D]
    (R : Type r) [Ring R] (e : C ≌ D) [e.functor.Additive] :
    (scalarActionCongrRight R e).functor ⋙ AdditiveFunctor.forget _ _ ⋙
        (CategoryTheory.evaluation _ _).obj (SingleObj.star R) ≅
      AdditiveFunctor.forget _ _ ⋙
        (CategoryTheory.evaluation _ _).obj (SingleObj.star R) ⋙ e.functor :=
  Iso.refl _

/-! ### Sheaves of modules as abelian sheaves with scalar operations -/

/-- Evaluation of an abelian sheaf at an object of the site. -/
public abbrev abelianSheafEvaluation {D : Type u₃} [Category.{v₃} D]
    (K : GrothendieckTopology D) (U : Dᵒᵖ) :
    Sheaf K AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  sheafToPresheaf K AddCommGrpCat.{u} ⋙ (CategoryTheory.evaluation _ _).obj U

public instance abelianSheafEvaluation_additive {D : Type u₃} [Category.{v₃} D]
    (K : GrothendieckTopology D) (U : Dᵒᵖ) :
    (abelianSheafEvaluation.{v₃, u₃, u} K U).Additive where
  map_add := by intros; rfl

section ModuleSheafScalars

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  (R : Type r) [Ring R]
  [J.HasSheafCompose (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})]
  [ReflectsLimitsOfSize.{v₁, max v₁ u₁}
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})]

/-- Scalar multiplication on a sheaf of modules, as a functor from the one-object category
on `R`. -/
public def moduleSheafScalarFunctor (M : Sheaf J (ModuleCat.{u} R)) :
    SingleObj R ⥤ Sheaf J AddCommGrpCat.{u} where
  obj _ := (sheafCompose J (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj M
  map a := ObjectProperty.homMk
    { app := fun U ↦ (moduleScalarFunctor R (M.obj.obj U)).map a
      naturality := fun U V f ↦ by
        ext x
        exact ((M.obj.map f).hom.map_smul a x).symm }
  map_id _ := by
    apply ObjectProperty.hom_ext
    ext U x
    exact one_smul R (show M.obj.obj U from x)
  map_comp a b := by
    apply ObjectProperty.hom_ext
    ext U x
    exact mul_smul (show R from b) (show R from a) (show M.obj.obj U from x)

public instance moduleSheafScalarFunctor_additive (M : Sheaf J (ModuleCat.{u} R)) :
    (moduleSheafScalarFunctor J R M).Additive where
  map_add := by
    rintro ⟨⟩ ⟨⟩ a b
    apply ObjectProperty.hom_ext
    ext U x
    exact add_smul (show R from a) (show R from b) (show M.obj.obj U from x)

/-- A sheaf of modules, read as an abelian sheaf with additive scalar operations. -/
public def moduleSheafToScalarAction :
    Sheaf J (ModuleCat.{u} R) ⥤ (SingleObj R ⥤+ Sheaf J AddCommGrpCat.{u}) where
  obj M := AdditiveFunctor.of (moduleSheafScalarFunctor J R M)
  map f := ObjectProperty.homMk
    { app := fun _ ↦ (sheafCompose J
        (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).map f
      naturality := fun _ _ a ↦ by
        apply ObjectProperty.hom_ext
        ext U x
        exact (f.hom.app U).hom.map_smul a x }
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

/-- The presheaf of modules attached to an abelian sheaf with additive scalar operations. -/
public def scalarActionToModulePresheaf
    (F : SingleObj R ⥤+ Sheaf J AddCommGrpCat.{u}) :
    Cᵒᵖ ⥤ ModuleCat.{u} R where
  obj U := (scalarActionToModule R).obj
    (AdditiveFunctor.of (F.obj ⋙ abelianSheafEvaluation J U))
  map {U V} f := by
    letI := scalarActionModule R (AdditiveFunctor.of (F.obj ⋙ abelianSheafEvaluation J U))
    letI := scalarActionModule R (AdditiveFunctor.of (F.obj ⋙ abelianSheafEvaluation J V))
    exact ModuleCat.ofHom
      { ((F.obj.obj (SingleObj.star R)).obj.map f).hom with
        map_smul' := fun a x ↦
          (ConcreteCategory.congr_hom ((F.obj.map a).hom.naturality f) x).symm }
  map_id _ := by
    apply (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map_injective
    exact (F.obj.obj (SingleObj.star R)).obj.map_id _
  map_comp f g := by
    apply (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map_injective
    exact (F.obj.obj (SingleObj.star R)).obj.map_comp f g

/-- The sheaf of modules attached to an abelian sheaf with additive scalar operations. -/
public def scalarActionToModuleSheaf :
    (SingleObj R ⥤+ Sheaf J AddCommGrpCat.{u}) ⥤ Sheaf J (ModuleCat.{u} R) where
  obj F := ⟨scalarActionToModulePresheaf J R F,
    Presheaf.isSheaf_of_isSheaf_comp J _
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})
      (F.obj.obj (SingleObj.star R)).property⟩
  map {F H} f := ObjectProperty.homMk
    { app := fun U ↦ by
        letI := scalarActionModule R (AdditiveFunctor.of
          (F.obj ⋙ abelianSheafEvaluation J U))
        letI := scalarActionModule R (AdditiveFunctor.of
          (H.obj ⋙ abelianSheafEvaluation J U))
        exact ModuleCat.ofHom
          { ((f.hom.app (SingleObj.star R)).hom.app U).hom with
            map_smul' := fun a x ↦ ConcreteCategory.congr_hom
              (congrArg (fun g ↦ (abelianSheafEvaluation J U).map g)
                (f.hom.naturality a)) x }
      naturality := fun U V g ↦ by
        ext x
        exact ConcreteCategory.congr_hom
          ((f.hom.app (SingleObj.star R)).hom.naturality g) x }
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

/-- **A sheaf of modules is an abelian sheaf with additive scalar operations.** -/
public def moduleSheafScalarActionEquivalence :
    Sheaf J (ModuleCat.{u} R) ≌ (SingleObj R ⥤+ Sheaf J AddCommGrpCat.{u}) where
  functor := moduleSheafToScalarAction J R
  inverse := scalarActionToModuleSheaf J R
  unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)
  counitIso := NatIso.ofComponents (fun _ ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun ⟨⟩ ↦ Iso.refl _) (by rintro ⟨⟩ ⟨⟩ a; ext; rfl)))
    (by intros; rfl)

/-- Evaluation of the scalar-action presentation of a sheaf of modules is the underlying
abelian sheaf. -/
public def moduleSheafScalarActionEquivalence_underlyingIso :
    (moduleSheafScalarActionEquivalence J R).functor ⋙ AdditiveFunctor.forget _ _ ⋙
        (CategoryTheory.evaluation _ _).obj (SingleObj.star R) ≅
      sheafCompose J (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) :=
  Iso.refl _

end ModuleSheafScalars

end CategoryTheory

end
