module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.ConstantBaseRing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sheaves of `Λ`-modules are the modules over the constant sheaf of rings `Λ̲`

Let `(C, J)` be a site and `Λ` a ring. A `ModuleCat Λ`-valued sheaf, in which `Λ` acts by
constant scalars, and a sheaf of modules over the constant sheaf of rings `Λ̲`, in which the
locally constant `Λ`-valued functions act, are the same thing: the forgetful functor
`SheafOfModules Λ̲ ⥤ Sheaf J (ModuleCat Λ)` is an equivalence of categories. More generally it is
an equivalence for any sheaf of rings `R` equipped with a locally bijective morphism out of the
constant presheaf of rings on `Λ`. Over the constant presheaf of rings, a presheaf of modules is
the same data as a `ModuleCat Λ`-valued presheaf.

## Main definitions

* `Stacks.ConstantRingModules.toFunctor`: a presheaf of modules over the constant presheaf of
  rings on `Λ`, read as a `ModuleCat Λ`-valued presheaf.
* `Stacks.ConstantRingModules.presheafEquivalence`: the resulting equivalence
  `PresheafOfModules Λ ≌ (Cᵒᵖ ⥤ ModuleCat Λ)`.
* `Stacks.ConstantRingModules.toModuleSheaf`: a sheaf of modules over a sheaf of rings which is
  the sheafification of the constant presheaf of rings on `Λ`, read as a `ModuleCat Λ`-valued
  sheaf.
* `Stacks.ConstantRingModules.constantRingSheaf` and
  `Stacks.ConstantRingModules.constantRingMap`: the constant sheaf of rings on `Λ` and the
  sheafification map into it.
* `Stacks.ConstantRingModules.moduleSheafEquivalence`: the equivalence
  `SheafOfModules R ≌ Sheaf J (ModuleCat Λ)`.
* `Stacks.ConstantRingModules.constantModuleSheafEquivalence`: its instance at the constant
  sheaf of rings itself, `SheafOfModules Λ̲ ≌ Sheaf J (ModuleCat Λ)`.

## Main results

* `Stacks.ConstantRingModules.toModuleSheafFullyFaithful`: `toModuleSheaf` is fully faithful.
* `Stacks.ConstantRingModules.toModuleSheaf_isEquivalence`: `toModuleSheaf` is an equivalence.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe a r v u

namespace Stacks.ConstantRingModules

open Stacks.PresheafOfModules

variable {C : Type u} [Category.{v} C] (Λ : Type r) [Ring Λ]

/-! ### Presheaves of modules over the constant presheaf of rings -/

/-- A presheaf of modules over the constant presheaf of rings with value `Λ`, read as a
`ModuleCat Λ`-valued presheaf. -/
def toFunctorObj (M : _root_.PresheafOfModules.{a} (constRing (C := C) Λ)) :
    Cᵒᵖ ⥤ ModuleCat.{a} Λ where
  obj X := M.obj X
  map {_X Y} f := M.map f ≫
    (ModuleCat.restrictScalarsId'App _ (constRing_map_hom (C := C) Λ f) (M.obj Y)).hom
  map_id X := by
    ext x
    exact ConcreteCategory.congr_hom (M.map_id X) x
  map_comp f g := by
    ext x
    exact M.map_comp_apply f g x

/-- The value of `toFunctorObj Λ M` at `X` is `M.obj X`. -/
@[simp]
theorem toFunctorObj_obj (M : _root_.PresheafOfModules.{a} (constRing (C := C) Λ)) (X : Cᵒᵖ) :
    (toFunctorObj Λ M).obj X = M.obj X := rfl

/-- The restriction maps of `toFunctorObj Λ M` are those of `M`. -/
@[simp]
theorem toFunctorObj_map_apply (M : _root_.PresheafOfModules.{a} (constRing (C := C) Λ))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : M.obj X) : (toFunctorObj Λ M).map f x = M.map f x := rfl

/-- A presheaf of modules over the constant presheaf of rings with value `Λ`, read as a
`ModuleCat Λ`-valued presheaf, functorially. -/
def toFunctor : _root_.PresheafOfModules.{a} (constRing (C := C) Λ) ⥤
    (Cᵒᵖ ⥤ ModuleCat.{a} Λ) where
  obj M := toFunctorObj Λ M
  map {_M _N} φ :=
    { app X := φ.app X
      naturality := fun {_X _Y} f => by
        ext x
        exact _root_.PresheafOfModules.naturality_apply φ f x }

/-- The components of `(toFunctor Λ).map φ` are those of `φ`. -/
@[simp]
theorem toFunctor_map_app {M N : _root_.PresheafOfModules.{a} (constRing (C := C) Λ)}
    (φ : M ⟶ N) (X : Cᵒᵖ) : ((toFunctor Λ).map φ).app X = φ.app X := rfl

/-- Reading a `ModuleCat Λ`-valued presheaf as a presheaf of modules over the constant presheaf
of rings and back changes nothing. -/
def ofFunctorCompToFunctorIso :
    ofFunctor.{a} (C := C) Λ ⋙ toFunctor.{a} Λ ≅ 𝟭 (Cᵒᵖ ⥤ ModuleCat.{a} Λ) :=
  NatIso.ofComponents
    (fun _ => NatIso.ofComponents (fun _ => Iso.refl _) (by intros; ext x; rfl))
    (by intros; ext X x; rfl)

/-- Reading a presheaf of modules over the constant presheaf of rings as a `ModuleCat Λ`-valued
presheaf and back changes nothing. -/
def toFunctorCompOfFunctorIso :
    toFunctor.{a} (C := C) Λ ⋙ ofFunctor.{a} Λ ≅
      𝟭 (_root_.PresheafOfModules.{a} (constRing (C := C) Λ)) :=
  NatIso.ofComponents
    (fun _ => _root_.PresheafOfModules.isoMk (fun _ => Iso.refl _) (by intros; ext x; rfl))
    (by intros; ext X x; rfl)

/-- **The functor `toFunctor Λ` is fully faithful.** -/
def toFunctorFullyFaithful : (toFunctor.{a} (C := C) Λ).FullyFaithful where
  preimage {M N} φ :=
    { app X := φ.app X
      naturality := fun {_X _Y} f => by
        ext x
        exact ConcreteCategory.congr_hom (φ.naturality f) x }
  map_preimage _ := rfl
  preimage_map _ := _root_.PresheafOfModules.hom_ext (fun _ => rfl)

/-- The functor `toFunctor Λ` is full. -/
instance : (toFunctor.{a} (C := C) Λ).Full := (toFunctorFullyFaithful Λ).full

/-- The functor `toFunctor Λ` is faithful. -/
instance : (toFunctor.{a} (C := C) Λ).Faithful := (toFunctorFullyFaithful Λ).faithful

/-- **Presheaves of modules over the constant presheaf of rings on `Λ` are
`ModuleCat Λ`-valued presheaves.** -/
@[sga "7 VI 3.1(a)" "partial"]
def presheafEquivalence :
    _root_.PresheafOfModules.{a} (constRing (C := C) Λ) ≌ (Cᵒᵖ ⥤ ModuleCat.{a} Λ) where
  functor := toFunctor Λ
  inverse := ofFunctor Λ
  unitIso := (toFunctorCompOfFunctorIso Λ).symm
  counitIso := ofFunctorCompToFunctorIso Λ
  functor_unitIso_comp _ := by ext X x; rfl

/-! ### Sheaves of modules over the constant sheaf of rings -/

section Sheaves

variable (J : GrothendieckTopology C) {R : Sheaf J RingCat.{r}}
  (α : constRing (C := C) Λ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{a}] [HasWeakSheafify J AddCommGrpCat.{a}]

/-- A sheaf of modules over a sheaf of rings `R` which is the sheafification of the constant
presheaf of rings on `Λ`, read as a `ModuleCat Λ`-valued sheaf by restricting the scalars to
`Λ`. -/
def toModuleSheafObj (M : SheafOfModules.{a} R) : Sheaf J (ModuleCat.{a} Λ) :=
  ⟨toFunctorObj Λ ((_root_.PresheafOfModules.restrictScalars α).obj M.val),
    Presheaf.isSheaf_of_isSheaf_comp _ _
      (forget₂ (ModuleCat.{a} Λ) AddCommGrpCat.{a}) M.isSheaf⟩

/-- A sheaf of modules over a sheaf of rings which is the sheafification of the constant
presheaf of rings on `Λ`, read as a `ModuleCat Λ`-valued sheaf, functorially. -/
def toModuleSheaf : SheafOfModules.{a} R ⥤ Sheaf J (ModuleCat.{a} Λ) where
  obj M := toModuleSheafObj Λ J α M
  map f := ⟨(toFunctor Λ).map ((_root_.PresheafOfModules.restrictScalars α).map f.val)⟩

/-- The underlying `ModuleCat Λ`-valued presheaf of a sheaf of modules over `R`, read in two
ways: by forgetting the sheaf condition after restricting the scalars, and by restricting the
scalars after forgetting the sheaf condition. -/
def toModuleSheafCompSheafToPresheafIso :
    toModuleSheaf.{a} Λ J α ⋙ sheafToPresheaf J (ModuleCat.{a} Λ) ≅
      (SheafOfModules.forget.{a} R ⋙ _root_.PresheafOfModules.restrictScalars α) ⋙
        toFunctor.{a} Λ :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

/-- **The functor `toModuleSheaf Λ J α` is fully faithful.** -/
def toModuleSheafFullyFaithful : (toModuleSheaf.{a} Λ J α).FullyFaithful := by
  refine Functor.FullyFaithful.ofCompFaithful (G := sheafToPresheaf J (ModuleCat.{a} Λ)) ?_
  refine Functor.FullyFaithful.ofIso ?_ (toModuleSheafCompSheafToPresheafIso.{a} Λ J α).symm
  exact ((_root_.PresheafOfModules.sheafificationAdjunction
    α).fullyFaithfulROfIsIsoCounit).comp (toFunctorFullyFaithful.{a} Λ)

/-- The functor `toModuleSheaf Λ J α` is full. -/
instance : (toModuleSheaf.{a} Λ J α).Full := (toModuleSheafFullyFaithful Λ J α).full

/-- The functor `toModuleSheaf Λ J α` is faithful. -/
instance : (toModuleSheaf.{a} Λ J α).Faithful := (toModuleSheafFullyFaithful Λ J α).faithful

variable [J.HasSheafCompose (forget₂ (ModuleCat.{a} Λ) AddCommGrpCat.{a})]

/-- **Every sheaf of `Λ`-modules comes from a sheaf of modules over `R`.** -/
instance toModuleSheaf_essSurj : (toModuleSheaf.{a} Λ J α).EssSurj where
  mem_essImage F := by
    let P := (ofFunctor.{a} Λ).obj F.obj
    let η := (_root_.PresheafOfModules.sheafificationAdjunction α).unit.app P
    have : IsIso ((_root_.PresheafOfModules.toPresheaf _).map η) :=
      CategoryTheory.isIso_toSheafify J (P := P.presheaf)
        (GrothendieckTopology.HasSheafCompose.isSheaf
          (F := forget₂ (ModuleCat.{a} Λ) AddCommGrpCat.{a}) F.obj F.property)
    have : IsIso η := isIso_of_reflects_iso η (_root_.PresheafOfModules.toPresheaf _)
    exact ⟨(_root_.PresheafOfModules.sheafification α).obj P,
      ⟨(sheafToPresheaf J (ModuleCat.{a} Λ)).preimageIso
        (((toFunctor.{a} Λ).mapIso (asIso η)).symm ≪≫
          (ofFunctorCompToFunctorIso.{a} Λ).app F.obj)⟩⟩

/-- **The functor `toModuleSheaf Λ J α` is an equivalence of categories.** -/
instance toModuleSheaf_isEquivalence : (toModuleSheaf.{a} Λ J α).IsEquivalence where

/-- The functor `toModuleSheaf Λ J α` is additive. -/
instance : (toModuleSheaf.{a} Λ J α).Additive where
  map_add := rfl

/-- **Sheaves of modules over a sheafification of the constant presheaf of rings on `Λ` are
sheaves of `Λ`-modules.** -/
@[sga "4 IV 13.8" "special case"]
def moduleSheafEquivalence : SheafOfModules.{a} R ≌ Sheaf J (ModuleCat.{a} Λ) :=
  (toModuleSheaf.{a} Λ J α).asEquivalence

end Sheaves

/-! ### The constant sheaf of rings -/

section ConstantRingSheaf

variable (J : GrothendieckTopology C)
  [HasWeakSheafify J RingCat.{r}] [J.WEqualsLocallyBijective RingCat.{r}]

/-- The constant sheaf of rings with value `Λ`. -/
abbrev constantRingSheaf : Sheaf J RingCat.{r} :=
  (constantSheaf J RingCat.{r}).obj (RingCat.of Λ)

/-- The sheafification map from the constant presheaf of rings with value `Λ` to the constant
sheaf of rings with value `Λ`. -/
def constantRingMap : constRing (C := C) Λ ⟶ (constantRingSheaf Λ J).obj :=
  toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))

/-- The map `constantRingMap Λ J` is locally injective. -/
instance constantRingMap_isLocallyInjective :
    Presheaf.IsLocallyInjective J (constantRingMap Λ J) :=
  (J.W_toSheafify ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).isLocallyInjective

/-- The map `constantRingMap Λ J` is locally surjective. -/
instance constantRingMap_isLocallySurjective :
    Presheaf.IsLocallySurjective J (constantRingMap Λ J) :=
  (J.W_toSheafify ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).isLocallySurjective

variable [J.WEqualsLocallyBijective AddCommGrpCat.{a}] [HasWeakSheafify J AddCommGrpCat.{a}]
  [J.HasSheafCompose (forget₂ (ModuleCat.{a} Λ) AddCommGrpCat.{a})]

/-- **Sheaves of `Λ`-modules are the sheaves of modules over the constant sheaf of rings on
`Λ`.** -/
def constantModuleSheafEquivalence :
    SheafOfModules.{a} (constantRingSheaf Λ J) ≌ Sheaf J (ModuleCat.{a} Λ) :=
  moduleSheafEquivalence.{a} Λ J (constantRingMap Λ J)

end ConstantRingSheaf

end Stacks.ConstantRingModules

end
