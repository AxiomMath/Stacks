module

public import StacksFrontier.CategoryTheory.Sites.Modules.ModuleSheavesAsConstantRingModules
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.ConstantBaseRing

/-!
# Sheaves of `Λ`-modules are sheaves of modules over the constant sheaf of rings `Λ̲`

Let `(C, J)` be a site and `Λ` a ring. Two categories formalise "sheaves of `Λ`-modules on `C`":
sheaves `Sheaf J (ModuleCat Λ)` with values in `Λ`-modules, and sheaves of modules
`SheafOfModules Λ̲` over the constant sheaf of rings `Λ̲`, the sheafification of the constant
presheaf of rings with value `Λ`. This file identifies them, together with the functors
forgetting the module structure.

## Main definitions

* `Stacks.SheafOfModules.ConstantRing.forgetToModuleSheaf`: for a locally bijective morphism
  `α` from the constant presheaf of rings to a sheaf of rings `R`, a sheaf of `R`-modules read
  as a sheaf of `Λ`-modules through `α`.
* `Stacks.SheafOfModules.ConstantRing.moduleSheafEquivOfLocallyBijective`: the equivalence
  `Sheaf J (ModuleCat Λ) ≌ SheafOfModules R` it induces.
* `Stacks.SheafOfModules.ConstantRing.sheafifiedConstRing`: the constant sheaf of rings `Λ̲`, and
  `Stacks.SheafOfModules.ConstantRing.sheafifiedConstRingModulesEquivalence` the equivalence
  `Sheaf J (ModuleCat Λ) ≌ SheafOfModules Λ̲`.

## Main results

* `Stacks.SheafOfModules.ConstantRing.moduleSheafEquivOfLocallyBijectiveFunctorCompToSheaf`:
  the functor of the equivalence followed by `SheafOfModules.toSheaf` is the functor
  `sheafCompose J (forget₂ (ModuleCat Λ) AddCommGrpCat)` forgetting the module structure.

## Implementation notes

The functor which is constructed by hand is the one from sheaves of `R`-modules: restrict the
scalars along `α`, which lands in presheaves of modules over the constant presheaf of rings,
i.e. in `ModuleCat Λ`-valued presheaves, and the sheaf condition is the one of the underlying
abelian presheaf because `forget₂ (ModuleCat Λ) AddCommGrpCat` reflects limits. Mathlib proves
that restriction of scalars along a locally bijective `α` is fully faithful on sheaves
(`PresheafOfModules.sheafificationAdjunction` has invertible counit), and essential surjectivity
is `PresheafOfModules.sheafify`: a sheaf of `Λ`-modules is the restriction of the sheaf of
`R`-modules obtained by extending the action of the constant presheaf to its sheafification,
which does not change the underlying abelian sheaf.

The ring and the modules may live in different universes, as in Mathlib's sheafification of
presheaves of modules: `Λ : Type w`, `R` takes values in `RingCat.{w}` and the modules in
`ModuleCat.{t} Λ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe t w v u

namespace Stacks.SheafOfModules.ConstantRing

open Stacks.PresheafOfModules

section LocallyBijective

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {Λ : Type w} [Ring Λ]
  {R : Sheaf J RingCat.{w}} (α : constRing (C := C) Λ ⟶ R.obj)

/-- The `ModuleCat Λ`-valued presheaf underlying a sheaf of `R`-modules, its scalars restricted
along `α`, is a sheaf: its sheaf condition is that of the underlying abelian presheaf, because
the forgetful functor from `Λ`-modules to abelian groups reflects limits. -/
theorem isSheaf_toFunctorObj_restrictScalars (M : _root_.SheafOfModules.{t} R) :
    Presheaf.IsSheaf J
      ((Stacks.ConstantRingModules.toFunctor Λ).obj
        ((_root_.PresheafOfModules.restrictScalars α).obj M.val)) :=
  Presheaf.isSheaf_of_isSheaf_comp J _ (forget₂ (ModuleCat.{t} Λ) AddCommGrpCat.{t}) M.isSheaf

/-- A sheaf of `R`-modules read as a sheaf of `Λ`-modules: restriction of scalars along
`α : Λ ⟶ R`. -/
def forgetToModuleSheaf : _root_.SheafOfModules.{t} R ⥤ Sheaf J (ModuleCat.{t} Λ) where
  obj M := ⟨(Stacks.ConstantRingModules.toFunctor Λ).obj
      ((_root_.PresheafOfModules.restrictScalars α).obj M.val),
    isSheaf_toFunctorObj_restrictScalars α M⟩
  map φ := ⟨(Stacks.ConstantRingModules.toFunctor Λ).map
    ((_root_.PresheafOfModules.restrictScalars α).map φ.val)⟩
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

/-- The sections over `X` of `(forgetToModuleSheaf α).obj M` are the sections of `M` over `X`
with scalars restricted along `α.app X`. -/
@[simp]
theorem forgetToModuleSheaf_obj_obj_obj (M : _root_.SheafOfModules.{t} R) (X : Cᵒᵖ) :
    ((forgetToModuleSheaf α).obj M).obj.obj X =
      (ModuleCat.restrictScalars (α.app X).hom).obj (M.val.obj X) := rfl

/-- The functor `forgetToModuleSheaf α` is additive. -/
instance : (forgetToModuleSheaf.{t} α).Additive where

/-- Reading a sheaf of `R`-modules as a sheaf of `Λ`-modules does not change its underlying
abelian sheaf. -/
def forgetToModuleSheafCompForget
    [J.HasSheafCompose (forget₂ (ModuleCat.{t} Λ) AddCommGrpCat.{t})] :
    forgetToModuleSheaf.{t} α ⋙ sheafCompose J (forget₂ (ModuleCat.{t} Λ) AddCommGrpCat.{t}) ≅
      _root_.SheafOfModules.toSheaf.{t} R :=
  NatIso.ofComponents
    (fun M => (fullyFaithfulSheafToPresheaf J AddCommGrpCat.{t}).preimageIso
      (NatIso.ofComponents (fun _ => Iso.refl _) (by intro X Y f; rfl)))
    (by intro M N φ; rfl)

variable [HasWeakSheafify J AddCommGrpCat.{t}] [J.WEqualsLocallyBijective AddCommGrpCat.{t}]
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]

/-- For a locally bijective `α`, the functor `forgetToModuleSheaf α` is full. -/
instance : (forgetToModuleSheaf.{t} α).Full :=
  have : (forgetToModuleSheaf.{t} α ⋙ sheafToPresheaf J _).Full :=
    inferInstanceAs ((_root_.SheafOfModules.forget.{t} R ⋙
      _root_.PresheafOfModules.restrictScalars α) ⋙ Stacks.ConstantRingModules.toFunctor Λ).Full
  Functor.Full.of_comp_faithful _ (sheafToPresheaf J _)

/-- For a locally bijective `α`, the functor `forgetToModuleSheaf α` is faithful. -/
instance : (forgetToModuleSheaf.{t} α).Faithful :=
  have : (forgetToModuleSheaf.{t} α ⋙ sheafToPresheaf J _).Faithful :=
    inferInstanceAs ((_root_.SheafOfModules.forget.{t} R ⋙
      _root_.PresheafOfModules.restrictScalars α) ⋙ Stacks.ConstantRingModules.toFunctor Λ).Faithful
  Functor.Faithful.of_comp _ (sheafToPresheaf J _)

variable [J.HasSheafCompose (forget₂ (ModuleCat.{t} Λ) AddCommGrpCat.{t})]

/-- The abelian sheaf underlying a sheaf of `Λ`-modules, spelled as the underlying abelian
presheaf of the corresponding presheaf of modules over the constant presheaf of rings. -/
abbrev underlyingAbelianSheaf (F : Sheaf J (ModuleCat.{t} Λ)) : Sheaf J AddCommGrpCat.{t} :=
  ⟨((ofFunctor Λ).obj F.obj).presheaf,
    ((sheafCompose J (forget₂ (ModuleCat.{t} Λ) AddCommGrpCat.{t})).obj F).property⟩

/-- A sheaf of `Λ`-modules, as a sheaf of `R`-modules: the action of the constant presheaf of
rings on the sections extended to its sheafification `R` (`PresheafOfModules.sheafify`). The
underlying abelian sheaf is the one of the given sheaf. -/
def toSheafOfModules (F : Sheaf J (ModuleCat.{t} Λ)) : _root_.SheafOfModules.{t} R :=
  _root_.PresheafOfModules.sheafify (A := underlyingAbelianSheaf F) α
    (𝟙 ((ofFunctor Λ).obj F.obj).presheaf)

/-- The sheaf of `R`-modules `toSheafOfModules α F` gives back `F` when read as a sheaf of
`Λ`-modules. -/
def forgetToModuleSheafObjToSheafOfModulesIso (F : Sheaf J (ModuleCat.{t} Λ)) :
    (forgetToModuleSheaf.{t} α).obj (toSheafOfModules α F) ≅ F := by
  haveI : IsIso (_root_.PresheafOfModules.toSheafify α (A := underlyingAbelianSheaf F)
      (𝟙 ((ofFunctor Λ).obj F.obj).presheaf)) := by
    rw [← isIso_iff_of_reflects_iso _ (_root_.PresheafOfModules.toPresheaf _),
      _root_.PresheafOfModules.toPresheaf_map_toSheafify]
    exact IsIso.id _
  exact (fullyFaithfulSheafToPresheaf J _).preimageIso
    ((Stacks.ConstantRingModules.toFunctor Λ).mapIso (asIso (_root_.PresheafOfModules.toSheafify α
      (A := underlyingAbelianSheaf F) (𝟙 ((ofFunctor Λ).obj F.obj).presheaf))).symm ≪≫
      (Stacks.ConstantRingModules.ofFunctorCompToFunctorIso Λ).app F.obj)

/-- For a locally bijective `α`, the functor `forgetToModuleSheaf α` is essentially surjective. -/
instance : (forgetToModuleSheaf.{t} α).EssSurj where
  mem_essImage F := ⟨toSheafOfModules α F, ⟨forgetToModuleSheafObjToSheafOfModulesIso α F⟩⟩

/-- For a locally bijective `α`, the functor `forgetToModuleSheaf α` is an equivalence. -/
instance : (forgetToModuleSheaf.{t} α).IsEquivalence where

/-- **Sheaves of `Λ`-modules are sheaves of `R`-modules**, for a sheaf of rings `R` receiving a
locally bijective morphism `α` from the constant presheaf of rings with value `Λ`. The inverse
functor is `Stacks.SheafOfModules.ConstantRing.forgetToModuleSheaf`, restriction of scalars along
`α`. -/
def moduleSheafEquivOfLocallyBijective :
    Sheaf J (ModuleCat.{t} Λ) ≌ _root_.SheafOfModules.{t} R :=
  (forgetToModuleSheaf.{t} α).asEquivalence.symm

/-- The inverse functor of `moduleSheafEquivOfLocallyBijective α` is `forgetToModuleSheaf α`. -/
theorem moduleSheafEquivOfLocallyBijective_inverse :
    (moduleSheafEquivOfLocallyBijective.{t} α).inverse = forgetToModuleSheaf α := rfl

/-- **The equivalence `Sheaf J (ModuleCat Λ) ≌ SheafOfModules R` is compatible with forgetting
the module structure**: its functor followed by `SheafOfModules.toSheaf` is postcomposition with
`forget₂ (ModuleCat Λ) AddCommGrpCat`. -/
def moduleSheafEquivOfLocallyBijectiveFunctorCompToSheaf :
    (moduleSheafEquivOfLocallyBijective.{t} α).functor ⋙ _root_.SheafOfModules.toSheaf.{t} R ≅
      sheafCompose J (forget₂ (ModuleCat.{t} Λ) AddCommGrpCat.{t}) :=
  Functor.isoWhiskerLeft _ (forgetToModuleSheafCompForget α).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (moduleSheafEquivOfLocallyBijective.{t} α).unitIso.symm _ ≪≫
    Functor.leftUnitor _

end LocallyBijective

section Constant

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (Λ : Type w) [Ring Λ]
  [HasWeakSheafify J RingCat.{w}]

/-- The constant sheaf of rings `Λ̲` on a site: the sheafification of the constant presheaf of
rings with value `Λ`. -/
abbrev sheafifiedConstRing : Sheaf J RingCat.{w} :=
  (constantSheaf J RingCat.{w}).obj (RingCat.of Λ)

/-- The sheafification map from the constant presheaf of rings with value `Λ` to the constant
sheaf of rings `Λ̲`. -/
abbrev toSheafifiedConstRing : constRing (C := C) Λ ⟶ (sheafifiedConstRing J Λ).obj :=
  toSheafify J (constRing (C := C) Λ)

variable [J.WEqualsLocallyBijective RingCat.{w}]

/-- The sheafification map `toSheafifiedConstRing J Λ` is locally injective. -/
instance : Presheaf.IsLocallyInjective J (toSheafifiedConstRing J Λ) :=
  inferInstanceAs (Presheaf.IsLocallyInjective J (toSheafify J (constRing (C := C) Λ)))

/-- The sheafification map `toSheafifiedConstRing J Λ` is locally surjective. -/
instance : Presheaf.IsLocallySurjective J (toSheafifiedConstRing J Λ) :=
  inferInstanceAs (Presheaf.IsLocallySurjective J (toSheafify J (constRing (C := C) Λ)))

variable [HasWeakSheafify J AddCommGrpCat.{t}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{t}]
  [J.HasSheafCompose (forget₂ (ModuleCat.{t} Λ) AddCommGrpCat.{t})]

/-- **Sheaves of `Λ`-modules are sheaves of modules over the constant sheaf of rings `Λ̲`.** -/
def sheafifiedConstRingModulesEquivalence :
    Sheaf J (ModuleCat.{t} Λ) ≌ _root_.SheafOfModules.{t} (sheafifiedConstRing J Λ) :=
  moduleSheafEquivOfLocallyBijective (toSheafifiedConstRing J Λ)

/-- The equivalence `Sheaf J (ModuleCat Λ) ≌ SheafOfModules Λ̲` followed by
`SheafOfModules.toSheaf` is the functor forgetting the module structure. -/
def sheafifiedConstRingModulesEquivalenceFunctorCompToSheaf :
    (sheafifiedConstRingModulesEquivalence.{t} J Λ).functor ⋙
        _root_.SheafOfModules.toSheaf.{t} (sheafifiedConstRing J Λ) ≅
      sheafCompose J (forget₂ (ModuleCat.{t} Λ) AddCommGrpCat.{t}) :=
  moduleSheafEquivOfLocallyBijectiveFunctorCompToSheaf (toSheafifiedConstRing J Λ)

end Constant

end Stacks.SheafOfModules.ConstantRing

end
