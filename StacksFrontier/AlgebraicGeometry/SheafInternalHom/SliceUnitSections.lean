module

public import StacksFrontier.AlgebraicGeometry.SectionRingGeometric.GlobalSections
public import StacksFrontier.AlgebraicGeometry.SheafInternalHom.SliceRestriction

/-!
# Morphisms out of a slice site's monoidal unit are sections over the slicing object

`StacksFrontier/AlgebraicGeometry/SectionRingGeometric/GlobalSections.lean` identifies the morphisms
out of the monoidal unit of `Stacks.SheafInternalHom.monoidalCategory` with the sections over a
*terminal* object of the site: `Stacks.SectionRingGeometric.tensorUnitHomAddEquiv`. On the site of
opens of a scheme the terminal object is `⊤`, and the identification is
`Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv`.

**The slice site `Over U` has a terminal object too**, namely `U` over itself, and restriction to
the slice site sends a sheaf of modules to one whose sections there are the sections of the
original over `U`. So the identification holds on the slice site as well, and reads

`(𝟙_ ⟶ M|_U) ≃+ Γ(U, M)`.

This file records it. Nothing is reproved: `tensorUnitHomAddEquiv` is already stated for an
arbitrary site and an arbitrary terminal object, and the two inputs supplied here are
`CategoryTheory.Over.mkIdTerminal` and the definitional identification
`overFunctor_obj_val_obj_mkId`.

## Main definitions

* `Stacks.SheafInternalHom.SliceRestriction.overTensorUnitHomAddEquiv`: **the bridge**, for a
  sheaf of modules on an arbitrary site and an arbitrary object `U` of it.
* `Stacks.SheafInternalHom.SliceRestriction.schemeOpenUnitHomAddEquiv`: the same for an
  `𝒪_X`-module on a scheme and an open `V`, with the source category spelled `X.Modules` and the
  target `Γ(F, V)`. This is the shape the twisted-section machinery consumes: Stacks Tag 0B5L's
  comparison map `Stacks.TwistedSections.localizationLiftOverOpen` lands in
  `twistSections (F|_V) (L|_V) 0`, which is a morphism out of the slice site's monoidal unit, and
  Stacks Tag 0B5I's local data asks for a section over the open.

## Main results

* `Stacks.SheafInternalHom.SliceRestriction.overFunctor_obj_val_obj_mkId`: **the sections of
  `M|_U` over the terminal object of the slice site are the sections of `M` over `U`**, by `rfl`.
  Restriction to the slice site is `SheafOfModules.overFunctor`, which is pushforward along
  `Over.forget U`, so its value on the object `U ⟶ U` of `Over U` is the value of `M` on `U`.

## Implementation notes

Each monoidal structure is a local instance and never a `have`: `MonoidalCategory` is a data
class. The scheme-level statement needs the retyped `schemeOpenRestriction` of
`StacksFrontier/AlgebraicGeometry/SheafInternalHom/SliceRestriction.lean` rather than the site-level
`overFunctor`, for the reason recorded there — the two spellings of the structure sheaf are
definitionally equal but instance search is keyed syntactically.

## References

* [Stacks Project, Tag 0B5L](https://stacks.math.columbia.edu/tag/0B5L)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite
open Stacks.SheafOfModules.TensorSheafification

universe v u w

namespace Stacks.SheafInternalHom.SliceRestriction

open Stacks.SheafOfModules.SliceRestriction (sliceRingPresheaf sliceStructureSheaf
  isSheaf_sliceRingPresheaf overFunctor)

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory

section Site

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
  (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))
  (U : C)
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{w}]

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{w}] in
/-- **The sections of `M|_U` over the terminal object of the slice site are the sections of `M`
over `U`**, by `rfl`. Restriction to the slice site is `SheafOfModules.overFunctor`, pushforward
along `CategoryTheory.Over.forget U`, so its value on an object `W ⟶ U` of `Over U` is the value
of `M` on `W`; at the terminal object `U ⟶ U` that is the value on `U`. -/
theorem overFunctor_obj_val_obj_mkId (F : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) :
    ((overFunctor 𝒪 h𝒪 U).obj F).val.obj (op (Over.mk (𝟙 U))) = F.val.obj (op U) :=
  rfl

/-- **Morphisms out of the slice site's monoidal unit into `M|_U` are the sections of `M` over
`U`.** `Stacks.SectionRingGeometric.tensorUnitHomAddEquiv` says this for the sections over any
terminal object of any site; the terminal object of `Over U` is `U` over itself
(`CategoryTheory.Over.mkIdTerminal`), and `overFunctor_obj_val_obj_mkId` identifies the sections
of `M|_U` there with `Γ(U, M)`. -/
def overTensorUnitHomAddEquiv (F : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) :
    ((𝟙_ (SheafOfModules.{w} (sliceStructureSheaf 𝒪 h𝒪 U))) ⟶
        (overFunctor 𝒪 h𝒪 U).obj F) ≃+ F.val.obj (op U) :=
  Stacks.SectionRingGeometric.tensorUnitHomAddEquiv (sliceRingPresheaf 𝒪 U)
    (isSheaf_sliceRingPresheaf 𝒪 h𝒪 U) Over.mkIdTerminal ((overFunctor 𝒪 h𝒪 U).obj F)

end Site

section Scheme

variable {X : Scheme.{u}}

/-- **Morphisms out of the monoidal unit of the modules on an open `V` of a scheme are the
sections over `V`.** This is `overTensorUnitHomAddEquiv` with the source category spelled
`X.Modules`, which is the spelling the twisted-section development uses; see the implementation
notes of `Stacks.SheafInternalHom.SliceRestriction.schemeOpenRestriction`. -/
def schemeOpenUnitHomAddEquiv (V : X.Opens) (F : X.Modules) :
    ((𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.SliceRestriction.sliceStructureSheaf
        X.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) V))) ⟶
      (schemeOpenRestriction X V).obj F) ≃+ Γ(F, V) :=
  overTensorUnitHomAddEquiv X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) V F

end Scheme

end Stacks.SheafInternalHom.SliceRestriction

end
