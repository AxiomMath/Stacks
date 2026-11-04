module

public import StacksFrontier.AlgebraicGeometry.SheafInternalHom.Basic

/-!
# The tensor product of sheaves of modules on sections

The monoidal product of sheaves of modules `Stacks.SheafInternalHom.monoidalCategory` is obtained
by localizing the sectionwise monoidal product of presheaves of modules at the local
isomorphisms, so the object `F ⊗ G` is not given by a formula. This file identifies it with the
sheafification of the sectionwise tensor product, and describes the resulting comparison from the
sectionwise tensor product of the underlying presheaves into the sections of `F ⊗ G`.

## Main definitions

* `Stacks.SectionTensorFormula.tensorSheafIsoTensorObj`: the isomorphism between the native sheaf
  tensor `Stacks.SheafOfModules.Tensor.sheafTensor` and `F ⊗ G`.
* `Stacks.SectionTensorFormula.toTensorSection`: the comparison morphism of presheaves of modules
  `F.val ⊗ G.val ⟶ (F ⊗ G).val`.

## Main results

* `Stacks.SectionTensorFormula.toTensorSection_app_apply`: the comparison is the sheafification
  unit followed by `tensorSheafIsoTensorObj`.
* `Stacks.SectionTensorFormula.isLocallySurjective_toSheafify_tensor` and
  `Stacks.SectionTensorFormula.isLocallyInjective_toSheafify_tensor`: the sheafification unit of
  the sectionwise tensor product is locally surjective and locally injective.

## Implementation notes

The tensor product of `CategoryTheory.LocalizedMonoidal` is defined through `Localization.lift₂`,
so it is not definitionally equal to the native sheaf tensor; the two are identified by an
isomorphism. That isomorphism is built from `CategoryTheory.Functor.Monoidal.μIso` for the monoidal
functor `Stacks.SheafOfModules.TensorSheafification.sheafify` and from
`Stacks.SheafInternalHom.sheafifyCounitIso`, which identifies `sheafify F.val` with `F`.

## References

* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open TopologicalSpace Opposite Stacks.SheafOfModules.TensorSheafification

universe w v u

namespace Stacks.SectionTensorFormula

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
  (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

/-! ### The identification of the localized tensor product -/

section Identification

variable (F G : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))

/-- The isomorphism between the native sheaf tensor `Stacks.SheafOfModules.Tensor.sheafTensor`,
the sheafification of the sectionwise tensor product of the underlying presheaves, and the
monoidal product `F ⊗ G` of `Stacks.SheafInternalHom.monoidalCategory`. -/
def tensorSheafIsoTensorObj :
    ((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj F).obj G ≅
      @MonoidalCategoryStruct.tensorObj _ _
        (Stacks.SheafInternalHom.monoidalCategory 𝒪 h𝒪).toMonoidalCategoryStruct F G :=
  (Functor.Monoidal.μIso (sheafify 𝒪 h𝒪) F.val G.val).symm ≪≫
    @tensorIso _ _ (Stacks.SheafInternalHom.monoidalCategory 𝒪 h𝒪) _ _ _ _
      ((Stacks.SheafInternalHom.sheafifyCounitIso 𝒪 h𝒪).app F)
      ((Stacks.SheafInternalHom.sheafifyCounitIso 𝒪 h𝒪).app G)

/-- `tensorSheafIsoTensorObj` on underlying presheaves of modules. -/
def tensorPresheafIsoTensorObj :
    (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj F).obj
        G).val ≅
      (F ⊗ G).val :=
  (SheafOfModules.forget _).mapIso (tensorSheafIsoTensorObj 𝒪 h𝒪 F G)

/-- The forward map of `tensorPresheafIsoTensorObj` is the underlying morphism of presheaves of
the forward map of `tensorSheafIsoTensorObj`. -/
@[simp]
lemma tensorPresheafIsoTensorObj_hom :
    (tensorPresheafIsoTensorObj 𝒪 h𝒪 F G).hom = (tensorSheafIsoTensorObj 𝒪 h𝒪 F G).hom.val :=
  rfl

/-! ### The comparison on sections -/

/-- The comparison morphism from the sectionwise tensor product of the underlying presheaves of
`F` and `G` to the underlying presheaf of `F ⊗ G`: the sheafification unit followed by
`tensorSheafIsoTensorObj`. Over an object `U` it is a map
`F.val.obj U ⊗ G.val.obj U ⟶ (F ⊗ G).val.obj U`. -/
def toTensorSection : F.val ⊗ G.val ⟶ (F ⊗ G).val :=
  toSheafify 𝒪 h𝒪 (F.val ⊗ G.val) ≫ (tensorSheafIsoTensorObj 𝒪 h𝒪 F G).hom.val

/-- `toTensorSection` sends a section of the sectionwise tensor product to the image under
`tensorSheafIsoTensorObj` of its image under the sheafification unit. -/
lemma toTensorSection_app_apply (U : Cᵒᵖ) (t : (F.val ⊗ G.val).obj U) :
    (toTensorSection 𝒪 h𝒪 F G).app U t =
      (tensorSheafIsoTensorObj 𝒪 h𝒪 F G).hom.val.app U
        ((toSheafify 𝒪 h𝒪 (F.val ⊗ G.val)).app U t) :=
  rfl

/-- The sheafification unit of `F.val ⊗ G.val` composed with `tensorSheafIsoTensorObj` is
`toTensorSection`. -/
lemma toSheafify_comp_eq_toTensorSection :
    toSheafify 𝒪 h𝒪 (F.val ⊗ G.val) ≫ (tensorSheafIsoTensorObj 𝒪 h𝒪 F G).hom.val =
      toTensorSection 𝒪 h𝒪 F G :=
  rfl

/-- The sheafification unit `Stacks.SheafOfModules.TensorSheafification.toSheafify` at a presheaf
of modules `P` is `PresheafOfModules.toSheafify` applied to `CategoryTheory.toSheafify`. -/
lemma toSheafify_eq (P : PresheafOfModules.{w} (structureSheaf 𝒪 h𝒪).obj) :
    toSheafify 𝒪 h𝒪 P =
      PresheafOfModules.toSheafify (𝟙 (structureSheaf 𝒪 h𝒪).obj)
        (CategoryTheory.toSheafify J P.presheaf) :=
  rfl

/-! ### Local bijectivity of the sheafification unit -/

/-- The sheafification unit of the sectionwise tensor product is locally surjective. -/
instance isLocallySurjective_toSheafify_tensor :
    PresheafOfModules.IsLocallySurjective J (toSheafify 𝒪 h𝒪 (F.val ⊗ G.val)) :=
  inferInstanceAs (PresheafOfModules.IsLocallySurjective J
    (PresheafOfModules.toSheafify (𝟙 (structureSheaf 𝒪 h𝒪).obj)
      (CategoryTheory.toSheafify J (F.val ⊗ G.val).presheaf)))

/-- The sheafification unit of the sectionwise tensor product is locally injective. -/
instance isLocallyInjective_toSheafify_tensor :
    PresheafOfModules.IsLocallyInjective J (toSheafify 𝒪 h𝒪 (F.val ⊗ G.val)) :=
  inferInstanceAs (PresheafOfModules.IsLocallyInjective J
    (PresheafOfModules.toSheafify (𝟙 (structureSheaf 𝒪 h𝒪).obj)
      (CategoryTheory.toSheafify J (F.val ⊗ G.val).presheaf)))

end Identification

end Stacks.SectionTensorFormula

end
