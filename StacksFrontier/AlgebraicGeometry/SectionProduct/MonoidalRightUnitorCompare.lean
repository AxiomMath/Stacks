module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalTypesOfModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalInduced
public import StacksFrontier.AlgebraicGeometry.SectionProduct.MonoidalUnitBridge
public import StacksFrontier.AlgebraicGeometry.TensorSectionNonvanishing.Basic

/-!
# The unit constraints of the tensor product sheaf, in the localized monoidal structure

Let `X` be a scheme. Multiplication by a global section of an `𝒪_X`-module `L` in the second
factor can be written in two ways, and they use different right unit constraints:

* with the *fixed* unit constraint of the tensor product sheaf,
  `Stacks.SheafOfModules.Invertible.tensorProductRightUnitor`, whose unit object is Mathlib's
  `SheafOfModules.unit X.ringCatSheaf`;
* with the right unitor of the *localized* monoidal structure
  `Stacks.SheafInternalHom.schemeMonoidalCategory`, whose unit object is the sheafification of
  the presheaf unit, and which is the spelling
  `Stacks.TensorSectionNonvanishing.mulRight` — hence clause 2 of [Stacks, Tag 01CY] — is
  stated at.

This file identifies the two, so that a statement written with the fixed unit constraint can be
fed to the monicity criterion stated with the localized one.

## Main results

* `AlgebraicGeometry.leftUnitor_sheafOfModulesMonoidal_hom` and
  `AlgebraicGeometry.rightUnitor_sheafOfModulesMonoidal_hom`: the two localized monoidal
  structures on sheaves of modules have the same unitors up to the comparison of their units.
  The unitors are the only place the two structures differ, so these are what carries a
  statement about one of them to the other.
* `AlgebraicGeometry.tensorProductRightUnitor_inv_comp_tensorObjIso_inv`: the right unit
  constraint of the tensor product sheaf, read in the monoidal structure
  `Stacks.TensorSectionNonvanishing.mulRight` is stated for.
* `AlgebraicGeometry.tensorProductRightUnitor_inv_comp_sheafifyWhiskerLeft`: **multiplication by
  a global section is the same arrow in the two monoidal structures.**

## Implementation notes

Every proof here is a term or a rewrite behind a helper lemma: a goal mentioning both unit
objects at once is not type-correct at the reducible transparency `rw` checks its motive at,
which is why the two private lemmas `comp_eq_comp_id_comp` and `comp_reassoc_of_eq` exist.

## References

* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open TopologicalSpace Opposite

universe v u w

attribute [local instance_reducible] Stacks.SheafOfModules.TensorSheafification.structureSheaf

/-- **The two comparison isomorphisms between the localized tensor product and the tensor product
sheaf of Stacks Tag 01CA agree.** `AlgebraicGeometry.SheafOfModules.tensorIso` is a component of
the comparison natural isomorphism `Stacks.SheafInternalHom.tensorLeftIso`, and
`Stacks.SheafOfModules.tensorObjIso` is the monoidality isomorphism of sheafification read at a
pair of sheaves; their forward maps agree by `rfl`, so the isomorphisms agree. -/
theorem Stacks.AlgebraicGeometry.ThetaMul.tensorIso_eq
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u})
    (h𝒪 : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪))
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    (F G : SheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)) :
    AlgebraicGeometry.SheafOfModules.tensorIso 𝒪 h𝒪 F G =
      Stacks.SheafOfModules.tensorObjIso 𝒪 h𝒪 F G := by
  apply Iso.ext
  rw [Stacks.SheafOfModules.tensorObjIso_hom_eq]
  rfl

namespace AlgebraicGeometry

section MonoidalCompare

/-- Inserting an arrow known to be an identity into a composite. Isolated as a lemma because the
goal below mentions two monoidal structures at once and is not type-correct at the transparency
`rw` checks its motive at. -/
private theorem comp_eq_comp_id_comp {C : Type*} [Category C] {A B D : C} (a : A ⟶ B)
    (i : B ⟶ B) (hi : i = 𝟙 B) (r : B ⟶ D) : a ≫ r = a ≫ i ≫ r := by
  rw [hi, Category.id_comp]

/-- Rebracketing a four-fold composite after rewriting its first two factors. -/
private theorem comp_reassoc_of_eq {C : Type*} [Category C] {A B B' D E G : C}
    (a : A ⟶ B) (b : B ⟶ D) (p : A ⟶ B') (q : B' ⟶ D) (c : D ⟶ E) (d : E ⟶ G)
    (h : a ≫ b = p ≫ q) : a ≫ b ≫ c ≫ d = (p ≫ q ≫ c) ≫ d := by
  rw [← Category.assoc a b, h]
  simp only [Category.assoc]

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso Stacks.SheafInternalHom.isLocalization_sheafify
  Stacks.SheafInternalHom.monoidalCategory Stacks.SheafInternalHom.sheafifyMonoidal
  Stacks.SheafInternalHom.schemeMonoidalCategory

open Stacks.SectionProduct (hStruct ofUnitHom)
open Stacks.SheafOfModules (tensorObjIso sheafifyWhiskerLeft)
open Stacks.SheafOfModules.Invertible (tensorProductRightUnitor)

section Unitors

open Stacks.SheafOfModules.TensorSheafification

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
  (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **The two localized monoidal structures on sheaves of `𝒪`-modules have the same left unitor
up to the comparison of their units.** `Stacks.SheafOfModules.monoidalCategory` and
`Stacks.SheafInternalHom.monoidalCategory` localize the same monoidal structure on presheaves of
modules along the same sheafification; they differ only in the chosen unit object, the first
taking `SheafOfModules.unit` and the second the sheafification of the presheaf unit. The left
unitor of a localized monoidal structure is whiskering by the inverse of that choice followed by
a factor that does not depend on it, so the two unitors differ by
`AlgebraicGeometry.SheafOfModules.unitIso` whiskered into the first variable. -/
theorem leftUnitor_sheafOfModulesMonoidal_hom
    (M : _root_.SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) :
    (@MonoidalCategoryStruct.leftUnitor _ _
      (Stacks.SheafOfModules.monoidalCategory 𝒪 h𝒪).toMonoidalCategoryStruct M).hom
      = (AlgebraicGeometry.SheafOfModules.unitIso 𝒪 h𝒪).inv ▷ M ≫ (λ_ M).hom := by
  exact comp_eq_comp_id_comp _ _ (MonoidalCategory.id_whiskerRight _ M) _

end Unitors

variable (X : Scheme.{u}) (M : X.Modules)

/-- **The two localized monoidal structures on `𝒪_X`-modules have the same right unitor up to
the comparison of their units.** `Stacks.SheafOfModules.monoidalCategory` and
`Stacks.SheafInternalHom.monoidalCategory` localize the same monoidal structure on presheaves of
modules along the same sheafification; they differ only in the chosen unit object, the first
taking `SheafOfModules.unit` and the second the sheafification of the presheaf unit. The right
unitor of a localized monoidal structure is whiskering by the inverse of that choice followed by
a factor that does not depend on it, so the two unitors differ by
`AlgebraicGeometry.SheafOfModules.unitIso` whiskered into the second variable. -/
theorem rightUnitor_sheafOfModulesMonoidal_hom :
    (@MonoidalCategoryStruct.rightUnitor _ _
      (Stacks.SheafOfModules.monoidalCategory X.presheaf
        (hStruct X)).toMonoidalCategoryStruct M).hom
      = M ◁ (AlgebraicGeometry.SheafOfModules.unitIso X.presheaf (hStruct X)).inv ≫
        (ρ_ M).hom := by
  exact comp_eq_comp_id_comp _ _ (MonoidalCategory.whiskerLeft_id M _) _

/-- **The right unit constraint of the tensor product sheaf, read in the monoidal structure
`Stacks.TensorSectionNonvanishing.mulRight` is stated for.** Composing the comparison
`M ⊗ 𝒪 ≅ M ⊗ₛ 𝒪` with the fixed unit constraint of [Stacks, Tag 01CU] gives the right unitor of
`Stacks.SheafOfModules.monoidalCategory`, by
`Stacks.SheafOfModules.tensorObjIso_rightUnitor`, and that is the right unitor of
`Stacks.SheafInternalHom.monoidalCategory` preceded by the unit comparison. -/
theorem tensorProductRightUnitor_inv_comp_tensorObjIso_inv :
    (tensorProductRightUnitor X.presheaf (hStruct X) M).inv ≫
      (tensorObjIso X.presheaf (hStruct X) M (SheafOfModules.unit _)).inv
      = (ρ_ M).inv ≫ M ◁ (AlgebraicGeometry.SheafOfModules.unitIso X.presheaf (hStruct X)).hom :=
  congrArg Iso.inv (Iso.ext
    ((Stacks.SheafOfModules.tensorObjIso_rightUnitor X.presheaf (hStruct X) M).trans
      (rightUnitor_sheafOfModulesMonoidal_hom X M)) :
      (tensorObjIso X.presheaf (hStruct X) M (SheafOfModules.unit _) ≪≫
        tensorProductRightUnitor X.presheaf (hStruct X) M) =
        (MonoidalCategory.whiskerLeftIso M
          (AlgebraicGeometry.SheafOfModules.unitIso X.presheaf (hStruct X)).symm ≪≫ ρ_ M))

/-- **Multiplication by a global section is the same arrow in the two monoidal structures.** The
right unit constraint of the tensor product sheaf followed by whiskering a morphism
`g : 𝒪_X ⟶ L` out of Mathlib's unit into the second variable is
`Stacks.TensorSectionNonvanishing.mulRight` of the re-seated section, followed by the comparison
of the monoidal tensor product with the tensor product sheaf. -/
theorem tensorProductRightUnitor_inv_comp_sheafifyWhiskerLeft {L : X.Modules}
    (g : SheafOfModules.unit X.ringCatSheaf ⟶ L) :
    (tensorProductRightUnitor X.presheaf (hStruct X) M).inv ≫
        sheafifyWhiskerLeft X.presheaf (hStruct X) M g
      = Stacks.TensorSectionNonvanishing.mulRight M (ofUnitHom g) ≫
        (Stacks.AmplePullbackPart1.tensorIsoTensorModules X M L).hom := by
  have h1 := congrArg
    (fun k => (tensorProductRightUnitor X.presheaf (hStruct X) M).inv ≫ k)
    (Stacks.SheafOfModules.sheafifyWhiskerLeft_eq_comparison X.presheaf (hStruct X) M g)
  have h2 := comp_reassoc_of_eq (tensorProductRightUnitor X.presheaf (hStruct X) M).inv
    (tensorObjIso X.presheaf (hStruct X) M (SheafOfModules.unit _)).inv
    (ρ_ M).inv (M ◁ (AlgebraicGeometry.SheafOfModules.unitIso X.presheaf (hStruct X)).hom)
    (M ◁ g) (tensorObjIso X.presheaf (hStruct X) M L).hom
    (tensorProductRightUnitor_inv_comp_tensorObjIso_inv X M)
  have h3 := congrArg
    (fun k => k ≫ (tensorObjIso X.presheaf (hStruct X) M L).hom)
    (Stacks.SectionProduct.mulRight_ofUnitHom M g).symm
  have comparisonHom : (tensorObjIso X.presheaf (hStruct X) M L).hom =
      (Stacks.AmplePullbackPart1.tensorIsoTensorModules X M L).hom :=
    (congrArg Iso.hom (Stacks.AlgebraicGeometry.ThetaMul.tensorIso_eq
      X.presheaf (hStruct X) M L)).symm
  exact h1.trans (h2.trans (h3.trans (congrArg
    (fun comparison => Stacks.TensorSectionNonvanishing.mulRight M (ofUnitHom g) ≫ comparison)
    comparisonHom)))

end MonoidalCompare

end AlgebraicGeometry

end
