module

public import StacksFrontier.CategoryTheory.Monoidal.Reseat
public import StacksFrontier.CategoryTheory.Monoidal.ReseatConstraints
public import StacksFrontier.AlgebraicGeometry.ProjBundleInverseBaseChange.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalSheafTensor

/-!
# The two monoidal structures of Tag 0B3V's inverse line are one re-seating apart

The conormal construction of Tag 0B3V uses two monoidal structures on the sheaves of modules of a
scheme, and the inverse-line factor of its base-change square is stated over both:

* `Stacks.SheafInternalHom.monoidalCategory`, over which Tag 01CU's trivialisations
  `Stacks.ProjBundleInverseBaseChange.negOneMulIso` and `negOneMulIso'` and hence the only pin of
  `Stacks.ProjBundleInverseBaseChange.inverseQuotientBaseChangeIso` are stated;
* `SheafOfModules.monoidalCategorySheafTensor`, over which
  `Stacks.ProjectiveBundleConormal.invertibleEvaluation`,
  `Stacks.Monoidal.isoOfTensorInverseBraided` and every `⊗ₘ` of the conormal construction are
  taken.

Ascribing a morphism of one at the other is a *type* mismatch — the tensor products and the unit
objects are different objects — so an equation across them is not even well-formed. This file
supplies the comparison, and the measurement that makes it cheap: **the second structure is
literally a re-seating of the first.**

## Main results

* `SheafOfModules.monoidalCategorySheafTensor_eq_reseat`: for a scheme `X`,
  `SheafOfModules.monoidalCategorySheafTensor X.toRingedSpace.sheaf` is
  `CategoryTheory.MonoidalCategory.reseat (SheafOfModules.sheafTensorNatIso …)
  (SheafOfModules.unitIso …)` taken over
  `Stacks.SheafInternalHom.monoidalCategory X.presheaf (isSheaf_structureRingPresheaf X)`, **by
  `rfl`**. So the comparison of the two structures is already in the repository:
  `CategoryTheory.MonoidalCategory.reseatIso` on the tensor products and
  `SheafOfModules.unitIso` on the units, with the whole of
  `StacksFrontier.CategoryTheory.Monoidal.Reseat`'s API relating their constraints.
* `Stacks.TensorPowers.reseatTensorInverse`: a two-sided tensor inverse carried across a
  re-seating. The inverse object is unchanged; each trivialisation is conjugated by `reseatIso`
  on its source and by `ε` on its target.
* `Stacks.TensorPowers.invIso_reseatTensorInverse`: **the bridge.** The canonical comparison
  `Stacks.TensorPowers.TensorInverse.invIso` of two tensor inverses is *unchanged* by
  re-seating. Every `reseatIso` and every `ε` cancels: the five factors of `invIso` are a
  unitor, a left whiskering, an associator, a right whiskering and a unitor, and the re-seated
  form of each is the given one conjugated by exactly the comparisons that the neighbouring two
  factors contribute in the opposite direction.
* `CategoryTheory.MonoidalCategory.reseat_tensorObj`,
  `reseat_leftUnitor_hom`, `reseat_associator_inv`: three of the four constraint identities of a
  re-seating that `Reseat.lean` does not record. That file has `reseat_associator` for the
  forward map only, and no unitor companion; all three here are `rfl`, and the parenthesisation
  is the one `CategoryTheory.Iso.trans_hom` and `Iso.trans_inv` produce from `reseatStruct`, not
  the associativity-normalised one. The fourth, the backward right unitor, is
  `CategoryTheory.MonoidalCategory.reseat_rightUnitor_inv` of
  `StacksFrontier.CategoryTheory.Monoidal.ReseatConstraints`, imported here: it states the same
  identity with the unit comparison whiskered rather than tensored with an identity, which is
  the form `id_tensorHom` normalises to anyway.

## What this does and does not reach

With `invIso_reseatTensorInverse` the inverse-line comparison of Tag 0B3V can be *stated* at the
monoidal structure of the conormal construction. What it does not yet reach is the
hypothesis `hinv` of `Stacks.ProjectiveBundleConormal.sourceCoherence`, and the obstruction
there is not a monoidal structure at all.

`Stacks.ProjBundleInverseBaseChange.inverseQuotientBaseChangeIso` is
`TensorInverse.invIso` of two tensor inverses whose trivialisations are `negOneMulIso` and
`negOneMulIso'`, and the pin it satisfies — `inverseQuotientBaseChangeIso_evaluation`, which is
`TensorInverse.invIso_inv_evaluation` — therefore transports to the re-seated structure through
this file as a pin against the *conjugated* trivialisations
`(reseatIso …).symm ≪≫ negOneMulIso' … ≪≫ SheafOfModules.unitIso …`. The other side of `hinv`
runs through `Stacks.ProjectiveBundleConormal.inverseTwistBundleBaseChangeIso`, pinned by
`inverseTwistBundleBaseChangeIso_tensorHom_comp` against
`Stacks.ProjectiveBundleConormal.invertibleEvaluation`, which is
`Stacks.SheafOfModules.Invertible.mulNegOneIso`. So `hinv` by
`Stacks.Monoidal.eq_of_tensorHom_comp_eq` needs the two sides pinned against *one* pairing, and
what is left owed is exactly

**the identification of the conjugated `negOneMulIso'` with `mulNegOneIso`** — two
independently constructed trivialisations of `L ⊗ L^{⊗ -1}`, one Tag 01CU's successor
comparison read through the braiding, the other its `tensorPowerOneIso` conjugate. That is a
statement about Tag 01CU's multiplication, not about a monoidal structure.

**That identification is proved**, in the sibling module
`StacksFrontier.AlgebraicGeometry.ProjBundleInverseBaseChange.MulNegOne`:
`Stacks.ProjBundleInverseBaseChange.negOneMulIso'_eq`. **No section is involved**: the statement
on sections,
`Stacks.ProjectiveBundleConormal.sectionMulNegOne_eq_negOneMulIso` together with
`Stacks.SheafOfModules.Invertible.mulNegOneIso_toSheafify`, is not used. The whole
content is the naturality of the braiding of the tensor product sheaf
(`Stacks.SheafOfModules.Invertible.tensorProductBraiding_naturality`), which is one application
of `CategoryTheory.BraidedCategory.braiding_naturality` to the underlying presheaves of modules.

**What `hinv` still needs is a different piece.** It is neither a
trivialisation nor a monoidal structure: it is the *handedness* of the pin that
`TensorInverse.invIso` satisfies. `invIso h k` contracts with `h.mulIso'` on the left and
`k.mulIso` on the right, so its only pins — `TensorInverse.invIso_hom_evaluation` and
`invIso_inv_evaluation` — are the triangle on `(h⁻¹ ⊗ L) ⊗ k⁻¹`, in
whiskering-associator-unitor form. What `Stacks.Monoidal.eq_of_tensorHom_comp_eq` consumes is
the single-tensor form `(e.hom ⊗ₘ φ.hom) ≫ hy.hom = hx.hom`, with both pairings in the order
`positive ⊗ inverse`; and `Stacks.Monoidal.isoOfTensorInverse_tensorHom_comp_of_mulIso`, which
supplies exactly that, is stated for `Stacks.Monoidal.isoOfTensorInverse` — a chain of the
*opposite* handedness, built from `hx : A ⊗ X ≅ 𝟙` and `hy : Y ⊗ B ≅ 𝟙`. So it does not apply
to `invIso`, and no single-tensor pin for `invIso` exists in the repository. Deriving one needs
the compatibility of `mulIso` with `mulIso'` — the snake
`(α_ L h.inv L).hom ≫ L ◁ h.mulIso'.hom ≫ (ρ_ L).hom = h.mulIso.hom ▷ L ≫ (λ_ L).hom` — for
*both* tensor inverses, which `Stacks.TensorPowers.TensorInverse` does not carry as a field and
which for `negOneTensorInverse` holds only through the braiding
(`Stacks.Monoidal.braiding_eval_snake`, `Stacks.GradedSections.HasTrivialSelfBraiding`). That is
new monoidal algebra rather than a translation.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory MonoidalCategory AlgebraicGeometry
open Stacks.SheafInternalHom (isSheaf_structureRingPresheaf)

universe v u

namespace CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {T : C ⥤ C ⥤ C} {U : C}

/-- The tensor product of the re-seated structure on a pair of objects is the prescribed
bifunctor's value there. `CategoryTheory.MonoidalCategory.curriedTensor_reseat` says this of the
bifunctors; this is the objectwise form, which is what a statement mixing the two structures
needs in order to name the same object twice. -/
theorem reseat_tensorObj (e : curriedTensor C ≅ T) (ε : 𝟙_ C ≅ U) (X Y : C) :
    @MonoidalCategoryStruct.tensorObj C _ (reseat e ε).toMonoidalCategoryStruct X Y =
      (T.obj X).obj Y := rfl

/-- **The left unit constraint of the re-seated structure is the given one**, with the unit
objects compared by `ε` and the tensor products by `reseatIso`. The companion of
`CategoryTheory.MonoidalCategory.reseat_associator`, which that file records for the associator
alone. -/
theorem reseat_leftUnitor_hom (e : curriedTensor C ≅ T) (ε : 𝟙_ C ≅ U) (X : C) :
    (@leftUnitor C _ (reseat e ε).toMonoidalCategoryStruct X).hom =
      ((reseatIso e U X).inv ≫ (ε.inv ⊗ₘ 𝟙 X)) ≫ (λ_ X).hom := rfl

/-- `CategoryTheory.MonoidalCategory.reseat_associator` in the backward direction, which is the
direction a threefold product is read through. -/
theorem reseat_associator_inv (e : curriedTensor C ≅ T) (ε : 𝟙_ C ≅ U) (X Y Z : C) :
    (@associator C _ (reseat e ε).toMonoidalCategoryStruct X Y Z).inv =
      (((reseatIso e X ((T.obj Y).obj Z)).inv ≫ (𝟙 X ⊗ₘ (reseatIso e Y Z).inv)) ≫
          (α_ X Y Z).inv) ≫
        (((reseatIso e X Y).hom ⊗ₘ 𝟙 Z) ≫ (reseatIso e ((T.obj X).obj Y) Z).hom) := rfl

/-- `CategoryTheory.MonoidalCategory.reseat_whiskerLeft` with the re-seated structure named by
`@`-application instead of left to unfold to `T`. Only `simp` needs this: the two sides of
`reseat_whiskerLeft` are definitionally these, but a goal produced by the re-seated structure
carries `MonoidalCategoryStruct.whiskerLeft` as its head and does not match `(T.obj X).map`
syntactically. -/
private theorem reseat_whiskerLeft_eq (e : curriedTensor C ≅ T) (ε : 𝟙_ C ≅ U) (X : C)
    {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) :
    @MonoidalCategoryStruct.whiskerLeft C _ (reseat e ε).toMonoidalCategoryStruct X Y₁ Y₂ g =
      (reseatIso e X Y₁).inv ≫ (X ◁ g) ≫ (reseatIso e X Y₂).hom :=
  reseat_whiskerLeft e X g

/-- `CategoryTheory.MonoidalCategory.reseat_whiskerRight` with the re-seated structure named by
`@`-application, for the reason `reseat_whiskerLeft_eq` is. -/
private theorem reseat_whiskerRight_eq (e : curriedTensor C ≅ T) (ε : 𝟙_ C ≅ U) {X₁ X₂ : C}
    (f : X₁ ⟶ X₂) (Y : C) :
    @MonoidalCategoryStruct.whiskerRight C _ (reseat e ε).toMonoidalCategoryStruct X₁ X₂ f Y =
      (reseatIso e X₁ Y).inv ≫ (f ▷ Y) ≫ (reseatIso e X₂ Y).hom :=
  reseat_whiskerRight e f Y

end CategoryTheory.MonoidalCategory

namespace Stacks.TensorPowers

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {T : C ⥤ C ⥤ C} {U : C}

/-- **A two-sided tensor inverse carried across a re-seating.** The inverse object is the same;
each of the two trivialisations is conjugated by `reseatIso` on its source — the re-seated
tensor product is the prescribed bifunctor, not the given `⊗` — and by `ε` on its target, the
re-seated unit being the prescribed `U`. -/
def reseatTensorInverse (e : curriedTensor C ≅ T) (ε : 𝟙_ C ≅ U) {L : C}
    (h : TensorInverse L) : @TensorInverse C _ (reseat e ε) L :=
  @TensorInverse.mk C _ (reseat e ε) L h.inv
    ((reseatIso e L h.inv).symm ≪≫ h.mulIso ≪≫ ε)
    ((reseatIso e h.inv L).symm ≪≫ h.mulIso' ≪≫ ε)

/-- **The comparison of two tensor inverses is unchanged by re-seating.** For two two-sided
tensor inverses of one object, the canonical isomorphism
`Stacks.TensorPowers.TensorInverse.invIso` computed in a re-seated monoidal structure, from the
transported inverses, is the *same morphism* as the one computed in the given structure.

This is the bridge between the two monoidal structures of Tag 0B3V's inverse line, and it is an
equality rather than a conjugation because every comparison cancels. `invIso` is a right
unitor, a left whiskering, an associator, a right whiskering and a left unitor; re-seating
replaces each by the given one conjugated by `reseatIso` on both sides and by `ε` where the unit
occurs (`reseat_rightUnitor_inv`, `reseat_whiskerLeft_eq`, `reseat_associator_inv`,
`reseat_whiskerRight_eq`, `reseat_leftUnitor_hom`), and the conjugating factor each step
contributes on its right is exactly the one the next step contributes on its left. The two `ε`
cancel against the two that `reseatTensorInverse` inserts into the trivialisations. -/
theorem invIso_reseatTensorInverse (e : curriedTensor C ≅ T) (ε : 𝟙_ C ≅ U) {L : C}
    (h k : TensorInverse L) :
    @TensorInverse.invIso C _ (reseat e ε) L
        (reseatTensorInverse e ε h) (reseatTensorInverse e ε k) =
      TensorInverse.invIso h k := by
  refine Iso.ext ?_
  simp only [TensorInverse.invIso, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv,
    whiskerLeftIso_hom, whiskerRightIso_hom, reseatTensorInverse, reseat_rightUnitor_inv,
    reseat_leftUnitor_hom, reseat_associator_inv, reseat_whiskerLeft_eq, reseat_whiskerRight_eq]
  simp only [tensorUnit_reseat, reseat_tensorObj]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, id_tensorHom, tensorHom_id]
  simp only [← whiskerLeft_comp_assoc, ← comp_whiskerRight_assoc]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

end Stacks.TensorPowers

namespace SheafOfModules

/-- **The monoidal structure of Tag 0B3V's conormal construction is a re-seating of the one its
inverse line is stated over**, on the nose.

`SheafOfModules.monoidalCategorySheafTensor` is built as a re-seating, and the structure it
re-seats is `SheafOfModules.monoidalCategory`, the localization of the sectionwise
tensor product along sheafification with the comparison `ε` of
`CategoryTheory.Localization.Monoidal` taken to be `Iso.refl`. So is
`Stacks.SheafInternalHom.monoidalCategory`: same localizing class, same localization functor,
same `Iso.refl`. The two are therefore the same term, and this is the identification that makes
`StacksFrontier.CategoryTheory.Monoidal.Reseat`'s whole API — in particular
`CategoryTheory.MonoidalCategory.reseatIso` and `SheafOfModules.unitIso` — the comparison of the
tensor products and of the units of the two structures that the inverse line is stated over.

The record this replaces said that a comparison isomorphism of the two monoidal structures had
to be built. It does not: the repository already contains it, and the two structures are one
`reseat` apart rather than merely isomorphic. -/
theorem monoidalCategorySheafTensor_eq_reseat (X : Scheme.{u}) :
    monoidalCategorySheafTensor X.toRingedSpace.sheaf =
      @reseat _ _
        (Stacks.SheafInternalHom.monoidalCategory X.presheaf (isSheaf_structureRingPresheaf X)) _ _
        (sheafTensorNatIso X.toRingedSpace.sheaf) (unitIso X.toRingedSpace.sheaf) := rfl

/-- The structure `SheafOfModules.monoidalCategorySheafTensor` re-seats is the structure
`Stacks.ProjBundleInverseBaseChange.negOneMulIso` and `negOneMulIso'` are stated over, read at
the scheme spelling. This is the content of
`SheafOfModules.monoidalCategorySheafTensor_eq_reseat` separated from the re-seating, since it
is the half that is about the two *spellings* `Stacks.SheafOfModules.Tensor.ringSheaf` and
`Stacks.SheafOfModules.TensorSheafification.structureSheaf` of one sheaf of rings. -/
theorem sheafInternalHom_monoidalCategory_eq (X : Scheme.{u}) :
    Stacks.SheafInternalHom.monoidalCategory X.presheaf (isSheaf_structureRingPresheaf X) =
      monoidalCategory X.toRingedSpace.sheaf := rfl

end SheafOfModules

end
