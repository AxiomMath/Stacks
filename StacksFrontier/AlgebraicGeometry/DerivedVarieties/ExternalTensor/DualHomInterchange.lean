module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OnSpaceMonoidalBraided
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.ExternalTensor.DualHomPure
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.ExternalTensor.Monoidal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrictSheafTensorAgree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackSheafTensorBraided
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafCoherence

/-!
# The value of the duality bijection at a pure map, through the interchange

`StacksFrontier.AlgebraicGeometry.DerivedVarieties.ExternalTensor.DualHomPure` computes the value of

`Hom_{𝒪_{X ×_S Y}}(ℰ ⊠ 𝒢, ℱ) ≃ Γ(X ×_S Y, ℱ ⊗ (ℰ^∨ ⊠ 𝒢^∨))`

at a pure map `a ⊠ b`, as the *nested* product
`CategoryTheory.nestedTensorSection` of the two one-factor duality sections followed by the
symmetry `Stacks.SheafOfModules.tensorSheafBraiding` of the tensor product sheaf, and — through
`CategoryTheory.nestedTensorSection_eq_swappedTensorSection` — as their monoidal product read
through two symmetries.  What it could not do is name those two symmetries: the interchange
`AlgebraicGeometry.tensorSheafInterchange`, which is what a Künneth statement consumes, is built
from the associator and the braiding of `AlgebraicGeometry.ringedSpaceMonoidal`, the structure of
[Stacks, Tag 01CA] obtained by *re-seating* the localized one, while the duality statements live
at `Stacks.SheafOfModules.OnSpace.monoidal`, the structure of the same tag obtained by *inducing*
along a comparison isomorphism, which carried no braiding and whose associator was not identified
with any other presentation.

`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OnSpaceMonoidalBraided` supplies the braiding.
This file supplies the identification of the interchange and draws the consequence: **the value at
a pure map is the monoidal product of the two one-factor duality sections followed by the
interchange**, with no bare symmetry left in the statement.

**The last step, and the shape of its statement.**  `externalTensorProductTensorIso` goes from
`(ℰ ⊠ 𝒢) ⊗ (ℰ' ⊠ 𝒢')` to `(ℰ ⊗ ℰ') ⊠ (𝒢 ⊗ 𝒢')`, which is the interchange with the middle two
factors in the *other* order from the one the duality section needs; the two are mutually inverse
because the braiding is a symmetry, which is
`AlgebraicGeometry.tensorSheafInterchange_hom_eq_inv`.  The statement at
`externalTensorProductTensorIso` is therefore phrased as a composite — the value *followed by*
the interchange — rather than with an inverse: writing the inverse out needs the *nested*
comparison of `AlgebraicGeometry.externalTensorProduct f g ℰ 𝒢` with the tensor product sheaf of
the two pullbacks inside a twice-nested tensor product sheaf, and asking the elaborator for that
exhausts the heartbeat budget, as the implementation notes of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAssociatorRingedSpace` record.

## Main results

* `CategoryTheory.nestedTensorSection_comp_whiskerLeft_braiding_inv`: **in a braided category the
  nested product of two sections, read through the braiding of the second factor of the first
  section, is their monoidal product followed by `CategoryTheory.tensorμ`.**  This is the abstract
  half of the computation; it is the forward hexagon and coherence.
* `CategoryTheory.Functor.map_tensorμ` (and `…_aux`): **a braided monoidal functor carries the
  interchange to the interchange**, conjugated by its tensorators.
* `AlgebraicGeometry.tensorSheafInterchange_hom_eq_tensorμ`: the interchange of the tensor product
  sheaf is `CategoryTheory.tensorμ` of the structure it is built from,
  `AlgebraicGeometry.ringedSpaceMonoidal`.  This is its definition with the middle factor named.
* `AlgebraicGeometry.onSpace_associator_eq_strict`, `onSpace_whiskerLeft_eq_strict`,
  `onSpace_whiskerRight_eq_strict` and `onSpace_braiding_eq_strict`: **the structural morphisms of
  `Stacks.SheafOfModules.OnSpace.monoidal` are those of the strict monoidal structure of
  [Stacks, Tag 01CA]**, which is what identifies that structure with
  `AlgebraicGeometry.ringedSpaceMonoidal` — `AlgebraicGeometry.reseated_tensorμ_eq_onSpace`.
* `AlgebraicGeometry.tensorSheafInterchange_hom_eq`: **`AlgebraicGeometry.tensorSheafInterchange`
  is `CategoryTheory.tensorμ` of the monoidal structure of [Stacks, Tag 01CA]**, the structure the
  duality statements are phrased at.
* `AlgebraicGeometry.externalTensorDualTensorHomEquiv_externalTensorProductMap_interchange`:
  **the value of the duality bijection at a pure map `a ⊠ b` is the monoidal product of the
  duality section of `pr₁^*a` and that of `pr₂^*b`, followed by the interchange.**
* `CategoryTheory.tensorμ_comp_tensorμ` and
  `AlgebraicGeometry.tensorSheafInterchange_hom_eq_inv`: the interchange is inverse to the
  interchange with the middle two factors exchanged, the braiding being a symmetry.
* `AlgebraicGeometry.tensorSheafInterchange_comp_externalTensorProductTensorIso` and
  `AlgebraicGeometry.externalTensorDualTensorHomEquiv_externalTensorProductMap_tensorIso`: **the
  same value read through `AlgebraicGeometry.externalTensorProductTensorIso`** of
  [Stacks, Tag 0G46], up to the comparison of a pullback with a tensor product.

## Implementation notes

**Two re-seatings of one localization.** `AlgebraicGeometry.tensorSheafInterchange` is written
over `AlgebraicGeometry.ringedSpaceMonoidal`, which replaces the localized tensor product by the
tensor product sheaf along `SheafOfModules.sheafTensorNatIso`, and the duality statements over
`Stacks.SheafOfModules.OnSpace.monoidal`, which replaces it by the same sheaf along
`Stacks.SheafOfModules.OnSpace.sheafModuleTensorCompareIso`.  The two agree on the tensor product
of objects and on the unit by `rfl`, but they are not the same *term*, and a composite mixing them
is not type-correct at `implicit` transparency — whereupon `rw` and `simp` silently refuse to
fire.  The `onSpace_*_eq_strict` and `reseated_*_eq_onSpace` lemmas below are the translation,
routed through the third presentation `Stacks.PullbackGradedAlgebra.monoidalCategory` for which
the re-seated half is already proved, and every statement is written in one presentation
throughout.

**Why `tensorSheafInterchange_hom_eq_tensorμ` has its own section.** `rw` and `simp` synthesize
the instance arguments of a lemma rather than reading them off the term, so a lemma stated over
`[MonoidalCategory C]` — `CategoryTheory.MonoidalCategory.whiskerLeft_comp`, for instance — does
not fire on a goal written at a monoidal structure which is not the ambient instance.  That
statement is therefore proved in a section where `AlgebraicGeometry.ringedSpaceMonoidal` *is* the
ambient instance, and the rest in a section where
`Stacks.SheafOfModules.OnSpace.monoidal` is.

**Why `Functor.map_tensorμ_aux` writes its tensorator pairs out.** `monoidal` normalises a
composite of structural morphisms around a *fixed* sequence of non-structural factors; it does
not reorder them.  `CategoryTheory.MonoidalCategory.tensorHom_def` and `…tensorHom_def'` order
the two factors of a monoidal product differently, so the two sides of the identity have to be
written with the orders already matching.  The same statement with `⊗ₘ` is
`CategoryTheory.Functor.map_tensorμ`.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 0G46](https://stacks.math.columbia.edu/tag/0G46)
* [Stacks Project, Tag 0G0A](https://stacks.math.columbia.edu/tag/0G0A)
-/

@[expose] public noncomputable section

-- `AlgebraicGeometry.ringedSpaceMonoidal` is indexed by `X.sheaf : TopCat.Sheaf CommRingCat X`,
-- whose type is a definition for `Sheaf (Opens.grothendieckTopology X) CommRingCat`, and
-- `⟨X.presheaf, X.IsSheaf⟩` has its `property` field at `X.presheaf.IsSheaf` where the sheaf
-- structure wants `Presheaf.IsSheaf (JX X) X.presheaf`.  Both identifications hold by
-- definition but not at `implicit` transparency, so without these the statements below are not
-- type-correct for `rw` and `simp`.
-- `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrictSheafTensorAgree` does the same.
attribute [local implicit_reducible] TopCat.Sheaf TopCat.Presheaf.IsSheaf

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- **The nested product of two sections, read through the symmetry, is their monoidal product
followed by the interchange.** -/
theorem nestedTensorSection_comp_whiskerLeft_braiding_inv [BraidedCategory C] {A B D₀ E : C}
    (s : 𝟙_ C ⟶ A ⊗ B) (t : 𝟙_ C ⟶ D₀ ⊗ E) :
    nestedTensorSection s t ≫ (A ⊗ D₀) ◁ (β_ B E).inv =
      (λ_ (𝟙_ C)).inv ≫ (s ⊗ₘ t) ≫ tensorμ A B D₀ E := by
  rw [nestedTensorSection_eq_swappedTensorSection_braiding]
  dsimp only [swappedTensorSection]
  rw [BraidedCategory.braiding_tensor_right_hom, tensorμ]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [← Category.assoc,
    show (A ⊗ D₀) ◁ (β_ B E).inv = (whiskerLeftIso (A ⊗ D₀) (β_ B E)).inv from rfl,
    Iso.comp_inv_eq]
  change _ = _ ≫ (A ⊗ D₀) ◁ (β_ B E).hom
  monoidal

/-- A whiskered tensorator cancels its whiskered inverse. -/
@[reassoc]
theorem Functor.whiskerLeft_whiskerRight_μ_δ {D : Type*} [Category* D] [MonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] (T : D) (X Y : C) (S : D) :
    T ◁ Functor.LaxMonoidal.μ F X Y ▷ S ≫ T ◁ Functor.OplaxMonoidal.δ F X Y ▷ S = 𝟙 _ := by
  rw [← MonoidalCategory.whiskerLeft_comp, ← MonoidalCategory.comp_whiskerRight,
    Functor.Monoidal.μ_δ, MonoidalCategory.id_whiskerRight, MonoidalCategory.whiskerLeft_id]

/-- **A braided monoidal functor carries the interchange to the interchange**, conjugated by its
tensorators.  The two tensorator pairs are written out as whiskerings rather than as monoidal
products so that the five non-structural factors occur in the same order on the two sides, which
is what `monoidal` needs. -/
theorem Functor.map_tensorμ_aux {D : Type*} [Category* D] [MonoidalCategory D] [BraidedCategory C]
    [BraidedCategory D] (F : C ⥤ D) [F.Braided] (X₁ X₂ Y₁ Y₂ : C) :
    F.map (tensorμ X₁ X₂ Y₁ Y₂) =
      Functor.OplaxMonoidal.δ F (X₁ ⊗ X₂) (Y₁ ⊗ Y₂) ≫
        Functor.OplaxMonoidal.δ F X₁ X₂ ▷ F.obj (Y₁ ⊗ Y₂) ≫
          (F.obj X₁ ⊗ F.obj X₂) ◁ Functor.OplaxMonoidal.δ F Y₁ Y₂ ≫
            tensorμ (F.obj X₁) (F.obj X₂) (F.obj Y₁) (F.obj Y₂) ≫
              (F.obj X₁ ⊗ F.obj Y₁) ◁ Functor.LaxMonoidal.μ F X₂ Y₂ ≫
                Functor.LaxMonoidal.μ F X₁ Y₁ ▷ F.obj (X₂ ⊗ Y₂) ≫
                  Functor.LaxMonoidal.μ F (X₁ ⊗ Y₁) (X₂ ⊗ Y₂) := by
  simp only [tensorμ, Functor.map_comp, Category.assoc]
  simp only [Functor.Monoidal.map_whiskerLeft, Functor.Monoidal.map_whiskerRight,
    Functor.Monoidal.map_associator, Functor.Monoidal.map_associator_inv,
    Functor.map_braiding, Category.assoc, MonoidalCategory.whiskerLeft_comp,
    MonoidalCategory.comp_whiskerRight]
  simp only [Functor.Monoidal.μ_δ_assoc, Functor.Monoidal.whiskerLeft_μ_δ_assoc,
    Functor.whiskerLeft_whiskerRight_μ_δ_assoc]
  monoidal

/-- **A braided monoidal functor carries the interchange to the interchange**, conjugated by its
tensorators. -/
theorem Functor.map_tensorμ {D : Type*} [Category* D] [MonoidalCategory D] [BraidedCategory C]
    [BraidedCategory D] (F : C ⥤ D) [F.Braided] (X₁ X₂ Y₁ Y₂ : C) :
    F.map (tensorμ X₁ X₂ Y₁ Y₂) =
      Functor.OplaxMonoidal.δ F (X₁ ⊗ X₂) (Y₁ ⊗ Y₂) ≫
        (Functor.OplaxMonoidal.δ F X₁ X₂ ⊗ₘ Functor.OplaxMonoidal.δ F Y₁ Y₂) ≫
          tensorμ (F.obj X₁) (F.obj X₂) (F.obj Y₁) (F.obj Y₂) ≫
            (Functor.LaxMonoidal.μ F X₁ Y₁ ⊗ₘ Functor.LaxMonoidal.μ F X₂ Y₂) ≫
              Functor.LaxMonoidal.μ F (X₁ ⊗ Y₁) (X₂ ⊗ Y₂) := by
  rw [Functor.map_tensorμ_aux, tensorHom_def (Functor.OplaxMonoidal.δ F X₁ X₂)
      (Functor.OplaxMonoidal.δ F Y₁ Y₂),
    tensorHom_def' (Functor.LaxMonoidal.μ F X₁ Y₁) (Functor.LaxMonoidal.μ F X₂ Y₂)]
  simp only [Category.assoc]

/-- **In a symmetric category the interchange is inverse to the interchange with the two middle
factors exchanged.**  The symmetry is taken as an equation rather than as a
`CategoryTheory.SymmetricCategory` instance: the two braidings in play would otherwise have to be
the same instance, and the one at hand arrives as a `BraidedCategory`. -/
theorem tensorμ_comp_tensorμ [BraidedCategory C]
    (hsymm : ∀ P Q : C, (β_ P Q).hom ≫ (β_ Q P).hom = 𝟙 (P ⊗ Q)) (X₁ X₂ Y₁ Y₂ : C) :
    tensorμ X₁ X₂ Y₁ Y₂ ≫ tensorμ X₁ Y₁ X₂ Y₂ = 𝟙 _ := by
  have h : tensorμ X₁ Y₁ X₂ Y₂ = tensorδ X₁ X₂ Y₁ Y₂ := by
    simp only [tensorμ, tensorδ, Iso.inv_ext' (hsymm X₂ Y₁)]
  rw [h, tensorμ_tensorδ]

/-- The monoidal product of an inverse isomorphism with an identity is a right whiskering. -/
private theorem tensorIso_symm_refl_right_hom {A A' : C} (e : A' ≅ A) (B : C) :
    (e.symm ⊗ᵢ Iso.refl B).hom = e.inv ▷ B := by
  rw [tensorIso_hom, Iso.refl_hom, tensorHom_id, Iso.symm_hom]

/-- The monoidal product of an identity with an isomorphism is a left whiskering. -/
private theorem tensorIso_refl_left_hom (A : C) {B B' : C} (e : B ≅ B') :
    (Iso.refl A ⊗ᵢ e).hom = A ◁ e.hom := by
  rw [tensorIso_hom, Iso.refl_hom, id_tensorHom]

end CategoryTheory

namespace AlgebraicGeometry

open Stacks.SheafOfModules.TensorStalkRingedSpace Stacks.SheafOfModules.OnSpace

variable (X : AlgebraicGeometry.RingedSpace.{u, u})

/-! ### The interchange of the tensor product sheaf, in the re-seated structure -/

section Reseated

attribute [local instance] ringedSpaceMonoidal ringedSpaceBraided

/-- **The interchange isomorphism of the tensor product sheaf is the interchange
`CategoryTheory.tensorμ` of the monoidal structure it is built from.**  This is the definition of
`AlgebraicGeometry.tensorSheafInterchange` with its middle factor named. -/
theorem tensorSheafInterchange_hom_eq_tensorμ
    (A B C D : SheafOfModules.{u} (structureSheafRing X)) :
    (tensorSheafInterchange X A B C D).hom = tensorμ A B C D := by
  have h : (tensorSheafInterchange X A B C D).hom =
      (α_ A B (C ⊗ D)).hom ≫
        A ◁ ((α_ B C D).inv ≫ (β_ B C).hom ▷ D ≫ (α_ C B D).hom) ≫
          (α_ A C (B ⊗ D)).inv := rfl
  rw [h, MonoidalCategory.whiskerLeft_comp, MonoidalCategory.whiskerLeft_comp]
  simp only [tensorμ, Category.assoc]
  rfl

end Reseated

/-! ### Spelling bridges

`AlgebraicGeometry.tensorSheafInterchange` is written over `AlgebraicGeometry.ringedSpaceMonoidal`
and `AlgebraicGeometry.ringedSpaceBraided`, the structure of [Stacks, Tag 01CA] obtained by
*re-seating* the localized one along `SheafOfModules.sheafTensorNatIso`, while the duality
statements are at `Stacks.SheafOfModules.OnSpace.monoidal`, the structure of the same tag obtained
by *inducing* along `Stacks.SheafOfModules.OnSpace.sheafModuleTensorCompareIso`.  The two have the
same tensor product on objects and the same unit, by `rfl` in both cases, but they are different
terms, and a composite mixing them is not type-correct at `implicit` transparency, so neither `rw`
nor `simp` fires across them.

The identification goes through a third presentation, the strict structure
`Stacks.PullbackGradedAlgebra.monoidalCategory`, for which the re-seated half is already proved
(`Stacks.RingedSpace.associator_eq_strict` and its companions,
`Stacks.PullbackSheafTensor.braiding_eq_strict`).  The `OnSpace` half is supplied here: both
presentations express each structural morphism as the localized one conjugated by the same
comparison isomorphism — `Stacks.SheafOfModules.tensorObjIso` for the strict structure, by `rfl`,
and `sheafModuleTensorCompareIso` for `OnSpace`, which is that same isomorphism by
`Stacks.SheafOfModules.OnSpace.sheafModuleTensorCompareIso_eq`.  Nothing here is new mathematics. -/

section Bridges

attribute [local instance] Stacks.SheafOfModules.OnSpace.monoidal
  Stacks.SheafOfModules.OnSpace.braided

/-- **Left whiskering in `Stacks.SheafOfModules.OnSpace.monoidal` is left whiskering in the
strict monoidal structure of [Stacks, Tag 01CA].**  Both are the localized left whiskering
conjugated by `Stacks.SheafOfModules.tensorObjIso`. -/
theorem onSpace_whiskerLeft_eq_strict (A : SheafOfModules.{u} (structureSheafRing X))
    {B B' : SheafOfModules.{u} (structureSheafRing X)} (f : B ⟶ B') :
    A ◁ f =
      @MonoidalCategoryStruct.whiskerLeft _ _
        (Stacks.PullbackGradedAlgebra.monoidalCategory X).toMonoidalCategoryStruct A B B' f := by
  rw [Stacks.SheafOfModules.OnSpace.whiskerLeft_eq X A f]
  simp only [Stacks.SheafOfModules.OnSpace.sheafModuleTensorCompareIso_eq]
  exact (Stacks.SheafOfModules.Strict.whiskerLeft_eq X.presheaf
    (structureSheafRing X).property A f).symm

/-- **Right whiskering in `Stacks.SheafOfModules.OnSpace.monoidal` is right whiskering in the
strict monoidal structure of [Stacks, Tag 01CA].** -/
theorem onSpace_whiskerRight_eq_strict
    {A A' : SheafOfModules.{u} (structureSheafRing X)} (f : A ⟶ A')
    (B : SheafOfModules.{u} (structureSheafRing X)) :
    f ▷ B =
      @MonoidalCategoryStruct.whiskerRight _ _
        (Stacks.PullbackGradedAlgebra.monoidalCategory X).toMonoidalCategoryStruct A A' f B := by
  rw [Stacks.SheafOfModules.OnSpace.whiskerRight_eq X f B]
  simp only [Stacks.SheafOfModules.OnSpace.sheafModuleTensorCompareIso_eq]
  exact (Stacks.SheafOfModules.Strict.whiskerRight_eq X.presheaf
    (structureSheafRing X).property f B).symm

/-- **The braiding of `Stacks.SheafOfModules.OnSpace.braided` is the braiding of the strict
monoidal structure of [Stacks, Tag 01CA].**  Both are
`Stacks.SheafOfModules.tensorSheafBraiding`. -/
theorem onSpace_braiding_eq_strict (A B : SheafOfModules.{u} (structureSheafRing X)) :
    (β_ A B).hom =
      (@BraidedCategory.braiding _ _ (Stacks.PullbackGradedAlgebra.monoidalCategory X)
        (Stacks.PullbackTensorCoherence.braidedCategory X) A B).hom :=
  congrArg Iso.hom
    ((Stacks.SheafOfModules.OnSpace.braiding_eq_tensorSheafBraiding X A B).trans
      (Stacks.SheafOfModules.braiding_eq_tensorSheafBraiding X.presheaf
        (structureSheafRing X).property A B).symm)

/-- **The associator of `Stacks.SheafOfModules.OnSpace.monoidal` is the associator of the strict
monoidal structure of [Stacks, Tag 01CA].**  Both are the localized associator conjugated by
`Stacks.SheafOfModules.tensorObjIso`; the strict presentation writes the two conjugating factors
as monoidal products with an identity and `OnSpace` as whiskerings, which is what the two
`CategoryTheory.tensorIso` lemmas above reconcile. -/
theorem onSpace_associator_eq_strict (A B C : SheafOfModules.{u} (structureSheafRing X)) :
    α_ A B C =
      @MonoidalCategoryStruct.associator _ _
        (Stacks.PullbackGradedAlgebra.monoidalCategory X).toMonoidalCategoryStruct A B C := by
  apply Iso.ext
  have strictFormula := congrArg Iso.hom
    (Stacks.SheafOfModules.Strict.associator_eq X.presheaf (structureSheafRing X).property A B C)
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc] at strictFormula
  rw [@tensorIso_symm_refl_right_hom _ _
      (Stacks.SheafOfModules.monoidalCategory X.presheaf (structureSheafRing X).property) _ _
      (Stacks.SheafOfModules.tensorObjIso X.presheaf (structureSheafRing X).property A B) C,
    @tensorIso_refl_left_hom _ _
      (Stacks.SheafOfModules.monoidalCategory X.presheaf (structureSheafRing X).property) A _ _
      (Stacks.SheafOfModules.tensorObjIso X.presheaf (structureSheafRing X).property B C)]
    at strictFormula
  rw [Stacks.SheafOfModules.OnSpace.associator_hom_eq]
  refine Eq.trans ?_ strictFormula.symm
  rw [Stacks.SheafOfModules.OnSpace.sheafModuleTensorCompareIso_eq X
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj A).obj B) C,
    Stacks.SheafOfModules.OnSpace.sheafModuleTensorCompareIso_eq X A
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj B).obj C),
    Stacks.SheafOfModules.OnSpace.sheafModuleTensorCompareIso_eq X A B,
    Stacks.SheafOfModules.OnSpace.sheafModuleTensorCompareIso_eq X B C]
  rfl

/-- The associator of `AlgebraicGeometry.ringedSpaceMonoidal` is the associator of the strict
monoidal structure, as an isomorphism.  This is `SheafOfModules.associator_eq_strict` at the
ringed-space spelling of the ring sheaf, the form the interchange needs because
`CategoryTheory.tensorμ` uses the associator both ways round. -/
theorem reseated_associator_eq_strict (A B C : SheafOfModules.{u} (structureSheafRing X)) :
    @MonoidalCategoryStruct.associator _ _
        (ringedSpaceMonoidal X).toMonoidalCategoryStruct A B C =
      @MonoidalCategoryStruct.associator _ _
        (Stacks.PullbackGradedAlgebra.monoidalCategory X).toMonoidalCategoryStruct A B C :=
  _root_.SheafOfModules.associator_eq_strict X.sheaf A B C

/-- The two structures of [Stacks, Tag 01CA] have the same left whiskering. -/
theorem reseated_whiskerLeft_eq_onSpace (A : SheafOfModules.{u} (structureSheafRing X))
    {B B' : SheafOfModules.{u} (structureSheafRing X)} (f : B ⟶ B') :
    @MonoidalCategoryStruct.whiskerLeft _ _
        (ringedSpaceMonoidal X).toMonoidalCategoryStruct A B B' f = A ◁ f :=
  (Stacks.RingedSpace.whiskerLeft_eq_strict A f).trans
    (onSpace_whiskerLeft_eq_strict X A f).symm

/-- The two structures of [Stacks, Tag 01CA] have the same right whiskering. -/
theorem reseated_whiskerRight_eq_onSpace
    {A A' : SheafOfModules.{u} (structureSheafRing X)} (f : A ⟶ A')
    (B : SheafOfModules.{u} (structureSheafRing X)) :
    @MonoidalCategoryStruct.whiskerRight _ _
        (ringedSpaceMonoidal X).toMonoidalCategoryStruct A A' f B = f ▷ B :=
  (Stacks.RingedSpace.whiskerRight_eq_strict f B).trans
    (onSpace_whiskerRight_eq_strict X f B).symm

/-- The two structures of [Stacks, Tag 01CA] have the same braiding. -/
theorem reseated_braiding_eq_onSpace (A B : SheafOfModules.{u} (structureSheafRing X)) :
    (@BraidedCategory.braiding _ _ (ringedSpaceMonoidal X) (ringedSpaceBraided X) A B).hom =
      (β_ A B).hom :=
  (Stacks.PullbackSheafTensor.braiding_eq_strict X A B).trans
    (onSpace_braiding_eq_strict X A B).symm

/-- The two structures of [Stacks, Tag 01CA] have the same associator. -/
theorem reseated_associator_eq_onSpace (A B C : SheafOfModules.{u} (structureSheafRing X)) :
    @MonoidalCategoryStruct.associator _ _
        (ringedSpaceMonoidal X).toMonoidalCategoryStruct A B C = α_ A B C :=
  (reseated_associator_eq_strict X A B C).trans (onSpace_associator_eq_strict X A B C).symm

/-- **The two structures of [Stacks, Tag 01CA] have the same interchange.**  The interchange is a
composite of associators, whiskerings and one braiding, and the two structures agree on each. -/
theorem reseated_tensorμ_eq_onSpace (A B C D : SheafOfModules.{u} (structureSheafRing X)) :
    @tensorμ _ _ (ringedSpaceMonoidal X) (ringedSpaceBraided X) A B C D = tensorμ A B C D := by
  simp only [tensorμ]
  rw [reseated_associator_eq_onSpace, reseated_associator_eq_onSpace,
    reseated_associator_eq_onSpace, reseated_associator_eq_onSpace,
    reseated_whiskerLeft_eq_onSpace, reseated_whiskerLeft_eq_onSpace,
    reseated_whiskerLeft_eq_onSpace, reseated_whiskerRight_eq_onSpace,
    reseated_braiding_eq_onSpace]
  rfl

/-! ### The interchange is the interchange of Tag 01CA -/

/-- **The interchange isomorphism `AlgebraicGeometry.tensorSheafInterchange` of the tensor product
sheaf is the interchange `CategoryTheory.tensorμ` of the monoidal structure
`Stacks.SheafOfModules.OnSpace.monoidal` of [Stacks, Tag 01CA].**

This is the identification the duality statements need: `tensorSheafInterchange` is the
interchange of the *re-seated* structure of that tag, and the duality statements are at the
*induced* one; the two agree on every structural morphism the interchange is built from, by
`AlgebraicGeometry.reseated_tensorμ_eq_onSpace`. -/
theorem tensorSheafInterchange_hom_eq
    (A B C D : SheafOfModules.{u} (structureSheafRing X)) :
    (tensorSheafInterchange X A B C D).hom = tensorμ A B C D :=
  (tensorSheafInterchange_hom_eq_tensorμ X A B C D).trans
    (reseated_tensorμ_eq_onSpace X A B C D)

/-- **The interchange of the tensor product sheaf is inverse to the interchange with the two
middle factors exchanged.**  Both are `CategoryTheory.tensorμ` of the monoidal structure of
[Stacks, Tag 01CA], whose braiding is a symmetry. -/
theorem tensorSheafInterchange_hom_eq_inv
    (A B C D : SheafOfModules.{u} (structureSheafRing X)) :
    (tensorSheafInterchange X A C B D).hom = (tensorSheafInterchange X A B C D).inv :=
  Iso.inv_ext' (by
    simp only [tensorSheafInterchange_hom_eq]
    exact tensorμ_comp_tensorμ (braiding_symmetry X) A B C D)

end Bridges

/-! ### The value of the duality bijection at a pure map, through the interchange -/

section Scheme

open Stacks.FiniteLocallyFree Stacks.AlgebraicGeometry.ReflexiveModules
open AlgebraicGeometry.VectorBundleKZero

attribute [local instance] onSpaceModulesMonoidal

variable {X' Y' S : Scheme.{u}} (f : X' ⟶ S) (g : Y' ⟶ S)

/-- **The value of the duality bijection at a pure map `a ⊠ b`, as the monoidal product of the
two factor sections followed by the interchange.** -/
theorem externalTensorDualTensorHomEquiv_externalTensorProductMap_interchange
    (E E₂ : X'.Modules) (G G₂ : Y'.Modules)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X'.ringCatSheaf) E)
    (hG : IsFiniteLocallyFree.{u, u, u} (R := Y'.ringCatSheaf) G)
    (a : E ⟶ E₂) (b : G ⟶ G₂) :
    externalTensorDualTensorHomEquiv f g E G (externalTensorProduct f g E₂ G₂) hE hG
        (externalTensorProductMap f g a b) =
      (λ_ (𝟙_ (Limits.pullback f g).Modules)).inv ≫
        MonoidalCategory.tensorHom
            (@ExactPairing.coevaluation _ _ (onSpaceModulesMonoidal (Limits.pullback f g)) _ _
                (externalTensorProductFirstPairing f g E hE) ≫
              MonoidalCategory.whiskerRight
                ((Scheme.Modules.pullback (Limits.pullback.fst f g)).map a)
                ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj (dualSheaf E)))
            (@ExactPairing.coevaluation _ _ (onSpaceModulesMonoidal (Limits.pullback f g)) _ _
                (externalTensorProductSecondPairing f g G hG) ≫
              MonoidalCategory.whiskerRight
                ((Scheme.Modules.pullback (Limits.pullback.snd f g)).map b)
                ((Scheme.Modules.pullback (Limits.pullback.snd f g)).obj (dualSheaf G))) ≫
          (tensorSheafInterchange (Limits.pullback f g).toRingedSpace
            ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj E₂)
            ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj (dualSheaf E))
            ((Scheme.Modules.pullback (Limits.pullback.snd f g)).obj G₂)
            ((Scheme.Modules.pullback (Limits.pullback.snd f g)).obj (dualSheaf G))).hom := by
  let _ : @BraidedCategory _ _ (onSpaceModulesMonoidal (Limits.pullback f g)) :=
    Stacks.SheafOfModules.OnSpace.braided (Limits.pullback f g).toRingedSpace
  refine Eq.trans (externalTensorDualTensorHomEquiv_externalTensorProductMap f g E E₂ G G₂
    hE hG a b) ?_
  refine Eq.trans (nestedTensorSection_comp_whiskerLeft_braiding_inv _ _) ?_
  have hint := tensorSheafInterchange_hom_eq (Limits.pullback f g).toRingedSpace
    ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj E₂)
    ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj (dualSheaf E))
    ((Scheme.Modules.pullback (Limits.pullback.snd f g)).obj G₂)
    ((Scheme.Modules.pullback (Limits.pullback.snd f g)).obj (dualSheaf G))
  rw [hint]
  rfl

/-- **The interchange of the tensor product sheaf, followed by
`AlgebraicGeometry.externalTensorProductTensorIso`, is the comparison of a pullback with a tensor
product.**  `externalTensorProductTensorIso` of [Stacks, Tag 0G46] is the interchange with the
middle two factors in the *other* order followed by those comparisons, and the two interchanges
are mutually inverse by `AlgebraicGeometry.tensorSheafInterchange_hom_eq_inv`. -/
theorem tensorSheafInterchange_comp_externalTensorProductTensorIso
    (E E' : X'.Modules) (G G' : Y'.Modules) :
    (tensorSheafInterchange (Limits.pullback f g).toRingedSpace
          ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj E)
          ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj E')
          ((Scheme.Modules.pullback (Limits.pullback.snd f g)).obj G)
          ((Scheme.Modules.pullback (Limits.pullback.snd f g)).obj G')).hom ≫
        (externalTensorProductTensorIso f g E E' G G').hom =
      (tensorSheafMapIso (Limits.pullback f g).toRingedSpace
        (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso
          (Limits.pullback.fst f g) E E').symm
        (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso
          (Limits.pullback.snd f g) G G').symm).hom := by
  have h : (externalTensorProductTensorIso f g E E' G G').hom =
      (tensorSheafInterchange (Limits.pullback f g).toRingedSpace
            ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj E)
            ((Scheme.Modules.pullback (Limits.pullback.snd f g)).obj G)
            ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj E')
            ((Scheme.Modules.pullback (Limits.pullback.snd f g)).obj G')).hom ≫
        (tensorSheafMapIso (Limits.pullback f g).toRingedSpace
          (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso
            (Limits.pullback.fst f g) E E').symm
          (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso
            (Limits.pullback.snd f g) G G').symm).hom := rfl
  rw [h,
    tensorSheafInterchange_hom_eq_inv (Limits.pullback f g).toRingedSpace
      ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj E)
      ((Scheme.Modules.pullback (Limits.pullback.snd f g)).obj G)
      ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj E')
      ((Scheme.Modules.pullback (Limits.pullback.snd f g)).obj G')]
  exact Iso.inv_hom_id_assoc _ _

/-- **The value of the duality bijection at a pure map `a ⊠ b`, through
`AlgebraicGeometry.externalTensorProductTensorIso`.**  Read through the interchange of
[Stacks, Tag 0G46], the value is the monoidal product of the duality section of `pr₁^*a` and that
of `pr₂^*b`, up to the comparison of a pullback with a tensor product.  No bare symmetry is left:
the two symmetries of
`AlgebraicGeometry.externalTensorDualTensorHomEquiv_externalTensorProductMap_swapped` have become
one named interchange. -/
theorem externalTensorDualTensorHomEquiv_externalTensorProductMap_tensorIso
    (E E₂ : X'.Modules) (G G₂ : Y'.Modules)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X'.ringCatSheaf) E)
    (hG : IsFiniteLocallyFree.{u, u, u} (R := Y'.ringCatSheaf) G)
    (a : E ⟶ E₂) (b : G ⟶ G₂) :
    externalTensorDualTensorHomEquiv f g E G (externalTensorProduct f g E₂ G₂) hE hG
          (externalTensorProductMap f g a b) ≫
        (externalTensorProductTensorIso f g E₂ (dualSheaf E) G₂ (dualSheaf G)).hom =
      (λ_ (𝟙_ (Limits.pullback f g).Modules)).inv ≫
        MonoidalCategory.tensorHom
            (@ExactPairing.coevaluation _ _ (onSpaceModulesMonoidal (Limits.pullback f g)) _ _
                (externalTensorProductFirstPairing f g E hE) ≫
              MonoidalCategory.whiskerRight
                ((Scheme.Modules.pullback (Limits.pullback.fst f g)).map a)
                ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj (dualSheaf E)))
            (@ExactPairing.coevaluation _ _ (onSpaceModulesMonoidal (Limits.pullback f g)) _ _
                (externalTensorProductSecondPairing f g G hG) ≫
              MonoidalCategory.whiskerRight
                ((Scheme.Modules.pullback (Limits.pullback.snd f g)).map b)
                ((Scheme.Modules.pullback (Limits.pullback.snd f g)).obj (dualSheaf G))) ≫
          (tensorSheafMapIso (Limits.pullback f g).toRingedSpace
            (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso
              (Limits.pullback.fst f g) E₂ (dualSheaf E)).symm
            (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso
              (Limits.pullback.snd f g) G₂ (dualSheaf G)).symm).hom := by
  refine Eq.trans (congrArg (fun z => z ≫
    (externalTensorProductTensorIso f g E₂ (dualSheaf E) G₂ (dualSheaf G)).hom)
      (externalTensorDualTensorHomEquiv_externalTensorProductMap_interchange f g E E₂ G G₂
        hE hG a b)) ?_
  refine Eq.trans (Stacks.SheafOfModules.comp_assoc₃ _ _ _ _) ?_
  exact whisker_eq _ (whisker_eq _
    (tensorSheafInterchange_comp_externalTensorProductTensorIso f g E₂ (dualSheaf E) G₂
      (dualSheaf G)))

end Scheme

end AlgebraicGeometry

end
