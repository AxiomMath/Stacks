module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurrySourceNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsSourceNaturality
import StacksCore.Tactic.StacksAttribute

/-! # The tensor–internal-Hom bijection as tensoring and evaluating

Let `(C, O)` be a ringed site. Stacks 08J8 asserts that the bijection

`(A ⟶ RSheafHom(B, Z)) ≃ (A ⊗^L_O B ⟶ Z)`

of `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv` is functorial in the three objects. Its
naturality in the source variable is
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_naturality_source`. Read at the identity of
`RSheafHom(B, Z)` it says that the morphism matched with `h : A ⟶ RSheafHom(B, Z)` is `h ⊗ 1`
followed by the evaluation `RSheafHom(B, Z) ⊗^L_O B ⟶ Z`; this file records that consequence.

## Main results

* `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_eq_tensor_evaluation`: the bijection of
  Stacks 08J8 is tensoring with the identity and then evaluating.
* `AlgebraicGeometry.RingedSite.tensor_evaluation_derivedCurryHomEquiv_symm`: the transpose of a
  datum, tensored with the identity, evaluates back to the datum.

## References

* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 08J9](https://stacks.math.columbia.edu/tag/08J9)
* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.ModuleSections

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- **The bijection of Stacks 08J8 is tensoring with the identity and then evaluating.** The
morphism `A ⊗^L_O B ⟶ Z` matched with `h : A ⟶ RSheafHom(B, Z)` is `h ⊗ 1` followed by the
evaluation `RSheafHom(B, Z) ⊗^L_O B ⟶ Z`. So the bijection is determined by its value at an
identity map.

This is `derivedCurryHomEquiv_naturality_source` read at the identity of `RSheafHom(B, Z)`. -/
theorem derivedCurryHomEquiv_eq_tensor_evaluation
    (A B Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (h : A ⟶ ((derivedSheafHomBifunctor X).obj (op B)).obj Z) :
    derivedCurryHomEquiv X A B Z h =
      ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map h).app B ≫
        derivedCurryHomEquiv X (((derivedSheafHomBifunctor X).obj (op B)).obj Z) B Z (𝟙 _) := by
  have hn := derivedCurryHomEquiv_naturality_source X h
    (𝟙 (((derivedSheafHomBifunctor X).obj (op B)).obj Z))
  -- A rewrite or `exact` would have to unfold terms of this size to cancel the trailing `𝟙`;
  -- the congruence built by `convert` compares the two sides one argument at a time.
  convert hn using 2
  exact (Category.comp_id h).symm

/-- **The transpose of a datum, tensored with the identity, evaluates back to the datum.** For
`d : A ⊗^L_O B ⟶ Z` the morphism `A ⟶ RSheafHom(B, Z)` matched with `d` under the bijection of
Stacks 08J8, tensored with the identity of `B` and followed by the evaluation
`RSheafHom(B, Z) ⊗^L_O B ⟶ Z`, is `d` again.

This is `derivedCurryHomEquiv_eq_tensor_evaluation` read at the transpose of `d`. -/
theorem tensor_evaluation_derivedCurryHomEquiv_symm
    (A B Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (d : ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj A).obj B ⟶ Z) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
            ((derivedCurryHomEquiv X A B Z).symm d)).app B ≫
        derivedCurryHomEquiv X (((derivedSheafHomBifunctor X).obj (op B)).obj Z) B Z (𝟙 _) = d :=
  (derivedCurryHomEquiv_eq_tensor_evaluation X A B Z
        ((derivedCurryHomEquiv X A B Z).symm d)).symm.trans
    ((derivedCurryHomEquiv X A B Z).apply_symm_apply d)

end AlgebraicGeometry.RingedSite

end
