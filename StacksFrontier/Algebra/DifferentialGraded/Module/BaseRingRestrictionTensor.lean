module

public import StacksFrontier.Algebra.DifferentialGraded.Module.BaseRingRestrictionDerived
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorHomAdjunction
public import StacksFrontier.CategoryTheory.Adjunction.MateAlongEquivalences

/-!
# Changing the base ring commutes with derived extension of scalars

Let `S → R` be a homomorphism of commutative rings and `φ : A → B` a homomorphism of differential
graded algebras over `R`. Derived extension of scalars `- ⊗_A^𝐋 B : D(A, d) ⥤ D(B, d)` is left
adjoint to derived restriction of scalars (Stacks, Example 22.33.2), and so is its counterpart
over `S` for `φ` regarded over `S`. Since regarding over `S` is an equivalence of derived
categories commuting with derived restriction of scalars, it commutes with derived extension of
scalars as well, and it carries the transposes of the first adjunction to those of the second.
In particular a comparison map defined as a transpose is an isomorphism over `R` exactly when the
corresponding map over `S` is.

## Main definitions

* `DifferentialGradedModule.derivedTensorRestrictBaseIso`: regarding over `S` commutes with
  derived extension of scalars.

## Main results

* `DifferentialGradedModule.derivedRestrictBase_map_homEquiv_symm`: the transpose
  `X ⊗_A^𝐋 B ⟶ Y` of `g : X ⟶ Y_A` is carried to the transpose over `S` of the image of `g`.
* `DifferentialGradedModule.derivedRestrictBase_map_counit` and
  `DifferentialGradedModule.derivedRestrictBase_map_unit`: the same for the counit and the unit.
* `DifferentialGradedModule.isIso_homEquiv_symm_iff_restrictBase`: a transpose is an isomorphism
  exactly when the corresponding transpose over `S` is.

## Implementation notes

The isomorphism is the inverse of the mate, `CategoryTheory.Adjunction.mateOfRightIso`, of the
compatibility `DifferentialGradedModule.derivedRestrictionRestrictBaseIso` of regarding over `S`
with derived restriction; it is invertible because both vertical functors of the square are
equivalences (`CategoryTheory.Adjunction.isIso_mateOfRightIso`). Defining it as a mate rather
than by uniqueness of left adjoints is what makes the transposes computable.

## References

* [Stacks Project, Tag 0BYX](https://stacks.math.columbia.edu/tag/0BYX)
-/

@[expose] public noncomputable section

open CategoryTheory DifferentialGraded

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] (S : Type u) [CommRing S] [Algebra S R]
  {A B : DifferentialGradedAlgebra.{u, u} R}

/-- The mate of the compatibility of regarding over `S` with derived restriction of scalars:
`(X)_S ⊗_{A_S}^𝐋 B_S ⟶ (X ⊗_A^𝐋 B)_S`. -/
abbrev derivedTensorRestrictBaseMate (φ : A.Hom B) :
    (derivedRestrictBaseEquiv S A).functor ⋙
        Bimodule.derivedTensorFunctor (Bimodule.regular (φ.restrictBase S)) ⟶
      Bimodule.derivedTensorFunctor (Bimodule.regular φ) ⋙
        (derivedRestrictBaseEquiv S B).functor :=
  Adjunction.mateOfRightIso (Bimodule.derivedTensorFunctor_adj_derivedRestriction φ)
    (Bimodule.derivedTensorFunctor_adj_derivedRestriction (φ.restrictBase S))
    (derivedRestrictionRestrictBaseIso S φ)

/-- The mate is an isomorphism, both vertical functors of its square being equivalences. -/
instance (φ : A.Hom B) : IsIso (derivedTensorRestrictBaseMate S φ) :=
  Adjunction.isIso_mateOfRightIso _ _ _ (derivedRestrictBaseEquiv S A).fullyFaithfulFunctor
    (derivedRestrictBaseEquiv S B).fullyFaithfulFunctor

/-- **Changing the base ring commutes with derived extension of scalars.** For a homomorphism
`φ : A → B` of differential graded algebras over `R`, derived extension of scalars along `φ`
followed by regarding over `S` is derived extension of scalars along `φ` regarded over `S`,
preceded by regarding over `S`. -/
def derivedTensorRestrictBaseIso (φ : A.Hom B) :
    Bimodule.derivedTensorFunctor (Bimodule.regular φ) ⋙ (derivedRestrictBaseEquiv S B).functor ≅
      (derivedRestrictBaseEquiv S A).functor ⋙
        Bimodule.derivedTensorFunctor (Bimodule.regular (φ.restrictBase S)) :=
  (asIso (derivedTensorRestrictBaseMate S φ)).symm

/-- **Regarding over `S` carries transposes to transposes.** For `g : X ⟶ Y_A` in `D(A, d)`, the
image over `S` of its transpose `X ⊗_A^𝐋 B ⟶ Y` is, up to the identification
`DifferentialGradedModule.derivedTensorRestrictBaseIso`, the transpose of the image of `g`
followed by the identification `DifferentialGradedModule.derivedRestrictionRestrictBaseIso`. -/
theorem derivedRestrictBase_map_homEquiv_symm (φ : A.Hom B) {X : derivedCategory' A}
    {Y : derivedCategory' B} (g : X ⟶ (derivedRestriction φ).obj Y) :
    (derivedRestrictBaseEquiv S B).functor.map
        (((Bimodule.derivedTensorFunctor_adj_derivedRestriction φ).homEquiv X Y).symm g) =
      (derivedTensorRestrictBaseIso S φ).hom.app X ≫
        ((Bimodule.derivedTensorFunctor_adj_derivedRestriction (φ.restrictBase S)).homEquiv _
          _).symm ((derivedRestrictBaseEquiv S A).functor.map g ≫
            (derivedRestrictionRestrictBaseIso S φ).hom.app Y) := by
  rw [← Adjunction.mateOfRightIso_app_comp_map_homEquiv_symm, ← Category.assoc]
  show _ = ((derivedTensorRestrictBaseIso S φ).hom.app X ≫
    (derivedTensorRestrictBaseIso S φ).inv.app X) ≫ _
  rw [Iso.hom_inv_id_app, Category.id_comp]

/-- Regarding over `S` carries the counit of the adjunction between derived extension and
restriction of scalars along `φ` to the counit of the adjunction along `φ` regarded over `S`, up
to the identifications of the two functors. -/
theorem derivedRestrictBase_map_counit (φ : A.Hom B) (Y : derivedCategory' B) :
    (derivedRestrictBaseEquiv S B).functor.map
        ((Bimodule.derivedTensorFunctor_adj_derivedRestriction φ).counit.app Y) =
      (derivedTensorRestrictBaseIso S φ).hom.app ((derivedRestriction φ).obj Y) ≫
        (Bimodule.derivedTensorFunctor (Bimodule.regular (φ.restrictBase S))).map
          ((derivedRestrictionRestrictBaseIso S φ).hom.app Y) ≫
        (Bimodule.derivedTensorFunctor_adj_derivedRestriction (φ.restrictBase S)).counit.app
          ((derivedRestrictBaseEquiv S B).functor.obj Y) := by
  have h := derivedRestrictBase_map_homEquiv_symm S φ (𝟙 ((derivedRestriction φ).obj Y))
  simp only [Adjunction.homEquiv_counit, CategoryTheory.Functor.map_id, Category.id_comp] at h
  exact h

/-- Regarding over `S` carries the unit of the adjunction between derived extension and
restriction of scalars along `φ` to the unit of the adjunction along `φ` regarded over `S`, up
to the identifications of the two functors. -/
theorem derivedRestrictBase_map_unit (φ : A.Hom B) (X : derivedCategory' A) :
    (derivedRestrictBaseEquiv S A).functor.map
        ((Bimodule.derivedTensorFunctor_adj_derivedRestriction φ).unit.app X) ≫
      (derivedRestrictionRestrictBaseIso S φ).hom.app
        ((Bimodule.derivedTensorFunctor (Bimodule.regular φ)).obj X) =
      (Bimodule.derivedTensorFunctor_adj_derivedRestriction (φ.restrictBase S)).unit.app
          ((derivedRestrictBaseEquiv S A).functor.obj X) ≫
        (derivedRestriction (φ.restrictBase S)).map
          ((derivedTensorRestrictBaseIso S φ).inv.app X) :=
  unit_mateEquiv_symm _ _ _ X

/-- **A transpose is an isomorphism over `R` exactly when it is one over `S`.** For
`g : X ⟶ Y_A` in `D(A, d)`, the transpose `X ⊗_A^𝐋 B ⟶ Y` is an isomorphism exactly when the
transpose over `S` of the image of `g`, followed by the identification of the two derived
restrictions, is. -/
theorem isIso_homEquiv_symm_iff_restrictBase (φ : A.Hom B) {X : derivedCategory' A}
    {Y : derivedCategory' B} (g : X ⟶ (derivedRestriction φ).obj Y) :
    IsIso (((Bimodule.derivedTensorFunctor_adj_derivedRestriction φ).homEquiv X Y).symm g) ↔
      IsIso (((Bimodule.derivedTensorFunctor_adj_derivedRestriction (φ.restrictBase S)).homEquiv
        _ _).symm ((derivedRestrictBaseEquiv S A).functor.map g ≫
          (derivedRestrictionRestrictBaseIso S φ).hom.app Y)) :=
  Adjunction.isIso_homEquiv_symm_iff_of_mateOfRightIso _ _ _
    (derivedRestrictBaseEquiv S A).fullyFaithfulFunctor
    (derivedRestrictBaseEquiv S B).fullyFaithfulFunctor g

end DifferentialGradedModule
