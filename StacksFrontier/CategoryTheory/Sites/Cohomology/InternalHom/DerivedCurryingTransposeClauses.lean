module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingSourceNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingInternalHomNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryTargetNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsTargetNaturality

/-!
# The three clauses of Stacks 08J8 on a ringed site, at the uncurried derived tensor product

Let `X` be a ringed site.  The bijection of Stacks 08J8,

`Hom(A, RSheafHom(B, C)) ≃ Hom(A ⊗^L B, C)`,

is natural in `A`, dinatural in `B` and natural in `C`.  This file records the three clauses with
the derived tensor product written as a functor on pairs and the bijection read as a bijection
of types, which is the shape in which a transpose construction consumes them.

## Main results

* `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_toEquiv_naturality_source`
* `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_toEquiv_dinaturality`
* `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_toEquiv_naturality_target`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Prod

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The derived tensor product on pairs. -/
abbrev derivedTensorPair :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ×
        DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  Functor.uncurry.obj (Stacks.SheafOfModules.derivedTensorProductFunctor X)

/-- **Stacks 08J8 in the source variable.** -/
theorem derivedCurryHomEquiv_toEquiv_naturality_source
    (A A' B C : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (φ : A ⟶ A')
    (ψ : A' ⟶ ((derivedSheafHomBifunctor X).obj (op B)).obj C) :
    (derivedCurryHomEquiv X A B C).toEquiv (φ ≫ ψ) =
      (derivedTensorPair X).map (φ ×ₘ 𝟙 B) ≫ (derivedCurryHomEquiv X A' B C).toEquiv ψ := by
  have hu : (derivedTensorPair X).map (φ ×ₘ 𝟙 B) =
      ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map φ).app B := by
    simp [Functor.uncurry_obj_map]
  rw [hu]
  exact derivedCurryHomEquiv_naturality_source X φ ψ

/-- **Stacks 08J8 in the internal-hom variable**, a dinaturality. -/
theorem derivedCurryHomEquiv_toEquiv_dinaturality
    (A B B' C : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (φ : B' ⟶ B)
    (ψ : A ⟶ ((derivedSheafHomBifunctor X).obj (op B)).obj C) :
    (derivedCurryHomEquiv X A B' C).toEquiv (ψ ≫ ((derivedSheafHomBifunctor X).map φ.op).app C) =
      (derivedTensorPair X).map (𝟙 A ×ₘ φ) ≫ (derivedCurryHomEquiv X A B C).toEquiv ψ := by
  have hu : (derivedTensorPair X).map (𝟙 A ×ₘ φ) =
      ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj A).map φ := by
    simp [Functor.uncurry_obj_map]
  rw [hu]
  exact derivedCurryHomEquiv_dinaturality X A C φ ψ

/-- **Stacks 08J8 in the target variable.** -/
theorem derivedCurryHomEquiv_toEquiv_naturality_target
    (A B C C' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (k : C ⟶ C')
    (ψ : A ⟶ ((derivedSheafHomBifunctor X).obj (op B)).obj C) :
    (derivedCurryHomEquiv X A B C').toEquiv (ψ ≫ ((derivedSheafHomBifunctor X).obj (op B)).map k) =
      (derivedCurryHomEquiv X A B C).toEquiv ψ ≫ k :=
  derivedCurryHomEquiv_naturality_target X k ψ

end AlgebraicGeometry.RingedSite

end
