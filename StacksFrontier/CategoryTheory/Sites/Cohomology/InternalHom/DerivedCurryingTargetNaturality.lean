module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingSourceNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsTargetNaturality
import StacksCore.Tactic.StacksAttribute

/-! # Naturality of the tensor–internal-Hom bijection in its target variable

Let `(C, O)` be a ringed site. Stacks 08J8 asserts that the bijection

`(A ⟶ RSheafHom(B, Z)) ≃ (A ⊗^L_O B ⟶ Z)`

of `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv` is functorial in the three objects. The
companion files `…InternalHom.DerivedCurryingSourceNaturality` and
`…InternalHom.DerivedCurryingInternalHomNaturality` prove its naturality in the source variable
`A` and its dinaturality in the internal-Hom variable `B`. This file proves the third and last
clause, naturality in the target variable `Z`: postcomposing `h : A ⟶ RSheafHom(B, Z)` with the
map `RSheafHom(B, Z) ⟶ RSheafHom(B, Z')` induced by `m : Z ⟶ Z'` corresponds to postcomposing
the morphism matched with `h` with `m` itself.

`Z` is covariant on both sides of the bijection, so unlike the clause in `B` this is a genuine
naturality square.

## Main results

* `AlgebraicGeometry.RingedSite.derivedCurryIso_natural_target`: the naturality square of
  Stacks 08J9 in its target object.
* `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_naturality_target'`: **Stacks 08J8**,
  naturality of the bijection of morphism groups in the target variable.

With this clause the three naturality fields of
`Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi.TensorHomAdjunction` are all
theorems of the development, and the bijection of Stacks 08J8 becomes an honest
`CategoryTheory.Adjunction` between `− ⊗^L_O B` and `RSheafHom(B, −)`; that is
`AlgebraicGeometry.RingedSite.derivedTensorHomAdjunction` in
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorHomAdjunction`.

## Implementation notes

The proof is the one of the source clause with both ends taken in the other variance. The
bijection is the derived currying isomorphism of Stacks 08J9 read on degree-zero global
hypercohomology, with both ends identified with morphism groups by Stacks 08JA
(`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_globalSections`). So the clause is the
naturality of Stacks 08J9 in its *target* object — which is
`AlgebraicGeometry.RingedSite.derivedCurryIso_natural` at the identity of the first object and
of the middle one — together with the naturality of Stacks 08JA in its covariant variable,
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_naturality_target`, used at the
two ends: once at the source `A` and once at the source `A ⊗^L_O B`. The source clause uses the
contravariant naturality of Stacks 08JA at both ends and the dinaturality clause uses one of
each, which is the only difference between the three proofs.

Every hypothesis is instantiated at its arguments before it is rewritten, and the
global-sections image of the Stacks 08J9 square is a separate declaration: the elaborator's
budget is spent per declaration and the two halves do not fit in one. Both disciplines are the
ones recorded in `…InternalHom.DerivedCurryingSourceNaturality`.

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
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- **The derived currying isomorphism of Stacks 08J9 is natural in its target object.** This is
`AlgebraicGeometry.RingedSite.derivedCurryIso_natural` at the identity of the first object and
of the middle one. -/
theorem derivedCurryIso_natural_target
    (A B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {Z Z' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (m : Z ⟶ Z') :
    ((derivedSheafHomBifunctor X).obj (op A)).map
          (((derivedSheafHomBifunctor X).obj (op B)).map m) ≫
        (derivedCurryIso X A B Z').hom =
      (derivedCurryIso X A B Z).hom ≫
        ((derivedSheafHomBifunctor X).obj
          (op (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj A).obj B))).map m := by
  simpa using derivedCurryIso_natural X (𝟙 A) (𝟙 B) m

/-- **The derived currying isomorphism of Stacks 08J9 is natural in its target object on
degree-zero global hypercohomology.** This is `derivedCurryIso_natural_target` read on a
hypercohomology class.

It is a separate declaration rather than a step of `derivedCurryHomEquiv_naturality_target'`
below because the elaborator's budget is spent per declaration, and the two halves do not fit
in one. -/
private lemma derivedCurryIso_globalSections_natural_target
    (A B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {Z Z' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (m : Z ⟶ Z')
    (x : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op A)).obj
          (((derivedSheafHomBifunctor X).obj (op B)).obj Z))) : Type u)) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections X).map (derivedCurryIso X A B Z').hom)
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map
            (((derivedSheafHomBifunctor X).obj (op A)).map
              (((derivedSheafHomBifunctor X).obj (op B)).map m))) x) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections X).map
          (((derivedSheafHomBifunctor X).obj
            (op (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj A).obj B))).map m))
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map (derivedCurryIso X A B Z).hom) x) := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← Functor.map_comp,
    derivedCurryIso_natural_target, Functor.map_comp, Functor.map_comp,
    ConcreteCategory.comp_apply]

/-- **Stacks 08J8, naturality in the target variable.** Postcomposing a morphism
`h : A ⟶ RSheafHom(B, Z)` with the map `RSheafHom(B, Z) ⟶ RSheafHom(B, Z')` induced by
`m : Z ⟶ Z'` corresponds, under the tensor–internal-Hom bijection, to postcomposing the
morphism `A ⊗^L_O B ⟶ Z` matched with `h` with `m`. -/
theorem derivedCurryHomEquiv_naturality_target'
    (A B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {Z Z' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (m : Z ⟶ Z')
    (h : A ⟶ ((derivedSheafHomBifunctor X).obj (op B)).obj Z) :
    derivedCurryHomEquiv X A B Z' (h ≫ ((derivedSheafHomBifunctor X).obj (op B)).map m) =
      derivedCurryHomEquiv X A B Z h ≫ m := by
  obtain ⟨x, hx⟩ : ∃ x, derivedSheafHomGlobalSectionsEquiv X A
      (((derivedSheafHomBifunctor X).obj (op B)).obj Z) x = h :=
    ⟨_, (derivedSheafHomGlobalSectionsEquiv X A
      (((derivedSheafHomBifunctor X).obj (op B)).obj Z)).apply_symm_apply h⟩
  subst hx
  -- Every hypothesis is instantiated at its arguments before it is rewritten: a rewrite that
  -- has to match a pattern with metavariables against terms of this size exhausts the
  -- elaborator's budget.
  have hN := derivedSheafHomGlobalSectionsEquiv_naturality_target X A
    (((derivedSheafHomBifunctor X).obj (op B)).map m) x
  have hl := derivedCurryHomEquiv_globalSections_homologyMap X A B Z'
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
      ((derivedModuleGlobalSections X).map
        (((derivedSheafHomBifunctor X).obj (op A)).map
          (((derivedSheafHomBifunctor X).obj (op B)).map m))) x)
  have hr := derivedCurryHomEquiv_globalSections_homologyMap X A B Z x
  have hmid := congrArg (fun t => derivedSheafHomGlobalSectionsEquiv X
    (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj A).obj B) Z' t)
    (derivedCurryIso_globalSections_natural_target X A B m x)
  rw [← hN, hl, hmid, hr]
  exact derivedSheafHomGlobalSectionsEquiv_naturality_target X
    (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj A).obj B) m _

end AlgebraicGeometry.RingedSite

end
