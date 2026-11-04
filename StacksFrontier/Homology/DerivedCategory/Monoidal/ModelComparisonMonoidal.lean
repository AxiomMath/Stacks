module

public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.DerivedRestrictUnit
public import StacksFrontier.Homology.DerivedCategory.ModelComparison
public import StacksFrontier.Homology.DerivedCategory.Monoidal.KFlatComputedMonoidal

/-!
# The comparison of two models of a derived category is monoidal

Let `A` be an abelian monoidal category in which every complex has a K-flat resolution, so that
`D(A)` carries the derived tensor product `CochainComplex.KFlatMonoidal.derivedMonoidal`. The
monoidal structure is defined at any chosen model `HasDerivedCategory A`; this file shows that the
comparison equivalence `StacksDraft.DerivedModel.modelEquiv h₁ h₂` between two models is a strong
monoidal functor for the derived tensor products at the two models.

On K-flat complexes the comparison is the identity — both models are localizations of the
homotopy category, and the comparison identifies the two localization functors — so this is
`CategoryTheory.Functor.kFlatComputedMonoidal` for the identity functor of `A`.

## Main definitions

* `CategoryTheory.modelEquivKFlatQIso` — the comparison, restricted to the K-flat objects, is the
  identity.
* `CategoryTheory.modelEquivFunctorMonoidal` — the comparison is monoidal.

## References

* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory
open CochainComplex.KFlatMonoidal CochainComplex.KFlatBifunctor StacksDraft.DerivedModel

universe w w' v₁ u₁

namespace CategoryTheory

attribute [local instance] homotopyMonoidal homotopyBraided

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [MonoidalCategory A]
  [(curriedTensor A).Additive] [∀ X : A, ((curriedTensor A).obj X).Additive]
  [∀ (X₁ X₂ : GradedObject ℤ A), GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).obj X₁)]
  [∀ X₂ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

omit [∀ X₁ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).obj X₁)]
  [∀ X₂ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃] in
/-- The identity functor preserves K-flatness of complexes. -/
theorem kFlat_mapHomologicalComplex_id (K : CochainComplex A ℤ)
    (hK : KFlat (curriedTensor A) K) :
    KFlat (curriedTensor A) (((𝟭 A).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  hK

/-- **On K-flat complexes the comparison of two models is the identity.** Both models localize
the homotopy category at the quasi-isomorphisms, and the comparison equivalence identifies the
two localization functors (`CategoryTheory.Localization.compUniqFunctor`). -/
def modelEquivKFlatQIso (h₁ : HasDerivedCategory.{w} A) (h₂ : HasDerivedCategory.{w'} A) :
    @kFlatQ A A A _ _ _ _ _ _ (curriedTensor A) _ _ _ h₁ ⋙ (modelEquiv h₁ h₂).functor ≅
      Functor.kFlatLift (𝟭 A) kFlat_mapHomologicalComplex_id ⋙
        @kFlatQ A A A _ _ _ _ _ _ (curriedTensor A) _ _ _ h₂ :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Localization.compUniqFunctor (@DerivedCategory.Qh A _ _ h₁)
      (@DerivedCategory.Qh A _ _ h₂) (HomotopyCategory.subcategoryAcyclic A).trW) ≪≫
    Functor.isoWhiskerRight ((kFlatObjects (curriedTensor A)).ι.rightUnitor.symm ≪≫
      Functor.isoWhiskerLeft _ (Stacks.SmallDerivedCategory.mapHomotopyCategoryIdIso A).symm ≪≫
      (ObjectProperty.liftCompιIso _ _ _).symm) _ ≪≫
    Functor.associator _ _ _

/-- **The comparison of two models of `D(A)` is a strong monoidal functor** for the derived
tensor products `CochainComplex.KFlatMonoidal.derivedMonoidal` at the two models. -/
@[instance_reducible]
def modelEquivFunctorMonoidal [BraidedCategory (CochainComplex A ℤ)]
    (hres : ∀ G : CochainComplex A ℤ, ∃ (P : CochainComplex A ℤ) (f : P ⟶ G),
      KFlat (curriedTensor A) P ∧ QuasiIso f)
    (h₁ : HasDerivedCategory.{w} A) (h₂ : HasDerivedCategory.{w'} A) :
    @Functor.Monoidal _ _ (@derivedMonoidal A _ _ _ _ _ _ _ _ _ _ _ h₁ _ hres) _ _
      (@derivedMonoidal A _ _ _ _ _ _ _ _ _ _ _ h₂ _ hres) (modelEquiv h₁ h₂).functor :=
  @Functor.kFlatComputedMonoidal A _ _ _ _ _ _ _ _ _ _ _ A _ _ _ _ _ _ _ _ _ _ _ (𝟭 A) _ _ _
    kFlat_mapHomologicalComplex_id _ _ h₁ h₂ hres hres _ (modelEquivKFlatQIso h₁ h₂)

end CategoryTheory

end
