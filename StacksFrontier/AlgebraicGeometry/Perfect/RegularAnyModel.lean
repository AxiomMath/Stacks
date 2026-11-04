module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import StacksFrontier.Homology.DerivedCategory.ModelComparison
public import StacksFrontier.Homology.Perfect.CompactObjectAnyModel
public import StacksFrontier.Homology.Perfect.Regular

/-!
# Perfect objects over a regular ring, at an arbitrary derived-category model

`HasDerivedCategory.{w} C` is a chosen localization of `CochainComplex C ℤ` at the
quasi-isomorphisms, with morphisms in `Type w`. This file shows that the comparison equivalence
`StacksDraft.DerivedModel.modelEquiv` of two chosen models identifies their cohomology functors
and the bounds of their canonical t-structures, and deduces the characterisation of perfect
objects over a regular ring at an arbitrary chosen derived category.

## Main definitions

* `StacksDraft.DerivedModel.modelEquivCompHomologyFunctorIso`: the comparison equivalence
  identifies the cohomology functors of the two models.

## Main results

* `StacksDraft.DerivedModel.isLE_modelEquiv_iff` and
  `StacksDraft.DerivedModel.isGE_modelEquiv_iff`: the comparison equivalence carries the bounds
  of the canonical t-structure both ways.
* `StacksDraft.Perfect.AnyModel.isPerfect_iff_bounded_finiteCohomology`: over a regular ring an
  object of `D(R)`, at an arbitrary chosen derived category, is perfect exactly when it is
  bounded with finite cohomology modules.

## References

* [Stacks Project, Tag 066Z](https://stacks.math.columbia.edu/tag/066Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

universe u v w z

namespace StacksDraft.DerivedModel

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- **The comparison equivalence of two chosen derived categories identifies their cohomology
functors.** -/
def modelEquivCompHomologyFunctorIso (h₁ : HasDerivedCategory.{w} C)
    (h₂ : HasDerivedCategory.{z} C) (n : ℤ) :
    (modelEquiv h₁ h₂).functor ⋙ @DerivedCategory.homologyFunctor C _ _ h₂ n ≅
      @DerivedCategory.homologyFunctor C _ _ h₁ n :=
  letI := h₁
  letI _l₁ : Localization.Lifting (@DerivedCategory.Q C _ _ h₁)
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n)
      ((modelEquiv h₁ h₂).functor ⋙ @DerivedCategory.homologyFunctor C _ _ h₂ n) :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (modelCompQIso h₁ h₂) _ ≪≫
      @DerivedCategory.homologyFunctorFactors C _ _ h₂ n⟩
  letI _l₂ : Localization.Lifting (@DerivedCategory.Q C _ _ h₁)
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n)
      (@DerivedCategory.homologyFunctor C _ _ h₁ n) :=
    ⟨@DerivedCategory.homologyFunctorFactors C _ _ h₁ n⟩
  Localization.liftNatIso (@DerivedCategory.Q C _ _ h₁)
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n)
    (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n)
    ((modelEquiv h₁ h₂).functor ⋙ @DerivedCategory.homologyFunctor C _ _ h₂ n)
    (@DerivedCategory.homologyFunctor C _ _ h₁ n) (Iso.refl _)

/-- Vanishing of the cohomology in degrees satisfying `p` is model-independent. -/
private theorem forall_isZero_homology_modelEquiv_iff (h₁ : HasDerivedCategory.{w} C)
    (h₂ : HasDerivedCategory.{z} C) (K : @DerivedCategory C _ _ h₁) (p : ℤ → Prop) :
    (∀ i, p i → IsZero ((@DerivedCategory.homologyFunctor C _ _ h₂ i).obj
      ((modelEquiv h₁ h₂).functor.obj K))) ↔
      ∀ i, p i → IsZero ((@DerivedCategory.homologyFunctor C _ _ h₁ i).obj K) :=
  forall_congr' fun i ↦ forall_congr' fun _ ↦
    ((modelEquivCompHomologyFunctorIso h₁ h₂ i).app K).isZero_iff

/-- **Being `≤ n` for the canonical t-structure is model-independent.** -/
theorem isLE_modelEquiv_iff (h₁ : HasDerivedCategory.{w} C) (h₂ : HasDerivedCategory.{z} C)
    (K : @DerivedCategory C _ _ h₁) (n : ℤ) :
    @DerivedCategory.IsLE C _ _ h₂ ((modelEquiv h₁ h₂).functor.obj K) n ↔
      @DerivedCategory.IsLE C _ _ h₁ K n := by
  rw [@DerivedCategory.isLE_iff C _ _ h₂, @DerivedCategory.isLE_iff C _ _ h₁]
  exact forall_isZero_homology_modelEquiv_iff h₁ h₂ K _

/-- **Being `≥ n` for the canonical t-structure is model-independent.** -/
theorem isGE_modelEquiv_iff (h₁ : HasDerivedCategory.{w} C) (h₂ : HasDerivedCategory.{z} C)
    (K : @DerivedCategory C _ _ h₁) (n : ℤ) :
    @DerivedCategory.IsGE C _ _ h₂ ((modelEquiv h₁ h₂).functor.obj K) n ↔
      @DerivedCategory.IsGE C _ _ h₁ K n := by
  rw [@DerivedCategory.isGE_iff C _ _ h₂, @DerivedCategory.isGE_iff C _ _ h₁]
  exact forall_isZero_homology_modelEquiv_iff h₁ h₂ K _

end StacksDraft.DerivedModel

namespace StacksDraft.Perfect.AnyModel

open StacksDraft.DerivedModel

/-- **Perfect objects over a regular ring, at an arbitrary chosen derived category.** Over a
regular ring `R`, an object of `D(R)` is perfect if and only if it is bounded on both sides for
the canonical t-structure and all of its cohomology modules are finite. -/
theorem isPerfect_iff_bounded_finiteCohomology {R : Type u} [CommRing R] [IsRegularRing R]
    [h : HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    (K : DerivedCategory (ModuleCat.{max u v} R)) :
    IsPerfect K ↔
      ((∃ a : ℤ, K.IsGE a) ∧ (∃ b : ℤ, K.IsLE b) ∧
        ∀ i : ℤ, Module.Finite R
          ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj K)) := by
  let hstd := HasDerivedCategory.standard (ModuleCat.{max u v} R)
  rw [isPerfect_iff_isPerfect_modelEquiv h hstd K,
    (StacksDraft.Perfect.isPerfectModule_iff_finite_and_isPerfect_iff_bounded_finiteCohomology.{u,
      v} (R := R)).2]
  refine and_congr (exists_congr fun a ↦ isGE_modelEquiv_iff h hstd K a)
    (and_congr (exists_congr fun b ↦ isLE_modelEquiv_iff h hstd K b)
      (forall_congr' fun i ↦ ?_))
  exact Module.Finite.equiv_iff ((modelEquivCompHomologyFunctorIso h hstd i).app K).toLinearEquiv

end StacksDraft.Perfect.AnyModel

end
