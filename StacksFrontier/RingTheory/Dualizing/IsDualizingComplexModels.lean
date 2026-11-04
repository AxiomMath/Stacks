module

public import StacksFrontier.RingTheory.Dualizing.Complex
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategoryModel

/-!
# Being a dualizing complex over a ring does not depend on the chosen derived category

`Dualizing.IsDualizingComplex K` ([Stacks, Tag 0A7B]) is stated for `K` in a chosen model
`HasDerivedCategory.{w} (ModuleCat.{v} A)` of `D(A)`. Different parts of the library work at
different models (`HasDerivedCategory.standard` versus the locally small models), and
`HasDerivedCategory` carries data, so two models give genuinely different types. This file
proves that the predicate is invariant under the comparison equivalence
`StacksDraft.DerivedModel.modelEquiv` of two models, and hence that a Noetherian ring *has a
dualizing complex* at one model iff it has one at any other.

Each of the three clauses of the definition reads `K` only up to isomorphism, through the
localization functor `Q`, which the comparison intertwines (`modelCompQIso`), and through the
cohomology functors, which it also intertwines (`modelHomologyFunctorIso`).

## Main results

* `StacksDraft.InjectiveDimension.hasInjectiveAmplitude_modelEquiv_iff`,
  `StacksDraft.InjectiveDimension.hasFiniteInjectiveDimension_modelEquiv_iff`
* `Dualizing.isDualizingComplex_modelEquiv_iff`
* `Dualizing.exists_isDualizingComplex_iff_of_models`

## References

* [Stacks Project, Tag 0A7B](https://stacks.math.columbia.edu/tag/0A7B)
* [Stacks Project, Tag 0A5S](https://stacks.math.columbia.edu/tag/0A5S)
-/

@[expose] public section

open CategoryTheory StacksDraft.DerivedModel

universe u v w z

namespace StacksDraft.InjectiveDimension

variable {C : Type u} [Category.{v} C] [Abelian C]
  (h₁ : HasDerivedCategory.{w} C) (h₂ : HasDerivedCategory.{z} C)

/-- Being isomorphic to `Q.obj I` is invariant under the comparison of two models. -/
private theorem nonempty_iso_Q_modelEquiv_iff (K : @DerivedCategory C _ _ h₁)
    (I : CochainComplex C ℤ) :
    Nonempty ((modelEquiv h₁ h₂).functor.obj K ≅ @DerivedCategory.Q C _ _ h₂ |>.obj I) ↔
      Nonempty (K ≅ @DerivedCategory.Q C _ _ h₁ |>.obj I) :=
  ⟨fun ⟨e⟩ => ⟨(modelEquiv h₁ h₂).fullyFaithfulFunctor.preimageIso
      (e ≪≫ ((modelCompQIso h₁ h₂).app I).symm)⟩,
    fun ⟨e⟩ => ⟨(modelEquiv h₁ h₂).functor.mapIso e ≪≫ (modelCompQIso h₁ h₂).app I⟩⟩

/-- Injective amplitude in `[a, b]` is invariant under the comparison of two models of the
derived category. -/
theorem hasInjectiveAmplitude_modelEquiv_iff (K : @DerivedCategory C _ _ h₁) (a b : ℤ) :
    @HasInjectiveAmplitude C _ _ h₂ ((modelEquiv h₁ h₂).functor.obj K) a b ↔
      @HasInjectiveAmplitude C _ _ h₁ K a b := by
  unfold HasInjectiveAmplitude
  simp only [nonempty_iso_Q_modelEquiv_iff]

/-- Finite injective dimension is invariant under the comparison of two models of the derived
category. -/
theorem hasFiniteInjectiveDimension_modelEquiv_iff (K : @DerivedCategory C _ _ h₁) :
    @HasFiniteInjectiveDimension C _ _ h₂ ((modelEquiv h₁ h₂).functor.obj K) ↔
      @HasFiniteInjectiveDimension C _ _ h₁ K := by
  unfold HasFiniteInjectiveDimension
  simp only [hasInjectiveAmplitude_modelEquiv_iff]

end StacksDraft.InjectiveDimension

namespace Dualizing

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  (h₁ : HasDerivedCategory.{w} (ModuleCat.{v} A)) (h₂ : HasDerivedCategory.{z} (ModuleCat.{v} A))

/-- **Being a dualizing complex does not depend on the model.** For two models `h₁`, `h₂` of the
derived category of `A`-modules and `K` in the first, the comparison `modelEquiv h₁ h₂` carries
`K` to a dualizing complex iff `K` is one. -/
theorem isDualizingComplex_modelEquiv_iff (K : @DerivedCategory (ModuleCat.{v} A) _ _ h₁) :
    @IsDualizingComplex A _ _ h₂ ((modelEquiv h₁ h₂).functor.obj K) ↔
      @IsDualizingComplex A _ _ h₁ K := by
  have hhom : ∀ i : ℤ,
      Module.Finite A ((@DerivedCategory.homologyFunctor (ModuleCat.{v} A) _ _ h₂ i).obj
          ((modelEquiv h₁ h₂).functor.obj K)) ↔
        Module.Finite A ((@DerivedCategory.homologyFunctor (ModuleCat.{v} A) _ _ h₁ i).obj K) :=
    fun i =>
      let e : ((@DerivedCategory.homologyFunctor (ModuleCat.{v} A) _ _ h₂ i).obj
            ((modelEquiv h₁ h₂).functor.obj K)) ≃ₗ[A]
          ((@DerivedCategory.homologyFunctor (ModuleCat.{v} A) _ _ h₁ i).obj K) :=
        ((modelHomologyFunctorIso h₁ h₂ i).app K).toLinearEquiv
      ⟨fun _ => Module.Finite.equiv e, fun _ => Module.Finite.equiv e.symm⟩
  have hQ : ∀ I : CochainComplex (ModuleCat.{v} A) ℤ,
      Nonempty ((@DerivedCategory.Q (ModuleCat.{v} A) _ _ h₂).obj I ≅
          (modelEquiv h₁ h₂).functor.obj K) ↔
        Nonempty ((@DerivedCategory.Q (ModuleCat.{v} A) _ _ h₁).obj I ≅ K) := fun I => by
    rw [Iso.nonempty_iso_symm, StacksDraft.InjectiveDimension.nonempty_iso_Q_modelEquiv_iff,
      Iso.nonempty_iso_symm]
  constructor
  · intro hK
    exact @IsDualizingComplex.mk A _ _ h₁ K
      ((StacksDraft.InjectiveDimension.hasFiniteInjectiveDimension_modelEquiv_iff h₁ h₂ K).mp
        (@IsDualizingComplex.finiteInjectiveDimension A _ _ h₂ _ hK))
      (fun i => (hhom i).mp (@IsDualizingComplex.finiteCohomology A _ _ h₂ _ hK i))
      (fun I hI => @IsDualizingComplex.homothetyQuasiIso A _ _ h₂ _ hK I ((hQ I).mpr hI))
  · intro hK
    exact @IsDualizingComplex.mk A _ _ h₂ _
      ((StacksDraft.InjectiveDimension.hasFiniteInjectiveDimension_modelEquiv_iff h₁ h₂ K).mpr
        (@IsDualizingComplex.finiteInjectiveDimension A _ _ h₁ _ hK))
      (fun i => (hhom i).mpr (@IsDualizingComplex.finiteCohomology A _ _ h₁ _ hK i))
      (fun I hI => @IsDualizingComplex.homothetyQuasiIso A _ _ h₁ _ hK I ((hQ I).mp hI))

/-- **Having a dualizing complex does not depend on the model.** A Noetherian ring has a
dualizing complex in one model of the derived category of its modules iff it has one in any
other. -/
theorem exists_isDualizingComplex_iff_of_models :
    (∃ K : @DerivedCategory (ModuleCat.{v} A) _ _ h₁, @IsDualizingComplex A _ _ h₁ K) ↔
      ∃ K : @DerivedCategory (ModuleCat.{v} A) _ _ h₂, @IsDualizingComplex A _ _ h₂ K :=
  ⟨fun ⟨K, hK⟩ => ⟨(modelEquiv h₁ h₂).functor.obj K,
      (isDualizingComplex_modelEquiv_iff h₁ h₂ K).mpr hK⟩,
    fun ⟨K, hK⟩ => ⟨(modelEquiv h₂ h₁).functor.obj K,
      (isDualizingComplex_modelEquiv_iff h₂ h₁ K).mpr hK⟩⟩

end Dualizing

end
