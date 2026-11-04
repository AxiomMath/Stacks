module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexScheme
public import StacksFrontier.Homology.DerivedCategory.ModelComparisonExactFunctor

/-!
# Being a dualizing complex does not depend on the chosen derived category

`Stacks.Duality.IsDualizingComplex K` ([Stacks, Tag 0A87]) is stated for `K` in a chosen model
`HasDerivedCategory.{w} X.Modules` of `D(𝒪_X)`, and different parts of the library work at
different models: the twisted inverse image of [Stacks, Tag 0A9E] exists only at the locally
small model `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, while much of the rest is
stated at `CategoryTheory.HasDerivedCategory.standard`. This file proves that the predicate is
invariant under the comparison equivalence `StacksDraft.DerivedModel.modelEquiv` of two models.

The predicate reads `K` only through its restrictions to the affine opens, that is through the
exact functor `(Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory` into the (sealed,
standard) model of `D(𝒪_U)`, and that functor commutes with the comparison by
`StacksDraft.DerivedModel.modelEquivCompMapDerivedCategoryIso`.

## Main results

* `Stacks.Duality.isDualizingComplex_modelEquiv_iff` — for two models `h₁`, `h₂` and `K` in the
  first, `modelEquiv h₁ h₂` carries `K` to a dualizing complex iff `K` is one.
* `Stacks.Duality.isDualizingComplex_singleFunctor_model_iff` — a module placed in degree `n` is
  a dualizing complex at one model iff it is one at another.

## References

* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits StacksDraft.DerivedModel

universe u w z

namespace Stacks.Duality

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- At one affine open, carrying a dualizing model is invariant under the comparison of two
chosen derived categories of `𝒪_X`-modules. -/
theorem hasDualizingModelOn_modelEquiv_iff (h₁ : HasDerivedCategory.{w} X.Modules)
    (h₂ : HasDerivedCategory.{z} X.Modules) (K : @DerivedCategory X.Modules _ _ h₁)
    (U : X.Opens) (hU : IsAffineOpen U) :
    @HasDualizingModelOn X _ h₂ ((modelEquiv h₁ h₂).functor.obj K) U hU ↔
      @HasDualizingModelOn X _ h₁ K U hU := by
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let hU' := HasDerivedCategory.standard U.toScheme.Modules
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ(X, U))
  let e := (modelEquivCompMapDerivedCategoryIso (Scheme.Modules.restrictFunctor U.ι)
    h₁ h₂ hU').app K
  constructor
  · rintro ⟨ω, hω, ⟨i⟩⟩
    exact ⟨ω, hω, ⟨e.symm ≪≫ i⟩⟩
  · rintro ⟨ω, hω, ⟨i⟩⟩
    exact ⟨ω, hω, ⟨e ≪≫ i⟩⟩

/-- **Being a dualizing complex is model-independent.** For two chosen models `h₁`, `h₂` of the
derived category of `𝒪_X`-modules and `K` in the first, the comparison equivalence carries `K`
to a dualizing complex ([Stacks, Tag 0A87]) iff `K` is one. -/
theorem isDualizingComplex_modelEquiv_iff (h₁ : HasDerivedCategory.{w} X.Modules)
    (h₂ : HasDerivedCategory.{z} X.Modules) (K : @DerivedCategory X.Modules _ _ h₁) :
    @IsDualizingComplex X _ h₂ ((modelEquiv h₁ h₂).functor.obj K) ↔
      @IsDualizingComplex X _ h₁ K :=
  forall_congr' fun U => forall_congr' fun hU => hasDualizingModelOn_modelEquiv_iff h₁ h₂ K U hU

/-- **A module in one degree is a dualizing complex at one model iff at another.** For an
`𝒪_X`-module `M` and an integer `n`, `M[-n]` is a dualizing complex in the derived category of
the model `h₂` iff it is one in that of the model `h₁`. -/
theorem isDualizingComplex_singleFunctor_model_iff (h₁ : HasDerivedCategory.{w} X.Modules)
    (h₂ : HasDerivedCategory.{z} X.Modules) (n : ℤ) (M : X.Modules) :
    @IsDualizingComplex X _ h₂ ((@DerivedCategory.singleFunctor X.Modules _ _ h₂ n).obj M) ↔
      @IsDualizingComplex X _ h₁ ((@DerivedCategory.singleFunctor X.Modules _ _ h₁ n).obj M) := by
  have e : (modelEquiv h₁ h₂).functor.obj
      ((@DerivedCategory.singleFunctor X.Modules _ _ h₁ n).obj M) ≅
        (@DerivedCategory.singleFunctor X.Modules _ _ h₂ n).obj M :=
    (Functor.associator (CochainComplex.singleFunctor X.Modules n)
      (@DerivedCategory.Q X.Modules _ _ h₁) (modelEquiv h₁ h₂).functor).app M ≪≫
    (Functor.isoWhiskerLeft (CochainComplex.singleFunctor X.Modules n)
      (modelCompQIso h₁ h₂)).app M
  rw [← isDualizingComplex_modelEquiv_iff h₁ h₂]
  exact ⟨fun h => @isDualizingComplex_of_iso X _ h₂ _ _ e.symm h,
    fun h => @isDualizingComplex_of_iso X _ h₂ _ _ e h⟩

end Stacks.Duality

end
