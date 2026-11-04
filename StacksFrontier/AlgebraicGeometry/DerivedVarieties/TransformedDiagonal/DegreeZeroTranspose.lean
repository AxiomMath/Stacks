module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.TransformedDiagonal.ImageKunnethAssembly

/-!
# The transpose of a morphism is natural in the target

`AlgebraicGeometry.homTranspose φ : 𝒪_V ⟶ R𝓗om(K, K')` is the morphism that [Stacks, Tag 08JA]
matches with the class [Stacks, Tag 08DK] attaches to `φ : K ⟶ K'`.  It is natural in the target,
so it is the transpose of the identity followed by `R𝓗om(K, φ)`, and it is a bijection.

## Main results

* `AlgebraicGeometry.homTranspose_comp`: `homTranspose` is natural in the target.
* `AlgebraicGeometry.homTranspose_eq_comp`: `homTranspose φ` is `homTranspose (𝟙 K)` followed by
  `R𝓗om(K, φ)`.
* `AlgebraicGeometry.homTranspose_surjective`: `homTranspose` is surjective.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

universe u


namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard


variable (k : Type u) [Field k] (V : Over (Spec (.of k)))

/-- **`homTranspose` is natural in the target**: `t_{φ ≫ χ} = t_φ ≫ R𝓗om(K, χ)`.  Both sides have
the same class, by the naturality of [Stacks, Tag 08DK]
(`AlgebraicGeometry.homLinearEquivDegreeZeroSections_comp`) and of the class map
(`AlgebraicGeometry.degreeZeroClassAddEquiv_comp`), and the class map is injective. -/
theorem homTranspose_comp (K K' K'' : DerivedCategory V.left.Modules) (φ : K ⟶ K')
    (χ : K' ⟶ K'') :
    homTranspose k V K K'' (φ ≫ χ) = homTranspose k V K K' φ ≫ (sheafHomOutOf k V K).map χ := by
  let : Linear k V.left.Modules := modulesLinear k V
  apply (degreeZeroClassAddEquiv k V (derivedSheafHomObj k V K K'')).injective
  refine (homLinearEquivDegreeZeroSections_eq_class k V K K'' (φ ≫ χ)).symm.trans ?_
  refine (homLinearEquivDegreeZeroSections_comp k V K K' K'' φ χ).trans ?_
  refine (congrArg _ (homLinearEquivDegreeZeroSections_eq_class k V K K' φ)).trans ?_
  exact (degreeZeroClassAddEquiv_comp k V (homTranspose k V K K' φ)
    ((sheafHomOutOf k V K).map χ)).symm

/-- `homTranspose` is surjective: it is the composite of two bijections. -/
theorem homTranspose_surjective (K K' : DerivedCategory V.left.Modules) :
    Function.Surjective (homTranspose k V K K') := fun y =>
  ⟨derivedSheafHomGlobalSectionsEquivScheme k V K K'
    ((structureSheafGlobalSectionsEquivScheme k V (derivedSheafHomObj k V K K')).symm y), by
    rw [homTranspose, AddEquiv.symm_apply_apply, AddEquiv.apply_symm_apply]⟩

/-- `homTranspose` at a morphism is the transpose of the identity followed by `R𝓗om(K, φ)`. -/
theorem homTranspose_eq_comp (K K' : DerivedCategory V.left.Modules) (φ : K ⟶ K') :
    homTranspose k V K K' φ = homTranspose k V K K (𝟙 K) ≫ (sheafHomOutOf k V K).map φ := by
  have h1 := homTranspose_comp k V K K K' (𝟙 K) φ
  rw [Category.id_comp] at h1
  exact h1


end AlgebraicGeometry

end
