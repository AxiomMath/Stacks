module

public import StacksFrontier.CategoryTheory.Monoidal.MateAsInternalHomPre
public import StacksFrontier.Algebra.Homology.SignedDualComplexFunctorial
public import StacksFrontier.Homology.MapHomologicalComplexMonoidal

/-!
# The mate of a chain map for the dual-complex pairings is the induced map of dual complexes

`CochainComplex.exactPairingDualComplex` exhibits `CochainComplex.dualComplex K D q` as a dual of
`K` in the monoidal category of complexes, and `CochainComplex.dualComplexMap` is the morphism of
dual complexes that a chain map `φ : K ⟶ K'` induces — defined degreewise, as the mate of `φ^n`
for the *degreewise* pairings, with no reference to the pairing of complexes. This file identifies
the two: the mate of `φ` for the two complex-level pairings **is** `dualComplexMap`.

Without this, the degreewise construction and the complex-level duality have nothing to do with
each other, and a mate taken in the derived category cannot be computed by the explicit map of
dual complexes.

## Main results

* `CochainComplex.ι_evaluation_exactPairingDualComplex`: the evaluation of the complex-level
  pairing, restricted to the summand `D^{-m} ⊗ K^m` of its degree-zero part, is the degreewise
  evaluation.
* `CochainComplex.mate_exactPairingDualComplex`: **the mate of `φ` for the pairings of
  `CochainComplex.exactPairingDualComplex` is `CochainComplex.dualComplexMap`.**

## Implementation notes

**Why a contraction and not a degreewise comparison.** The components of
`CategoryTheory.ExactPairing.mate` of complexes are not available: the mate is built from the
summed coevaluation and the associator of complexes. What *is* available is
`CategoryTheory.ExactPairing.eq_mate`, which pins a candidate down from the identity
`g ▷ K ≫ ε_K = D'^• ◁ φ ≫ ε_{K'}` without unfolding the mate at all. Both sides of that identity
are morphisms out of `D'^• ⊗ K` into the unit complex, which is concentrated in degree zero; in
degree zero they are compared summand by summand, and on the summand `D'^{-m} ⊗ K^m` each side is
the corresponding whiskering followed by the degreewise evaluation
(`CochainComplex.ι_evaluation_exactPairingDualComplex`), so the identity is exactly
`CategoryTheory.ExactPairing.mate_comp_evaluation` for the degreewise pairings — which is what
`CochainComplex.dualComplexMap` is defined by.

**No tag.** [Stacks, Tag 0FPR] constructs the dual complex and its pairing but states no
functoriality, and §4.21.48 has no numbered statement comparing a mate of complexes with a
degreewise mate.

## References

* [Stacks Project, Tag 0FPR](https://stacks.math.columbia.edu/tag/0FPR)
* [Stacks Project, Tag 0FNK](https://stacks.math.columbia.edu/tag/0FNK)
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory GradedObject

noncomputable section

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]
  [MonoidalPreadditive C] [HasZeroObject C]
  [∀ (X₁ X₂ : GradedObject ℤ C), GradedObject.HasTensor X₁ X₂]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ X₁ : C, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂ : C, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]

variable (K : CochainComplex C ℤ) (D : ℤ → C)
  (q : ∀ i j : ℤ, i + j = 0 → ExactPairing (K.X i) (D j))

/-- **The evaluation of the dual-complex pairing on a summand is the degreewise evaluation.**
The evaluation is concentrated in degree zero, and the summands of the degree-zero part of
`D^• ⊗ K` are the `D^{-m} ⊗ K^m`. -/
theorem ι_evaluation_exactPairingDualComplex (s : Finset ℤ)
    (hK : ∀ m, m ∉ s → IsZero (K.X m)) (m : ℤ) :
    HomologicalComplex.ιTensorObj (dualComplex K D q) K (-m) m 0 (by omega) ≫
        (exactPairingDualComplex K D q s hK).evaluation'.f 0 =
      (dualPairing K D q m).evaluation' ≫ Monoidal.tensorUnit₀.inv ≫
        (HomologicalComplex.tensorUnitIso C (ComplexShape.up ℤ)).hom 0 :=
  ι_evaluationHom_f_zero K (dualComplex K D q) (dualPairing K D q) _ m

variable (K' : CochainComplex C ℤ) (D' : ℤ → C)
  (q' : ∀ i j : ℤ, i + j = 0 → ExactPairing (K'.X i) (D' j))
  (φ : K ⟶ K')

/-- **The mate of a chain map for the dual-complex pairings is the induced map of dual
complexes.** The mate of `φ : K ⟶ K'` for the two pairings of
`CochainComplex.exactPairingDualComplex` is `CochainComplex.dualComplexMap`, whose degree-`j`
component is the mate of `φ^{-j}` for the degreewise pairings. -/
theorem mate_exactPairingDualComplex (s : Finset ℤ) (hK : ∀ m, m ∉ s → IsZero (K.X m))
    (s' : Finset ℤ) (hK' : ∀ m, m ∉ s' → IsZero (K'.X m)) :
    ExactPairing.mate (exactPairingDualComplex K D q s hK)
        (exactPairingDualComplex K' D' q' s' hK') φ =
      dualComplexMap K D q K' D' q' φ := by
  refine (ExactPairing.eq_mate _ _ φ _ (HomologicalComplex.hom_ext _ _ fun j => ?_)).symm
  by_cases hj : j = 0
  · subst hj
    refine HomologicalComplex.mapBifunctor.hom_ext fun a b hab => ?_
    have hab' : a + b = 0 := hab
    obtain rfl : a = -b := by omega
    have hdeg : (dualComplexMap K D q K' D' q' φ).f (-b) ▷ K.X b ≫
          (dualPairing K D q b).evaluation' =
        (dualComplex K' D' q').X (-b) ◁ φ.f b ≫ (dualPairing K' D' q' b).evaluation' := by
      rw [dualComplexMap_f, dualComplexMapX_eq K D q K' D' q' φ b (-b) (by omega),
        dualMate_eq_mate_dualPairing]
      exact ExactPairing.mate_comp_evaluation (dualPairing K D q b) (dualPairing K' D' q' b)
        (φ.f b)
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
      HomologicalComplex.Monoidal.ι_whiskerRight_assoc,
      HomologicalComplex.Monoidal.ι_whiskerLeft_assoc,
      ι_evaluation_exactPairingDualComplex, ι_evaluation_exactPairingDualComplex]
    exact (Category.assoc _ _ _).symm.trans ((hdeg =≫ _).trans (Category.assoc _ _ _))
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (𝟙_ C) j hj).eq_of_tgt _ _

end CochainComplex

end

end
