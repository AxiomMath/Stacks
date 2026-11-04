module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianDerivedRealization
public import StacksFrontier.CategoryTheory.Sites.Simplicial.IntegerProjectionStructure

/-!
# The face identity of Stacks 0D9K, in the spelling of the derived transition

Let `S` be a simplicial-site situation. The transition of Stacks 07TF has two spellings:
`CategoryTheory.SimplicialSiteSituation.fiberTransitionAb'`, built from the inverse image
`CategoryTheory.SimplicialSiteSituation.transitionInverseImageAb` of Stacks 04JC, and
`CategoryTheory.SimplicialSiteSituation.abelianTransitionOfFiber'`, built from the inverse image
`CategoryTheory.SimplicialSiteSituation.abelianTransition` along the transition morphism of
topoi; they differ by the comparison
`CategoryTheory.SimplicialSiteSituation.transitionInverseImageAbIso`. This file states the face
identity relating the comparison map of Stacks 0D9E (1) and the simplicial structure map of the
integral resolution of Stacks 09WI in the second spelling.

## Main results

* `CategoryTheory.SimplicialSiteSituation.fiberTransitionAb_app_eq`: the transition
  `fiberTransitionAb'` at a sheaf is the comparison of the two inverse images followed by
  `abelianTransitionOfFiber'`.
* `CategoryTheory.SimplicialSiteSituation.componentSumFormulaLeg_eq_abelianTransitionLeg_app`: the
  `φ`-labelled leg of the direct-sum formula of Stacks 09WG is the comparison of the two inverse
  images followed by the leg in the spelling of the derived transition.
* `CategoryTheory.SimplicialSiteSituation`
  `.abelianTransitionOfFiber_comp_integerProjectionSheaf_comp_integerTensorFace`: the comparison
  of Stacks 0D9E in degree `q` followed by the structure map of the integral resolution at
  `φ : p ⟶ q`, both transported along `abelianTransitionOfFiber'`, is the transpose of the leg in
  that spelling followed by the comparison in degree `p`.
* `CategoryTheory.SimplicialSiteSituation`
  `.whiskerRight_abelianTransitionOfFiber_comp_integerProjectionSheaf_comp_integerTensorFace`:
  the same identity as an identity of transformations of functors.

## References

* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 09WI](https://stacks.math.columbia.edu/tag/09WI)
* [Stacks Project, Tag 0D9E](https://stacks.math.columbia.edu/tag/0D9E)
* [Stacks Project, Tag 0D9K](https://stacks.math.columbia.edu/tag/0D9K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u})

/-- The transition of Stacks 07TF at a sheaf `F`, in the spelling of the derived transition: the
comparison of the inverse image of Stacks 04JC with the inverse image along the transition morphism
of topoi, followed by `abelianTransitionOfFiber'`. -/
theorem fiberTransitionAb_app_eq {p q : SimplexCategory} (φ : p ⟶ q)
    (F : Sheaf S.totalTopology Ab.{u}) :
    (S.fiberTransitionAb' φ).app F =
      (S.transitionInverseImageAbIso φ).hom.app ((S.restrictAb p).obj F) ≫
        (S.abelianTransitionOfFiber' φ).app F :=
  congr_app (S.fiberTransitionAb_eq' φ) F

/-- The `φ`-labelled leg `componentSumFormulaLeg'` of the direct-sum formula of Stacks 09WG is the
comparison of the two inverse images, followed by the unit of `g_{p!} ⊣ g_p^{-1}` transported
along the inverse image along the transition morphism of topoi, followed by
`abelianTransitionOfFiber'`. -/
theorem componentSumFormulaLeg_eq_abelianTransitionLeg_app {p q : SimplexCategory} (φ : p ⟶ q)
    (X : Sheaf (S.componentTopology p) Ab.{u}) :
    (S.componentSumFormulaLeg' φ).app X =
      (S.transitionInverseImageAbIso φ).hom.app X ≫
        (abelianTransition S φ).map ((S.componentLowerShriekAbAdjunction' p).unit.app X) ≫
          (S.abelianTransitionOfFiber' φ).app ((componentLowerShriekAb S p).obj X) := by
  refine Eq.trans (S.componentSumFormulaLeg_app' φ X) ?_
  refine Eq.trans (congrArg
    (fun k => (S.transitionInverseImageAb φ).map
      ((S.componentLowerShriekAbAdjunction' p).unit.app X) ≫ k)
    (S.fiberTransitionAb_app_eq φ ((componentLowerShriekAb S p).obj X))) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg
    (fun k => k ≫ (S.abelianTransitionOfFiber' φ).app ((componentLowerShriekAb S p).obj X))
    ((S.transitionInverseImageAbIso φ).hom.naturality
      ((S.componentLowerShriekAbAdjunction' p).unit.app X))) ?_
  exact Category.assoc _ _ _

/-- The face identity of Stacks 0D9K, in the spelling of the derived transition: the
comparison of Stacks 0D9E in degree `q` followed by the structure map of the integral resolution
of Stacks 09WI at `φ : p ⟶ q`, both transported along the transition `abelianTransitionOfFiber'`
of Stacks 07TF, is the transpose along `g_{q!} ⊣ g_q^{-1}` of the `φ`-labelled leg of the
direct-sum formula of Stacks 09WG in that same spelling, followed by the comparison of
Stacks 0D9E in degree `p`. -/
theorem abelianTransitionOfFiber_comp_integerProjectionSheaf_comp_integerTensorFace
    {p q : SimplexCategory} (φ : p ⟶ q) (F : Sheaf S.totalTopology Ab.{u}) :
    (componentLowerShriekAb S q).map ((S.abelianTransitionOfFiber' φ).app F) ≫
        (integerProjectionSheaf S q).app F ≫ (integerTensorFace S φ).app F =
      ((S.componentLowerShriekAbAdjunction' q).homEquiv _ _).symm
          ((abelianTransition S φ).map
              ((S.componentLowerShriekAbAdjunction' p).unit.app ((S.restrictAb p).obj F)) ≫
            (S.abelianTransitionOfFiber' φ).app
              ((componentLowerShriekAb S p).obj ((S.restrictAb p).obj F))) ≫
        (integerProjectionSheaf S p).app F := by
  refine (cancel_epi ((componentLowerShriekAb S q).map
    ((S.transitionInverseImageAbIso φ).hom.app ((S.restrictAb p).obj F)))).1 ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg
    (fun k => k ≫ (integerProjectionSheaf S q).app F ≫ (integerTensorFace S φ).app F)
    (Eq.trans ((componentLowerShriekAb S q).map_comp _ _).symm
      (congrArg (componentLowerShriekAb S q).map
        (S.fiberTransitionAb_app_eq φ F).symm))) ?_
  refine Eq.trans
    (S.fiberTransition_comp_integerProjectionSheaf_comp_integerTensorFace φ F) ?_
  refine Eq.trans (congrArg
    (fun k => ((S.componentLowerShriekAbAdjunction' q).homEquiv _ _).symm k ≫
      (integerProjectionSheaf S p).app F)
    (S.componentSumFormulaLeg_eq_abelianTransitionLeg_app φ ((S.restrictAb p).obj F))) ?_
  refine Eq.trans (congrArg (fun k => k ≫ (integerProjectionSheaf S p).app F)
    ((S.componentLowerShriekAbAdjunction' q).homEquiv_naturality_left_symm
      ((S.transitionInverseImageAbIso φ).hom.app ((S.restrictAb p).obj F)) _)) ?_
  exact Category.assoc _ _ _

/-- The face identity of Stacks 0D9K as an identity of transformations of functors
`(g_p^{-1} ⋙ f_φ^{-1}) ⋙ g_{q!} ⟶ g_{p!}ℤ ⊗_ℤ -`: the components are the two sides of
`abelianTransitionOfFiber_comp_integerProjectionSheaf_comp_integerTensorFace`, with the transpose
of the leg spelled out as `g_{q!}` of the leg followed by the counit of `g_{q!} ⊣ g_q^{-1}`. -/
theorem whiskerRight_abelianTransitionOfFiber_comp_integerProjectionSheaf_comp_integerTensorFace
    {p q : SimplexCategory} (φ : p ⟶ q) :
    Functor.whiskerRight (S.abelianTransitionOfFiber' φ) (componentLowerShriekAb S q) ≫
        integerProjectionSheaf S q ≫ integerTensorFace S φ =
      Functor.whiskerRight
          (Functor.whiskerLeft (S.restrictAb p)
            (Functor.whiskerRight (S.componentLowerShriekAbAdjunction' p).unit
                (abelianTransition S φ) ≫
              Functor.whiskerLeft (componentLowerShriekAb S p)
                (S.abelianTransitionOfFiber' φ)))
          (componentLowerShriekAb S q) ≫
        Functor.whiskerLeft (S.restrictAb p ⋙ componentLowerShriekAb S p)
            (S.componentLowerShriekAbAdjunction' q).counit ≫
          (Functor.rightUnitor (S.restrictAb p ⋙ componentLowerShriekAb S p)).hom ≫
            integerProjectionSheaf S p := by
  refine NatTrans.ext (funext fun F => ?_)
  refine Eq.trans
    (S.abelianTransitionOfFiber_comp_integerProjectionSheaf_comp_integerTensorFace φ F) ?_
  refine Eq.trans (congrArg (fun k => k ≫ (integerProjectionSheaf S p).app F)
    ((S.componentLowerShriekAbAdjunction' q).homEquiv_counit _ _ _)) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact congrArg
    (fun k => (componentLowerShriekAb S q).map
      ((Functor.whiskerLeft (S.restrictAb p)
        (Functor.whiskerRight (S.componentLowerShriekAbAdjunction' p).unit
            (abelianTransition S φ) ≫
          Functor.whiskerLeft (componentLowerShriekAb S p)
            (S.abelianTransitionOfFiber' φ))).app F) ≫
      (S.componentLowerShriekAbAdjunction' q).counit.app
        ((componentLowerShriekAb S p).obj ((S.restrictAb p).obj F)) ≫ k)
    (Category.id_comp ((integerProjectionSheaf S p).app F)).symm

end CategoryTheory.SimplicialSiteSituation

end
