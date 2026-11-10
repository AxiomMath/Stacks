module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationResolutionTerms

/-!
# The simplicial structure of the simplex-coefficient resolution, read through Stacks 09WG

Let `S` be a simplicial-site situation and `F` an abelian sheaf on its total site. The
simplex-coefficient resolution `barSimplicial S F` of
`StacksFrontier/CategoryTheory/Sites/Simplicial/AugmentationResolution.lean` has in degree `n` the
sheafification of the presheaf whose sections over an object of simplicial degree `k` are indexed
by the simplex maps `⦋n⦌ ⟶ ⦋k⦌`, and
`StacksFrontier/CategoryTheory/Sites/Simplicial/AugmentationResolutionTerms.lean` identifies that
degree with the lower shriek image `g_{n!}(F_n)` through the comparison
`CategoryTheory.SimplicialSiteSituation.componentLowerShriekMap`, which Stacks 09WG makes an
isomorphism for a cartesian `F`.

What that file does *not* say is what the simplicial structure maps of the resolution become
under the comparison. This file says it. Over the component of degree `q`, the degree-`q` term of
the resolution carries the distinguished summand labelled by the identity simplex map
(`componentSheafInclusion`), and the structure map at `φ : ⦋p⦌ ⟶ ⦋q⦌` reindexes the summands by
precomposition with `φ`, so it carries that summand to the summand labelled `φ`
(`componentSheafSummand`). Transposed along `g_{q!} ⊣ g_q^{-1}` this says that the `φ`-structure
map of the resolution is, under the comparison, the `φ`-labelled leg
`CategoryTheory.SimplicialSiteSituation.componentSumFormulaLeg` of the direct-sum formula of
Stacks 09WG.

This is what a proof of the exactness of the complex of Stacks 0D79 in every degree needs about
the resolution of Stacks 0D78: that the differentials of that resolution, which are the
alternating sums of the maps described here, are the mates of the cosimplicial transitions of
that complex.

## Main results

* `CategoryTheory.SimplicialSiteSituation`
  `.componentPresheafInclusion_comp_simplexCoefficientDiagram_map`: on sections, the
  identity-labelled summand of degree `q` followed by the simplicial structure map at `φ` is the
  `φ`-labelled summand of degree `p`.
* `CategoryTheory.SimplicialSiteSituation.componentSheafInclusion_comp_barSimplicial_map`: the
  same after sheafification, as a statement about abelian sheaves on the component of degree `q`.
* `CategoryTheory.SimplicialSiteSituation.componentLowerShriekMap_comp_barSimplicial_map`: the
  comparison of degree `q` followed by the simplicial structure map at `φ` is the transpose of
  the `φ`-labelled summand.
* `CategoryTheory.SimplicialSiteSituation`
  `.componentSumFormulaLeg_comp_abelianComponent_map_componentLowerShriekMap`:
  the `φ`-labelled leg of the direct-sum formula of Stacks 09WG, followed by the comparison of
  degree `p`, is the `φ`-labelled summand, transported along the inverse-image transition at `φ`.
* `CategoryTheory.SimplicialSiteSituation`
  `.fiberTransitionAb_app_comp_componentSheafInclusion_comp_barSimplicial_map`:
  the two together — **the simplicial structure map of the resolution at `φ`, transposed along
  `g_{q!} ⊣ g_q^{-1}`, is the `φ`-labelled leg of Stacks 09WG followed by the comparison of
  degree `p`.** For a cartesian `F` the inverse-image transition on the left is invertible and
  the comparisons are isomorphisms, so this determines the structure map outright.

## Implementation notes

The presheaf computation is one application of
`CategoryTheory.SimplicialSiteSituation.ι_copowerMap`: the structure map of the
simplex-coefficient diagram at `φ.op` is the copower map of precomposition by `φ`, so it sends
the summand labelled by a simplex map `σ` to the one labelled `φ ≫ σ`, and the identity label
travels to the label `φ`.

The transposed form is proved through the naturality of the inverse-image transition rather than
through the direct-sum decomposition of the degree-`q` restriction of the resolution: the
codomain of `componentSumFormulaLeg` is spelled with
`CategoryTheory.SimplicialSiteSituation.abelianComponent` and that of the sum formula
`componentLowerShriekRestrictionIsoCoproduct` with the direct image along the component functor,
and although the two functors are definitionally equal a rewrite elaborates its motive at a
reduced transparency and fails between them.

## References

* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 0D78](https://stacks.math.columbia.edu/tag/0D78)
* [Stacks Project, Tag 0D79](https://stacks.math.columbia.edu/tag/0D79)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (F : Sheaf S.totalTopology Ab.{u})

/-- On sections over an object of the component of degree `q`, the summand of the degree-`q` term
of the simplex-coefficient presheaf labelled by the identity, followed by the simplicial structure
map at `φ : ⦋p⦌ ⟶ ⦋q⦌`, is the summand of the degree-`p` term labelled by `φ`: the structure map
reindexes the summands by precomposition with `φ`. -/
theorem componentPresheafInclusion_comp_simplexCoefficientDiagram_map
    {p q : SimplexCategory} (φ : p ⟶ q) (U : S.component q) :
    (componentPresheafInclusion S F q).app (Opposite.op U) ≫
        ((simplexCoefficientDiagram ((degreeFunctor S).leftOp) F.obj).map φ.op).app
          (Opposite.op ((S.componentFunctor q).obj U)) =
      (componentPresheafSummand S F φ).app (Opposite.op U) := by
  rw [componentPresheafSummand_app]
  change Sigma.ι _ (eqToHom (degreeFunctor_leftOp_obj_op_componentFunctor_obj S q U).symm) ≫
      copowerMap (fun α => φ ≫ α) (𝟙 (F.obj.obj
        (Opposite.op ((S.componentFunctor q).obj U)))) = _
  rw [ι_copowerMap, Category.id_comp]

/-- On sections over an object of the component of degree `q`, the summand of the degree-`q` term
of the simplex-coefficient presheaf labelled by the identity, followed by the simplicial structure
map at `φ : ⦋p⦌ ⟶ ⦋q⦌`, is the summand of the degree-`p` term labelled by `φ`: the structure map
reindexes the summands by precomposition with `φ`. -/
theorem componentPresheafInclusion_comp_simplexCoefficientDiagram_map'
    {p q : SimplexCategory} (φ : p ⟶ q) (U : S.component q) :
    (componentPresheafInclusion' S F q).app (Opposite.op U) ≫
        (((simplexCoefficientDiagram' (totalSimplexDegree S).leftOp).obj F.obj).map φ.op).app
          (Opposite.op ((S.componentFunctor q).obj U)) =
      (componentPresheafSummand' S F φ).app (Opposite.op U) := by
  rw [componentPresheafSummand_app']
  change Sigma.ι _ (eqToHom (totalSimplexDegree_leftOp_obj_op_componentFunctor_obj S q U).symm) ≫
      copowerMap (fun α => φ ≫ α) (𝟙 (F.obj.obj
        (Opposite.op ((S.componentFunctor q).obj U)))) = _
  rw [ι_copowerMap, Category.id_comp]

/-- **The simplicial structure of the simplex-coefficient resolution, over one component.** Over
the component of degree `q`, the identity-labelled summand inclusion of `F` into the degree-`q`
term of the resolution, followed by the simplicial structure map at `φ : ⦋p⦌ ⟶ ⦋q⦌`, is the
`φ`-labelled summand of the degree-`p` term. -/
theorem componentSheafInclusion_comp_barSimplicial_map
    {p q : SimplexCategory} (φ : p ⟶ q) :
    componentSheafInclusion S F q ≫
        (S.abelianComponent q).map ((barSimplicial S F).map φ.op) =
      componentSheafSummand S F φ := by
  apply (sheafToPresheaf (S.componentTopology q) Ab.{u}).map_injective
  apply NatTrans.ext
  funext Y
  obtain ⟨U⟩ := Y
  change (componentSheafInclusion S F q).hom.app (Opposite.op U) ≫
      ((S.abelianComponent q).map ((barSimplicial S F).map φ.op)).hom.app (Opposite.op U) =
    (componentSheafSummand S F φ).hom.app (Opposite.op U)
  have hnat := congr_app (toSheafify_naturality S.totalTopology
    ((simplexCoefficientDiagram ((degreeFunctor S).leftOp) F.obj).map φ.op))
    (Opposite.op ((S.componentFunctor q).obj U))
  rw [NatTrans.comp_app, NatTrans.comp_app] at hnat
  refine Eq.trans (congrArg (fun g => g ≫ ((S.abelianComponent q).map
      ((barSimplicial S F).map φ.op)).hom.app (Opposite.op U))
      (componentSheafInclusion_hom_app S F q U)) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun g =>
      (componentPresheafInclusion S F q).app (Opposite.op U) ≫ g) hnat.symm) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun g => g ≫ (toSheafify S.totalTopology
      ((simplexCoefficientDiagram ((degreeFunctor S).leftOp) F.obj).obj (Opposite.op p))).app
        (Opposite.op ((S.componentFunctor q).obj U)))
      (componentPresheafInclusion_comp_simplexCoefficientDiagram_map S F φ U)) ?_
  exact (componentSheafSummand_hom_app S F φ U).symm

/-- **The simplicial structure of the simplex-coefficient resolution, over one component.** Over
the component of degree `q`, the identity-labelled summand inclusion of `F` into the degree-`q`
term of the resolution, followed by the simplicial structure map at `φ : ⦋p⦌ ⟶ ⦋q⦌`, is the
`φ`-labelled summand of the degree-`p` term. -/
theorem componentSheafInclusion_comp_barSimplicial_map'
    {p q : SimplexCategory} (φ : p ⟶ q) :
    (componentSheafInclusion' S q).app F ≫
        (S.restrictAb q).map (((barSimplicial' S).obj F).map φ.op) =
      componentSheafSummand' S F φ := by
  apply (sheafToPresheaf (S.componentTopology q) Ab.{u}).map_injective
  apply NatTrans.ext
  funext Y
  obtain ⟨U⟩ := Y
  change ((componentSheafInclusion' S q).app F).hom.app (Opposite.op U) ≫
      ((S.restrictAb q).map (((barSimplicial' S).obj F).map φ.op)).hom.app (Opposite.op U) =
    (componentSheafSummand' S F φ).hom.app (Opposite.op U)
  have hnat := congr_app (toSheafify_naturality S.totalTopology
    (((simplexCoefficientDiagram' (totalSimplexDegree S).leftOp).obj F.obj).map φ.op))
    (Opposite.op ((S.componentFunctor q).obj U))
  rw [NatTrans.comp_app, NatTrans.comp_app] at hnat
  refine Eq.trans (congrArg (fun g => g ≫ ((S.restrictAb q).map
      (((barSimplicial' S).obj F).map φ.op)).hom.app (Opposite.op U))
      (componentSheafInclusion_hom_app' S F q U)) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun g =>
      (componentPresheafInclusion' S F q).app (Opposite.op U) ≫ g) hnat.symm) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun g => g ≫ (toSheafify S.totalTopology
      (((simplexCoefficientDiagram' (totalSimplexDegree S).leftOp).obj F.obj).obj
        (Opposite.op p))).app (Opposite.op ((S.componentFunctor q).obj U)))
      (componentPresheafInclusion_comp_simplexCoefficientDiagram_map' S F φ U)) ?_
  exact (componentSheafSummand_hom_app' S F φ U).symm

/-- The comparison of Stacks 09WG in degree `q`, followed by the simplicial structure map of the
resolution at `φ : ⦋p⦌ ⟶ ⦋q⦌`, is the transpose along `g_{q!} ⊣ g_q^{-1}` of the `φ`-labelled
summand. -/
theorem componentLowerShriekMap_comp_barSimplicial_map
    {p q : SimplexCategory} (φ : p ⟶ q) :
    componentLowerShriekMap S F q ≫ (barSimplicial S F).map φ.op =
      ((S.componentLowerShriekAbAdjunction q).homEquiv _ _).symm
        (componentSheafSummand S F φ) := by
  exact ((S.componentLowerShriekAbAdjunction q).homEquiv_naturality_right_symm _ _).symm.trans
    (congrArg _ (componentSheafInclusion_comp_barSimplicial_map S F φ))

/-- The comparison of Stacks 09WG in degree `q`, followed by the simplicial structure map of the
resolution at `φ : ⦋p⦌ ⟶ ⦋q⦌`, is the transpose along `g_{q!} ⊣ g_q^{-1}` of the `φ`-labelled
summand. -/
theorem componentLowerShriekMap_comp_barSimplicial_map'
    {p q : SimplexCategory} (φ : p ⟶ q) :
    (componentLowerShriekMap' S q).app F ≫ ((barSimplicial' S).obj F).map φ.op =
      ((S.componentLowerShriekAbAdjunction' q).homEquiv _ _).symm
        (componentSheafSummand' S F φ) := by
  exact ((S.componentLowerShriekAbAdjunction' q).homEquiv_naturality_right_symm _ _).symm.trans
    (congrArg _ (componentSheafInclusion_comp_barSimplicial_map' S F φ))

section Summand

/-- The unit of an adjunction followed by `R` applied to the transpose of `f` is `f`. -/
private theorem unit_comp_map_homEquiv_symm {C D : Type*} [Category* C] [Category* D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {X : C} {Y : D} (f : X ⟶ R.obj Y) :
    adj.unit.app X ≫ R.map ((adj.homEquiv _ _).symm f) = f := by
  exact (adj.homEquiv_unit _ _ _).symm.trans (Equiv.apply_symm_apply _ _)

attribute [local instance] componentFunctorHasCoproductsOfShape
attribute [local instance] hasColimitsOfShapeDiscreteSheafComponent

/-- **The `φ`-labelled leg of the direct-sum formula of Stacks 09WG, through the comparison.** The
canonical map from the inverse image along the transition at `φ : ⦋p⦌ ⟶ ⦋q⦌` into the degree-`q`
restriction of `g_{p!}(F_p)`, followed by the comparison of Stacks 09WG in degree `p`, is the
`φ`-labelled summand of the degree-`p` term of the resolution, transported along the
inverse-image transition at `φ`. -/
theorem componentSumFormulaLeg_comp_abelianComponent_map_componentLowerShriekMap
    {p q : SimplexCategory} (φ : p ⟶ q) :
    (S.componentSumFormulaLeg φ).app ((S.abelianComponent p).obj F) ≫
        (S.abelianComponent q).map (componentLowerShriekMap S F p) =
      (S.fiberTransitionAb φ).app F ≫ componentSheafSummand S F φ := by
  have hnat := (S.fiberTransitionAb φ).naturality (componentLowerShriekMap S F p)
  have hend := transitionInverseImageAb_map_componentSheafInclusion_comp_fiberTransitionAb S F φ
  rw [sigma_ι_comp_abelianComponentBarIsoCoproduct_inv] at hend
  rw [componentSumFormulaLeg_app, Category.assoc, ← hnat]
  simp only [Functor.comp_map]
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp]
  erw [unit_comp_map_homEquiv_symm, hend]

/-- **The `φ`-labelled leg of the direct-sum formula of Stacks 09WG, through the comparison.** The
canonical map from the inverse image along the transition at `φ : ⦋p⦌ ⟶ ⦋q⦌` into the degree-`q`
restriction of `g_{p!}(F_p)`, followed by the comparison of Stacks 09WG in degree `p`, is the
`φ`-labelled summand of the degree-`p` term of the resolution, transported along the
inverse-image transition at `φ`. -/
theorem componentSumFormulaLeg_comp_restrictAb_map_componentLowerShriekMap
    {p q : SimplexCategory} (φ : p ⟶ q) :
    (S.componentSumFormulaLeg' φ).app ((S.restrictAb p).obj F) ≫
        (S.restrictAb q).map ((componentLowerShriekMap' S p).app F) =
      (S.fiberTransitionAb' φ).app F ≫ componentSheafSummand' S F φ := by
  have hnat : (S.restrictAb p ⋙ S.transitionInverseImageAb φ).map
          ((componentLowerShriekMap' S p).app F) ≫
        (S.fiberTransitionAb' φ).app (((barSimplicial' S).obj F).obj (Opposite.op p)) =
      (S.fiberTransitionAb' φ).app
          ((componentLowerShriekAb S p).obj ((S.restrictAb p).obj F)) ≫
        (S.restrictAb q).map ((componentLowerShriekMap' S p).app F) :=
    (S.fiberTransitionAb' φ).naturality ((componentLowerShriekMap' S p).app F)
  have hend := transitionInverseImageAb_map_componentSheafInclusion_comp_fiberTransitionAb' S F φ
  rw [sigma_ι_comp_abelianComponentBarIsoCoproduct_inv'] at hend
  rw [componentSumFormulaLeg_app', Category.assoc, ← hnat]
  simp only [Functor.comp_map]
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp]
  erw [unit_comp_map_homEquiv_symm, hend]

/-- **The simplicial structure map of the simplex-coefficient resolution, under the comparison of
Stacks 09WG.** Transposed along `g_{q!} ⊣ g_q^{-1}`, the structure map at `φ : ⦋p⦌ ⟶ ⦋q⦌` of the
resolution is the `φ`-labelled leg of the direct-sum formula of Stacks 09WG followed by the
comparison of Stacks 09WG in degree `p`, both sides read after transport along the inverse-image
transition at `φ`.

For a cartesian abelian sheaf the inverse-image transition is invertible
(`isIso_fiberTransitionAb_app_of_isCartesianAbSheaf`) and the comparisons are isomorphisms
(`isIso_componentLowerShriekMap`), so this determines the structure map of the resolution of
Stacks 0D78 in terms of the direct-sum formula. -/
theorem fiberTransitionAb_app_comp_componentSheafInclusion_comp_barSimplicial_map
    {p q : SimplexCategory} (φ : p ⟶ q) :
    (S.fiberTransitionAb φ).app F ≫ componentSheafInclusion S F q ≫
        (S.abelianComponent q).map ((barSimplicial S F).map φ.op) =
      (S.componentSumFormulaLeg φ).app ((S.abelianComponent p).obj F) ≫
        (S.abelianComponent q).map (componentLowerShriekMap S F p) := by
  rw [componentSheafInclusion_comp_barSimplicial_map,
    componentSumFormulaLeg_comp_abelianComponent_map_componentLowerShriekMap]

/-- **The simplicial structure map of the simplex-coefficient resolution, under the comparison of
Stacks 09WG.** Transposed along `g_{q!} ⊣ g_q^{-1}`, the structure map at `φ : ⦋p⦌ ⟶ ⦋q⦌` of the
resolution is the `φ`-labelled leg of the direct-sum formula of Stacks 09WG followed by the
comparison of Stacks 09WG in degree `p`, both sides read after transport along the inverse-image
transition at `φ`.

For a cartesian abelian sheaf the inverse-image transition is invertible
(`isIso_fiberTransitionAb_app_of_isCartesianAbSheaf'`) and the comparisons are isomorphisms
(`isIso_componentLowerShriekMap'`), so this determines the structure map of the resolution of
Stacks 0D78 in terms of the direct-sum formula. -/
theorem fiberTransitionAb_app_comp_componentSheafInclusion_comp_barSimplicial_map'
    {p q : SimplexCategory} (φ : p ⟶ q) :
    (S.fiberTransitionAb' φ).app F ≫ (componentSheafInclusion' S q).app F ≫
        (S.restrictAb q).map (((barSimplicial' S).obj F).map φ.op) =
      (S.componentSumFormulaLeg' φ).app ((S.restrictAb p).obj F) ≫
        (S.restrictAb q).map ((componentLowerShriekMap' S p).app F) := by
  rw [componentSheafInclusion_comp_barSimplicial_map',
    componentSumFormulaLeg_comp_restrictAb_map_componentLowerShriekMap]

end Summand

end CategoryTheory.SimplicialSiteSituation

end
