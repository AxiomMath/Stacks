module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.Duality.TriangleComposites
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DualityZigZag
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.EquidimensionalGraph
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.EquidimensionalTensor
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TensorCategory
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TensorClosedSubscheme

/-!
# The triangle identities for the self-duality of the motive of a smooth projective scheme

Third part of `StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.Duality`.
For a smooth projective scheme `X` over a field `k`, equidimensional of dimension `d`, this
file reads the composites computed in
`StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.Duality.TriangleComposites`
as classes in a common degree and proves the two triangle identities of Stacks 0FGI in the
category of correspondences.

## Main results

* `Stacks.WeilCohomology.dualityUnit_tensorHom_associator_tensorHom_dualityCounit`: the first
  triangle identity `(η ⊗ 1) ≫ α ≫ (1 ⊗ ε) = λ ≫ ρ⁻¹`.
* `Stacks.WeilCohomology.tensorHom_dualityUnit_associator_tensorHom_dualityCounit`: the second
  triangle identity `(1 ⊗ η) ≫ α⁻¹ ≫ (ε ⊗ 1) = ρ ≫ λ⁻¹`.

## References

* [Stacks Project, Tag 0FGI](https://stacks.math.columbia.edu/tag/0FGI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Stacks.Chow

universe u

namespace Stacks.WeilCohomology

variable (k : Type u) [Field k]

open CorrespondenceCategory

variable {k} (X : (SmoothProjectiveScheme k).FullSubcategory) {d : ℕ}
    (hX : RelativeDimension X.obj.hom d)

attribute [local instance] isClosedImmersion_unitDiagonal isClosedImmersion_counitDiagonal

section FirstTriangleClasses

attribute [local instance] isClosedImmersion_pointSwapMap isClosedImmersion_graphMorphism

/-- The composite of the first triangle identity, read on the products as a composite of the
classes of its three pieces: the composite `(1 ⊗ ε) ∘ α ∘ (η ⊗ 1)` of the category of
correspondences, read in `CH_d((Spec k × X) × (X × Spec k)) ⊗ ℚ`. -/
theorem corrEquivCorrespondence_firstTriangle_composition :
    corrEquivCorrespondence k _ _ (relativeDimension_unitTensor X hX)
        (relativeDimension_tensorUnitRight X hX) ((d : ℤ) + 0 + 0 + (0 + -(d : ℤ)))
        (SmoothProjectiveCorr.toCorr _ _ _ ((canonicalCorrespondenceCompositionData k).comp
          ((canonicalCorrespondenceCompositionData k).comp
            (tensorCorr (d : ℤ) 0 (dualityUnitCorr X hX) (correspondenceDiagonal k X))
            (graphCorrespondenceSP (α_ X X X).inv))
          (tensorCorr 0 (-(d : ℤ)) (correspondenceDiagonal k X) (dualityCounitCorr X hX)))) =
    composition k (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X).obj.hom
        (X ⊗ (X ⊗ X)).obj.hom
        (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom
            (canonicalDiagonalClassFamily k)
        (relativeDimension_unitTensor X hX) (relativeDimension_tensorTensorSelf X hX)
        (relativeDimension_tensorUnitRight X hX) (((d : ℤ) + 0) + 0) (0 + -(d : ℤ))
        (composition k (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X).obj.hom
            ((X ⊗ X) ⊗ X).obj.hom
          (X ⊗ (X ⊗ X)).obj.hom (canonicalDiagonalClassFamily k)
          (relativeDimension_unitTensor X hX) (relativeDimension_tensorSelfTensor X hX)
          (relativeDimension_tensorTensorSelf X hX) ((d : ℤ) + 0) 0
          ((1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme
            (fieldChowSituation k) (tensorBase _ _ _ _) (tensorEmbedding _ _ _ _ (unitDiagonal X)
              (graphMorphism X.obj.hom X.obj.hom (𝟙 _) (Category.id_comp _))
              (unitDiagonal_prodBase X) (graphMorphism_id_prodBase X))
            ((((d + d) + d : ℕ) : ℤ) - (d + 0))))
          (graphCorrespondence ((X ⊗ X) ⊗ X).obj.hom (X ⊗ (X ⊗ X)).obj.hom
            (α_ X X X).inv.hom.left (Over.w (α_ X X X).inv.hom) ((d + (d + d) : ℕ) : ℤ)))
        ((1 * 1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme
          (fieldChowSituation k) (tensorBase _ _ _ _) (tensorEmbedding _ _ _ _
            (graphMorphism X.obj.hom X.obj.hom (𝟙 _) (Category.id_comp _)) (counitDiagonal X)
            (graphMorphism_id_prodBase X) (counitDiagonal_prodBase X))
          (((d + 0 : ℕ) : ℤ) - (0 + -d)))) := by
  show corrEquivCorrespondence k _ _ (relativeDimension_unitTensor X hX)
      (relativeDimension_tensorUnitRight X hX) ((d : ℤ) + 0 + 0 + (0 + -(d : ℤ)))
      (comp k (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X).obj.hom (X ⊗ (X ⊗ X)).obj.hom
        (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom
            (canonicalDiagonalClassFamily k) _ _
        (comp k (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X).obj.hom ((X ⊗ X) ⊗ X).obj.hom
          (X ⊗ (X ⊗ X)).obj.hom (canonicalDiagonalClassFamily k) _ _
          (SmoothProjectiveCorr.toCorr _ _ _ (tensorCorr (d : ℤ) 0 (dualityUnitCorr X hX)
            (correspondenceDiagonal k X)))
          (SmoothProjectiveCorr.toCorr _ _ _ (graphCorrespondenceSP (α_ X X X).inv)))
        (SmoothProjectiveCorr.toCorr _ _ _ (tensorCorr 0 (-(d : ℤ))
          (correspondenceDiagonal k X) (dualityCounitCorr X hX)))) = _
  have h := corrEquivCorrespondence_comp_comp k (canonicalDiagonalClassFamily k)
      (canonicalDiagonalClassFamily_isoInvariant k)
          (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X).obj.hom
      ((X ⊗ X) ⊗ X).obj.hom (X ⊗ (X ⊗ X)).obj.hom
          (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom
      (relativeDimension_unitTensor X hX)
      (relativeDimension_tensorSelfTensor X hX) (relativeDimension_tensorTensorSelf X hX)
      (relativeDimension_tensorUnitRight X hX) ((d : ℤ) + 0) 0 (0 + -(d : ℤ))
      (SmoothProjectiveCorr.toCorr (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X)
          ((X ⊗ X) ⊗ X)
        ((d : ℤ) + 0) (tensorCorr (d : ℤ) 0 (dualityUnitCorr X hX) (correspondenceDiagonal k X)))
      (SmoothProjectiveCorr.toCorr ((X ⊗ X) ⊗ X) (X ⊗ (X ⊗ X)) 0
        (graphCorrespondenceSP (α_ X X X).inv))
      (SmoothProjectiveCorr.toCorr (X ⊗ (X ⊗ X))
          (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory))
        (0 + -(d : ℤ)) (tensorCorr 0 (-(d : ℤ)) (correspondenceDiagonal k X)
          (dualityCounitCorr X hX)))
  refine h.trans ?_
  simp only [corrEquivCorrespondence_tensorCorr_dualityUnit X hX,
    corrEquivCorrespondence_graph_associator_inv X hX,
    corrEquivCorrespondence_tensorCorr_dualityCounit X hX]

/-- The first triangle identity on the classes: the composite `(1 ⊗ ε) ∘ α ∘ (η ⊗ 1)` of the
category of correspondences, read in `CH_d((Spec k × X) × (X × Spec k)) ⊗ ℚ`, is the class of the
small diagonal. -/
theorem corrEquivCorrespondence_firstTriangle :
    corrEquivCorrespondence k _ _ (relativeDimension_unitTensor X hX)
        (relativeDimension_tensorUnitRight X hX) ((d : ℤ) + 0 + 0 + (0 + -(d : ℤ)))
        (SmoothProjectiveCorr.toCorr _ _ _ ((canonicalCorrespondenceCompositionData k).comp
          ((canonicalCorrespondenceCompositionData k).comp
            (tensorCorr (d : ℤ) 0 (dualityUnitCorr X hX) (correspondenceDiagonal k X))
            (graphCorrespondenceSP (α_ X X X).inv))
          (tensorCorr 0 (-(d : ℤ)) (correspondenceDiagonal k X) (dualityCounitCorr X hX)))) =
      (1 * 1 * (1 * 1) : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme
        (fieldChowSituation k)
            (prodBase (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X).obj.hom
          (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom) (pointSwapMap k X.obj.hom)
        (((d + 0 : ℕ) : ℤ) - ((d + 0 + 0) + (0 + -d)))) :=
  (corrEquivCorrespondence_firstTriangle_composition X hX).trans (composition_firstTriangle X hX)

/-- The class of a composite of two graph correspondences is the composition of the classes of
the two graphs. -/
private theorem corrEquivCorrespondence_comp_graphCorrespondenceSP
    {P Q R : (SmoothProjectiveScheme k).FullSubcategory} {p q r : ℕ}
    (hP : RelativeDimension P.obj.hom p) (hQ : RelativeDimension Q.obj.hom q)
    (hR : RelativeDimension R.obj.hom r) (u : Q ⟶ P) (v : R ⟶ Q) :
    corrEquivCorrespondence k _ _ hP hR (0 + 0)
        (SmoothProjectiveCorr.toCorr _ _ _ ((canonicalCorrespondenceCompositionData k).comp
          (graphCorrespondenceSP u) (graphCorrespondenceSP v))) =
      composition k P.obj.hom Q.obj.hom R.obj.hom (canonicalDiagonalClassFamily k) hP hQ hR 0 0
        (graphCorrespondence P.obj.hom Q.obj.hom u.hom.left (Over.w u.hom) q)
        (graphCorrespondence Q.obj.hom R.obj.hom v.hom.left (Over.w v.hom) r) := by
  refine (corrEquivCorrespondence_comp k _ _ (canonicalDiagonalClassFamily k)
    (canonicalDiagonalClassFamily_isoInvariant k) _ hP hQ hR 0 0 _ _).trans ?_
  exact congrArg₂ (fun a b ↦ composition k _ _ _ (canonicalDiagonalClassFamily k) hP hQ hR 0 0 a b)
    (corrEquivCorrespondence_graphCorr k _ _ hP hQ _ _)
    (corrEquivCorrespondence_graphCorr k _ _ hQ hR _ _)

/-- `λ ≫ ρ⁻¹`, read on the products as the composite of the classes of the two graphs. -/
theorem corrEquivCorrespondence_unitors_composition :
    corrEquivCorrespondence k _ _ (relativeDimension_unitTensor X hX)
        (relativeDimension_tensorUnitRight X hX) (0 + 0)
        (SmoothProjectiveCorr.toCorr _ _ _ ((canonicalCorrespondenceCompositionData k).comp
          (graphCorrespondenceSP (λ_ X).inv) (graphCorrespondenceSP (ρ_ X).hom))) =
      composition k (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X).obj.hom X.obj.hom
        (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom
            (canonicalDiagonalClassFamily k)
        (relativeDimension_unitTensor X hX) hX (relativeDimension_tensorUnitRight X hX) 0 0
        (graphCorrespondence (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X).obj.hom X.obj.hom
          (λ_ X).inv.hom.left (Over.w (λ_ X).inv.hom) d)
        (graphCorrespondence X.obj.hom (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom
          (ρ_ X).hom.hom.left (Over.w (ρ_ X).hom.hom) ((d + 0 : ℕ) : ℤ)) :=
  corrEquivCorrespondence_comp_graphCorrespondenceSP _ hX _ _ _

/-- `λ ≫ ρ⁻¹`, read on the products, is the class of the small diagonal. -/
theorem composition_unitors :
    composition k (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X).obj.hom X.obj.hom
        (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom
            (canonicalDiagonalClassFamily k)
        (relativeDimension_unitTensor X hX) hX (relativeDimension_tensorUnitRight X hX) 0 0
        (graphCorrespondence (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X).obj.hom X.obj.hom
          (λ_ X).inv.hom.left (Over.w (λ_ X).inv.hom) d)
        (graphCorrespondence X.obj.hom (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom
          (ρ_ X).hom.hom.left (Over.w (ρ_ X).hom.hom) ((d + 0 : ℕ) : ℤ)) =
      (1 * 1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme
        (fieldChowSituation k)
            (prodBase (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X).obj.hom
          (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom) (pointSwapMap k X.obj.hom)
        (((d + 0 : ℕ) : ℤ) - (0 + 0))) := by
  have : IsClosedImmersion
      (graphMorphism X.obj.hom (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom
      (ρ_ X).hom.hom.left (Over.w (ρ_ X).hom.hom) ≫
      pullback.map X.obj.hom (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom
        (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X).obj.hom (X ⊗ 𝟙_
            ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom
        (λ_ X).inv.hom.left (𝟙 _) (𝟙 _) (by simp)
        (by simp)) := by
    rw [graphMorphism_rightUnitor_comp_map]; infer_instance
  have hB : RelativeDimension (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom (d + 0)
      :=
    relativeDimension_tensorUnitRight X hX
  have e : ((d + 0 : ℕ) : ℤ) = ((d + 0 : ℕ) : ℤ) - 0 := by simp
  rw [graphCorrespondence, graphCorrespondence, composition_tmul,
    compositionInt_graph_left k _ _ _ (relativeDimension_unitTensor X hX) hX
      (relativeDimension_tensorUnitRight X hX) 0 (λ_ X).inv.hom.left (Over.w (λ_ X).inv.hom)
      (graphMorphism X.obj.hom (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom
          (ρ_ X).hom.hom.left
        (Over.w (ρ_ X).hom.hom))
      (by rw [prodBase, ← Category.assoc, graphMorphism_fst]; exact Over.w (ρ_ X).hom.hom) hB e,
    cycleAssociatedToClosedSubscheme_congr _ _ _ _ (graphMorphism_rightUnitor_comp_map X),
    cycle_graph_rightUnitor_leftUnitor]

/-- The first triangle identity on the products, as an equation of classes in a common degree. -/
theorem correspondenceCongr_firstTriangle :
    correspondenceCongr k (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X).obj.hom
        (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom
        (show (d : ℤ) + 0 + 0 + (0 + -(d : ℤ)) = 0 + 0 by ring)
        (corrEquivCorrespondence k _ _ (relativeDimension_unitTensor X hX)
          (relativeDimension_tensorUnitRight X hX) ((d : ℤ) + 0 + 0 + (0 + -(d : ℤ)))
          (SmoothProjectiveCorr.toCorr _ _ _ ((canonicalCorrespondenceCompositionData k).comp
            ((canonicalCorrespondenceCompositionData k).comp
              (tensorCorr (d : ℤ) 0 (dualityUnitCorr X hX) (correspondenceDiagonal k X))
              (graphCorrespondenceSP (α_ X X X).inv))
            (tensorCorr 0 (-(d : ℤ)) (correspondenceDiagonal k X) (dualityCounitCorr X hX))))) =
      corrEquivCorrespondence k _ _ (relativeDimension_unitTensor X hX)
        (relativeDimension_tensorUnitRight X hX) (0 + 0)
        (SmoothProjectiveCorr.toCorr _ _ _ ((canonicalCorrespondenceCompositionData k).comp
          (graphCorrespondenceSP (λ_ X).inv) (graphCorrespondenceSP (ρ_ X).hom))) := by
  rw [corrEquivCorrespondence_firstTriangle X hX, corrEquivCorrespondence_unitors_composition X hX,
    composition_unitors X hX, correspondenceCongr_tmul,
    chowGroupDegreeEquiv_mk_cycleAssociatedToClosedSubscheme]
  norm_num

/-- The first triangle identity, as an equation of homogeneous morphisms of the category of
correspondences. -/
theorem of_firstTriangle :
    DirectSum.of (fun i ↦ SmoothProjectiveCorr (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X)
        (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)) i) ((d : ℤ) + 0 + 0 + (0 + -(d : ℤ)))
        ((canonicalCorrespondenceCompositionData k).comp
          ((canonicalCorrespondenceCompositionData k).comp
            (tensorCorr (d : ℤ) 0 (dualityUnitCorr X hX) (correspondenceDiagonal k X))
            (graphCorrespondenceSP (α_ X X X).inv))
          (tensorCorr 0 (-(d : ℤ)) (correspondenceDiagonal k X) (dualityCounitCorr X hX))) =
      DirectSum.of
          (fun i ↦ SmoothProjectiveCorr (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X)
        (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)) i) (0 + 0)
        ((canonicalCorrespondenceCompositionData k).comp
          (graphCorrespondenceSP (λ_ X).inv) (graphCorrespondenceSP (ρ_ X).hom)) :=
  of_eq_of_corrEquivCorrespondence (relativeDimension_unitTensor X hX)
    (relativeDimension_tensorUnitRight X hX)
    (show (d : ℤ) + 0 + 0 + (0 + -(d : ℤ)) = 0 + 0 by ring) _ _
    (correspondenceCongr_firstTriangle X hX)

/-- **The first triangle identity** in the category of correspondences:
`(η ⊗ 1) ≫ α ≫ (1 ⊗ ε) = λ ≫ ρ⁻¹` as morphisms `𝟏 ⊗ X ⟶ X ⊗ 𝟏`, where `η` and `ε` are both the
class of the diagonal. -/
theorem dualityUnit_tensorHom_associator_tensorHom_dualityCounit :
    CorrespondenceCategory.tensorHom (dualityUnit X hX)
        (𝟙 (GradedCompositionData.Obj.mk X : CorrespondenceCategory k)) ≫
      (associatorIso (GradedCompositionData.Obj.mk X) (GradedCompositionData.Obj.mk X)
        (GradedCompositionData.Obj.mk X)).hom ≫
      CorrespondenceCategory.tensorHom
        (𝟙 (GradedCompositionData.Obj.mk X : CorrespondenceCategory k)) (dualityCounit X hX) =
    (leftUnitorIso (GradedCompositionData.Obj.mk X : CorrespondenceCategory k)).hom ≫
      (rightUnitorIso (GradedCompositionData.Obj.mk X : CorrespondenceCategory k)).inv := by
  rw [graphIso_hom, graphIso_hom, graphIso_inv, GradedCompositionData.id_eq,
    show (canonicalCorrespondenceCompositionData k).diagonal X = correspondenceDiagonal k X from
      rfl,
    dualityUnit, dualityCounit, tensorHom_of_of, tensorHom_of_of]
  simp only [graphHom]
  rw [← Category.assoc, GradedCompositionData.of_comp_of, GradedCompositionData.of_comp_of,
    GradedCompositionData.of_comp_of]
  dsimp only
  exact of_firstTriangle X hX

end FirstTriangleClasses


section SecondTriangleClasses

attribute [local instance] isClosedImmersion_swapPointMap isClosedImmersion_graphMorphism

/-- **The second triangle identity, on the products.** In
`CH_d((X × Spec k) × (Spec k × X)) ⊗ ℚ`, the composite `(ε ⊗ 1) ∘ α⁻¹ ∘ (1 ⊗ η)` is the class of
the small diagonal. -/
theorem composition_secondTriangle :
    composition k (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom
        ((X ⊗ X) ⊗ X).obj.hom
        (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X).obj.hom
            (canonicalDiagonalClassFamily k)
        (relativeDimension_tensorUnitRight X hX) (relativeDimension_tensorSelfTensor X hX)
        (relativeDimension_unitTensor X hX) (0 + (d : ℤ) + 0) (-(d : ℤ) + 0)
        (composition k (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom
            (X ⊗ (X ⊗ X)).obj.hom
          ((X ⊗ X) ⊗ X).obj.hom (canonicalDiagonalClassFamily k)
          (relativeDimension_tensorUnitRight X hX) (relativeDimension_tensorTensorSelf X hX)
          (relativeDimension_tensorSelfTensor X hX) (0 + (d : ℤ)) 0
          ((1 * 1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme
            (fieldChowSituation k) (tensorBase _ _ _ _) (tensorEmbedding _ _ _ _
              (graphMorphism X.obj.hom X.obj.hom (𝟙 _) (Category.id_comp _)) (unitDiagonal X)
              (graphMorphism_id_prodBase X) (unitDiagonal_prodBase X))
            (((d + (d + d) : ℕ) : ℤ) - (0 + d))))
          (graphCorrespondence (X ⊗ (X ⊗ X)).obj.hom ((X ⊗ X) ⊗ X).obj.hom
            (α_ X X X).hom.hom.left (Over.w (α_ X X X).hom.hom) (((d + d) + d : ℕ) : ℤ)))
        ((1 * 1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme
          (fieldChowSituation k) (tensorBase _ _ _ _) (tensorEmbedding _ _ _ _ (counitDiagonal X)
            (graphMorphism X.obj.hom X.obj.hom (𝟙 _) (Category.id_comp _))
            (counitDiagonal_prodBase X) (graphMorphism_id_prodBase X))
          (((0 + d : ℕ) : ℤ) - (-d + 0)))) =
      (1 * 1 * 1 * (1 * 1) : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme
        (fieldChowSituation k)
            (prodBase (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom
          (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X).obj.hom) (swapPointMap k X.obj.hom)
        (((0 + d : ℕ) : ℤ) - ((0 + d + 0) + (-d + 0)))) := by
  rw [graphCorrespondence, composition_tmul, compositionInt_tensorUnit_associator X hX,
    composition_tmul, compositionInt_tensorUnitMap_counitTensor X hX]

/-- The composite of the second triangle identity, read on the products as a composite of the
classes of its three pieces. -/
theorem corrEquivCorrespondence_secondTriangle_composition :
    corrEquivCorrespondence k _ _ (relativeDimension_tensorUnitRight X hX)
        (relativeDimension_unitTensor X hX) (0 + (d : ℤ) + 0 + (-(d : ℤ) + 0))
        (SmoothProjectiveCorr.toCorr _ _ _ ((canonicalCorrespondenceCompositionData k).comp
          ((canonicalCorrespondenceCompositionData k).comp
            (tensorCorr 0 (d : ℤ) (correspondenceDiagonal k X) (dualityUnitCorr X hX))
            (graphCorrespondenceSP (α_ X X X).hom))
          (tensorCorr (-(d : ℤ)) 0 (dualityCounitCorr X hX) (correspondenceDiagonal k X)))) =
    composition k (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom
        ((X ⊗ X) ⊗ X).obj.hom
        (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X).obj.hom
            (canonicalDiagonalClassFamily k)
        (relativeDimension_tensorUnitRight X hX) (relativeDimension_tensorSelfTensor X hX)
        (relativeDimension_unitTensor X hX) (0 + (d : ℤ) + 0) (-(d : ℤ) + 0)
        (composition k (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom
            (X ⊗ (X ⊗ X)).obj.hom
          ((X ⊗ X) ⊗ X).obj.hom (canonicalDiagonalClassFamily k)
          (relativeDimension_tensorUnitRight X hX) (relativeDimension_tensorTensorSelf X hX)
          (relativeDimension_tensorSelfTensor X hX) (0 + (d : ℤ)) 0
          ((1 * 1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme
            (fieldChowSituation k) (tensorBase _ _ _ _) (tensorEmbedding _ _ _ _
              (graphMorphism X.obj.hom X.obj.hom (𝟙 _) (Category.id_comp _)) (unitDiagonal X)
              (graphMorphism_id_prodBase X) (unitDiagonal_prodBase X))
            (((d + (d + d) : ℕ) : ℤ) - (0 + d))))
          (graphCorrespondence (X ⊗ (X ⊗ X)).obj.hom ((X ⊗ X) ⊗ X).obj.hom
            (α_ X X X).hom.hom.left (Over.w (α_ X X X).hom.hom) (((d + d) + d : ℕ) : ℤ)))
        ((1 * 1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme
          (fieldChowSituation k) (tensorBase _ _ _ _) (tensorEmbedding _ _ _ _ (counitDiagonal X)
            (graphMorphism X.obj.hom X.obj.hom (𝟙 _) (Category.id_comp _))
            (counitDiagonal_prodBase X) (graphMorphism_id_prodBase X))
          (((0 + d : ℕ) : ℤ) - (-d + 0)))) := by
  have hG : corrEquivCorrespondence k _ _ (relativeDimension_tensorTensorSelf X hX)
      (relativeDimension_tensorSelfTensor X hX) 0
      (SmoothProjectiveCorr.toCorr _ _ _ (graphCorrespondenceSP (α_ X X X).hom)) =
      graphCorrespondence (X ⊗ (X ⊗ X)).obj.hom ((X ⊗ X) ⊗ X).obj.hom
        (α_ X X X).hom.hom.left (Over.w (α_ X X X).hom.hom) (((d + d) + d : ℕ) : ℤ) :=
    corrEquivCorrespondence_graphCorr k _ _ (relativeDimension_tensorTensorSelf X hX)
      (relativeDimension_tensorSelfTensor X hX) _ _
  have h := corrEquivCorrespondence_comp_comp k (canonicalDiagonalClassFamily k)
      (canonicalDiagonalClassFamily_isoInvariant k)
          (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom
      (X ⊗ (X ⊗ X)).obj.hom ((X ⊗ X) ⊗ X).obj.hom
          (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X).obj.hom
      (relativeDimension_tensorUnitRight X hX)
      (relativeDimension_tensorTensorSelf X hX) (relativeDimension_tensorSelfTensor X hX)
      (relativeDimension_unitTensor X hX) (0 + (d : ℤ)) 0 (-(d : ℤ) + 0)
      (SmoothProjectiveCorr.toCorr (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory))
          (X ⊗ (X ⊗ X))
        (0 + (d : ℤ)) (tensorCorr 0 (d : ℤ) (correspondenceDiagonal k X) (dualityUnitCorr X hX)))
      (SmoothProjectiveCorr.toCorr (X ⊗ (X ⊗ X)) ((X ⊗ X) ⊗ X) 0
        (graphCorrespondenceSP (α_ X X X).hom))
      (SmoothProjectiveCorr.toCorr ((X ⊗ X) ⊗ X)
          (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X)
        (-(d : ℤ) + 0) (tensorCorr (-(d : ℤ)) 0 (dualityCounitCorr X hX)
          (correspondenceDiagonal k X)))
  refine h.trans ?_
  simp only [corrEquivCorrespondence_tensorCorr_dualityUnit_right X hX, hG,
    corrEquivCorrespondence_tensorCorr_dualityCounit_left X hX]

/-- The second triangle identity on the classes. -/
theorem corrEquivCorrespondence_secondTriangle :
    corrEquivCorrespondence k _ _ (relativeDimension_tensorUnitRight X hX)
        (relativeDimension_unitTensor X hX) (0 + (d : ℤ) + 0 + (-(d : ℤ) + 0))
        (SmoothProjectiveCorr.toCorr _ _ _ ((canonicalCorrespondenceCompositionData k).comp
          ((canonicalCorrespondenceCompositionData k).comp
            (tensorCorr 0 (d : ℤ) (correspondenceDiagonal k X) (dualityUnitCorr X hX))
            (graphCorrespondenceSP (α_ X X X).hom))
          (tensorCorr (-(d : ℤ)) 0 (dualityCounitCorr X hX) (correspondenceDiagonal k X)))) =
      (1 * 1 * 1 * (1 * 1) : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme
        (fieldChowSituation k)
            (prodBase (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom
          (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X).obj.hom) (swapPointMap k X.obj.hom)
        (((0 + d : ℕ) : ℤ) - ((0 + d + 0) + (-d + 0)))) :=
  (corrEquivCorrespondence_secondTriangle_composition X hX).trans (composition_secondTriangle X hX)

/-- `ρ ≫ λ⁻¹`, read on the products as the composite of the classes of the two graphs. -/
theorem corrEquivCorrespondence_unitors_composition' :
    corrEquivCorrespondence k _ _ (relativeDimension_tensorUnitRight X hX)
        (relativeDimension_unitTensor X hX) (0 + 0)
        (SmoothProjectiveCorr.toCorr _ _ _ ((canonicalCorrespondenceCompositionData k).comp
          (graphCorrespondenceSP (ρ_ X).inv) (graphCorrespondenceSP (λ_ X).hom))) =
      composition k (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom X.obj.hom
        (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X).obj.hom
            (canonicalDiagonalClassFamily k)
        (relativeDimension_tensorUnitRight X hX) hX (relativeDimension_unitTensor X hX) 0 0
        (graphCorrespondence (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom X.obj.hom
          (ρ_ X).inv.hom.left (Over.w (ρ_ X).inv.hom) d)
        (graphCorrespondence X.obj.hom (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X).obj.hom
          (λ_ X).hom.hom.left (Over.w (λ_ X).hom.hom) ((0 + d : ℕ) : ℤ)) :=
  corrEquivCorrespondence_comp_graphCorrespondenceSP _ hX _ _ _

/-- `ρ ≫ λ⁻¹`, read on the products, is the class of the small diagonal. -/
theorem composition_unitors' :
    composition k (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom X.obj.hom
        (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X).obj.hom
            (canonicalDiagonalClassFamily k)
        (relativeDimension_tensorUnitRight X hX) hX (relativeDimension_unitTensor X hX) 0 0
        (graphCorrespondence (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom X.obj.hom
          (ρ_ X).inv.hom.left (Over.w (ρ_ X).inv.hom) d)
        (graphCorrespondence X.obj.hom (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X).obj.hom
          (λ_ X).hom.hom.left (Over.w (λ_ X).hom.hom) ((0 + d : ℕ) : ℤ)) =
      (1 * 1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme
        (fieldChowSituation k)
            (prodBase (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom
          (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X).obj.hom) (swapPointMap k X.obj.hom)
        (((0 + d : ℕ) : ℤ) - (0 + 0))) := by
  have : IsClosedImmersion
      (graphMorphism X.obj.hom (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X).obj.hom
      (λ_ X).hom.hom.left (Over.w (λ_ X).hom.hom) ≫
      pullback.map X.obj.hom (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X).obj.hom
        (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom (𝟙_
            ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X).obj.hom
        (ρ_ X).inv.hom.left (𝟙 _) (𝟙 _) (by simp)
        (by simp)) := by
    rw [graphMorphism_leftUnitor_comp_map]; infer_instance
  have hB : RelativeDimension (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X).obj.hom (0 + d)
      :=
    relativeDimension_unitTensor X hX
  have e : ((0 + d : ℕ) : ℤ) = ((0 + d : ℕ) : ℤ) - 0 := by simp
  rw [graphCorrespondence, graphCorrespondence, composition_tmul,
    compositionInt_graph_left k _ _ _ (relativeDimension_tensorUnitRight X hX) hX
      (relativeDimension_unitTensor X hX) 0 (ρ_ X).inv.hom.left (Over.w (ρ_ X).inv.hom)
      (graphMorphism X.obj.hom (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X).obj.hom
          (λ_ X).hom.hom.left
        (Over.w (λ_ X).hom.hom))
      (by rw [prodBase, ← Category.assoc, graphMorphism_fst]; exact Over.w (λ_ X).hom.hom) hB e,
    cycleAssociatedToClosedSubscheme_congr _ _ _ _ (graphMorphism_leftUnitor_comp_map X),
    cycle_graph_leftUnitor_rightUnitor]

/-- The second triangle identity on the products, as an equation of classes in a common
degree. -/
theorem correspondenceCongr_secondTriangle :
    correspondenceCongr k (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom
        (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X).obj.hom
        (show 0 + (d : ℤ) + 0 + (-(d : ℤ) + 0) = 0 + 0 by ring)
        (corrEquivCorrespondence k _ _ (relativeDimension_tensorUnitRight X hX)
          (relativeDimension_unitTensor X hX) (0 + (d : ℤ) + 0 + (-(d : ℤ) + 0))
          (SmoothProjectiveCorr.toCorr _ _ _ ((canonicalCorrespondenceCompositionData k).comp
            ((canonicalCorrespondenceCompositionData k).comp
              (tensorCorr 0 (d : ℤ) (correspondenceDiagonal k X) (dualityUnitCorr X hX))
              (graphCorrespondenceSP (α_ X X X).hom))
            (tensorCorr (-(d : ℤ)) 0 (dualityCounitCorr X hX) (correspondenceDiagonal k X))))) =
      corrEquivCorrespondence k _ _ (relativeDimension_tensorUnitRight X hX)
        (relativeDimension_unitTensor X hX) (0 + 0)
        (SmoothProjectiveCorr.toCorr _ _ _ ((canonicalCorrespondenceCompositionData k).comp
          (graphCorrespondenceSP (ρ_ X).inv) (graphCorrespondenceSP (λ_ X).hom))) := by
  rw [corrEquivCorrespondence_secondTriangle X hX,
    corrEquivCorrespondence_unitors_composition' X hX, composition_unitors' X hX,
    correspondenceCongr_tmul, chowGroupDegreeEquiv_mk_cycleAssociatedToClosedSubscheme]
  norm_num

/-- The second triangle identity, as an equation of homogeneous morphisms of the category of
correspondences. -/
theorem of_secondTriangle :
    DirectSum.of (fun i ↦ SmoothProjectiveCorr (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory))
        (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X) i) (0 + (d : ℤ) + 0 + (-(d : ℤ) + 0))
        ((canonicalCorrespondenceCompositionData k).comp
          ((canonicalCorrespondenceCompositionData k).comp
            (tensorCorr 0 (d : ℤ) (correspondenceDiagonal k X) (dualityUnitCorr X hX))
            (graphCorrespondenceSP (α_ X X X).hom))
          (tensorCorr (-(d : ℤ)) 0 (dualityCounitCorr X hX) (correspondenceDiagonal k X))) =
      DirectSum.of
          (fun i ↦ SmoothProjectiveCorr (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory))
        (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X) i) (0 + 0)
        ((canonicalCorrespondenceCompositionData k).comp
          (graphCorrespondenceSP (ρ_ X).inv) (graphCorrespondenceSP (λ_ X).hom)) :=
  of_eq_of_corrEquivCorrespondence (relativeDimension_tensorUnitRight X hX)
    (relativeDimension_unitTensor X hX)
    (show 0 + (d : ℤ) + 0 + (-(d : ℤ) + 0) = 0 + 0 by ring) _ _
    (correspondenceCongr_secondTriangle X hX)

/-- **The second triangle identity** in the category of correspondences:
`(1 ⊗ η) ≫ α⁻¹ ≫ (ε ⊗ 1) = ρ ≫ λ⁻¹` as morphisms `X ⊗ 𝟏 ⟶ 𝟏 ⊗ X`, where `η` and `ε` are both the
class of the diagonal. -/
theorem tensorHom_dualityUnit_associator_tensorHom_dualityCounit :
    CorrespondenceCategory.tensorHom
        (𝟙 (GradedCompositionData.Obj.mk X : CorrespondenceCategory k)) (dualityUnit X hX) ≫
      (associatorIso (GradedCompositionData.Obj.mk X) (GradedCompositionData.Obj.mk X)
        (GradedCompositionData.Obj.mk X)).inv ≫
      CorrespondenceCategory.tensorHom (dualityCounit X hX)
        (𝟙 (GradedCompositionData.Obj.mk X : CorrespondenceCategory k)) =
    (rightUnitorIso (GradedCompositionData.Obj.mk X : CorrespondenceCategory k)).hom ≫
      (leftUnitorIso (GradedCompositionData.Obj.mk X : CorrespondenceCategory k)).inv := by
  rw [graphIso_inv, graphIso_hom, graphIso_inv, GradedCompositionData.id_eq,
    show (canonicalCorrespondenceCompositionData k).diagonal X = correspondenceDiagonal k X from
      rfl,
    dualityUnit, dualityCounit, tensorHom_of_of, tensorHom_of_of]
  simp only [graphHom]
  rw [← Category.assoc, GradedCompositionData.of_comp_of, GradedCompositionData.of_comp_of,
    GradedCompositionData.of_comp_of]
  dsimp only
  exact of_secondTriangle X hX

end SecondTriangleClasses

end Stacks.WeilCohomology

end
