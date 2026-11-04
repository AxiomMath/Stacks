module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.Duality.UnitCounit
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DualityZigZag
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.EquidimensionalGraph
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.EquidimensionalTensor
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TensorCategory
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TensorClosedSubscheme

/-!
# The composites of the triangle identities on the products

Second part of `StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.Duality`.
For a smooth projective scheme `X` over a field `k`, equidimensional of dimension `d`, this
file computes, on the products, the composites
`(1 ⊗ ε) ∘ α ∘ (η ⊗ 1)` and `(ε ⊗ 1) ∘ α⁻¹ ∘ (1 ⊗ η)` of the two triangle identities of
Stacks 0FGI, and the graphs of the unit constraints `λ ≫ ρ⁻¹` and `ρ ≫ λ⁻¹`, as classes of the
small diagonal.

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

/-! ### The first triangle identity -/

section FirstTriangle

attribute [local instance] isClosedImmersion_graphMorphism isClosedImmersion_unitTensorMap
  isClosedImmersion_tensorCounitMap isClosedImmersion_pointSwapMap

/-- An isomorphism of smooth projective schemes is an isomorphism of the underlying schemes. -/
theorem isIso_hom_left {Y Z : (SmoothProjectiveScheme k).FullSubcategory}
    (e : Y ≅ Z) : IsIso e.hom.hom.left :=
  ⟨e.inv.hom.left,
    by rw [← Over.comp_left, ← ObjectProperty.FullSubcategory.comp_hom, e.hom_inv_id]; rfl,
    by rw [← Over.comp_left, ← ObjectProperty.FullSubcategory.comp_hom, e.inv_hom_id]; rfl⟩

/-- The inverse of the underlying morphism of schemes of an isomorphism is that of its inverse. -/
private theorem inv_hom_hom_left {Y Z : (SmoothProjectiveScheme k).FullSubcategory} (e : Y ≅ Z) :
    haveI := isIso_hom_left e
    inv e.hom.hom.left = e.inv.hom.left := by
  have := isIso_hom_left e
  refine IsIso.inv_eq_of_hom_inv_id ?_
  rw [← Over.comp_left, ← ObjectProperty.FullSubcategory.comp_hom, Iso.hom_inv_id]
  rfl

/-- `η ⊗ 1`, moved by the associator, is the morphism `A` of the first triangle identity. -/
theorem tensorEmbedding_unitDiagonal_comp_associator :
    tensorEmbedding _ _ _ _ (unitDiagonal X)
        (graphMorphism X.obj.hom X.obj.hom (𝟙 _) (Category.id_comp _))
        (unitDiagonal_prodBase X) (graphMorphism_id_prodBase X) ≫
      pullback.map _ _ _ _ (𝟙 _) (α_ X X X).hom.hom.left (𝟙 _) (by simp)
        (by rw [Category.comp_id]; exact (Over.w (α_ X X X).hom.hom).symm) =
      unitTensorMap k X.obj.hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, Category.comp_id, unitTensorMap_fst]
    apply pullback.hom_ext
    · rw [Category.assoc, tensorEmbedding_fst_fst, unitDiagonal_fst, pointSnd_fst']
      exact pullback.condition (f := X.obj.hom) (g := X.obj.hom)
    · rw [Category.assoc, tensorEmbedding_fst_snd, graphMorphism_fst, Category.comp_id,
        pointSnd_snd']
  · rw [Category.assoc, pullback.lift_snd, unitTensorMap_snd]
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, associator_hom_hom_left_fst,
        tensorEmbedding_snd_fst_assoc, unitDiagonal_snd_assoc, pullback.diagonal_fst,
        Category.comp_id, diagFstPair_fst']
    · apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, Category.assoc, associator_hom_hom_left_snd_fst,
          tensorEmbedding_snd_fst_assoc, unitDiagonal_snd_assoc, pullback.diagonal_snd,
          Category.comp_id, diagFstPair_snd', Category.id_comp]
      · rw [Category.assoc, Category.assoc, Category.assoc, associator_hom_hom_left_snd_snd,
          tensorEmbedding_snd_snd, graphMorphism_snd, Category.comp_id, diagFstPair_snd',
          Category.id_comp]

/-- `1 ⊗ ε` is the morphism `B` of the first triangle identity. -/
theorem tensorEmbedding_graph_counitDiagonal :
    tensorEmbedding _ _ _ _ (graphMorphism X.obj.hom X.obj.hom (𝟙 _) (Category.id_comp _))
        (counitDiagonal X) (graphMorphism_id_prodBase X) (counitDiagonal_prodBase X) =
      tensorCounitMap k X.obj.hom := by
  apply pullback.hom_ext
  · rw [tensorCounitMap_fst']
    apply pullback.hom_ext
    · rw [Category.assoc, tensorEmbedding_fst_fst, graphMorphism_fst, Category.comp_id,
        sndDiagPair_fst']
    · rw [Category.assoc, tensorEmbedding_fst_snd, counitDiagonal_fst, sndDiagPair_snd']
  · rw [tensorCounitMap_snd']
    apply pullback.hom_ext
    · rw [Category.assoc, tensorEmbedding_snd_fst, graphMorphism_snd, Category.comp_id,
        fstPoint_fst']
    · rw [Category.assoc, tensorEmbedding_snd_snd, counitDiagonal_snd, fstPoint_snd']
      exact (pullback.condition (f := X.obj.hom) (g := X.obj.hom)).symm

/-- The first component of the small diagonal `pointSwapMap` in `Spec k × X` is `pointPair`. -/
@[reassoc] theorem pointSwapMap_fst' :
    pointSwapMap k X.obj.hom ≫ pullback.fst
        (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X).obj.hom
      (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom = pointPair k X.obj.hom :=
  pointSwapMap_fst k X.obj.hom
/-- The second component of the small diagonal `pointSwapMap` in `X × Spec k` is `pairPoint`. -/
@[reassoc] theorem pointSwapMap_snd' :
    pointSwapMap k X.obj.hom ≫ pullback.snd
        (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X).obj.hom
      (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom = pairPoint k X.obj.hom :=
  pointSwapMap_snd k X.obj.hom

/-- `λ⁻¹ : X ⟶ Spec k × X` is `x ↦ (⋆, x)`. -/
theorem leftUnitor_inv_hom_left_eq : (λ_ X).inv.hom.left = pointPair k X.obj.hom := by
  apply pullback.hom_ext
  · rw [leftUnitor_inv_hom_left_fst]; exact (pointPair_fst k X.obj.hom).symm
  · rw [leftUnitor_inv_hom_left_snd]; exact (pointPair_snd k X.obj.hom).symm

/-- `ρ : X × Spec k ⟶ X` followed by `x ↦ (x, ⋆)` is the identity. -/
theorem rightUnitor_hom_hom_left_pairPoint :
    (ρ_ X).hom.hom.left ≫ pairPoint k X.obj.hom = 𝟙 _ := by
  have c := pullback.condition (f := X.obj.hom)
      (g := (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom)
  apply pullback.hom_ext
  · rw [Category.assoc, rightUnitor_hom_hom_left]
    exact (congrArg
        (pullback.fst X.obj.hom (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom ≫ ·)
      (pairPoint_fst k X.obj.hom)).trans (by rw [Category.comp_id, Category.id_comp]; rfl)
  · rw [Category.assoc, rightUnitor_hom_hom_left]
    refine (congrArg
        (pullback.fst X.obj.hom (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom ≫ ·)
      (pairPoint_snd k X.obj.hom)).trans ?_
    rw [Category.id_comp]
    exact c.trans (Category.comp_id _)

/-- **`λ ≫ ρ⁻¹` is the small diagonal**: the graph of `ρ ≫ λ⁻¹ : X × Spec k ⟶ Spec k × X`, a
closed subscheme of `(Spec k × X) × (X × Spec k)`, is `z ↦ ((⋆, z), (z, ⋆))`. -/
theorem cycle_graph_rightUnitor_leftUnitor (n : ℤ) :
    cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (prodBase (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X).obj.hom
          (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom)
        (graphMorphism _ _ ((ρ_ X).hom ≫ (λ_ X).inv).hom.left
          (Over.w ((ρ_ X).hom ≫ (λ_ X).inv).hom)) n =
      cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (prodBase (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X).obj.hom
          (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom)
        (pointSwapMap k X.obj.hom) n := by
  have := isIso_hom_left (ρ_ X)
  refine cycleAssociatedToClosedSubscheme_eq_of_iso _ _ _ _ (asIso (ρ_ X).hom.hom.left) ?_ n
  apply pullback.hom_ext
  · rw [asIso_hom, Category.assoc, pointSwapMap_fst', graphMorphism_fst,
      ObjectProperty.FullSubcategory.comp_hom, Over.comp_left, leftUnitor_inv_hom_left_eq]
  · rw [asIso_hom, Category.assoc, pointSwapMap_snd', graphMorphism_snd,
      rightUnitor_hom_hom_left_pairPoint]

/-- The associator `(X × X) × X ⟶ X × (X × X)` of the category of correspondences is the class
of the graph of `α⁻¹`, read in `CH_{3d}(((X × X) × X) × (X × (X × X))) ⊗ ℚ`. -/
theorem corrEquivCorrespondence_graph_associator_inv :
    corrEquivCorrespondence k _ _ (relativeDimension_tensorSelfTensor X hX)
        (relativeDimension_tensorTensorSelf X hX) 0
        (SmoothProjectiveCorr.toCorr _ _ _ (graphCorrespondenceSP (α_ X X X).inv)) =
      graphCorrespondence ((X ⊗ X) ⊗ X).obj.hom (X ⊗ (X ⊗ X)).obj.hom (α_ X X X).inv.hom.left
        (Over.w (α_ X X X).inv.hom) ((d + (d + d) : ℕ) : ℤ) :=
  corrEquivCorrespondence_graphCorr k _ _ (relativeDimension_tensorSelfTensor X hX)
    (relativeDimension_tensorTensorSelf X hX) _ _

/-- `λ ≫ ρ⁻¹` of the category of correspondences, read in `CH_d((Spec k × X) × (X × Spec k)) ⊗ ℚ`,
is the class of the small diagonal. -/
theorem corrEquivCorrespondence_graph_rightUnitor_leftUnitor :
    corrEquivCorrespondence k _ _ (relativeDimension_unitTensor X hX)
        (relativeDimension_tensorUnitRight X hX) 0
        (SmoothProjectiveCorr.toCorr _ _ _ (graphCorrespondenceSP ((ρ_ X).hom ≫ (λ_ X).inv))) =
      (1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (prodBase (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X).obj.hom
          (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom)
        (pointSwapMap k X.obj.hom) (((d + 0 : ℕ) : ℤ) - 0)) := by
  refine (corrEquivCorrespondence_graphCorr k _ _ (relativeDimension_unitTensor X hX)
    (relativeDimension_tensorUnitRight X hX) _ _).trans ?_
  rw [graphCorrespondence, cycle_graph_rightUnitor_leftUnitor]

/-- `η ⊗ 1` followed by the associator, read through any expression of the associator. -/
theorem tensorEmbedding_unitDiagonal_comp_map {m : ((X ⊗ X) ⊗ X).obj.left ⟶ (X ⊗ (X ⊗ X)).obj.left}
    (hm : m = (α_ X X X).hom.hom.left) (h₁ h₂) :
    tensorEmbedding _ _ _ _ (unitDiagonal X)
        (graphMorphism X.obj.hom X.obj.hom (𝟙 _) (Category.id_comp _))
        (unitDiagonal_prodBase X) (graphMorphism_id_prodBase X) ≫
      pullback.map (prodBase (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom X.obj.hom)
        ((X ⊗ X) ⊗ X).obj.hom
            (prodBase (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom X.obj.hom)
        (X ⊗ (X ⊗ X)).obj.hom (𝟙 _) m (𝟙 _) h₁ h₂ =
      unitTensorMap k X.obj.hom := by
  subst hm
  exact tensorEmbedding_unitDiagonal_comp_associator X

/-- The inverse of `α⁻¹` on the underlying schemes is `α`. -/
theorem inv_associator_inv_hom_left :
    haveI := isIso_hom_left (α_ X X X).symm
    inv (α_ X X X).inv.hom.left = (α_ X X X).hom.hom.left :=
  inv_hom_hom_left (α_ X X X).symm

/-- `α ∘ (η ⊗ 1)` is the class of the morphism `A` of the first triangle identity. -/
theorem compositionInt_unitTensor_associator :
    compositionInt k (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X).obj.hom
    ((X ⊗ X) ⊗ X).obj.hom (X ⊗ (X ⊗ X)).obj.hom (canonicalDiagonalClassFamily k)
    (relativeDimension_unitTensor X hX) (relativeDimension_tensorSelfTensor X hX)
    (relativeDimension_tensorTensorSelf X hX) ((d : ℤ) + 0) 0
    (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme
      (fieldChowSituation k) (tensorBase _ _ _ _) (tensorEmbedding _ _ _ _ (unitDiagonal X)
        (graphMorphism X.obj.hom X.obj.hom (𝟙 _) (Category.id_comp _))
        (unitDiagonal_prodBase X) (graphMorphism_id_prodBase X))
      ((((d + d) + d : ℕ) : ℤ) - (d + 0))))
    (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
      (pullback.fst ((X ⊗ X) ⊗ X).obj.hom (X ⊗ (X ⊗ X)).obj.hom ≫ ((X ⊗ X) ⊗ X).obj.hom)
      (graphMorphism ((X ⊗ X) ⊗ X).obj.hom (X ⊗ (X ⊗ X)).obj.hom (α_ X X X).inv.hom.left
        (Over.w (α_ X X X).inv.hom)) (((d + (d + d) : ℕ) : ℤ) - 0))) =
    QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
      (prodBase (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X).obj.hom (X ⊗ (X ⊗ X)).obj.hom)
      (unitTensorMap k X.obj.hom) (((d + (d + d) : ℕ) : ℤ) - ((d : ℤ) + 0 + 0))) := by
  have := isIso_hom_left (α_ X X X).symm
  have hA : RelativeDimension (prodBase X.obj.hom X.obj.hom) (d + d) :=
    relativeDimension_prodBase k X.obj.hom X.obj.hom hX hX
  have e₁ : ((d + d : ℕ) : ℤ) = (((d + d) + d : ℕ) : ℤ) - (d + 0) := by push_cast; ring
  have e₂ : ((d + d : ℕ) : ℤ) = ((d + (d + d) : ℕ) : ℤ) - (d + 0) := by push_cast; ring
  exact
    (compositionInt_graph_right_of_isIso k _ _ _ (relativeDimension_unitTensor X hX)
      (relativeDimension_tensorSelfTensor X hX) (relativeDimension_tensorTensorSelf X hX)
      ((d : ℤ) + 0) (α_ X X X).inv.hom.left (Over.w (α_ X X X).inv.hom) _
      (tensorEmbedding_tensorBase _ _ _ _ _ _ _ _) hA e₁ e₂).trans
    (congrArg QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme_congr _ _ _ _
      (tensorEmbedding_unitDiagonal_comp_map X (inv_associator_inv_hom_left X) _ _) _))

/-- `(1 ⊗ ε) ∘ [A]` is the class of the small diagonal. -/
theorem compositionInt_unitTensorMap_tensorCounit :
    compositionInt k (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X).obj.hom
    (X ⊗ (X ⊗ X)).obj.hom (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom
    (canonicalDiagonalClassFamily k) (relativeDimension_unitTensor X hX)
    (relativeDimension_tensorTensorSelf X hX) (relativeDimension_tensorUnitRight X hX)
    ((d : ℤ) + 0 + 0) (0 + -(d : ℤ))
    (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
      (prodBase (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X).obj.hom (X ⊗ (X ⊗ X)).obj.hom)
      (unitTensorMap k X.obj.hom) (((d + (d + d) : ℕ) : ℤ) - ((d : ℤ) + 0 + 0))))
    (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme
        (fieldChowSituation k) (tensorBase _ _ _ _) (tensorEmbedding _ _ _ _
          (graphMorphism X.obj.hom X.obj.hom (𝟙 _) (Category.id_comp _)) (counitDiagonal X)
          (graphMorphism_id_prodBase X) (counitDiagonal_prodBase X))
        (((d + 0 : ℕ) : ℤ) - (0 + -d)))) =
    QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme
      (fieldChowSituation k) (prodBase (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X).obj.hom
        (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom) (pointSwapMap k X.obj.hom)
      (((d + 0 : ℕ) : ℤ) - ((d + 0 + 0) + (0 + -d)))) := by
  exact
    (congrArg (compositionInt k (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X).obj.hom
      (X ⊗ (X ⊗ X)).obj.hom (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom
      (canonicalDiagonalClassFamily k) (relativeDimension_unitTensor X hX)
      (relativeDimension_tensorTensorSelf X hX) (relativeDimension_tensorUnitRight X hX)
      ((d : ℤ) + 0 + 0) (0 + -(d : ℤ))
      (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (prodBase (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X).obj.hom
            (X ⊗ (X ⊗ X)).obj.hom)
        (unitTensorMap k X.obj.hom) (((d + (d + d) : ℕ) : ℤ) - ((d : ℤ) + 0 + 0)))))
      (congrArg QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme_congr _ _ _ _
        (tensorEmbedding_graph_counitDiagonal X) _))).trans
    (compositionInt_unitTensor_tensorCounit k X.obj.hom hX (relativeDimension_unitTensor X hX)
      (relativeDimension_tensorTensorSelf X hX) (relativeDimension_tensorUnitRight X hX)
      ((d : ℤ) + 0 + 0) (0 + -(d : ℤ)) (by push_cast; ring) (by push_cast; ring)
      (by push_cast; ring))

/-- **The first triangle identity, on the products.** In
`CH_d((Spec k × X) × (X × Spec k)) ⊗ ℚ`, the composite `(1 ⊗ ε) ∘ α ∘ (η ⊗ 1)` is the class of the
small diagonal. -/
theorem composition_firstTriangle :
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
          (((d + 0 : ℕ) : ℤ) - (0 + -d)))) =
      (1 * 1 * (1 * 1) : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme
        (fieldChowSituation k)
            (prodBase (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X).obj.hom
          (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom) (pointSwapMap k X.obj.hom)
        (((d + 0 : ℕ) : ℤ) - ((d + 0 + 0) + (0 + -d)))) := by
  rw [graphCorrespondence, composition_tmul, compositionInt_unitTensor_associator X hX,
    composition_tmul, compositionInt_unitTensorMap_tensorCounit X hX]


/-- `ρ` followed by `λ⁻¹`, as a closed subscheme of `(Spec k × X) × (X × Spec k)`: the graph of
`ρ` moved by `λ⁻¹ × 1` is the graph of `ρ ≫ λ⁻¹`. -/
theorem graphMorphism_rightUnitor_comp_map :
    graphMorphism X.obj.hom (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom
        (ρ_ X).hom.hom.left
        (Over.w (ρ_ X).hom.hom) ≫
      pullback.map X.obj.hom (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom
        (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X).obj.hom (X ⊗ 𝟙_
            ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom
        (λ_ X).inv.hom.left (𝟙 _) (𝟙 _) (by simp)
        (by simp) =
      graphMorphism _ _ ((ρ_ X).hom ≫ (λ_ X).inv).hom.left
        (Over.w ((ρ_ X).hom ≫ (λ_ X).inv).hom) := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, graphMorphism_fst, graphMorphism_fst,
      ObjectProperty.FullSubcategory.comp_hom, Over.comp_left]
  · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, graphMorphism_snd, graphMorphism_snd,
      Category.comp_id]

end FirstTriangle

/-! ### The second triangle identity -/

section SecondTriangle

attribute [local instance] isClosedImmersion_graphMorphism isClosedImmersion_tensorUnitMap
  isClosedImmersion_counitTensorMap isClosedImmersion_swapPointMap

/-- The first component of `(y, a) ↦ ((y, a), a)` is `(y, a)`. -/
@[reassoc] theorem pairDiagSnd_fst' :
    pairDiagSnd k X.obj.hom ≫ pullback.fst (X ⊗ X).obj.hom X.obj.hom = 𝟙 _ :=
  pairDiagSnd_fst k X.obj.hom
/-- The second component of `(y, a) ↦ ((y, a), a)` is `a`. -/
@[reassoc] theorem pairDiagSnd_snd' :
    pairDiagSnd k X.obj.hom ≫ pullback.snd (X ⊗ X).obj.hom X.obj.hom =
      pullback.snd X.obj.hom X.obj.hom :=
  pairDiagSnd_snd k X.obj.hom
/-- The first component of `(b, z) ↦ ((b, b), z)` is `(b, b)`. -/
@[reassoc] theorem diagPairFst_fst' :
    diagPairFst k X.obj.hom ≫ pullback.fst (X ⊗ X).obj.hom X.obj.hom =
      pullback.fst X.obj.hom X.obj.hom ≫ pullback.diagonal X.obj.hom :=
  diagPairFst_fst k X.obj.hom
/-- The second component of `(b, z) ↦ ((b, b), z)` is `z`. -/
@[reassoc] theorem diagPairFst_snd' :
    diagPairFst k X.obj.hom ≫ pullback.snd (X ⊗ X).obj.hom X.obj.hom =
      pullback.snd X.obj.hom X.obj.hom :=
  diagPairFst_snd k X.obj.hom
/-- The first component of `counitTensorMap` in `(X × X) × X` is `diagPairFst`. -/
@[reassoc] theorem counitTensorMap_fst' :
    counitTensorMap k X.obj.hom ≫ pullback.fst (prodBase (X ⊗ X).obj.hom X.obj.hom)
      (prodBase (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom X.obj.hom)
          = diagPairFst k X.obj.hom :=
  counitTensorMap_fst k X.obj.hom
/-- The second component of `counitTensorMap` in `Spec k × X` is `pointSnd`. -/
@[reassoc] theorem counitTensorMap_snd' :
    counitTensorMap k X.obj.hom ≫ pullback.snd (prodBase (X ⊗ X).obj.hom X.obj.hom)
      (prodBase (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom X.obj.hom)
          = pointSnd k X.obj.hom :=
  counitTensorMap_snd k X.obj.hom
/-- The first component of the small diagonal `swapPointMap` in `X × Spec k` is `pairPoint`. -/
@[reassoc] theorem swapPointMap_fst' :
    swapPointMap k X.obj.hom ≫ pullback.fst
        (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom
      (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X).obj.hom = pairPoint k X.obj.hom :=
  swapPointMap_fst k X.obj.hom
/-- The second component of the small diagonal `swapPointMap` in `Spec k × X` is `pointPair`. -/
@[reassoc] theorem swapPointMap_snd' :
    swapPointMap k X.obj.hom ≫ pullback.snd
        (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom
      (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X).obj.hom = pointPair k X.obj.hom :=
  swapPointMap_snd k X.obj.hom

/-- `1 ⊗ η`, moved by the inverse associator, is the morphism `A` of the second triangle
identity. -/
theorem tensorEmbedding_graph_unitDiagonal_comp_associator :
    tensorEmbedding _ _ _ _ (graphMorphism X.obj.hom X.obj.hom (𝟙 _) (Category.id_comp _))
        (unitDiagonal X) (graphMorphism_id_prodBase X) (unitDiagonal_prodBase X) ≫
      pullback.map _ _ _ _ (𝟙 _) (α_ X X X).inv.hom.left (𝟙 _) (by simp)
        (by rw [Category.comp_id]; exact (Over.w (α_ X X X).inv.hom).symm) =
      tensorUnitMap k X.obj.hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, Category.comp_id, tensorUnitMap_fst]
    apply pullback.hom_ext
    · rw [Category.assoc, tensorEmbedding_fst_fst, graphMorphism_fst, Category.comp_id,
        fstPoint_fst']
    · rw [Category.assoc, tensorEmbedding_fst_snd, unitDiagonal_fst, fstPoint_snd']
      exact (pullback.condition (f := X.obj.hom) (g := X.obj.hom)).symm
  · rw [Category.assoc, pullback.lift_snd, tensorUnitMap_snd]
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, Category.assoc, associator_inv_hom_left_fst_fst,
          tensorEmbedding_snd_fst, graphMorphism_snd, Category.comp_id, pairDiagSnd_fst',
          Category.id_comp]
      · rw [Category.assoc, Category.assoc, Category.assoc, associator_inv_hom_left_fst_snd,
          tensorEmbedding_snd_snd_assoc, unitDiagonal_snd_assoc, pullback.diagonal_fst,
          Category.comp_id, pairDiagSnd_fst', Category.id_comp]
    · rw [Category.assoc, Category.assoc, associator_inv_hom_left_snd,
        tensorEmbedding_snd_snd_assoc, unitDiagonal_snd_assoc, pullback.diagonal_snd,
        Category.comp_id, pairDiagSnd_snd']

/-- `ε ⊗ 1` is the morphism `B` of the second triangle identity. -/
theorem tensorEmbedding_counitDiagonal_graph :
    tensorEmbedding _ _ _ _ (counitDiagonal X)
        (graphMorphism X.obj.hom X.obj.hom (𝟙 _) (Category.id_comp _))
        (counitDiagonal_prodBase X) (graphMorphism_id_prodBase X) =
      counitTensorMap k X.obj.hom := by
  apply pullback.hom_ext
  · rw [counitTensorMap_fst']
    apply pullback.hom_ext
    · rw [Category.assoc, tensorEmbedding_fst_fst, counitDiagonal_fst, diagPairFst_fst']
    · rw [Category.assoc, tensorEmbedding_fst_snd, graphMorphism_fst, Category.comp_id,
        diagPairFst_snd']
  · rw [counitTensorMap_snd']
    apply pullback.hom_ext
    · rw [Category.assoc, tensorEmbedding_snd_fst, counitDiagonal_snd, pointSnd_fst']
      exact pullback.condition (f := X.obj.hom) (g := X.obj.hom)
    · rw [Category.assoc, tensorEmbedding_snd_snd, graphMorphism_snd, Category.comp_id,
        pointSnd_snd']

/-- `ρ⁻¹ : X ⟶ X × Spec k` is `x ↦ (x, ⋆)`. -/
theorem rightUnitor_inv_hom_left_eq : (ρ_ X).inv.hom.left = pairPoint k X.obj.hom := by
  apply pullback.hom_ext
  · rw [rightUnitor_inv_hom_left_fst]; exact (pairPoint_fst k X.obj.hom).symm
  · rw [rightUnitor_inv_hom_left_snd]; exact (pairPoint_snd k X.obj.hom).symm

/-- `λ : Spec k × X ⟶ X` followed by `x ↦ (⋆, x)` is the identity. -/
theorem leftUnitor_hom_hom_left_pointPair :
    (λ_ X).hom.hom.left ≫ pointPair k X.obj.hom = 𝟙 _ := by
  have c := pullback.condition (f := (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom)
      (g := X.obj.hom)
  apply pullback.hom_ext
  · rw [Category.assoc, leftUnitor_hom_hom_left]
    refine (congrArg
        (pullback.snd (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom X.obj.hom ≫ ·)
      (pointPair_fst k X.obj.hom)).trans ?_
    rw [Category.id_comp]
    exact c.symm.trans (Category.comp_id _)
  · rw [Category.assoc, leftUnitor_hom_hom_left]
    exact (congrArg
        (pullback.snd (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom X.obj.hom ≫ ·)
      (pointPair_snd k X.obj.hom)).trans (by rw [Category.comp_id, Category.id_comp]; rfl)

/-- **`ρ ≫ λ⁻¹` is the small diagonal**: the graph of `λ ≫ ρ⁻¹ : Spec k × X ⟶ X × Spec k`, a
closed subscheme of `(X × Spec k) × (Spec k × X)`, is `z ↦ ((z, ⋆), (⋆, z))`. -/
theorem cycle_graph_leftUnitor_rightUnitor (n : ℤ) :
    cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (prodBase (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom
          (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X).obj.hom)
        (graphMorphism _ _ ((λ_ X).hom ≫ (ρ_ X).inv).hom.left
          (Over.w ((λ_ X).hom ≫ (ρ_ X).inv).hom)) n =
      cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (prodBase (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom
          (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X).obj.hom)
        (swapPointMap k X.obj.hom) n := by
  have := isIso_hom_left (λ_ X)
  refine cycleAssociatedToClosedSubscheme_eq_of_iso _ _ _ _ (asIso (λ_ X).hom.hom.left) ?_ n
  apply pullback.hom_ext
  · rw [asIso_hom, Category.assoc, swapPointMap_fst', graphMorphism_fst,
      ObjectProperty.FullSubcategory.comp_hom, Over.comp_left, rightUnitor_inv_hom_left_eq]
  · rw [asIso_hom, Category.assoc, swapPointMap_snd', graphMorphism_snd,
      leftUnitor_hom_hom_left_pointPair]

/-- `λ` followed by `ρ⁻¹`: the graph of `λ` moved by `ρ⁻¹ × 1` is the graph of `λ ≫ ρ⁻¹`. -/
theorem graphMorphism_leftUnitor_comp_map :
    graphMorphism X.obj.hom (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X).obj.hom
        (λ_ X).hom.hom.left
        (Over.w (λ_ X).hom.hom) ≫
      pullback.map X.obj.hom (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X).obj.hom
        (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom (𝟙_
            ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X).obj.hom
        (ρ_ X).inv.hom.left (𝟙 _) (𝟙 _) (by simp)
        (by simp) =
      graphMorphism _ _ ((λ_ X).hom ≫ (ρ_ X).inv).hom.left
        (Over.w ((λ_ X).hom ≫ (ρ_ X).inv).hom) := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, graphMorphism_fst, graphMorphism_fst,
      ObjectProperty.FullSubcategory.comp_hom, Over.comp_left]
  · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, graphMorphism_snd, graphMorphism_snd,
      Category.comp_id]

/-- The inverse of `α` on the underlying schemes is `α⁻¹`. -/
theorem inv_associator_hom_hom_left :
    haveI := isIso_hom_left (α_ X X X)
    inv (α_ X X X).hom.hom.left = (α_ X X X).inv.hom.left :=
  inv_hom_hom_left (α_ X X X)

/-- `1 ⊗ η` moved by any expression of the inverse associator. -/
theorem tensorEmbedding_graph_unitDiagonal_comp_map
    {m : (X ⊗ (X ⊗ X)).obj.left ⟶ ((X ⊗ X) ⊗ X).obj.left}
    (hm : m = (α_ X X X).inv.hom.left) (h₁ h₂) :
    tensorEmbedding _ _ _ _ (graphMorphism X.obj.hom X.obj.hom (𝟙 _) (Category.id_comp _))
        (unitDiagonal X) (graphMorphism_id_prodBase X) (unitDiagonal_prodBase X) ≫
      pullback.map (prodBase X.obj.hom (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom)
        (X ⊗ (X ⊗ X)).obj.hom
            (prodBase X.obj.hom (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom)
        ((X ⊗ X) ⊗ X).obj.hom (𝟙 _) m (𝟙 _) h₁ h₂ =
      tensorUnitMap k X.obj.hom := by
  subst hm
  exact tensorEmbedding_graph_unitDiagonal_comp_associator X

/-- `α⁻¹ ∘ (1 ⊗ η)` is the class of the morphism `A` of the second triangle identity. -/
theorem compositionInt_tensorUnit_associator :
    compositionInt k (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom
        (X ⊗ (X ⊗ X)).obj.hom
      ((X ⊗ X) ⊗ X).obj.hom (canonicalDiagonalClassFamily k)
      (relativeDimension_tensorUnitRight X hX) (relativeDimension_tensorTensorSelf X hX)
      (relativeDimension_tensorSelfTensor X hX) (0 + (d : ℤ)) 0
      (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme
        (fieldChowSituation k) (tensorBase _ _ _ _) (tensorEmbedding _ _ _ _
          (graphMorphism X.obj.hom X.obj.hom (𝟙 _) (Category.id_comp _)) (unitDiagonal X)
          (graphMorphism_id_prodBase X) (unitDiagonal_prodBase X))
        (((d + (d + d) : ℕ) : ℤ) - (0 + d))))
      (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (pullback.fst (X ⊗ (X ⊗ X)).obj.hom ((X ⊗ X) ⊗ X).obj.hom ≫ (X ⊗ (X ⊗ X)).obj.hom)
        (graphMorphism (X ⊗ (X ⊗ X)).obj.hom ((X ⊗ X) ⊗ X).obj.hom (α_ X X X).hom.hom.left
          (Over.w (α_ X X X).hom.hom)) ((((d + d) + d : ℕ) : ℤ) - 0))) =
      QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (prodBase (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom
            ((X ⊗ X) ⊗ X).obj.hom)
        (tensorUnitMap k X.obj.hom) ((((d + d) + d : ℕ) : ℤ) - (0 + (d : ℤ) + 0))) := by
  have := isIso_hom_left (α_ X X X)
  have hA : RelativeDimension (prodBase X.obj.hom X.obj.hom) (d + d) :=
    relativeDimension_prodBase k X.obj.hom X.obj.hom hX hX
  have e₁ : ((d + d : ℕ) : ℤ) = ((d + (d + d) : ℕ) : ℤ) - (0 + d) := by push_cast; ring
  have e₂ : ((d + d : ℕ) : ℤ) = (((d + d) + d : ℕ) : ℤ) - (0 + d) := by push_cast; ring
  exact
    (compositionInt_graph_right_of_isIso k _ _ _ (relativeDimension_tensorUnitRight X hX)
      (relativeDimension_tensorTensorSelf X hX) (relativeDimension_tensorSelfTensor X hX)
      (0 + (d : ℤ)) (α_ X X X).hom.hom.left (Over.w (α_ X X X).hom.hom) _
      (tensorEmbedding_tensorBase _ _ _ _ _ _ _ _) hA e₁ e₂).trans
    (congrArg QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme_congr _ _ _ _
      (tensorEmbedding_graph_unitDiagonal_comp_map X (inv_associator_hom_hom_left X) _ _) _))

/-- `(ε ⊗ 1) ∘ [A]` is the class of the small diagonal. -/
theorem compositionInt_tensorUnitMap_counitTensor :
    compositionInt k (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom
        ((X ⊗ X) ⊗ X).obj.hom
      (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X).obj.hom (canonicalDiagonalClassFamily k)
      (relativeDimension_tensorUnitRight X hX) (relativeDimension_tensorSelfTensor X hX)
      (relativeDimension_unitTensor X hX) (0 + (d : ℤ) + 0) (-(d : ℤ) + 0)
      (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (prodBase (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom
            ((X ⊗ X) ⊗ X).obj.hom)
        (tensorUnitMap k X.obj.hom) ((((d + d) + d : ℕ) : ℤ) - (0 + (d : ℤ) + 0))))
      (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme
        (fieldChowSituation k) (tensorBase _ _ _ _) (tensorEmbedding _ _ _ _ (counitDiagonal X)
          (graphMorphism X.obj.hom X.obj.hom (𝟙 _) (Category.id_comp _))
          (counitDiagonal_prodBase X) (graphMorphism_id_prodBase X))
        (((0 + d : ℕ) : ℤ) - (-d + 0)))) =
      QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme
        (fieldChowSituation k)
            (prodBase (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom
          (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X).obj.hom) (swapPointMap k X.obj.hom)
        (((0 + d : ℕ) : ℤ) - ((0 + d + 0) + (-d + 0)))) := by
  exact
    (congrArg (compositionInt k (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom
      ((X ⊗ X) ⊗ X).obj.hom (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X).obj.hom
      (canonicalDiagonalClassFamily k) (relativeDimension_tensorUnitRight X hX)
      (relativeDimension_tensorSelfTensor X hX) (relativeDimension_unitTensor X hX)
      (0 + (d : ℤ) + 0) (-(d : ℤ) + 0)
      (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (prodBase (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom
            ((X ⊗ X) ⊗ X).obj.hom)
        (tensorUnitMap k X.obj.hom) ((((d + d) + d : ℕ) : ℤ) - (0 + (d : ℤ) + 0)))))
      (congrArg QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme_congr _ _ _ _
        (tensorEmbedding_counitDiagonal_graph X) _))).trans
    (compositionInt_tensorUnit_counitTensor k X.obj.hom hX (relativeDimension_tensorUnitRight X hX)
      (relativeDimension_tensorSelfTensor X hX) (relativeDimension_unitTensor X hX)
      (0 + (d : ℤ) + 0) (-(d : ℤ) + 0) (by push_cast; ring) (by push_cast; ring)
      (by push_cast; ring))

end SecondTriangle

end Stacks.WeilCohomology

end
