module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CorrespondenceMonoidal
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.GraphFundamentalPairing
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.SmoothTransversalComposition
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# The fundamental class of a product

Let `X` and `Y` be smooth projective schemes over a field `k`, equidimensional of dimensions `d`
and `e`. In the category of correspondences, the fundamental class `[X × Y] ∈ Corr^{-d-e}(X × Y,
Spec k)` is `[X] ∘ ρ_X ∘ (1_X ⊗ [Y])`: on cycles, the composite is the class of
`(x, y) ↦ ((x, y), ⋆)`. Equivalently, `([X] ⊗ [Y]) ≫ λ = [X × Y]`, which on cycles says
`[X] × [Y] = [X × Y]`. This makes the trace maps `∫_X` of a realization of motives
multiplicative, axiom (B)(b) in the proof of Stacks 0FHK.

## Main results

* `Stacks.WeilCohomology.tensorHom_id_fundamentalClassHom_comp`:
  `[X] ∘ ρ_X ∘ (1_X ⊗ [Y]) = [X × Y]`.
* `Stacks.WeilCohomology.tensorHom_fundamentalClassHom_comp_leftUnitorIso`,
  `Stacks.WeilCohomology.fundamentalClassHom_tensorHom_comp_leftUnitor`:
  `([X] ⊗ [Y]) ≫ λ = [X × Y]`.

## Implementation notes

The statements are written with the primitive operations `CorrespondenceCategory.tensorHom`,
`rightUnitorIso`, `leftUnitorIso` of the category of correspondences rather than with `◁`, `ρ_`,
`λ_` of its monoidal structure (which are these by definition): comparing `𝐎 X ⊗ 𝟙_` with
`𝐎 (X ⊗ Spec k)` during unification is expensive, and the primitive spelling avoids it. For the
same reason the dimension hypotheses are binders of each lemma rather than section variables.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Stacks.Chow

universe u

namespace Stacks.WeilCohomology

open CorrespondenceCategory ChowMotiveCat

variable {k : Type u} [Field k]

local notation "𝐏" => 𝟙_ (CategoryTheory.ObjectProperty.FullSubcategory (SmoothProjectiveScheme k))

attribute [local instance] isClosedImmersion_unitSectionEmbedding isClosedImmersion_graphMorphism

section Maps

variable (X Y : (SmoothProjectiveScheme k).FullSubcategory)

/-- The unit section `x ↦ (x, ⋆)` followed by the structure morphism of `X × Spec k`. -/
theorem unitSectionEmbedding_prodBase :
    unitSectionEmbedding k X.obj.hom 𝐏.obj.hom ≫ prodBase X.obj.hom 𝐏.obj.hom = X.obj.hom := by
  rw [prodBase, pullback.lift_fst_assoc, Category.id_comp]

/-- `[Δ_X] ⊗ [Y]` as a closed subscheme of `(X × Y) × (X × Spec k)`:
`(x, y) ↦ ((x, y), (x, ⋆))`. -/
def diagUnitEmbedding :
    (Limits.pullback X.obj.hom Y.obj.hom : Scheme.{u}) ⟶
      Limits.pullback (prodBase X.obj.hom Y.obj.hom) (prodBase X.obj.hom 𝐏.obj.hom) :=
  tensorEmbedding X.obj.hom Y.obj.hom X.obj.hom 𝐏.obj.hom
    (graphMorphism X.obj.hom X.obj.hom (𝟙 _) (Category.id_comp _))
    (unitSectionEmbedding k Y.obj.hom 𝐏.obj.hom) (graphMorphism_id_prodBase_self _)
    (unitSectionEmbedding_prodBase Y)

/-- The morphism `diagUnitEmbedding X Y` is a closed immersion. -/
@[instance] theorem isClosedImmersion_diagUnitEmbedding :
    IsClosedImmersion (diagUnitEmbedding X Y) :=
  isClosedImmersion_tensorEmbedding _ _ _ _ _ _ _ _

/-- `diagUnitEmbedding X Y` is the product of the diagonal embedding of `X` with the unit section
of `Y`. -/
theorem diagUnitEmbedding_eq : diagUnitEmbedding X Y =
    tensorEmbedding X.obj.hom Y.obj.hom X.obj.hom 𝐏.obj.hom
      (graphMorphism X.obj.hom X.obj.hom (𝟙 _) (Category.id_comp _))
      (unitSectionEmbedding k Y.obj.hom 𝐏.obj.hom) (graphMorphism_id_prodBase_self _)
      (unitSectionEmbedding_prodBase Y) :=
  rfl

/-- `(x, y) ↦ ((x, y), x)`, a closed subscheme of `(X × Y) × X`: the transposed graph of the
first projection. -/
def projEmbedding :
    (Limits.pullback X.obj.hom Y.obj.hom : Scheme.{u}) ⟶
      Limits.pullback (prodBase X.obj.hom Y.obj.hom) X.obj.hom :=
  pullback.lift (𝟙 _) (pullback.fst X.obj.hom Y.obj.hom) (by simp [prodBase])

/-- The first component of `projEmbedding X Y` is the identity of `X × Y`. -/
@[reassoc (attr := simp)]
theorem projEmbedding_fst : projEmbedding X Y ≫ pullback.fst _ _ = 𝟙 _ :=
  pullback.lift_fst _ _ _

/-- The second component of `projEmbedding X Y` is the first projection `X × Y ⟶ X`. -/
@[reassoc (attr := simp)]
theorem projEmbedding_snd : projEmbedding X Y ≫ pullback.snd _ _ = pullback.fst _ _ :=
  pullback.lift_snd _ _ _

/-- `projEmbedding X Y` commutes with the structure morphisms of `(X × Y) × X` and `X × Y`. -/
theorem projEmbedding_prodBase :
    projEmbedding X Y ≫ prodBase (prodBase X.obj.hom Y.obj.hom) X.obj.hom =
      prodBase X.obj.hom Y.obj.hom := by
  simp only [prodBase, projEmbedding_fst_assoc]

/-- The morphism `projEmbedding X Y` is a closed immersion. -/
@[instance] theorem isClosedImmersion_projEmbedding : IsClosedImmersion (projEmbedding X Y) :=
  isClosedImmersion_of_retraction _ (pullback.fst _ _) (projEmbedding_fst X Y)
    (prodBase X.obj.hom Y.obj.hom) (prodBase (prodBase X.obj.hom Y.obj.hom) X.obj.hom) rfl

end Maps

section Pieces

variable {X Y : (SmoothProjectiveScheme k).FullSubcategory} {d e : ℕ}

/-- `1_X ⊗ [Y] = [Δ_X] ⊗ [Y]`, read in `CH_{d+e}((X × Y) × (X × Spec k)) ⊗ ℚ`. -/
theorem corrEquivCorrespondence_tensorCorr_diagonal_fundamentalClassCorr
    (hX : RelativeDimension X.obj.hom d) (hY : RelativeDimension Y.obj.hom e)
    (hXY : RelativeDimension (prodBase X.obj.hom Y.obj.hom) (d + e))
    (hXP : RelativeDimension (prodBase X.obj.hom 𝐏.obj.hom) (d + 0)) :
    corrEquivCorrespondence k (X ⊗ Y).obj.hom (X ⊗ 𝐏).obj.hom hXY hXP
        (0 + -(e : ℤ)) (SmoothProjectiveCorr.toCorr (X ⊗ Y) (X ⊗ 𝐏) (0 + -(e : ℤ))
          (tensorCorr 0 (-(e : ℤ)) (correspondenceDiagonal k X) (fundamentalClassCorr hY))) =
      (1 * 1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme
        (fieldChowSituation k) (prodBase (prodBase X.obj.hom Y.obj.hom)
          (prodBase X.obj.hom 𝐏.obj.hom))
        (diagUnitEmbedding X Y) (((d + 0 : ℕ) : ℤ) - (0 + -(e : ℤ)))) := by
  refine (corrEquivCorrespondence_tensor k (canonicalDiagonalClassFamily k) X.obj.hom Y.obj.hom
    X.obj.hom 𝐏.obj.hom (canonicalDiagonalClassFamily_isoInvariant k) hX hY hX
    relativeDimension_tensorUnit_hom hXY hXP 0 (-(e : ℤ)) _ _).trans ?_
  simp only [LinearEquiv.coe_coe]
  rw [corrEquivCorrespondence_correspondenceDiagonal X hX]
  rw [corrEquivCorrespondence_fundamentalClassCorr hY]
  rw [tensorBlock_closedSubscheme k _ _ _ _ hX hY hX relativeDimension_tensorUnit_hom 0 (-(e : ℤ))
      _ _ (graphMorphism_id_prodBase_self _) (unitSectionEmbedding_prodBase Y) hX hY (by simp)
      (by simp)]
  rfl

/-- `(x, y) ↦ ((x, y), (x, ⋆))` followed by `X × Spec k ≅ X` on the second factor is
`(x, y) ↦ ((x, y), x)`. -/
theorem diagUnitEmbedding_comp_map (X Y : (SmoothProjectiveScheme k).FullSubcategory) :
    diagUnitEmbedding X Y ≫ pullback.map (X ⊗ Y).obj.hom (X ⊗ 𝐏).obj.hom (X ⊗ Y).obj.hom
        X.obj.hom (𝟙 _) (inv (ρ_ X).inv.hom.left) (𝟙 _) (by simp)
        (by rw [Category.comp_id, IsIso.eq_inv_comp, Over.w (ρ_ X).inv.hom]) =
      projEmbedding X Y := by
  have hinv : inv (ρ_ X).inv.hom.left = pullback.fst X.obj.hom 𝐏.obj.hom :=
    IsIso.inv_eq_of_hom_inv_id (inv_hom_left_comp_hom_hom_left (ρ_ X))
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, Category.comp_id]
    show diagUnitEmbedding X Y ≫ pullback.fst (prodBase X.obj.hom Y.obj.hom)
      (prodBase X.obj.hom 𝐏.obj.hom) = projEmbedding X Y ≫ pullback.fst _ _
    rw [projEmbedding_fst]
    apply pullback.hom_ext
    · rw [Category.assoc, diagUnitEmbedding, tensorEmbedding_fst_fst, graphMorphism_fst,
        Category.comp_id, Category.id_comp]
    · rw [Category.assoc, diagUnitEmbedding, tensorEmbedding_fst_snd, pullback.lift_fst,
        Category.comp_id, Category.id_comp]
  · rw [Category.assoc, pullback.lift_snd, hinv]
    show diagUnitEmbedding X Y ≫ pullback.snd (prodBase X.obj.hom Y.obj.hom)
      (prodBase X.obj.hom 𝐏.obj.hom) ≫ pullback.fst X.obj.hom 𝐏.obj.hom =
        projEmbedding X Y ≫ pullback.snd (prodBase X.obj.hom Y.obj.hom) X.obj.hom
    rw [projEmbedding_snd, diagUnitEmbedding, tensorEmbedding_snd_fst, graphMorphism_snd,
      Category.comp_id]

/-- **`ρ_X ∘ (1_X ⊗ [Y])` on cycles**: composing `(x, y) ↦ ((x, y), (x, ⋆))` with the graph of
`X ≅ X × Spec k` gives `(x, y) ↦ ((x, y), x)`. -/
theorem compositionInt_diagUnit_rightUnitor (hX : RelativeDimension X.obj.hom d)
    (hXY : RelativeDimension (prodBase X.obj.hom Y.obj.hom) (d + e))
    (hXP : RelativeDimension (prodBase X.obj.hom 𝐏.obj.hom) (d + 0)) :
    compositionInt k (X ⊗ Y).obj.hom (X ⊗ 𝐏).obj.hom X.obj.hom (canonicalDiagonalClassFamily k)
        hXY hXP hX (0 + -(e : ℤ)) 0
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase (prodBase X.obj.hom Y.obj.hom) (prodBase X.obj.hom 𝐏.obj.hom))
          (diagUnitEmbedding X Y) (((d + 0 : ℕ) : ℤ) - (0 + -(e : ℤ)))))
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (pullback.fst (X ⊗ 𝐏).obj.hom X.obj.hom ≫ (X ⊗ 𝐏).obj.hom)
          (graphMorphism (X ⊗ 𝐏).obj.hom X.obj.hom (ρ_ X).inv.hom.left (Over.w (ρ_ X).inv.hom))
          ((d : ℤ) - 0))) =
      QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (prodBase (prodBase X.obj.hom Y.obj.hom) X.obj.hom) (projEmbedding X Y)
        ((d : ℤ) - ((0 + -(e : ℤ)) + 0))) := by
  have := isIso_iso_inv_hom_left (ρ_ X)
  refine (compositionInt_graph_right_of_isIso k (X ⊗ Y).obj.hom (X ⊗ 𝐏).obj.hom X.obj.hom hXY hXP
    hX (0 + -(e : ℤ)) (ρ_ X).inv.hom.left (Over.w (ρ_ X).inv.hom) (diagUnitEmbedding X Y)
    (qA := (X ⊗ Y).obj.hom) ((tensorEmbedding_tensorBase _ _ _ _ _ _ _ _).trans rfl) hXY
    (by push_cast; ring) (by push_cast; ring)).trans ?_
  exact congrArg _ (cycleAssociatedToClosedSubscheme_congr _ _ _ _
    (diagUnitEmbedding_comp_map X Y) _)

/-- **`[X] ∘ (ρ_X ∘ (1_X ⊗ [Y]))` on cycles**: composing `(x, y) ↦ ((x, y), x)` with the
fundamental class `x ↦ (x, ⋆)` gives `(x, y) ↦ ((x, y), ⋆)`. -/
theorem compositionInt_projEmbedding_unitSection (hX : RelativeDimension X.obj.hom d)
    (hXY : RelativeDimension (prodBase X.obj.hom Y.obj.hom) (d + e)) :
    compositionInt k (X ⊗ Y).obj.hom X.obj.hom 𝐏.obj.hom (canonicalDiagonalClassFamily k) hXY hX
        relativeDimension_tensorUnit_hom ((0 + -(e : ℤ)) + 0) (-(d : ℤ))
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase (prodBase X.obj.hom Y.obj.hom) X.obj.hom) (projEmbedding X Y)
          ((d : ℤ) - ((0 + -(e : ℤ)) + 0))))
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase X.obj.hom 𝐏.obj.hom) (unitSectionEmbedding k X.obj.hom 𝐏.obj.hom)
          (((0 : ℕ) : ℤ) - -(d : ℤ)))) =
      QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (prodBase (prodBase X.obj.hom Y.obj.hom) 𝐏.obj.hom)
        (unitSectionEmbedding k (prodBase X.obj.hom Y.obj.hom) 𝐏.obj.hom)
        (((0 : ℕ) : ℤ) - (((0 + -(e : ℤ)) + 0) + -(d : ℤ)))) := by
  have hiso : IsIso (unitSectionEmbedding k X.obj.hom 𝐏.obj.hom ≫
      pullback.fst X.obj.hom 𝐏.obj.hom) := by
    rw [pullback.lift_fst]; infer_instance
  have hc : pullback.fst (projEmbedding X Y ≫ pullback.snd (prodBase X.obj.hom Y.obj.hom) X.obj.hom)
        (unitSectionEmbedding k X.obj.hom 𝐏.obj.hom ≫ pullback.fst X.obj.hom 𝐏.obj.hom) ≫
        pullback.fst X.obj.hom Y.obj.hom = pullback.snd _ _ := by
    refine ((congrArg (pullback.fst _ _ ≫ ·) (projEmbedding_snd X Y)).symm.trans
      (pullback.condition.trans ?_))
    exact (congrArg (pullback.snd _ _ ≫ ·) (pullback.lift_fst _ _ _)).trans (Category.comp_id _)
  refine compositionInt_smoothTransversal k _ _ _ hXY hX relativeDimension_tensorUnit_hom
    ((0 + -(e : ℤ)) + 0) (-(d : ℤ)) (projEmbedding X Y) (unitSectionEmbedding k X.obj.hom 𝐏.obj.hom)
    (unitSectionEmbedding k (prodBase X.obj.hom Y.obj.hom) 𝐏.obj.hom)
    (asIso (pullback.fst _ _)) ?_ (qA := (X ⊗ Y).obj.hom) (qB := X.obj.hom)
    (qF := (X ⊗ Y).obj.hom) (projEmbedding_prodBase X Y) (unitSectionEmbedding_prodBase X)
    (unitSectionEmbedding_prodBase (X ⊗ Y)) hXY hX hXY (by push_cast; ring) (by simp)
    (by push_cast; ring)
  apply pullback.hom_ext
  · simp only [asIso_hom, compositionFibre.toProduct, Category.assoc, pullback.lift_fst,
      projEmbedding_fst, Category.comp_id]
  · simp only [asIso_hom, compositionFibre.toProduct, Category.assoc, pullback.lift_snd]
    rw [← reassoc_of% hc]

/-- The graph of `ρ⁻¹ : X ⟶ X × Spec k`, read in `CH_d((X × Spec k) × X) ⊗ ℚ`. -/
theorem corrEquivCorrespondence_graph_rightUnitor_inv (hX : RelativeDimension X.obj.hom d)
    (hXP : RelativeDimension (prodBase X.obj.hom 𝐏.obj.hom) (d + 0)) :
    corrEquivCorrespondence k (X ⊗ 𝐏).obj.hom X.obj.hom hXP hX 0
        (SmoothProjectiveCorr.toCorr (X ⊗ 𝐏) X 0 (graphCorrespondenceSP (ρ_ X).inv)) =
      (1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (pullback.fst (X ⊗ 𝐏).obj.hom X.obj.hom ≫ (X ⊗ 𝐏).obj.hom)
        (graphMorphism (X ⊗ 𝐏).obj.hom X.obj.hom (ρ_ X).inv.hom.left (Over.w (ρ_ X).inv.hom))
        ((d : ℤ) - 0)) :=
  corrEquivCorrespondence_graphCorr k _ _ hXP hX _ _

/-- **`ρ_X ∘ (1_X ⊗ [Y])`, read on `(X × Y) × X`**: the class of `(x, y) ↦ ((x, y), x)`. -/
theorem corrEquivCorrespondence_whiskerLeft_rightUnitor (hX : RelativeDimension X.obj.hom d)
    (hY : RelativeDimension Y.obj.hom e)
    (hXY : RelativeDimension (prodBase X.obj.hom Y.obj.hom) (d + e))
    (hXP : RelativeDimension (prodBase X.obj.hom 𝐏.obj.hom) (d + 0)) :
    corrEquivCorrespondence k (X ⊗ Y).obj.hom X.obj.hom hXY hX ((0 + -(e : ℤ)) + 0)
        (SmoothProjectiveCorr.toCorr (X ⊗ Y) X _ ((canonicalCorrespondenceCompositionData k).comp
          (tensorCorr 0 (-(e : ℤ)) (correspondenceDiagonal k X) (fundamentalClassCorr hY))
          (graphCorrespondenceSP (ρ_ X).inv))) =
      (1 * 1 * 1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme
        (fieldChowSituation k) (prodBase (prodBase X.obj.hom Y.obj.hom) X.obj.hom)
        (projEmbedding X Y) ((d : ℤ) - ((0 + -(e : ℤ)) + 0))) := by
  refine (corrEquivCorrespondence_comp k (X ⊗ Y).obj.hom (X ⊗ 𝐏).obj.hom
    (canonicalDiagonalClassFamily k) (canonicalDiagonalClassFamily_isoInvariant k) X.obj.hom
    hXY hXP hX (0 + -(e : ℤ)) 0 _ _).trans ?_
  simp only [LinearEquiv.coe_coe]
  rw [corrEquivCorrespondence_tensorCorr_diagonal_fundamentalClassCorr hX hY hXY hXP,
    corrEquivCorrespondence_graph_rightUnitor_inv hX hXP, composition_tmul,
    compositionInt_diagUnit_rightUnitor hX hXY hXP]
end Pieces

section Category

variable {X Y : (SmoothProjectiveScheme k).FullSubcategory} {d e : ℕ}

/-- **`[X] ∘ ρ_X ∘ (1_X ⊗ [Y])`, read in `CH_{d+e}((X × Y) × Spec k) ⊗ ℚ`**: the class of
`(x, y) ↦ ((x, y), ⋆)`. -/
theorem corrEquivCorrespondence_whiskerLeft_fundamentalClassCorr_comp
    (hX : RelativeDimension X.obj.hom d) (hY : RelativeDimension Y.obj.hom e)
    (hXY : RelativeDimension (prodBase X.obj.hom Y.obj.hom) (d + e))
    (hXP : RelativeDimension (prodBase X.obj.hom 𝐏.obj.hom) (d + 0)) :
    corrEquivCorrespondence k (X ⊗ Y).obj.hom 𝐏.obj.hom hXY relativeDimension_tensorUnit_hom
        ((0 + -(e : ℤ)) + 0 + -(d : ℤ))
        (SmoothProjectiveCorr.toCorr (X ⊗ Y) 𝐏 _ ((canonicalCorrespondenceCompositionData k).comp
          ((canonicalCorrespondenceCompositionData k).comp
            (tensorCorr 0 (-(e : ℤ)) (correspondenceDiagonal k X) (fundamentalClassCorr hY))
            (graphCorrespondenceSP (ρ_ X).inv))
          (fundamentalClassCorr hX))) =
      (1 * 1 * 1 * 1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme
        (fieldChowSituation k) (prodBase (prodBase X.obj.hom Y.obj.hom) 𝐏.obj.hom)
        (unitSectionEmbedding k (prodBase X.obj.hom Y.obj.hom) 𝐏.obj.hom)
        (((0 : ℕ) : ℤ) - (((0 + -(e : ℤ)) + 0) + -(d : ℤ)))) := by
  refine (corrEquivCorrespondence_comp k (X ⊗ Y).obj.hom X.obj.hom
    (canonicalDiagonalClassFamily k) (canonicalDiagonalClassFamily_isoInvariant k) 𝐏.obj.hom
    hXY hX relativeDimension_tensorUnit_hom ((0 + -(e : ℤ)) + 0) (-(d : ℤ)) _ _).trans ?_
  simp only [LinearEquiv.coe_coe]
  rw [corrEquivCorrespondence_whiskerLeft_rightUnitor hX hY hXY hXP,
    corrEquivCorrespondence_fundamentalClassCorr hX, composition_tmul,
    compositionInt_projEmbedding_unitSection hX hXY]

/-- `[X] ∘ ρ_X ∘ (1_X ⊗ [Y]) = [X × Y]` on homogeneous correspondences. -/
theorem of_comp_comp_fundamentalClassCorr (hX : RelativeDimension X.obj.hom d)
    (hY : RelativeDimension Y.obj.hom e) (hXY : RelativeDimension (X ⊗ Y).obj.hom (d + e)) :
    DirectSum.of (fun i ↦ SmoothProjectiveCorr (X ⊗ Y) 𝐏 i) ((0 + -(e : ℤ)) + 0 + -(d : ℤ))
        ((canonicalCorrespondenceCompositionData k).comp
          ((canonicalCorrespondenceCompositionData k).comp
            (tensorCorr 0 (-(e : ℤ)) (correspondenceDiagonal k X) (fundamentalClassCorr hY))
            (graphCorrespondenceSP (ρ_ X).inv))
          (fundamentalClassCorr hX)) =
      DirectSum.of (fun i ↦ SmoothProjectiveCorr (X ⊗ Y) 𝐏 i) (-((d + e : ℕ) : ℤ))
        (fundamentalClassCorr hXY) := by
  have hXY' : RelativeDimension (prodBase X.obj.hom Y.obj.hom) (d + e) := hXY
  have hXP : RelativeDimension (prodBase X.obj.hom 𝐏.obj.hom) (d + 0) :=
    (Nat.add_comm 0 d) ▸ relativeDimension_prodBase k X.obj.hom 𝐏.obj.hom hX
      relativeDimension_tensorUnit_hom
  refine of_eq_of_corrEquivCorrespondence hXY' relativeDimension_tensorUnit_hom
    (by push_cast; ring) _ _ ?_
  refine (congrArg (correspondenceCongr k _ _ _)
    (corrEquivCorrespondence_whiskerLeft_fundamentalClassCorr_comp hX hY hXY' hXP)).trans
    (Eq.trans ?_ (corrEquivCorrespondence_fundamentalClassCorr hXY).symm)
  rw [correspondenceCongr_tmul, mul_one, mul_one, mul_one]
  exact congrArg ((1 : ℚ) ⊗ₜ[ℤ] ·) (chowGroupDegreeEquiv_mk_cycleAssociatedToClosedSubscheme _ _ _)

/-- **`[X] ∘ ρ_X ∘ (1_X ⊗ [Y]) = [X × Y]`** in the category of correspondences, for `X`, `Y`
equidimensional of dimensions `d`, `e`: on cycles both are the class of `(x, y) ↦ ((x, y), ⋆)`. -/
theorem tensorHom_id_fundamentalClassHom_comp (hX : RelativeDimension X.obj.hom d)
    (hY : RelativeDimension Y.obj.hom e) (hXY : RelativeDimension (X ⊗ Y).obj.hom (d + e)) :
    (CorrespondenceCategory.tensorHom
        (𝟙 (GradedCompositionData.Obj.mk X : CorrespondenceCategory k))
        (fundamentalClassHom hY) ≫
          (rightUnitorIso (GradedCompositionData.Obj.mk X : CorrespondenceCategory k)).hom) ≫
        fundamentalClassHom hX =
      fundamentalClassHom hXY := by
  rw [rightUnitorIso, graphIso_hom, GradedCompositionData.id_eq,
    show (canonicalCorrespondenceCompositionData k).diagonal X =
      correspondenceDiagonal k X from rfl,
    fundamentalClassHom, fundamentalClassHom, fundamentalClassHom]
  simp only [graphHom]
  rw [tensorHom_of_of, GradedCompositionData.of_comp_of, GradedCompositionData.of_comp_of]
  dsimp only
  exact of_comp_comp_fundamentalClassCorr hX hY hXY

/-- **`([X] ⊗ [Y]) ≫ λ = [X × Y]`** in the category of correspondences (Stacks 0FG7): on
cycles, `[X] × [Y] = [X × Y]`. -/
theorem tensorHom_fundamentalClassHom_comp_leftUnitorIso (hX : RelativeDimension X.obj.hom d)
    (hY : RelativeDimension Y.obj.hom e) (hXY : RelativeDimension (X ⊗ Y).obj.hom (d + e)) :
    CorrespondenceCategory.tensorHom (fundamentalClassHom hX) (fundamentalClassHom hY) ≫
        (leftUnitorIso CorrespondenceCategory.tensorUnit).hom =
      fundamentalClassHom hXY := by
  have h₁ : CorrespondenceCategory.tensorHom (fundamentalClassHom hX) (fundamentalClassHom hY) =
      CorrespondenceCategory.tensorHom (𝟙 _) (fundamentalClassHom hY) ≫
        CorrespondenceCategory.tensorHom (fundamentalClassHom hX) (𝟙 _) := by
    rw [tensorHom_comp_tensorHom', Category.id_comp, Category.comp_id]
  have h₂ : (leftUnitorIso (CorrespondenceCategory.tensorUnit (k := k))).hom =
      (rightUnitorIso (CorrespondenceCategory.tensorUnit (k := k))).hom := by
    rw [leftUnitorIso, rightUnitorIso, graphIso_hom, graphIso_hom]
    exact congrArg graphHom (unitors_inv_equal (C := (SmoothProjectiveScheme k).FullSubcategory))
  rw [h₁, h₂]
  rw [Category.assoc]
  rw [rightUnitor_naturality' (fundamentalClassHom hX), ← Category.assoc]
  exact tensorHom_id_fundamentalClassHom_comp hX hY hXY

end Category

section Monoidal

variable {X Y : (SmoothProjectiveScheme k).FullSubcategory} {d e : ℕ}

/- The tensor product of the category of correspondences is taken through
`MonoidalCategory.toMonoidalCategoryStruct`, as in the generic results these statements are fed
into, rather than through the direct instance `CorrespondenceCategory.monoidalCategoryStruct`. -/
attribute [-instance] CorrespondenceCategory.monoidalCategoryStruct

/-- **`([X] ⊗ [Y]) ≫ λ = [X × Y]`**, with the monoidal structure of the category of
correspondences. -/
theorem fundamentalClassHom_tensorHom_comp_leftUnitor (hX : RelativeDimension X.obj.hom d)
    (hY : RelativeDimension Y.obj.hom e) (hXY : RelativeDimension (X ⊗ Y).obj.hom (d + e)) :
    (fundamentalClassHom hX ⊗ₘ fundamentalClassHom hY) ≫
        (λ_ (𝟙_ (CorrespondenceCategory k))).hom =
      fundamentalClassHom hXY := by
  have h := tensorHom_fundamentalClassHom_comp_leftUnitorIso hX hY hXY
  generalize fundamentalClassHom hX = a at h ⊢
  generalize fundamentalClassHom hY = b at h ⊢
  generalize fundamentalClassHom hXY = c at h ⊢
  exact h

/-- `([X] ⊗ [Y]) ≫ λ = 𝟙 ≫ [X × Y]` in the category of correspondences. -/
theorem fundamentalClassHom_tensorHom_comp_leftUnitor_eq_id_comp
    (hX : RelativeDimension X.obj.hom d) (hY : RelativeDimension Y.obj.hom e)
    (hXY : RelativeDimension (X ⊗ Y).obj.hom (d + e)) :
    (fundamentalClassHom hX ⊗ₘ fundamentalClassHom hY) ≫
        (λ_ (𝟙_ (CorrespondenceCategory k))).hom =
      𝟙 ((GradedCompositionData.Obj.mk X : CorrespondenceCategory k) ⊗
        GradedCompositionData.Obj.mk Y) ≫ fundamentalClassHom hXY := by
  rw [Category.id_comp]
  exact fundamentalClassHom_tensorHom_comp_leftUnitor hX hY hXY

end Monoidal


end Stacks.WeilCohomology

end
