module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.Duality
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RationalPointSummands
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilData
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.GraphAction
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# Graphs, diagonals and fundamental classes in the category of correspondences

Let `k` be a field and let `f : Y ⟶ X` be a morphism of smooth projective schemes over `k`, with
`X` and `Y` equidimensional of dimensions `d` and `e`. Write `a = [Γ_f] ∈ Corr⁰(X, Y)` and
`aᵗ = [Γ_fᵗ] ∈ Corr^{d-e}(Y, X)` for its transpose (Remark 0FG4), `η_X = [Γ_{X → X × X}]` and
`η_Y = [Γ_{Y → Y × Y}]` for the graphs of the diagonals, and `[X] ∈ Corr^{-d}(X, Spec k)`,
`[Y] ∈ Corr^{-e}(Y, Spec k)` for the fundamental classes. Stacks 0FG8 says that the square

  `X ⊗ Y --(a ⊗ 1)--> Y ⊗ Y --η_Y--> Y --[Y]--> Spec k`
  `X ⊗ Y --(1 ⊗ aᵗ)--> X ⊗ X --η_X--> X --[X]--> Spec k`

commutes in the category of correspondences: both composites are the class of the graph
`Γ_f ⊆ X × Y`, read in `Corr^{-e}(X × Y, Spec k) = CH_e(X × Y) ⊗ ℚ`.

## Main definitions

* `Stacks.WeilCohomology.transposeGraphHom`: `aᵗ = [Γ_f]ᵗ`, the transposed graph
  `Stacks.WeilCohomology.transposeGraphCorrespondenceSP` of Remark 0FG4, as a morphism `Y ⟶ X` of
  the category of correspondences.
* `Stacks.WeilCohomology.diagonalGraphHom`: `η_X = [Γ_{X → X × X}]`, as a morphism `X ⊗ X ⟶ X`.
* `Stacks.WeilCohomology.fundamentalClassHom`: `[X]`, as a morphism `X ⟶ Spec k`.

## Main results

* `Stacks.WeilCohomology.corrEquivCorrespondence_transposeGraphCorr`: the transposed graph class
  is the class of the transposed graph `y ↦ (y, f(y))` in `CH_e(Y × X) ⊗ ℚ`.
* `Stacks.WeilCohomology.compositionInt_topTensor_diagonal`,
  `Stacks.WeilCohomology.compositionInt_topPairing_unitSection`,
  `Stacks.WeilCohomology.compositionInt_bottomTensor_diagonal` and
  `Stacks.WeilCohomology.compositionInt_bottomPairing_unitSection`: the four compositions of the
  two rows of the diagram, on cycles, as transversal intersections of smooth subschemes.
* `Stacks.WeilCohomology.graph_tensor_diagonal_fundamental_comm`: **Stacks 0FG8**.

## Implementation notes

The proof here is not the source's, which converts each composite into pushforwards and Gysin
pullbacks of cycles (Stacks 0FG0, 0FG5) and concludes with Stacks 0FF7. Instead every one of the
six correspondences is read as the class of an explicit smooth closed subscheme of a product
(the tensor products by `Stacks.WeilCohomology.tensorBlock_closedSubscheme`), and each of the four
compositions is a transversal intersection of smooth subschemes of the expected dimension,
computed by `Stacks.WeilCohomology.compositionInt_smoothTransversal` (the proper-intersection
formula Stacks 0FFD for the canonical diagonal classes). Along the top row the intermediate
classes are `y ↦ ((f y, y), y)` and then `y ↦ ((f y, y), ⋆)`; along the bottom row they are
`y ↦ ((f y, y), f y)` and then again `y ↦ ((f y, y), ⋆)`.

Equidimensionality of dimension `d` is the hypothesis `RelativeDimension X.obj.hom d`, as in
`StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.Duality`; the schemes may be empty. The
point `Spec k` is the monoidal unit `𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)`, and `[X]` is
the class of `X` embedded in `X × Spec k`
(`Stacks.WeilCohomology.ChowMotiveCat.fundamentalClassCorr`), which is the fundamental class of `X`
under the identification `Corr^{-d}(X, Spec k) = CH_d(X) ⊗ ℚ` of Stacks 0FG0 (2).

## References

* [Stacks Project, Tag 0FG8](https://stacks.math.columbia.edu/tag/0FG8)
* [Stacks Project, Tag 0FG4](https://stacks.math.columbia.edu/tag/0FG4)
* [Stacks Project, Tag 0FFD](https://stacks.math.columbia.edu/tag/0FFD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Stacks.Chow

universe u

namespace Stacks.WeilCohomology

open CorrespondenceCategory ChowMotiveCat

variable {k : Type u} [Field k]

local notation "𝐏" => 𝟙_ (CategoryTheory.ObjectProperty.FullSubcategory (SmoothProjectiveScheme k))

/-! ### The transposed graph, read on the product -/

section Transpose

variable {X Y : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
  (sY : Y ⟶ (fieldChowSituation k).S) [Smooth sX] [IsSeparated sX] [Smooth sY]
  [QuasiCompact sY] {d e : ℕ}

attribute [local instance] isClosedImmersion_graphMorphism

/-- **The transposed graph is the class of the transposed graph**: for `X`, `Y` of constant
dimensions `d`, `e`, the identification `Corr^{d-e}(Y, X) = CH_e(Y × X) ⊗ ℚ` carries
`[Γ_f]ᵗ` to the class of `y ↦ (y, f y)`. -/
theorem corrEquivCorrespondence_transposeGraphCorr (hX : RelativeDimension sX d)
    (hY : RelativeDimension sY e) (f : Y ⟶ X) (hf : f ≫ sX = sY) :
    corrEquivCorrespondence k sY sX hY hX ((d : ℤ) - e) (transposeGraphCorr k sX sY f hf d e) =
      (1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (prodBase sY sX) (graphMorphism sX sY f hf ≫ (pullbackSymmetry sX sY).hom)
        ((d : ℤ) - ((d : ℤ) - e))) := by
  have := isIso_dimPart_self_ι sX hX
  have := isIso_dimPart_self_ι sY hY
  rw [transposeGraphCorr_eq, corrEquivCorrespondence_lof_lof, correspondenceEquivOfIso_tmul]
  congr 1
  set U := ((dimPart sY e).ι ≫ f) ⁻¹ᵁ dimPart sX d with hU
  have hUtop : U = ⊤ := by
    rw [hU, dimPart_self_eq_top sX hX]; rfl
  have : IsIso U.ι := by
    apply isIso_of_isOpenImmersion_of_opensRange_eq_top
    rw [Scheme.Opens.opensRange_ι, hUtop]
  have hcomp : (asIso (U.ι ≫ (dimPart sY e).ι)).hom ≫
        (graphMorphism sX sY f hf ≫ (pullbackSymmetry sX sY).hom) =
      (graphPiece k sX sY f hf d e ≫ (pullbackSymmetry (partBase sX d) (partBase sY e)).hom) ≫
        prodHom sY sX (partBase sY e) (partBase sX d) (dimPart sY e).ι (dimPart sX d).ι
          rfl rfl := by
    apply Limits.pullback.hom_ext
    · simp only [asIso_hom, Category.assoc, pullbackSymmetry_hom_comp_fst, graphMorphism_snd,
        Category.comp_id, Limits.pullback.lift_fst, pullbackSymmetry_hom_comp_fst_assoc,
        graphPiece_snd_assoc]
      rfl
    · simp only [asIso_hom, Category.assoc, pullbackSymmetry_hom_comp_snd, graphMorphism_fst,
        Limits.pullback.lift_snd, pullbackSymmetry_hom_comp_snd_assoc, graphPiece_fst_assoc]
      rw [morphismRestrict_ι]
  have : IsClosedImmersion ((graphPiece k sX sY f hf d e ≫
      (pullbackSymmetry (partBase sX d) (partBase sY e)).hom) ≫
      prodHom sY sX (partBase sY e) (partBase sX d) (dimPart sY e).ι (dimPart sX d).ι rfl rfl) := by
    rw [← hcomp]; infer_instance
  rw [chowPushforwardOfIso, ← QuotientAddGroup.mk'_apply, properChowPushforward_mk,
    properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp,
    QuotientAddGroup.mk'_apply,
    cycleAssociatedToClosedSubscheme_eq_of_iso _ _ _ _ (asIso (U.ι ≫ (dimPart sY e).ι)) hcomp]

end Transpose

/-! ### The closed subschemes of the two composites -/

section Maps

variable {X Y P : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
  (sY : Y ⟶ (fieldChowSituation k).S) (sP : P ⟶ (fieldChowSituation k).S) [IsIso sP]
  (φ : Y ⟶ X) (hφ : φ ≫ sX = sY)

attribute [local instance] isClosedImmersion_graphMorphism

/-- The graph of `φ : Y ⟶ X` over `k`, composed with the structure morphism of `X × Y`, is the
structure morphism of `Y`. -/
theorem graphMorphism_prodBase_of_comp :
    graphMorphism sX sY φ hφ ≫ prodBase sX sY = sY := by
  rw [prodBase, ← Category.assoc, graphMorphism_fst, hφ]

/-- The diagonal `X ⟶ X × X`, composed with the structure morphism of `X × X`, is the structure
morphism of `X`. -/
theorem graphMorphism_id_prodBase_self :
    graphMorphism sX sX (𝟙 _) (Category.id_comp _) ≫ prodBase sX sX = sX := by
  rw [prodBase, ← Category.assoc, graphMorphism_fst, Category.id_comp]

/-- The transposed graph `y ↦ (y, φ y)`, a closed subscheme of `Y ×_k X`. -/
abbrev transposedGraphMorphism : Y ⟶ Limits.pullback sY sX :=
  graphMorphism sX sY φ hφ ≫ (pullbackSymmetry sX sY).hom

/-- The first coordinate of the transposed graph `y ↦ (y, φ y)` is the identity of `Y`. -/
@[reassoc (attr := simp)]
theorem transposedGraphMorphism_fst :
    transposedGraphMorphism sX sY φ hφ ≫ pullback.fst sY sX = 𝟙 _ := by
  simp [transposedGraphMorphism]

/-- The second coordinate of the transposed graph `y ↦ (y, φ y)` is `φ`. -/
@[reassoc (attr := simp)]
theorem transposedGraphMorphism_snd :
    transposedGraphMorphism sX sY φ hφ ≫ pullback.snd sY sX = φ := by
  simp [transposedGraphMorphism]

/-- The transposed graph, composed with the structure morphism of `Y × X`, is the structure
morphism of `Y`. -/
theorem transposedGraphMorphism_prodBase :
    transposedGraphMorphism sX sY φ hφ ≫ prodBase sY sX = sY := by
  rw [prodBase, ← Category.assoc, transposedGraphMorphism_fst, Category.id_comp]

/-- The diagonal `X ⟶ X × X`, composed with the structure morphism of `X × X`, is the structure
morphism of `X`. -/
theorem diagonal_comp_prodBase_self : pullback.diagonal sX ≫ prodBase sX sX = sX := by
  rw [prodBase, pullback.diagonal_fst_assoc]

/-- The graph of the diagonal, `x ↦ ((x, x), x)`, a closed subscheme of `(X × X) × X`. -/
abbrev diagonalGraphMorphism : X ⟶ Limits.pullback (prodBase sX sX) sX :=
  graphMorphism (prodBase sX sX) sX (pullback.diagonal sX) (diagonal_comp_prodBase_self sX)

/-- The graph of the diagonal, composed with the structure morphism of `(X × X) × X`, is the
structure morphism of `X`. -/
theorem diagonalGraphMorphism_prodBase :
    diagonalGraphMorphism sX ≫ prodBase (prodBase sX sX) sX = sX := by
  simp only [diagonalGraphMorphism, graphMorphism, prodBase, pullback.lift_fst_assoc,
    pullback.diagonal_fst_assoc]

/-- `[Γ_φ] ⊗ [Δ_Y]` as a closed subscheme of `(X × Y) × (Y × Y)`:
`(t, t') ↦ ((φ t, t'), (t, t'))`. -/
abbrev topTensorEmbedding :
    (Limits.pullback sY sY : Scheme.{u}) ⟶ Limits.pullback (prodBase sX sY) (prodBase sY sY) :=
  tensorEmbedding sX sY sY sY (graphMorphism sX sY φ hφ)
    (graphMorphism sY sY (𝟙 _) (Category.id_comp _)) (graphMorphism_prodBase_of_comp sX sY φ hφ)
    (graphMorphism_id_prodBase_self sY)

/-- `[Δ_X] ⊗ [Γ_φᵗ]` as a closed subscheme of `(X × Y) × (X × X)`:
`(x, y) ↦ ((x, y), (x, φ y))`. -/
abbrev bottomTensorEmbedding :
    (Limits.pullback sX sY : Scheme.{u}) ⟶ Limits.pullback (prodBase sX sY) (prodBase sX sX) :=
  tensorEmbedding sX sY sX sX (graphMorphism sX sX (𝟙 _) (Category.id_comp _))
    (transposedGraphMorphism sX sY φ hφ) (graphMorphism_id_prodBase_self sX)
    (transposedGraphMorphism_prodBase sX sY φ hφ)

/-- `y ↦ ((φ y, y), y)`, a closed subscheme of `(X × Y) × Y`. -/
def topPairingMap : Y ⟶ Limits.pullback (prodBase sX sY) sY :=
  pullback.lift (graphMorphism sX sY φ hφ) (𝟙 _)
    ((graphMorphism_prodBase_of_comp sX sY φ hφ).trans (Category.id_comp _).symm)

/-- `y ↦ ((φ y, y), φ y)`, a closed subscheme of `(X × Y) × X`. -/
def bottomPairingMap : Y ⟶ Limits.pullback (prodBase sX sY) sX :=
  pullback.lift (graphMorphism sX sY φ hφ) φ
    ((graphMorphism_prodBase_of_comp sX sY φ hφ).trans hφ.symm)

/-- `y ↦ ((φ y, y), ⋆)`, a closed subscheme of `(X × Y) × P` for `P ≅ Spec k`: the graph of `φ`
read as a correspondence to the point. -/
def pointPairingMap : Y ⟶ Limits.pullback (prodBase sX sY) sP :=
  pullback.lift (graphMorphism sX sY φ hφ) (sY ≫ inv sP)
    ((graphMorphism_prodBase_of_comp sX sY φ hφ).trans (by simp))

/-- The first coordinate of `y ↦ ((φ y, y), y)` is the graph of `φ`. -/
@[reassoc (attr := simp)] theorem topPairingMap_fst :
    topPairingMap sX sY φ hφ ≫ pullback.fst _ _ = graphMorphism sX sY φ hφ :=
  pullback.lift_fst _ _ _
/-- The second coordinate of `y ↦ ((φ y, y), y)` is the identity of `Y`. -/
@[reassoc (attr := simp)] theorem topPairingMap_snd :
    topPairingMap sX sY φ hφ ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
/-- The first coordinate of `y ↦ ((φ y, y), φ y)` is the graph of `φ`. -/
@[reassoc (attr := simp)] theorem bottomPairingMap_fst :
    bottomPairingMap sX sY φ hφ ≫ pullback.fst _ _ = graphMorphism sX sY φ hφ :=
  pullback.lift_fst _ _ _
/-- The second coordinate of `y ↦ ((φ y, y), φ y)` is `φ`. -/
@[reassoc (attr := simp)] theorem bottomPairingMap_snd :
    bottomPairingMap sX sY φ hφ ≫ pullback.snd _ _ = φ := pullback.lift_snd _ _ _
/-- The first coordinate of `y ↦ ((φ y, y), ⋆)` is the graph of `φ`. -/
@[reassoc (attr := simp)] theorem pointPairingMap_fst :
    pointPairingMap sX sY sP φ hφ ≫ pullback.fst _ _ = graphMorphism sX sY φ hφ :=
  pullback.lift_fst _ _ _
/-- The second coordinate of `y ↦ ((φ y, y), ⋆)` is the structure morphism of `Y` followed by
the inverse of the isomorphism `sP : P ⟶ Spec k`. -/
@[reassoc (attr := simp)] theorem pointPairingMap_snd :
    pointPairingMap sX sY sP φ hφ ≫ pullback.snd _ _ = sY ≫ inv sP := pullback.lift_snd _ _ _

/-- `y ↦ ((φ y, y), y)`, composed with the structure morphism of `(X × Y) × Y`, is the structure
morphism of `Y`. -/
theorem topPairingMap_prodBase :
    topPairingMap sX sY φ hφ ≫ prodBase (prodBase sX sY) sY = sY := by
  simp only [prodBase, topPairingMap_fst_assoc]; exact graphMorphism_prodBase_of_comp sX sY φ hφ

/-- `y ↦ ((φ y, y), φ y)`, composed with the structure morphism of `(X × Y) × X`, is the
structure morphism of `Y`. -/
theorem bottomPairingMap_prodBase :
    bottomPairingMap sX sY φ hφ ≫ prodBase (prodBase sX sY) sX = sY := by
  simp only [prodBase, bottomPairingMap_fst_assoc]; exact graphMorphism_prodBase_of_comp sX sY φ hφ

/-- `y ↦ ((φ y, y), ⋆)`, composed with the structure morphism of `(X × Y) × P`, is the structure
morphism of `Y`. -/
theorem pointPairingMap_prodBase :
    pointPairingMap sX sY sP φ hφ ≫ prodBase (prodBase sX sY) sP = sY := by
  simp only [prodBase, pointPairingMap_fst_assoc]; exact graphMorphism_prodBase_of_comp sX sY φ hφ

variable [IsSeparated sX] [IsSeparated sY] [IsSeparated sP]

/-- `y ↦ ((φ y, y), y)` is a closed immersion. -/
theorem isClosedImmersion_topPairingMap : IsClosedImmersion (topPairingMap sX sY φ hφ) :=
  isClosedImmersion_of_retraction _ (pullback.snd _ _) (topPairingMap_snd sX sY φ hφ) sY
    (prodBase (prodBase sX sY) sY) pullback.condition.symm

/-- `y ↦ ((φ y, y), φ y)` is a closed immersion. -/
theorem isClosedImmersion_bottomPairingMap : IsClosedImmersion (bottomPairingMap sX sY φ hφ) :=
  isClosedImmersion_of_retraction _ (pullback.fst _ _ ≫ pullback.snd sX sY)
    (by rw [bottomPairingMap_fst_assoc, graphMorphism_snd]) sY (prodBase (prodBase sX sY) sX)
    (by rw [Category.assoc, ← pullback.condition (f := sX) (g := sY)])

/-- `y ↦ ((φ y, y), ⋆)` is a closed immersion. -/
theorem isClosedImmersion_pointPairingMap : IsClosedImmersion (pointPairingMap sX sY sP φ hφ) :=
  isClosedImmersion_of_retraction _ (pullback.fst _ _ ≫ pullback.snd sX sY)
    (by rw [pointPairingMap_fst_assoc, graphMorphism_snd]) sY (prodBase (prodBase sX sY) sP)
    (by rw [Category.assoc, ← pullback.condition (f := sX) (g := sY)])

end Maps

/-! ### The four compositions, on cycles -/

section Compositions

variable {X Y P : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
  (sY : Y ⟶ (fieldChowSituation k).S) (sP : P ⟶ (fieldChowSituation k).S) [IsIso sP]
  [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] [LocallyOfFiniteType sP]
  [Smooth sX] [Smooth sY] [Smooth sP] [IsSeparated sX] [IsSeparated sY] [IsSeparated sP]
  [IsProper sX] [IsProper sY]
  (φ : Y ⟶ X) (hφ : φ ≫ sX = sY) {d e : ℕ} (hX : RelativeDimension sX d)
  (hY : RelativeDimension sY e) (hP : RelativeDimension sP 0)
  (hXY : RelativeDimension (prodBase sX sY) (d + e))
  (hXX : RelativeDimension (prodBase sX sX) (d + d))
  (hYY : RelativeDimension (prodBase sY sY) (e + e))

attribute [local instance] isClosedImmersion_graphMorphism isClosedImmersion_topPairingMap
  isClosedImmersion_bottomPairingMap isClosedImmersion_pointPairingMap
  isClosedImmersion_unitSectionEmbedding

/-- `(t, t') ↦ ((φ t, t'), (t, t'))` is a closed immersion. -/
instance : IsClosedImmersion (topTensorEmbedding sX sY φ hφ) :=
  isClosedImmersion_tensorEmbedding _ _ _ _ _ _ _ _

/-- `(x, y) ↦ ((x, y), (x, φ y))` is a closed immersion. -/
instance : IsClosedImmersion (bottomTensorEmbedding sX sY φ hφ) :=
  isClosedImmersion_tensorEmbedding _ _ _ _ _ _ _ _

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] [Smooth sX] [Smooth sY] [IsSeparated sX]
    [IsSeparated sY] [IsProper sX] [IsProper sY] in
/-- The second coordinate of `[Γ_φ] ⊗ [Δ_Y]` is the identity of `Y × Y`. -/
theorem topTensorEmbedding_snd :
    topTensorEmbedding sX sY φ hφ ≫ pullback.snd (prodBase sX sY) (prodBase sY sY) = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, tensorEmbedding_snd_fst, graphMorphism_snd, Category.comp_id,
      Category.id_comp]
  · rw [Category.assoc, tensorEmbedding_snd_snd, graphMorphism_snd, Category.comp_id,
      Category.id_comp]

omit [IsProper sX] in
/-- **`η_Y ∘ ([Γ_φ] ⊗ [Δ_Y])` on cycles**: the fibre product over `Y × Y` is `Y`, and the
composite is the class of `y ↦ ((φ y, y), y)`. -/
theorem compositionInt_topTensor_diagonal :
    compositionInt k (prodBase sX sY) (prodBase sY sY) sY (canonicalDiagonalClassFamily k) hXY
        hYY hY (0 + 0) 0
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase (prodBase sX sY) (prodBase sY sY)) (topTensorEmbedding sX sY φ hφ)
          (((e + e : ℕ) : ℤ) - (0 + 0))))
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase (prodBase sY sY) sY) (diagonalGraphMorphism sY) ((e : ℤ) - 0))) =
      QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (prodBase (prodBase sX sY) sY) (topPairingMap sX sY φ hφ) ((e : ℤ) - ((0 + 0) + 0))) := by
  have hiso : IsIso (topTensorEmbedding sX sY φ hφ ≫
      pullback.snd (prodBase sX sY) (prodBase sY sY)) := by
    rw [topTensorEmbedding_snd]; infer_instance
  have hc : pullback.fst (topTensorEmbedding sX sY φ hφ ≫
        pullback.snd (prodBase sX sY) (prodBase sY sY))
        (diagonalGraphMorphism sY ≫ pullback.fst (prodBase sY sY) sY) =
      pullback.snd _ _ ≫ pullback.diagonal sY := by
    refine (Category.comp_id _).symm.trans ((congrArg (pullback.fst _ _ ≫ ·)
      (topTensorEmbedding_snd sX sY φ hφ).symm).trans (pullback.condition.trans ?_))
    exact congrArg (pullback.snd _ _ ≫ ·) (graphMorphism_fst _ _ _ _)
  refine compositionInt_smoothTransversal k _ _ _ hXY hYY hY (0 + 0) 0
    (topTensorEmbedding sX sY φ hφ) (diagonalGraphMorphism sY) (topPairingMap sX sY φ hφ)
    (asIso (pullback.snd _ _)) ?_ (qA := prodBase sY sY) (qB := sY) (qF := sY)
    (tensorEmbedding_tensorBase _ _ _ _ _ _ _ _) (diagonalGraphMorphism_prodBase sY)
    (topPairingMap_prodBase sX sY φ hφ) hYY hY hY (by push_cast; ring) (by simp) (by simp)
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp only [asIso_hom, compositionFibre.toProduct, Category.assoc, pullback.lift_fst,
        topPairingMap_fst, tensorEmbedding_fst_fst]
      rw [reassoc_of% hc, pullback.diagonal_fst_assoc]
    · simp only [asIso_hom, compositionFibre.toProduct, Category.assoc, pullback.lift_fst,
        topPairingMap_fst, graphMorphism_snd, Category.comp_id, tensorEmbedding_fst_snd]
      rw [reassoc_of% hc, pullback.diagonal_snd, Category.comp_id]
  · simp only [asIso_hom, compositionFibre.toProduct, Category.assoc, pullback.lift_snd,
      topPairingMap_snd, Category.comp_id]

omit [IsProper sX] in
/-- **`[Y] ∘ (η_Y ∘ (a ⊗ 1))` on cycles**: composing `y ↦ ((φ y, y), y)` with the fundamental
class `y ↦ (y, ⋆)` gives `y ↦ ((φ y, y), ⋆)`. -/
theorem compositionInt_topPairing_unitSection :
    compositionInt k (prodBase sX sY) sY sP (canonicalDiagonalClassFamily k) hXY hY hP
        ((0 + 0) + 0) (-(e : ℤ))
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase (prodBase sX sY) sY) (topPairingMap sX sY φ hφ) ((e : ℤ) - ((0 + 0) + 0))))
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase sY sP) (unitSectionEmbedding k sY sP) (((0 : ℕ) : ℤ) - -(e : ℤ)))) =
      QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (prodBase (prodBase sX sY) sP) (pointPairingMap sX sY sP φ hφ)
        (((0 : ℕ) : ℤ) - (((0 + 0) + 0) + -(e : ℤ)))) := by
  have hiso : IsIso (unitSectionEmbedding k sY sP ≫ pullback.fst sY sP) := by
    rw [pullback.lift_fst]; infer_instance
  have hc : pullback.fst (topPairingMap sX sY φ hφ ≫ pullback.snd (prodBase sX sY) sY)
        (unitSectionEmbedding k sY sP ≫ pullback.fst sY sP) = pullback.snd _ _ := by
    refine (Category.comp_id _).symm.trans ((congrArg (pullback.fst _ _ ≫ ·)
      (topPairingMap_snd sX sY φ hφ).symm).trans (pullback.condition.trans ?_))
    exact (congrArg (pullback.snd _ _ ≫ ·) (pullback.lift_fst _ _ _)).trans (Category.comp_id _)
  refine compositionInt_smoothTransversal k _ _ _ hXY hY hP ((0 + 0) + 0) (-(e : ℤ))
    (topPairingMap sX sY φ hφ) (unitSectionEmbedding k sY sP) (pointPairingMap sX sY sP φ hφ)
    (asIso (pullback.fst _ _)) ?_ (qA := sY) (qB := sY) (qF := sY)
    (topPairingMap_prodBase sX sY φ hφ) (by rw [prodBase, pullback.lift_fst_assoc,
      Category.id_comp]) (pointPairingMap_prodBase sX sY sP φ hφ) hY hY hY (by simp) (by simp)
    (by simp)
  apply pullback.hom_ext
  · simp only [asIso_hom, compositionFibre.toProduct, Category.assoc, pullback.lift_fst,
      pointPairingMap_fst, topPairingMap_fst]
  · simp only [asIso_hom, compositionFibre.toProduct, Category.assoc, pullback.lift_snd,
      pointPairingMap_snd]
    rw [reassoc_of% hc]

/-- The fibre product of `[Δ_X] ⊗ [Γ_φᵗ]` and `η_X` over `X × X`: a point `((x, y), x')` with
`(x, φ y) = (x', x')`. -/
abbrev bottomFibre : Scheme.{u} :=
  compositionFibre (bottomTensorEmbedding sX sY φ hφ) (diagonalGraphMorphism sX)

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] [Smooth sX] [Smooth sY] [IsSeparated sX]
    [IsSeparated sY] [IsProper sX] [IsProper sY] in
/-- The two coordinate equations on the fibre product: `x = x'` and `φ y = x'`. -/
theorem bottomFibre_eqs :
    pullback.fst _ _ ≫ pullback.fst sX sY = (pullback.snd _ _ : bottomFibre sX sY φ hφ ⟶ X) ∧
      pullback.fst _ _ ≫ pullback.snd sX sY ≫ φ =
        (pullback.snd _ _ : bottomFibre sX sY φ hφ ⟶ X) := by
  have hc := pullback.condition (f := bottomTensorEmbedding sX sY φ hφ ≫
    pullback.snd (prodBase sX sY) (prodBase sX sX))
    (g := diagonalGraphMorphism sX ≫ pullback.fst (prodBase sX sX) sX)
  have h₁ := congrArg (· ≫ pullback.fst sX sX) hc
  have h₂ := congrArg (· ≫ pullback.snd sX sX) hc
  simp only [Category.assoc, tensorEmbedding_snd_fst, tensorEmbedding_snd_snd,
    graphMorphism_snd, pullbackSymmetry_hom_comp_snd, graphMorphism_fst, pullback.diagonal_fst,
    pullback.diagonal_snd, Category.comp_id] at h₁ h₂
  exact ⟨h₁, h₂⟩

/-- The inverse `y ↦ ((φ y, y), φ y)` of the projection of the fibre product to `Y`. -/
def bottomFibreInv : Y ⟶ bottomFibre sX sY φ hφ :=
  pullback.lift (graphMorphism sX sY φ hφ) φ (by
    apply pullback.hom_ext
    · simp only [Category.assoc, tensorEmbedding_snd_fst, graphMorphism_fst, graphMorphism_snd,
        Category.comp_id, pullback.diagonal_fst, diagonalGraphMorphism]
    · simp only [Category.assoc, tensorEmbedding_snd_snd, pullbackSymmetry_hom_comp_snd,
        graphMorphism_fst, pullback.diagonal_snd, Category.comp_id, diagonalGraphMorphism]
      rw [← Category.assoc, graphMorphism_snd, Category.id_comp])

/-- **The fibre product of `[Δ_X] ⊗ [Γ_φᵗ]` and `η_X` is `Y`.** -/
def bottomFibreIso : bottomFibre sX sY φ hφ ≅ Y where
  hom := pullback.fst _ _ ≫ pullback.snd sX sY
  inv := bottomFibreInv sX sY φ hφ
  hom_inv_id := by
    obtain ⟨h₁, h₂⟩ := bottomFibre_eqs sX sY φ hφ
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [bottomFibreInv, Category.assoc, pullback.lift_fst, Category.id_comp]
        rw [h₁, h₂]
      · simp only [bottomFibreInv, Category.assoc, pullback.lift_fst, graphMorphism_snd,
          Category.comp_id, Category.id_comp]
    · simp only [bottomFibreInv, Category.assoc, pullback.lift_snd, Category.id_comp]
      exact h₂
  inv_hom_id := by
    rw [bottomFibreInv, pullback.lift_fst_assoc, graphMorphism_snd]

include hY in
omit [IsProper sY] in
/-- **`η_X ∘ ([Δ_X] ⊗ [Γ_φᵗ])` on cycles**: the composite is the class of
`y ↦ ((φ y, y), φ y)`. -/
theorem compositionInt_bottomTensor_diagonal :
    compositionInt k (prodBase sX sY) (prodBase sX sX) sX (canonicalDiagonalClassFamily k) hXY
        hXX hX (0 + ((d : ℤ) - e)) 0
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase (prodBase sX sY) (prodBase sX sX)) (bottomTensorEmbedding sX sY φ hφ)
          (((d + d : ℕ) : ℤ) - (0 + ((d : ℤ) - e)))))
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase (prodBase sX sX) sX) (diagonalGraphMorphism sX) ((d : ℤ) - 0))) =
      QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (prodBase (prodBase sX sY) sX) (bottomPairingMap sX sY φ hφ)
        ((d : ℤ) - ((0 + ((d : ℤ) - e)) + 0))) := by
  refine compositionInt_smoothTransversal k _ _ _ hXY hXX hX (0 + ((d : ℤ) - e)) 0
    (bottomTensorEmbedding sX sY φ hφ) (diagonalGraphMorphism sX) (bottomPairingMap sX sY φ hφ)
    (bottomFibreIso sX sY φ hφ) ?_ (qA := prodBase sX sY) (qB := sX) (qF := sY)
    (tensorEmbedding_tensorBase _ _ _ _ _ _ _ _) (diagonalGraphMorphism_prodBase sX)
    (bottomPairingMap_prodBase sX sY φ hφ) hXY hX hY (by push_cast; ring) (by simp)
    (by ring)
  obtain ⟨h₁, h₂⟩ := bottomFibre_eqs sX sY φ hφ
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp only [bottomFibreIso, compositionFibre.toProduct, Category.assoc, pullback.lift_fst,
        bottomPairingMap_fst, tensorEmbedding_fst_fst, Category.comp_id]
      rw [h₁, h₂]
    · simp only [bottomFibreIso, compositionFibre.toProduct, Category.assoc, pullback.lift_fst,
        bottomPairingMap_fst, graphMorphism_snd, Category.comp_id, tensorEmbedding_fst_snd,
        pullbackSymmetry_hom_comp_fst]
  · simp only [bottomFibreIso, compositionFibre.toProduct, Category.assoc, pullback.lift_snd,
      bottomPairingMap_snd, Category.comp_id]
    exact h₂

include hY in
omit [IsProper sY] in
/-- **`[X] ∘ (η_X ∘ (1 ⊗ aᵗ))` on cycles**: composing `y ↦ ((φ y, y), φ y)` with the
fundamental class `x ↦ (x, ⋆)` gives `y ↦ ((φ y, y), ⋆)`. -/
theorem compositionInt_bottomPairing_unitSection :
    compositionInt k (prodBase sX sY) sX sP (canonicalDiagonalClassFamily k) hXY hX hP
        ((0 + ((d : ℤ) - e)) + 0) (-(d : ℤ))
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase (prodBase sX sY) sX) (bottomPairingMap sX sY φ hφ)
          ((d : ℤ) - ((0 + ((d : ℤ) - e)) + 0))))
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase sX sP) (unitSectionEmbedding k sX sP) (((0 : ℕ) : ℤ) - -(d : ℤ)))) =
      QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (prodBase (prodBase sX sY) sP) (pointPairingMap sX sY sP φ hφ)
        (((0 : ℕ) : ℤ) - (((0 + ((d : ℤ) - e)) + 0) + -(d : ℤ)))) := by
  have hiso : IsIso (unitSectionEmbedding k sX sP ≫ pullback.fst sX sP) := by
    rw [pullback.lift_fst]; infer_instance
  have hc : pullback.fst (bottomPairingMap sX sY φ hφ ≫ pullback.snd (prodBase sX sY) sX)
        (unitSectionEmbedding k sX sP ≫ pullback.fst sX sP) ≫ φ = pullback.snd _ _ := by
    refine (congrArg (pullback.fst _ _ ≫ ·) (bottomPairingMap_snd sX sY φ hφ).symm).trans
      (pullback.condition.trans ?_)
    exact (congrArg (pullback.snd _ _ ≫ ·) (pullback.lift_fst _ _ _)).trans (Category.comp_id _)
  refine compositionInt_smoothTransversal k _ _ _ hXY hX hP ((0 + ((d : ℤ) - e)) + 0)
    (-(d : ℤ)) (bottomPairingMap sX sY φ hφ) (unitSectionEmbedding k sX sP)
    (pointPairingMap sX sY sP φ hφ) (asIso (pullback.fst _ _)) ?_ (qA := sY) (qB := sX) (qF := sY)
    (bottomPairingMap_prodBase sX sY φ hφ) (by rw [prodBase, pullback.lift_fst_assoc,
      Category.id_comp]) (pointPairingMap_prodBase sX sY sP φ hφ) hY hX hY
    (by ring) (by simp) (by push_cast; ring)
  apply pullback.hom_ext
  · simp only [asIso_hom, compositionFibre.toProduct, Category.assoc, pullback.lift_fst,
      pointPairingMap_fst, bottomPairingMap_fst]
  · simp only [asIso_hom, compositionFibre.toProduct, Category.assoc, pullback.lift_snd,
      pointPairingMap_snd]
    rw [← reassoc_of% hc, reassoc_of% hφ]

end Compositions

/-! ### The six correspondences, read on the products -/

section Pieces

variable {X Y : (SmoothProjectiveScheme k).FullSubcategory} {d e : ℕ}
  (hX : RelativeDimension X.obj.hom d)
  (hY : RelativeDimension Y.obj.hom e)
  (hXY : RelativeDimension (prodBase X.obj.hom Y.obj.hom) (d + e))
  (hXX : RelativeDimension (prodBase X.obj.hom X.obj.hom) (d + d))
  (hYY : RelativeDimension (prodBase Y.obj.hom Y.obj.hom) (e + e)) (f : Y ⟶ X)

attribute [local instance] isClosedImmersion_graphMorphism isClosedImmersion_unitSectionEmbedding
  isClosedImmersion_pointPairingMap

include hX hY in
/-- `a ⊗ 1 = [Γ_f] ⊗ [Δ_Y]`, read in `CH_{2e}((X × Y) × (Y × Y)) ⊗ ℚ`. -/
theorem corrEquivCorrespondence_tensorCorr_graph_diagonal :
    corrEquivCorrespondence k (X ⊗ Y).obj.hom (Y ⊗ Y).obj.hom hXY hYY
        (0 + 0) (SmoothProjectiveCorr.toCorr (X ⊗ Y) (Y ⊗ Y) (0 + 0)
          (tensorCorr 0 0 (graphCorrespondenceSP f) (correspondenceDiagonal k Y))) =
      (1 * 1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme
        (fieldChowSituation k) (prodBase (prodBase X.obj.hom Y.obj.hom)
          (prodBase Y.obj.hom Y.obj.hom))
        (topTensorEmbedding X.obj.hom Y.obj.hom f.hom.left (Over.w f.hom))
        (((e + e : ℕ) : ℤ) - (0 + 0))) := by
  refine (corrEquivCorrespondence_tensor k (canonicalDiagonalClassFamily k) X.obj.hom Y.obj.hom
    Y.obj.hom Y.obj.hom (canonicalDiagonalClassFamily_isoInvariant k) hX hY hY hY hXY hYY 0 0
    _ _).trans ?_
  simp only [LinearEquiv.coe_coe]
  rw [graphCorrespondenceSP, LinearEquiv.apply_symm_apply,
    corrEquivCorrespondence_graphCorr, corrEquivCorrespondence_correspondenceDiagonal Y hY,
    graphCorrespondence,
    tensorBlock_closedSubscheme k _ _ _ _ hX hY hY hY 0 0 _ _
      (graphMorphism_prodBase_of_comp _ _ _ (Over.w f.hom)) (graphMorphism_id_prodBase_self _) hY
      hY (by simp) (by simp)]
  rfl

include hX hY in
/-- `1 ⊗ aᵗ = [Δ_X] ⊗ [Γ_f]ᵗ`, read in `CH_{d+e}((X × Y) × (X × X)) ⊗ ℚ`. -/
theorem corrEquivCorrespondence_tensorCorr_diagonal_transpose :
    corrEquivCorrespondence k (X ⊗ Y).obj.hom (X ⊗ X).obj.hom hXY hXX
        (0 + ((d : ℤ) - e)) (SmoothProjectiveCorr.toCorr (X ⊗ Y) (X ⊗ X) _
          (tensorCorr 0 ((d : ℤ) - e) (correspondenceDiagonal k X)
            (transposeGraphCorrespondenceSP f d e))) =
      (1 * 1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme
        (fieldChowSituation k) (prodBase (prodBase X.obj.hom Y.obj.hom)
          (prodBase X.obj.hom X.obj.hom))
        (bottomTensorEmbedding X.obj.hom Y.obj.hom f.hom.left (Over.w f.hom))
        (((d + d : ℕ) : ℤ) - (0 + ((d : ℤ) - e)))) := by
  refine (corrEquivCorrespondence_tensor k (canonicalDiagonalClassFamily k) X.obj.hom Y.obj.hom
    X.obj.hom X.obj.hom (canonicalDiagonalClassFamily_isoInvariant k) hX hY hX hX hXY hXX 0
    ((d : ℤ) - e) _ _).trans ?_
  simp only [LinearEquiv.coe_coe]
  rw [corrEquivCorrespondence_correspondenceDiagonal X hX, transposeGraphCorrespondenceSP,
    LinearEquiv.apply_symm_apply, corrEquivCorrespondence_transposeGraphCorr _ _ hX hY,
    tensorBlock_closedSubscheme k _ _ _ _ hX hY hX hX 0 ((d : ℤ) - e) _ _
      (graphMorphism_id_prodBase_self _) (transposedGraphMorphism_prodBase _ _ _ (Over.w f.hom))
      hX hY (by simp) (by ring)]
  rfl

/-- `η_X = [Γ_{X → X × X}]`, read in `CH_d((X × X) × X) ⊗ ℚ`. -/
theorem corrEquivCorrespondence_graph_diag :
    corrEquivCorrespondence k (X ⊗ X).obj.hom X.obj.hom hXX hX 0
        (SmoothProjectiveCorr.toCorr (X ⊗ X) X 0
          (graphCorrespondenceSP (P := X ⊗ X) (SmoothProjectiveScheme.diag X))) =
      (1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (prodBase (prodBase X.obj.hom X.obj.hom) X.obj.hom) (diagonalGraphMorphism X.obj.hom)
        ((d : ℤ) - 0)) :=
  corrEquivCorrespondence_graphCorr k _ _ hXX hX _ _

/-- `[X]`, read in `CH_d(X × Spec k) ⊗ ℚ`, is the class of `x ↦ (x, ⋆)`. -/
theorem corrEquivCorrespondence_fundamentalClassCorr :
    corrEquivCorrespondence k X.obj.hom 𝐏.obj.hom hX relativeDimension_tensorUnit_hom (-(d : ℤ))
        (SmoothProjectiveCorr.toCorr X 𝐏 _ (fundamentalClassCorr hX)) =
      (1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (prodBase X.obj.hom 𝐏.obj.hom) (unitSectionEmbedding k X.obj.hom 𝐏.obj.hom)
        (((0 : ℕ) : ℤ) - -(d : ℤ))) := by
  rw [fundamentalClassCorr, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

attribute [local instance] isClosedImmersion_topPairingMap isClosedImmersion_bottomPairingMap

/-- `Stacks.WeilCohomology.compositionInt_topTensor_diagonal`, read with the structure morphisms
of the products of smooth projective schemes. -/
theorem compositionInt_topTensor_diagonal_tensorObj :
    compositionInt k (X ⊗ Y).obj.hom (Y ⊗ Y).obj.hom Y.obj.hom (canonicalDiagonalClassFamily k)
        hXY hYY hY (0 + 0) 0
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase (prodBase X.obj.hom Y.obj.hom) (prodBase Y.obj.hom Y.obj.hom))
          (topTensorEmbedding X.obj.hom Y.obj.hom f.hom.left (Over.w f.hom))
          (((e + e : ℕ) : ℤ) - (0 + 0))))
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase (prodBase Y.obj.hom Y.obj.hom) Y.obj.hom) (diagonalGraphMorphism Y.obj.hom)
          ((e : ℤ) - 0))) =
      QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (prodBase (prodBase X.obj.hom Y.obj.hom) Y.obj.hom)
        (topPairingMap X.obj.hom Y.obj.hom f.hom.left (Over.w f.hom)) ((e : ℤ) - ((0 + 0) + 0))) :=
  compositionInt_topTensor_diagonal X.obj.hom Y.obj.hom f.hom.left (Over.w f.hom) hY hXY hYY

/-- `Stacks.WeilCohomology.compositionInt_topPairing_unitSection`, read with the structure
morphisms of the products of smooth projective schemes. -/
theorem compositionInt_topPairing_unitSection_tensorObj :
    compositionInt k (X ⊗ Y).obj.hom Y.obj.hom 𝐏.obj.hom (canonicalDiagonalClassFamily k) hXY hY
        relativeDimension_tensorUnit_hom ((0 + 0) + 0) (-(e : ℤ))
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase (prodBase X.obj.hom Y.obj.hom) Y.obj.hom)
          (topPairingMap X.obj.hom Y.obj.hom f.hom.left (Over.w f.hom)) ((e : ℤ) - ((0 + 0) + 0))))
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase Y.obj.hom 𝐏.obj.hom) (unitSectionEmbedding k Y.obj.hom 𝐏.obj.hom)
          (((0 : ℕ) : ℤ) - -(e : ℤ)))) =
      QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (prodBase (prodBase X.obj.hom Y.obj.hom) 𝐏.obj.hom)
        (pointPairingMap X.obj.hom Y.obj.hom 𝐏.obj.hom f.hom.left (Over.w f.hom))
        (((0 : ℕ) : ℤ) - (((0 + 0) + 0) + -(e : ℤ)))) :=
  compositionInt_topPairing_unitSection X.obj.hom Y.obj.hom 𝐏.obj.hom f.hom.left (Over.w f.hom) hY
    relativeDimension_tensorUnit_hom hXY

include hY in
/-- `Stacks.WeilCohomology.compositionInt_bottomTensor_diagonal`, read with the structure
morphisms of the products of smooth projective schemes. -/
theorem compositionInt_bottomTensor_diagonal_tensorObj :
    compositionInt k (X ⊗ Y).obj.hom (X ⊗ X).obj.hom X.obj.hom (canonicalDiagonalClassFamily k)
        hXY hXX hX (0 + ((d : ℤ) - e)) 0
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase (prodBase X.obj.hom Y.obj.hom) (prodBase X.obj.hom X.obj.hom))
          (bottomTensorEmbedding X.obj.hom Y.obj.hom f.hom.left (Over.w f.hom))
          (((d + d : ℕ) : ℤ) - (0 + ((d : ℤ) - e)))))
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase (prodBase X.obj.hom X.obj.hom) X.obj.hom) (diagonalGraphMorphism X.obj.hom)
          ((d : ℤ) - 0))) =
      QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (prodBase (prodBase X.obj.hom Y.obj.hom) X.obj.hom)
        (bottomPairingMap X.obj.hom Y.obj.hom f.hom.left (Over.w f.hom))
        ((d : ℤ) - ((0 + ((d : ℤ) - e)) + 0))) :=
  compositionInt_bottomTensor_diagonal X.obj.hom Y.obj.hom f.hom.left (Over.w f.hom) hX hY hXY hXX

include hY in
/-- `Stacks.WeilCohomology.compositionInt_bottomPairing_unitSection`, read with the structure
morphisms of the products of smooth projective schemes. -/
theorem compositionInt_bottomPairing_unitSection_tensorObj :
    compositionInt k (X ⊗ Y).obj.hom X.obj.hom 𝐏.obj.hom (canonicalDiagonalClassFamily k) hXY hX
        relativeDimension_tensorUnit_hom ((0 + ((d : ℤ) - e)) + 0) (-(d : ℤ))
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase (prodBase X.obj.hom Y.obj.hom) X.obj.hom)
          (bottomPairingMap X.obj.hom Y.obj.hom f.hom.left (Over.w f.hom))
          ((d : ℤ) - ((0 + ((d : ℤ) - e)) + 0))))
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase X.obj.hom 𝐏.obj.hom) (unitSectionEmbedding k X.obj.hom 𝐏.obj.hom)
          (((0 : ℕ) : ℤ) - -(d : ℤ)))) =
      QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (prodBase (prodBase X.obj.hom Y.obj.hom) 𝐏.obj.hom)
        (pointPairingMap X.obj.hom Y.obj.hom 𝐏.obj.hom f.hom.left (Over.w f.hom))
        (((0 : ℕ) : ℤ) - (((0 + ((d : ℤ) - e)) + 0) + -(d : ℤ)))) :=
  compositionInt_bottomPairing_unitSection X.obj.hom Y.obj.hom 𝐏.obj.hom f.hom.left (Over.w f.hom)
    hX hY relativeDimension_tensorUnit_hom hXY

include hX hYY in
/-- **The top row, read on the products**: `[Y] ∘ η_Y ∘ (a ⊗ 1)` is the class of
`y ↦ ((f y, y), ⋆)` in `CH_e((X × Y) × Spec k) ⊗ ℚ`. -/
theorem corrEquivCorrespondence_topComposite :
    corrEquivCorrespondence k (X ⊗ Y).obj.hom 𝐏.obj.hom hXY
        relativeDimension_tensorUnit_hom ((0 + 0) + 0 + -(e : ℤ))
        (SmoothProjectiveCorr.toCorr (X ⊗ Y) 𝐏 _ ((canonicalCorrespondenceCompositionData k).comp
          ((canonicalCorrespondenceCompositionData k).comp
            (tensorCorr 0 0 (graphCorrespondenceSP f) (correspondenceDiagonal k Y))
            (graphCorrespondenceSP (P := Y ⊗ Y) (SmoothProjectiveScheme.diag Y)))
          (fundamentalClassCorr hY))) =
      (1 * 1 * 1 * 1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme
        (fieldChowSituation k) (prodBase (prodBase X.obj.hom Y.obj.hom) 𝐏.obj.hom)
        (pointPairingMap X.obj.hom Y.obj.hom 𝐏.obj.hom f.hom.left (Over.w f.hom))
        (((0 : ℕ) : ℤ) - (((0 + 0) + 0) + -(e : ℤ)))) := by
  simp only [canonicalCorrespondenceCompositionData, toCorr_correspondenceCompositionData_comp]
  refine (corrEquivCorrespondence_comp_comp k (canonicalDiagonalClassFamily k)
    (canonicalDiagonalClassFamily_isoInvariant k) (X ⊗ Y).obj.hom
    (Y ⊗ Y).obj.hom Y.obj.hom 𝐏.obj.hom hXY hYY hY relativeDimension_tensorUnit_hom
    (0 + 0) 0 (-(e : ℤ)) _ _ _).trans ?_
  simp only [corrEquivCorrespondence_fundamentalClassCorr hY,
    corrEquivCorrespondence_graph_diag hY hYY,
    corrEquivCorrespondence_tensorCorr_graph_diagonal hX hY hXY hYY f, composition_tmul]
  refine congrArg ((1 * 1 * 1 * 1 : ℚ) ⊗ₜ[ℤ] ·) ?_
  rw [compositionInt_topTensor_diagonal_tensorObj hY hXY hYY f]
  exact compositionInt_topPairing_unitSection_tensorObj hY hXY f

include hXX hY in
/-- **The bottom row, read on the products**: `[X] ∘ η_X ∘ (1 ⊗ aᵗ)` is the class of
`y ↦ ((f y, y), ⋆)` in `CH_e((X × Y) × Spec k) ⊗ ℚ`. -/
theorem corrEquivCorrespondence_bottomComposite :
    corrEquivCorrespondence k (X ⊗ Y).obj.hom 𝐏.obj.hom hXY
        relativeDimension_tensorUnit_hom ((0 + ((d : ℤ) - e)) + 0 + -(d : ℤ))
        (SmoothProjectiveCorr.toCorr (X ⊗ Y) 𝐏 _ ((canonicalCorrespondenceCompositionData k).comp
          ((canonicalCorrespondenceCompositionData k).comp
            (tensorCorr 0 ((d : ℤ) - e) (correspondenceDiagonal k X)
              (transposeGraphCorrespondenceSP f d e))
            (graphCorrespondenceSP (P := X ⊗ X) (SmoothProjectiveScheme.diag X)))
          (fundamentalClassCorr hX))) =
      (1 * 1 * 1 * 1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme
        (fieldChowSituation k) (prodBase (prodBase X.obj.hom Y.obj.hom) 𝐏.obj.hom)
        (pointPairingMap X.obj.hom Y.obj.hom 𝐏.obj.hom f.hom.left (Over.w f.hom))
        (((0 : ℕ) : ℤ) - (((0 + ((d : ℤ) - e)) + 0) + -(d : ℤ)))) := by
  simp only [canonicalCorrespondenceCompositionData, toCorr_correspondenceCompositionData_comp]
  refine (corrEquivCorrespondence_comp_comp k (canonicalDiagonalClassFamily k)
    (canonicalDiagonalClassFamily_isoInvariant k) (X ⊗ Y).obj.hom
    (X ⊗ X).obj.hom X.obj.hom 𝐏.obj.hom hXY hXX hX relativeDimension_tensorUnit_hom
    (0 + ((d : ℤ) - e)) 0 (-(d : ℤ)) _ _ _).trans ?_
  simp only [corrEquivCorrespondence_tensorCorr_diagonal_transpose hX hY hXY hXX f,
    corrEquivCorrespondence_graph_diag hX hXX, corrEquivCorrespondence_fundamentalClassCorr hX,
    composition_tmul]
  refine congrArg ((1 * 1 * 1 * 1 : ℚ) ⊗ₜ[ℤ] ·) ?_
  rw [compositionInt_bottomTensor_diagonal_tensorObj hX hY hXY hXX f]
  exact compositionInt_bottomPairing_unitSection_tensorObj hX hY hXY f

end Pieces

/-! ### Stacks 0FG8 -/

section Category

variable {X Y : (SmoothProjectiveScheme k).FullSubcategory} {d e : ℕ}
  (hX : RelativeDimension X.obj.hom d)
  (hY : RelativeDimension Y.obj.hom e)

attribute [local instance] isClosedImmersion_pointPairingMap

/-- **The transposed graph `aᵗ = [Γ_f]ᵗ ∈ Corr^{d-e}(Y, X)`** of a morphism `f : Y ⟶ X` of
equidimensional smooth projective schemes of dimensions `d` and `e` (Remark 0FG4), as a morphism
`Y ⟶ X` of the category of correspondences. -/
def transposeGraphHom (f : Y ⟶ X) (d e : ℕ) :
    (GradedCompositionData.Obj.mk Y : CorrespondenceCategory k) ⟶
      GradedCompositionData.Obj.mk X :=
  DirectSum.of (fun i ↦ SmoothProjectiveCorr _ _ i) ((d : ℤ) - e)
    (transposeGraphCorrespondenceSP f d e)

variable (X) in
/-- **`η_X = [Γ_{X → X × X}] ∈ Corr⁰(X × X, X)`**, the graph of the diagonal, as a morphism
`X ⊗ X ⟶ X` of the category of correspondences. -/
def diagonalGraphHom :
    CorrespondenceCategory.tensorObj (GradedCompositionData.Obj.mk X : CorrespondenceCategory k)
        (GradedCompositionData.Obj.mk X) ⟶ GradedCompositionData.Obj.mk X :=
  DirectSum.of (fun i ↦ SmoothProjectiveCorr _ _ i) 0
    (graphCorrespondenceSP (P := X ⊗ X) (SmoothProjectiveScheme.diag X))

/-- **The fundamental class `[X] ∈ Corr^{-d}(X, Spec k)`** of a smooth projective scheme
equidimensional of dimension `d`, as a morphism `X ⟶ 𝟏` of the category of correspondences. -/
def fundamentalClassHom :
    (GradedCompositionData.Obj.mk X : CorrespondenceCategory k) ⟶
      CorrespondenceCategory.tensorUnit (k := k) :=
  DirectSum.of (fun i ↦ SmoothProjectiveCorr _ _ i) (-(d : ℤ)) (fundamentalClassCorr hX)

/-- **Stacks Project, Tag 0FG8.** Let `f : Y ⟶ X` be a morphism of smooth projective schemes over
`k`, with `X` and `Y` equidimensional of dimensions `d` and `e`. Let `a = [Γ_f] ∈ Corr⁰(X, Y)`,
`aᵗ = [Γ_fᵗ] ∈ Corr^{d-e}(Y, X)`, `η_X = [Γ_{X → X × X}] ∈ Corr⁰(X × X, X)`,
`η_Y = [Γ_{Y → Y × Y}] ∈ Corr⁰(Y × Y, Y)`, and let `[X] ∈ Corr^{-d}(X, Spec k)` and
`[Y] ∈ Corr^{-e}(Y, Spec k)` be the fundamental classes. Then the diagram

  `X ⊗ Y --(a ⊗ 1)--> Y ⊗ Y --η_Y--> Y --[Y]--> Spec k`,
  `X ⊗ Y --(1 ⊗ aᵗ)--> X ⊗ X --η_X--> X --[X]--> Spec k`

commutes in the category of correspondences. Here `⊗` on morphisms is the tensor product of
correspondences `c ⊗ c' = pr₁₃^* c · pr₂₄^* c'`,
`Stacks.WeilCohomology.CorrespondenceCategory.tensorHom`, which is the tensor product of morphisms
of the symmetric monoidal structure of Stacks 0FG7 (`CorrespondenceCategory.tensorHom_eq` in
`StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CorrespondenceMonoidal`). -/
@[stacks 0FG8]
theorem graph_tensor_diagonal_fundamental_comm (f : Y ⟶ X) :
    CorrespondenceCategory.tensorHom (graphHom f : (GradedCompositionData.Obj.mk X :
        CorrespondenceCategory k) ⟶ GradedCompositionData.Obj.mk Y)
        (𝟙 (GradedCompositionData.Obj.mk Y : CorrespondenceCategory k)) ≫
        diagonalGraphHom Y ≫ fundamentalClassHom hY =
      CorrespondenceCategory.tensorHom (𝟙 (GradedCompositionData.Obj.mk X :
          CorrespondenceCategory k)) (transposeGraphHom f d e) ≫
        diagonalGraphHom X ≫ fundamentalClassHom hX := by
  have hXY : RelativeDimension (prodBase X.obj.hom Y.obj.hom) (d + e) :=
    (Nat.add_comm e d) ▸ relativeDimension_prodBase k X.obj.hom Y.obj.hom hX hY
  have hXX : RelativeDimension (prodBase X.obj.hom X.obj.hom) (d + d) :=
    relativeDimension_prodBase k X.obj.hom X.obj.hom hX hX
  have hYY : RelativeDimension (prodBase Y.obj.hom Y.obj.hom) (e + e) :=
    relativeDimension_prodBase k Y.obj.hom Y.obj.hom hY hY
  rw [GradedCompositionData.id_eq, GradedCompositionData.id_eq,
    show (canonicalCorrespondenceCompositionData k).diagonal X =
      correspondenceDiagonal k X from rfl,
    show (canonicalCorrespondenceCompositionData k).diagonal Y =
      correspondenceDiagonal k Y from rfl,
    transposeGraphHom, diagonalGraphHom, diagonalGraphHom, fundamentalClassHom,
    fundamentalClassHom]
  simp only [graphHom]
  rw [tensorHom_of_of, tensorHom_of_of, ← Category.assoc, ← Category.assoc,
    GradedCompositionData.of_comp_of, GradedCompositionData.of_comp_of,
    GradedCompositionData.of_comp_of, GradedCompositionData.of_comp_of]
  dsimp only
  refine of_eq_of_corrEquivCorrespondence hXY relativeDimension_tensorUnit_hom (by ring) _ _ ?_
  rw [corrEquivCorrespondence_topComposite hX hY hXY hYY f,
    corrEquivCorrespondence_bottomComposite hX hY hXY hXX f, correspondenceCongr_tmul]
  exact congrArg ((1 * 1 * 1 * 1 : ℚ) ⊗ₜ[ℤ] ·)
    (chowGroupDegreeEquiv_mk_cycleAssociatedToClosedSubscheme _ _ _)

end Category

end Stacks.WeilCohomology

end
