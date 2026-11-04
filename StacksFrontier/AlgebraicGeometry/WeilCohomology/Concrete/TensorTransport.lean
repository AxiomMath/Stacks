module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CorrespondenceTransport
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TensorAssociativity

/-!
# Transport of the tensor product of correspondences along isomorphisms

The tensor product of correspondences `c ⊗ c' = pr₁₃^* c · pr₂₄^* c'`
(`Stacks.WeilCohomology.tensor`, between smooth projective schemes over `k` of mixed dimension)
is natural with respect to isomorphisms over `k`: transporting `c ⊗ c'` along products of
isomorphisms gives the tensor product of the transports. This is one of the inputs of the
symmetric monoidal structure of Stacks 0FG7, where the constraints are graphs of isomorphisms and
composing with the graph of an isomorphism is transport
(`Stacks.WeilCohomology.comp_graphCorr_left`, `Stacks.WeilCohomology.comp_graphCorr_right`).

## Main results

* `Stacks.WeilCohomology.correspondenceEquivOfIso_trans`,
  `Stacks.WeilCohomology.corrEquivOfIso_trans`:
  transport along two composable pairs of isomorphisms is transport along the composites.
* `Stacks.WeilCohomology.corrEquivOfIso_congr`: transport depends only on the isomorphisms.
* `Stacks.WeilCohomology.corrEquivOfIso_tensor`: **the tensor product of correspondences is
  natural with respect to isomorphisms**, for an iso-invariant family of diagonal classes, and
  `Stacks.WeilCohomology.corrEquivOfIso_tensor_canonical` for the canonical family.

## References

* [Stacks Project, Tag 0FG7](https://stacks.math.columbia.edu/tag/0FG7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace Stacks.WeilCohomology

/-! ### Composition of transports -/

section Trans

variable (C : ChowSituation.{u}) {X Y X' Y' X'' Y'' : Scheme.{u}} (sX : X ⟶ C.S) (sY : Y ⟶ C.S)
  (sX' : X' ⟶ C.S) (sY' : Y' ⟶ C.S) (sX'' : X'' ⟶ C.S) (sY'' : Y'' ⟶ C.S)
  [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] [LocallyOfFiniteType sX']
  [LocallyOfFiniteType sY'] [LocallyOfFiniteType sX''] [LocallyOfFiniteType sY'']
  (φX : X' ⟶ X) [IsIso φX] (φY : Y' ⟶ Y) [IsIso φY] (hφX : φX ≫ sX = sX') (hφY : φY ≫ sY = sY')
  (ψX : X'' ⟶ X') [IsIso ψX] (ψY : Y'' ⟶ Y') [IsIso ψY] (hψX : ψX ≫ sX' = sX'')
  (hψY : ψY ≫ sY' = sY'')

/-- Transport of correspondences along `(ψX, ψY)` and then along `(φX, φY)` is transport along
the composites. -/
theorem correspondenceEquivOfIso_trans (e r : ℤ) (c : Correspondence C sX'' sY'' e r) :
    correspondenceEquivOfIso C sX sY sX' sY' φX φY hφX hφY e r
        (correspondenceEquivOfIso C sX' sY' sX'' sY'' ψX ψY hψX hψY e r c) =
      correspondenceEquivOfIso C sX sY sX'' sY'' (ψX ≫ φX) (ψY ≫ φY)
        (by rw [Category.assoc, hφX, hψX]) (by rw [Category.assoc, hφY, hψY]) e r c := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]
  | tmul q c =>
    rw [correspondenceEquivOfIso_tmul, correspondenceEquivOfIso_tmul,
      correspondenceEquivOfIso_tmul, chowPushforwardOfIso_comp_apply]
    congr 1
    refine chowPushforwardOfIso_congr_apply C _ _ _ _ ?_ _ _ _ _
    apply Limits.pullback.hom_ext <;> simp

end Trans

section Mixed

variable (k : Type u) [Field k] {X X' X'' Y Y' Y'' : Scheme.{u}}
  (sX : X ⟶ (fieldChowSituation k).S) (sX' : X' ⟶ (fieldChowSituation k).S)
  (sX'' : X'' ⟶ (fieldChowSituation k).S)
  (sY : Y ⟶ (fieldChowSituation k).S) (sY' : Y' ⟶ (fieldChowSituation k).S)
  (sY'' : Y'' ⟶ (fieldChowSituation k).S)
  [Smooth sX] [IsSeparated sX] [Smooth sX'] [IsSeparated sX'] [Smooth sX''] [IsSeparated sX'']
  [Smooth sY] [IsSeparated sY] [Smooth sY'] [IsSeparated sY'] [Smooth sY''] [IsSeparated sY'']

omit [IsSeparated sX] [IsSeparated sX'] [IsSeparated sX''] [IsSeparated sY] [IsSeparated sY']
  [IsSeparated sY''] in
/-- Transport of mixed-dimension correspondences along `(ψX, ψY)` and then along `(φX, φY)` is
transport along the composites. -/
theorem corrEquivOfIso_trans (φX : X' ⟶ X) [IsIso φX] (φY : Y' ⟶ Y) [IsIso φY]
    (hφX : φX ≫ sX = sX') (hφY : φY ≫ sY = sY') (ψX : X'' ⟶ X') [IsIso ψX] (ψY : Y'' ⟶ Y')
    [IsIso ψY] (hψX : ψX ≫ sX' = sX'') (hψY : ψY ≫ sY' = sY'') (r : ℤ) (c : Corr k sX'' sY'' r) :
    corrEquivOfIso k sX sX' sY sY' φX φY hφX hφY r
        (corrEquivOfIso k sX' sX'' sY' sY'' ψX ψY hψX hψY r c) =
      corrEquivOfIso k sX sX'' sY sY'' (ψX ≫ φX) (ψY ≫ φY) (by rw [Category.assoc, hφX, hψX])
        (by rw [Category.assoc, hφY, hψY]) r c := by
  induction c using Corr.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]
  | lof d e x =>
    have h := correspondenceEquivOfIso_congr (fieldChowSituation k) (partBase sX d)
      (partBase sY e) (partBase sX'' d) (partBase sY'' e)
      (partMap sX' sX'' ψX hψX d ≫ partMap sX sX' φX hφX d)
      (partMap sX sX'' (ψX ≫ φX) (by rw [Category.assoc, hφX, hψX]) d)
      (partMap sY' sY'' ψY hψY e ≫ partMap sY sY' φY hφY e)
      (partMap sY sY'' (ψY ≫ φY) (by rw [Category.assoc, hφY, hψY]) e)
      (by rw [Category.assoc, partMap_comp_partBase, partMap_comp_partBase])
      (partMap_comp_partBase _ _ _ _ _)
      (by rw [Category.assoc, partMap_comp_partBase, partMap_comp_partBase])
      (partMap_comp_partBase _ _ _ _ _)
      (partMap_comp sX sX' sX'' φX hφX ψX hψX d).symm
      (partMap_comp sY sY' sY'' φY hφY ψY hψY e).symm e r x
    have h₂ := correspondenceEquivOfIso_trans (fieldChowSituation k) (partBase sX d)
      (partBase sY e) (partBase sX' d) (partBase sY' e) (partBase sX'' d) (partBase sY'' e)
      (partMap sX sX' φX hφX d) (partMap sY sY' φY hφY e) (partMap_comp_partBase _ _ _ _ _)
      (partMap_comp_partBase _ _ _ _ _) (partMap sX' sX'' ψX hψX d) (partMap sY' sY'' ψY hψY e)
      (partMap_comp_partBase _ _ _ _ _) (partMap_comp_partBase _ _ _ _ _) e r x
    simp only [corrEquivOfIso_lof_lof]
    exact congrArg (DirectSum.lof ℚ ℕ _ d) (congrArg (DirectSum.lof ℚ ℕ _ e) (h₂.trans h))

omit [IsSeparated sX] [IsSeparated sX'] [IsSeparated sY] [IsSeparated sY'] in
/-- Transport of mixed-dimension correspondences depends only on the isomorphisms. -/
theorem corrEquivOfIso_congr {φX φX' : X' ⟶ X} [IsIso φX] [IsIso φX'] {φY φY' : Y' ⟶ Y}
    [IsIso φY] [IsIso φY'] (hφX : φX ≫ sX = sX') (hφX' : φX' ≫ sX = sX')
    (hφY : φY ≫ sY = sY') (hφY' : φY' ≫ sY = sY') (hX : φX = φX') (hY : φY = φY') (r : ℤ)
    (c : Corr k sX' sY' r) :
    corrEquivOfIso k sX sX' sY sY' φX φY hφX hφY r c =
      corrEquivOfIso k sX sX' sY sY' φX' φY' hφX' hφY' r c := by
  subst hX hY
  rfl

end Mixed

/-! ### Naturality of the tensor product -/

section Tensor

variable (k : Type u) [Field k] {X X' Y Y' X₀ X₀' Y₀ Y₀' : Scheme.{u}}
  (sX : X ⟶ (fieldChowSituation k).S) (sX' : X' ⟶ (fieldChowSituation k).S)
  (sY : Y ⟶ (fieldChowSituation k).S) (sY' : Y' ⟶ (fieldChowSituation k).S)
  (sX₀ : X₀ ⟶ (fieldChowSituation k).S) (sX₀' : X₀' ⟶ (fieldChowSituation k).S)
  (sY₀ : Y₀ ⟶ (fieldChowSituation k).S) (sY₀' : Y₀' ⟶ (fieldChowSituation k).S)

section Parts

variable [Smooth sX] [Smooth sX'] [Smooth sX₀] [Smooth sX₀']
  (φX : X₀ ⟶ X) [IsIso φX] (φX' : X₀' ⟶ X') [IsIso φX'] (hφX : φX ≫ sX = sX₀)
  (hφX' : φX' ≫ sX' = sX₀')

/-- The inclusion of the product of two parts in the part of the product commutes with the
transport along isomorphisms. -/
theorem partProdHom_partMap (d d' : ℕ) :
    partProdHom k sX₀ sX₀' d d' ≫
        partMap (prodBase sX sX') (prodBase sX₀ sX₀') (prodHom sX sX' sX₀ sX₀' φX φX' hφX hφX')
          (prodHom_comp_prodBase _ _ _ _ _ _ _ _) (d + d') =
      prodHom (partBase sX d) (partBase sX' d') (partBase sX₀ d) (partBase sX₀' d')
          (partMap sX sX₀ φX hφX d) (partMap sX' sX₀' φX' hφX' d')
          (partMap_comp_partBase _ _ _ _ _) (partMap_comp_partBase _ _ _ _ _) ≫
        partProdHom k sX sX' d d' := by
  rw [← cancel_mono (dimPart (prodBase sX sX') (d + d')).ι, Category.assoc, Category.assoc,
    partMap_ι, partProdHom_ι_assoc, partProdHom_ι]
  apply Limits.pullback.hom_ext <;> simp

end Parts

variable [Smooth sX] [IsSeparated sX] [Smooth sX'] [IsSeparated sX'] [Smooth sY] [IsSeparated sY]
  [Smooth sY'] [IsSeparated sY'] [IsProper sX] [IsProper sX'] [IsProper sY] [IsProper sY']
  [Smooth sX₀] [IsSeparated sX₀] [Smooth sX₀'] [IsSeparated sX₀'] [Smooth sY₀] [IsSeparated sY₀]
  [Smooth sY₀'] [IsSeparated sY₀'] [IsProper sX₀] [IsProper sX₀'] [IsProper sY₀] [IsProper sY₀']
  (φX : X₀ ⟶ X) [IsIso φX] (φX' : X₀' ⟶ X') [IsIso φX'] (φY : Y₀ ⟶ Y) [IsIso φY]
  (φY' : Y₀' ⟶ Y') [IsIso φY'] (hφX : φX ≫ sX = sX₀) (hφX' : φX' ≫ sX' = sX₀')
  (hφY : φY ≫ sY = sY₀) (hφY' : φY' ≫ sY' = sY₀')

omit [IsSeparated sX] [IsSeparated sX'] [IsSeparated sY] [IsSeparated sY'] [IsProper sX]
  [IsProper sX'] [IsProper sY] [IsProper sY'] [IsSeparated sX₀] [IsSeparated sX₀']
  [IsSeparated sY₀] [IsSeparated sY₀'] [IsProper sX₀] [IsProper sX₀'] [IsProper sY₀]
  [IsProper sY₀'] in
/-- The inclusion of a block of the fourfold product commutes with the transport along
isomorphisms. -/
theorem tensorBlockHom_prodHom_partMap (d d' e e' : ℕ) :
    tensorBlockHom k sX₀ sX₀' sY₀ sY₀' d d' e e' ≫
        prodHom (partBase (prodBase sX sX') (d + d')) (partBase (prodBase sY sY') (e + e'))
          (partBase (prodBase sX₀ sX₀') (d + d')) (partBase (prodBase sY₀ sY₀') (e + e'))
          (partMap (prodBase sX sX') (prodBase sX₀ sX₀') (prodHom sX sX' sX₀ sX₀' φX φX' hφX hφX')
            (prodHom_comp_prodBase _ _ _ _ _ _ _ _) (d + d'))
          (partMap (prodBase sY sY') (prodBase sY₀ sY₀') (prodHom sY sY' sY₀ sY₀' φY φY' hφY hφY')
            (prodHom_comp_prodBase _ _ _ _ _ _ _ _) (e + e'))
          (partMap_comp_partBase _ _ _ _ _) (partMap_comp_partBase _ _ _ _ _) =
      prodHom (prodBase (partBase sX d) (partBase sX' d'))
          (prodBase (partBase sY e) (partBase sY' e'))
          (prodBase (partBase sX₀ d) (partBase sX₀' d'))
          (prodBase (partBase sY₀ e) (partBase sY₀' e'))
          (prodHom (partBase sX d) (partBase sX' d') (partBase sX₀ d) (partBase sX₀' d')
            (partMap sX sX₀ φX hφX d) (partMap sX' sX₀' φX' hφX' d')
            (partMap_comp_partBase _ _ _ _ _) (partMap_comp_partBase _ _ _ _ _))
          (prodHom (partBase sY e) (partBase sY' e') (partBase sY₀ e) (partBase sY₀' e')
            (partMap sY sY₀ φY hφY e) (partMap sY' sY₀' φY' hφY' e')
            (partMap_comp_partBase _ _ _ _ _) (partMap_comp_partBase _ _ _ _ _))
          (prodHom_comp_prodBase _ _ _ _ _ _ _ _) (prodHom_comp_prodBase _ _ _ _ _ _ _ _) ≫
        tensorBlockHom k sX sX' sY sY' d d' e e' := by
  apply Limits.pullback.hom_ext
  · simp only [tensorBlockHom, Category.assoc, Limits.pullback.lift_fst,
      Limits.pullback.lift_fst_assoc]
    rw [partProdHom_partMap]
  · simp only [tensorBlockHom, Category.assoc, Limits.pullback.lift_snd,
      Limits.pullback.lift_snd_assoc]
    rw [partProdHom_partMap]

/-- Reading a block of the tensor product in the block of the product commutes with the
transport along isomorphisms. -/
theorem correspondenceEquivOfIso_tensorBlockInclusion_partMap (d d' e e' : ℕ) (r : ℤ)
    (z : Correspondence (fieldChowSituation k) (prodBase (partBase sX₀ d) (partBase sX₀' d'))
      (prodBase (partBase sY₀ e) (partBase sY₀' e')) ((e + e' : ℕ) : ℤ) r) :
    correspondenceEquivOfIso (fieldChowSituation k) (partBase (prodBase sX sX') (d + d'))
        (partBase (prodBase sY sY') (e + e')) (partBase (prodBase sX₀ sX₀') (d + d'))
        (partBase (prodBase sY₀ sY₀') (e + e'))
        (partMap (prodBase sX sX') (prodBase sX₀ sX₀') (prodHom sX sX' sX₀ sX₀' φX φX' hφX hφX')
          (prodHom_comp_prodBase _ _ _ _ _ _ _ _) (d + d'))
        (partMap (prodBase sY sY') (prodBase sY₀ sY₀') (prodHom sY sY' sY₀ sY₀' φY φY' hφY hφY')
          (prodHom_comp_prodBase _ _ _ _ _ _ _ _) (e + e'))
        (partMap_comp_partBase _ _ _ _ _) (partMap_comp_partBase _ _ _ _ _) ((e + e' : ℕ) : ℤ) r
        (tensorBlockInclusion k sX₀ sX₀' sY₀ sY₀' d d' e e' r z) =
      tensorBlockInclusion k sX sX' sY sY' d d' e e' r
        (correspondenceEquivOfIso (fieldChowSituation k)
          (prodBase (partBase sX d) (partBase sX' d')) (prodBase (partBase sY e) (partBase sY' e'))
          (prodBase (partBase sX₀ d) (partBase sX₀' d'))
          (prodBase (partBase sY₀ e) (partBase sY₀' e'))
          (prodHom (partBase sX d) (partBase sX' d') (partBase sX₀ d) (partBase sX₀' d')
            (partMap sX sX₀ φX hφX d) (partMap sX' sX₀' φX' hφX' d')
            (partMap_comp_partBase _ _ _ _ _) (partMap_comp_partBase _ _ _ _ _))
          (prodHom (partBase sY e) (partBase sY' e') (partBase sY₀ e) (partBase sY₀' e')
            (partMap sY sY₀ φY hφY e) (partMap sY' sY₀' φY' hφY' e')
            (partMap_comp_partBase _ _ _ _ _) (partMap_comp_partBase _ _ _ _ _))
          (prodHom_comp_prodBase _ _ _ _ _ _ _ _) (prodHom_comp_prodBase _ _ _ _ _ _ _ _)
          ((e + e' : ℕ) : ℤ) r z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul q c =>
    rw [tensorBlockInclusion_tmul, correspondenceEquivOfIso_tmul, correspondenceEquivOfIso_tmul,
      tensorBlockInclusion_tmul]
    congr 1
    rw [← properChowPushforward_eq_chowPushforwardOfIso _ _ _ _ _ _
        (properPushforwardDescends _ _ _ _ _ _),
      ← properChowPushforward_eq_chowPushforwardOfIso _ _ _ _ _ _
        (properPushforwardDescends _ _ _ _ _ _),
      ← properChowPushforward_comp_apply (fieldChowSituation k) _ _ _ _ _ _ rfl
        (tensorBlockHom_comp_prodBase k sX₀ sX₀' sY₀ sY₀' d d' e e')
        (prodHom_comp_prodBase _ _ _ _ _ _ _ _) (by
          rw [Category.assoc, prodHom_comp_prodBase, tensorBlockHom_comp_prodBase]) _ _ _ _ _,
      ← properChowPushforward_comp_apply (fieldChowSituation k) _ _ _ _ _ _ rfl
        (prodHom_comp_prodBase _ _ _ _ _ _ _ _)
        (tensorBlockHom_comp_prodBase k sX sX' sY sY' d d' e e') (by
          rw [Category.assoc, tensorBlockHom_comp_prodBase, prodHom_comp_prodBase]) _ _ _ _ _]
    · exact properChowPushforward_congr_hom (fieldChowSituation k) _ _
        (tensorBlockHom_prodHom_partMap k sX sX' sY sY' sX₀ sX₀' sY₀ sY₀' φX φX' φY φY' hφX hφX'
          hφY hφY' d d' e e') _ _ _ _ _ _
    all_goals exact properPushforwardDescends _ _ _ _ _ _

/-- `Stacks.WeilCohomology.corrEquivOfIso_tensor` on blocks. -/
theorem corrEquivOfIso_tensor_lof_lof {Δ : DiagonalClassFamily k} (hΔ : Δ.IsoInvariant)
    (r r' : ℤ) (d e d' e' : ℕ)
    (x : Correspondence (fieldChowSituation k) (partBase sX₀ d) (partBase sY₀ e) e r)
    (x' : Correspondence (fieldChowSituation k) (partBase sX₀' d') (partBase sY₀' e') e' r') :
    corrEquivOfIso k (prodBase sX sX') (prodBase sX₀ sX₀') (prodBase sY sY') (prodBase sY₀ sY₀')
        (prodHom sX sX' sX₀ sX₀' φX φX' hφX hφX') (prodHom sY sY' sY₀ sY₀' φY φY' hφY hφY')
        (prodHom_comp_prodBase _ _ _ _ _ _ _ _) (prodHom_comp_prodBase _ _ _ _ _ _ _ _) (r + r')
        (tensor k sX₀ sX₀' sY₀ sY₀' Δ r r' (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e x))
          (DirectSum.lof ℚ ℕ _ d' (DirectSum.lof ℚ ℕ _ e' x'))) =
      tensor k sX sX' sY sY' Δ r r'
        (corrEquivOfIso k sX sX₀ sY sY₀ φX φY hφX hφY r
          (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e x)))
        (corrEquivOfIso k sX' sX₀' sY' sY₀' φX' φY' hφX' hφY' r'
          (DirectSum.lof ℚ ℕ _ d' (DirectSum.lof ℚ ℕ _ e' x'))) := by
  simp only [tensor_lof_lof, corrEquivOfIso_lof_lof]
  congr 2
  rw [correspondenceEquivOfIso_tensorBlockInclusion_partMap,
    correspondenceEquivOfIso_tensorBlock k Δ (partBase sX d) (partBase sX' d')
      (partBase sY e) (partBase sY' e') (partBase sX₀ d) (partBase sX₀' d') (partBase sY₀ e)
      (partBase sY₀' e') (partMap sX sX₀ φX hφX d) (partMap sX' sX₀' φX' hφX' d')
      (partMap sY sY₀ φY hφY e) (partMap sY' sY₀' φY' hφY' e')
      (partMap_comp_partBase _ _ _ _ _) (partMap_comp_partBase _ _ _ _ _)
      (partMap_comp_partBase _ _ _ _ _) (partMap_comp_partBase _ _ _ _ _) hΔ
      (relativeDimension_partBase sX d) (relativeDimension_partBase sX' d')
      (relativeDimension_partBase sY e) (relativeDimension_partBase sY' e')
      (relativeDimension_partBase sX₀ d) (relativeDimension_partBase sX₀' d')
      (relativeDimension_partBase sY₀ e) (relativeDimension_partBase sY₀' e')]

/-- **The tensor product of correspondences is natural with respect to isomorphisms over `k`**:
for isomorphisms `φX : X₀ ≅ X`, `φX' : X₀' ≅ X'`, `φY : Y₀ ≅ Y`, `φY' : Y₀' ≅ Y'` over `k`, the
transport of `c ⊗ c'` along `φX × φX'` and `φY × φY'` is the tensor product of the transports of
`c` and `c'`, for an iso-invariant family of diagonal classes. -/
theorem corrEquivOfIso_tensor {Δ : DiagonalClassFamily k} (hΔ : Δ.IsoInvariant) (r r' : ℤ)
    (a : Corr k sX₀ sY₀ r) (b : Corr k sX₀' sY₀' r') :
    corrEquivOfIso k (prodBase sX sX') (prodBase sX₀ sX₀') (prodBase sY sY') (prodBase sY₀ sY₀')
        (prodHom sX sX' sX₀ sX₀' φX φX' hφX hφX') (prodHom sY sY' sY₀ sY₀' φY φY' hφY hφY')
        (prodHom_comp_prodBase _ _ _ _ _ _ _ _) (prodHom_comp_prodBase _ _ _ _ _ _ _ _) (r + r')
        (tensor k sX₀ sX₀' sY₀ sY₀' Δ r r' a b) =
      tensor k sX sX' sY sY' Δ r r' (corrEquivOfIso k sX sX₀ sY sY₀ φX φY hφX hφY r a)
        (corrEquivOfIso k sX' sX₀' sY' sY₀' φX' φY' hφX' hφY' r' b) := by
  have key : (tensor k sX₀ sX₀' sY₀ sY₀' Δ r r').compr₂
        (corrEquivOfIso k (prodBase sX sX') (prodBase sX₀ sX₀') (prodBase sY sY')
          (prodBase sY₀ sY₀') (prodHom sX sX' sX₀ sX₀' φX φX' hφX hφX')
          (prodHom sY sY' sY₀ sY₀' φY φY' hφY hφY') (prodHom_comp_prodBase _ _ _ _ _ _ _ _)
          (prodHom_comp_prodBase _ _ _ _ _ _ _ _) (r + r')).toLinearMap =
      (tensor k sX sX' sY sY' Δ r r').compl₁₂
        (corrEquivOfIso k sX sX₀ sY sY₀ φX φY hφX hφY r).toLinearMap
        (corrEquivOfIso k sX' sX₀' sY' sY₀' φX' φY' hφX' hφY' r').toLinearMap :=
    DirectSum.linearMap_ext ℚ fun d ↦ DirectSum.linearMap_ext ℚ fun e ↦
      LinearMap.ext fun x ↦ DirectSum.linearMap_ext ℚ fun d' ↦ DirectSum.linearMap_ext ℚ fun e' ↦
        LinearMap.ext fun x' ↦ corrEquivOfIso_tensor_lof_lof k sX sX' sY sY' sX₀ sX₀' sY₀ sY₀'
          φX φX' φY φY' hφX hφX' hφY hφY' hΔ r r' d e d' e' x x'
  exact LinearMap.congr_fun₂ key a b

/-- `Stacks.WeilCohomology.corrEquivOfIso_tensor` for the canonical diagonal classes. -/
theorem corrEquivOfIso_tensor_canonical (r r' : ℤ) (a : Corr k sX₀ sY₀ r)
    (b : Corr k sX₀' sY₀' r') :
    corrEquivOfIso k (prodBase sX sX') (prodBase sX₀ sX₀') (prodBase sY sY') (prodBase sY₀ sY₀')
        (prodHom sX sX' sX₀ sX₀' φX φX' hφX hφX') (prodHom sY sY' sY₀ sY₀' φY φY' hφY hφY')
        (prodHom_comp_prodBase _ _ _ _ _ _ _ _) (prodHom_comp_prodBase _ _ _ _ _ _ _ _) (r + r')
        (tensor k sX₀ sX₀' sY₀ sY₀' (canonicalDiagonalClassFamily k) r r' a b) =
      tensor k sX sX' sY sY' (canonicalDiagonalClassFamily k) r r'
        (corrEquivOfIso k sX sX₀ sY sY₀ φX φY hφX hφY r a)
        (corrEquivOfIso k sX' sX₀' sY' sY₀' φX' φY' hφX' hφY' r' b) :=
  corrEquivOfIso_tensor k sX sX' sY sY' sX₀ sX₀' sY₀ sY₀' φX φX' φY φY' hφX hφX' hφY hφY'
    (canonicalDiagonalClassFamily_isoInvariant k) r r' a b

end Tensor

end Stacks.WeilCohomology

end
