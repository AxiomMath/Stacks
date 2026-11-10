module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CoproductCorrespondences
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TensorClopen
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TensorClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.DiagonalUnit
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.GraphComposition

/-!
# The tensor product of the diagonals is the diagonal

For smooth proper schemes `X` and `X'` over a field `k`, the tensor product of correspondences
(Stacks 0FG7) of the diagonal classes is the diagonal class of the product:

  `[Δ_X] ⊗ [Δ_{X'}] = [Δ_{X × X'}]`  in  `Corr⁰(X × X', X × X')`,

that is, `𝟙 ⊗ 𝟙 = 𝟙` in the category of correspondences.

On the parts `X_d` and `X'_{d'}` of constant dimension this is `[A] ⊗ [A'] = [A ×_k A']`
(`Stacks.WeilCohomology.tensorBlock_closedSubscheme`) for the two diagonals, whose product is the
diagonal of `X_d × X'_{d'}`. The part `(X × X')_n` of the product is the disjoint union of the open
and closed pieces `X_d × X'_{d'}` with `d + d' = n`, and the cycle of its diagonal is the sum of
the cycles of the diagonals of the pieces.

## Main definitions

* `Stacks.WeilCohomology.partProdHomOfEq`: the open and closed immersion
  `X_d × X'_{d'} ⟶ (X × X')_n` for `d + d' = n`.

## Main results

* `Stacks.WeilCohomology.sum_cycle_partProdHomOfEq_graphMorphism`: the cycle of the diagonal of
  `(X × X')_n` is the sum of the cycles of the diagonals of the pieces `X_d × X'_{d'}`.
* `Stacks.WeilCohomology.tensor_diagonalCorr`: `[Δ_X] ⊗ [Δ_{X'}] = [Δ_{X × X'}]`.

## References

* [Stacks Project, Tag 0FG7](https://stacks.math.columbia.edu/tag/0FG7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace Stacks.WeilCohomology

variable (k : Type u) [Field k] {X X' : Scheme.{u}}
  (sX : X ⟶ (fieldChowSituation k).S) (sX' : X' ⟶ (fieldChowSituation k).S)
  [Smooth sX] [IsSeparated sX] [Smooth sX'] [IsSeparated sX']

attribute [local instance] isClosedImmersion_graphMorphism

/-! ### The pieces `X_d × X'_{d'}` of `(X × X')_n` -/

section Pieces

/-- **The product of two parts in a part of the product**: the open immersion
`X_d × X'_{d'} ⟶ (X × X')_n` for `d + d' = n`. -/
def partProdHomOfEq {d d' n : ℕ} (h : d + d' = n) :
    (Limits.pullback (partBase sX d) (partBase sX' d') : Scheme.{u}) ⟶
      (dimPart (prodBase sX sX') n).toScheme :=
  IsOpenImmersion.lift (dimPart (prodBase sX sX') n).ι (partProdMap sX sX' d d')
    (by subst h; rw [Scheme.Opens.range_ι]; exact range_partProdMap_subset k sX sX' d d')

omit [IsSeparated sX] [IsSeparated sX'] in
/-- The immersion `X_d × X'_{d'} ⟶ (X × X')_n` followed by the inclusion of `(X × X')_n` into
`X × X'` is `partProdMap`. -/
@[reassoc (attr := simp)]
theorem partProdHomOfEq_ι {d d' n : ℕ} (h : d + d' = n) :
    partProdHomOfEq k sX sX' h ≫ (dimPart (prodBase sX sX') n).ι = partProdMap sX sX' d d' :=
  IsOpenImmersion.lift_fac _ _ _

/-- The map `X_d × X'_{d'} ⟶ (X × X')_n` is an open immersion. -/
instance {d d' n : ℕ} (h : d + d' = n) : IsOpenImmersion (partProdHomOfEq k sX sX' h) := by
  have : IsOpenImmersion (partProdHomOfEq k sX sX' h ≫ (dimPart (prodBase sX sX') n).ι) := by
    rw [partProdHomOfEq_ι]; infer_instance
  exact IsOpenImmersion.of_comp _ (dimPart (prodBase sX sX') n).ι

omit [IsSeparated sX] [IsSeparated sX'] in
/-- The map `X_d × X'_{d'} ⟶ (X × X')_n` lies over the base. -/
theorem partProdHomOfEq_comp_partBase {d d' n : ℕ} (h : d + d' = n) :
    partProdHomOfEq k sX sX' h ≫ partBase (prodBase sX sX') n =
      prodBase (partBase sX d) (partBase sX' d') := by
  change partProdHomOfEq k sX sX' h ≫ (dimPart (prodBase sX sX') n).ι ≫ prodBase sX sX' = _
  rw [partProdHomOfEq_ι_assoc, partProdMap_comp_prodBase]

/-- For proper `X` and `X'`, the map `X_d × X'_{d'} ⟶ (X × X')_n` is proper. -/
instance [IsProper sX] [IsProper sX'] {d d' n : ℕ} (h : d + d' = n) :
    IsProper (partProdHomOfEq k sX sX' h) := by
  have : IsProper (partProdHomOfEq k sX sX' h ≫ partBase (prodBase sX sX') n) := by
    rw [partProdHomOfEq_comp_partBase]; infer_instance
  exact IsProper.of_comp _ (partBase (prodBase sX sX') n)

/-- For proper `X` and `X'`, the map `X_d × X'_{d'} ⟶ (X × X')_n` is a closed immersion. -/
instance [IsProper sX] [IsProper sX'] {d d' n : ℕ} (h : d + d' = n) :
    IsClosedImmersion (partProdHomOfEq k sX sX' h) :=
  IsClosedImmersion.of_isPreimmersion _ (partProdHomOfEq k sX sX' h).isClosedMap.isClosed_range

omit [IsSeparated sX] [IsSeparated sX'] in
/-- `partProdHomOfEq` at `n = d + d'` is `partProdHom`. -/
theorem partProdHomOfEq_rfl (d d' : ℕ) :
    partProdHomOfEq k sX sX' (rfl : d + d' = d + d') = partProdHom k sX sX' d d' :=
  rfl

omit [IsSeparated sX] [IsSeparated sX'] in
/-- A point of `X × X'` lies in the image of `X_d × X'_{d'}` for the parts `X_d`, `X'_{d'}`
containing its two projections. -/
theorem mem_range_partProdMap (z : (Limits.pullback sX sX' : Scheme.{u})) {d d' : ℕ}
    (hd : Limits.pullback.fst sX sX' z ∈ dimPart sX d)
    (hd' : Limits.pullback.snd sX sX' z ∈ dimPart sX' d') :
    z ∈ Set.range (partProdMap sX sX' d d') := by
  rw [Scheme.Pullback.range_map]
  exact ⟨by rw [Scheme.Opens.range_ι]; exact hd, by rw [Scheme.Opens.range_ι]; exact hd'⟩

/-- A point of `(X × X')_n` comes from a piece `X_d × X'_{d'}` with `d + d' = n`, where `X_d` and
`X'_{d'}` contain its two projections. -/
private theorem exists_partProdMap_eq_of_mem {Y Y' : Scheme.{u}}
    (tY : Y ⟶ (fieldChowSituation k).S) (tY' : Y' ⟶ (fieldChowSituation k).S)
    [Smooth tY] [Smooth tY'] {n : ℕ} (z : (Limits.pullback tY tY' : Scheme.{u}))
    (hz : z ∈ dimPart (prodBase tY tY') n) :
    ∃ (d d' : ℕ) (t : (Limits.pullback (partBase tY d) (partBase tY' d') : Scheme.{u})),
      d + d' = n ∧ partProdMap tY tY' d d' t = z ∧
        Limits.pullback.fst tY tY' z ∈ dimPart tY d ∧
        Limits.pullback.snd tY tY' z ∈ dimPart tY' d' := by
  obtain ⟨d, hd⟩ := (isClopenDecomposition_dimPart tY).exists_mem (Limits.pullback.fst tY tY' z)
  obtain ⟨d', hd'⟩ := (isClopenDecomposition_dimPart tY').exists_mem (Limits.pullback.snd tY tY' z)
  obtain ⟨t, ht⟩ := mem_range_partProdMap k tY tY' z hd hd'
  exact ⟨d, d', t, (isClopenDecomposition_dimPart (prodBase tY tY')).eq_of_mem
    (range_partProdMap_subset k tY tY' d d' ⟨t, ht⟩) hz, ht, hd, hd'⟩

end Pieces

/-! ### The diagonal of `(X × X')_n` -/

section Diagonal

variable [IsProper sX] [IsProper sX']

/-- The pairs `(d, d')` with `d + d' = n`, `d ∈ D` and `d' ∈ D'`. -/
abbrev partPairs (D D' : Finset ℕ) (n : ℕ) : Finset {p : ℕ × ℕ // p.1 + p.2 = n} :=
  (D ×ˢ D').subtype fun p ↦ p.1 + p.2 = n

/-- **The diagonal of `(X × X')_n` is the sum of the diagonals of the pieces**: the cycle of the
diagonal of `(X × X')_n` is the sum, over the pieces `X_d × X'_{d'}` with `d + d' = n`, of the
cycles of their diagonals. -/
theorem sum_cycle_partProdHomOfEq_graphMorphism {D D' : Finset ℕ}
    (hD : ∀ d, (dimPart sX d : Set X).Nonempty → d ∈ D)
    (hD' : ∀ d, (dimPart sX' d : Set X').Nonempty → d ∈ D') (n : ℕ) (m : ℤ) :
    ∑ i ∈ partPairs D D' n,
        cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase (partBase (prodBase sX sX') n) (partBase (prodBase sX sX') n))
          (partProdHomOfEq k sX sX' i.2 ≫
            graphMorphism (partBase (prodBase sX sX') n) (partBase (prodBase sX sX') n) (𝟙 _)
              (Category.id_comp _)) m =
      cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (prodBase (partBase (prodBase sX sX') n) (partBase (prodBase sX sX') n))
        (graphMorphism (partBase (prodBase sX sX') n) (partBase (prodBase sX sX') n) (𝟙 _)
          (Category.id_comp _)) m := by
  refine cycleAssociatedToClosedSubscheme_eq_sum_of_isOpenImmersion
    (ι := {p : ℕ × ℕ // p.1 + p.2 = n})
    (F := fun i ↦ (Limits.pullback (partBase sX i.1.1) (partBase sX' i.1.2) : Scheme.{u}))
    _ _ (partPairs D D' n) (fun i ↦ partProdHomOfEq k sX sX' i.2) ?_ ?_ m
  · intro w
    obtain ⟨d, d', t, hn, ht, hd, hd'⟩ :=
      exists_partProdMap_eq_of_mem k sX sX' ((dimPart (prodBase sX sX') n).ι w) w.2
    refine ⟨⟨(d, d'), hn⟩, ?_, t, ?_⟩
    · exact Finset.mem_subtype.2 (Finset.mem_product.2 ⟨hD _ ⟨_, hd⟩, hD' _ ⟨_, hd'⟩⟩)
    · apply (dimPart (prodBase sX sX') n).ι.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, partProdHomOfEq_ι, ht]
  · rintro ⟨⟨d₁, d₁'⟩, h₁⟩ - ⟨⟨d₂, d₂'⟩, h₂⟩ - hne
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨t₁, rfl⟩ ⟨t₂, ht₂⟩
    have hz : partProdMap sX sX' d₂ d₂' t₂ = partProdMap sX sX' d₁ d₁' t₁ := by
      rw [← partProdHomOfEq_ι k sX sX' h₂, ← partProdHomOfEq_ι k sX sX' h₁, Scheme.Hom.comp_apply,
        Scheme.Hom.comp_apply]
      exact congrArg _ ht₂
    have hfst : ∀ (e e' : ℕ) (t : (Limits.pullback (partBase sX e) (partBase sX' e') : Scheme.{u})),
        Limits.pullback.fst sX sX' (partProdMap sX sX' e e' t) ∈ dimPart sX e := by
      intro e e' t
      rw [← Scheme.Hom.comp_apply, partProdMap_fst, Scheme.Hom.comp_apply]
      exact (Limits.pullback.fst (partBase sX e) (partBase sX' e') t).2
    have hsnd : ∀ (e e' : ℕ) (t : (Limits.pullback (partBase sX e) (partBase sX' e') : Scheme.{u})),
        Limits.pullback.snd sX sX' (partProdMap sX sX' e e' t) ∈ dimPart sX' e' := by
      intro e e' t
      rw [← Scheme.Hom.comp_apply, partProdMap_snd, Scheme.Hom.comp_apply]
      exact (Limits.pullback.snd (partBase sX e) (partBase sX' e') t).2
    have he : d₂ = d₁ := (isClopenDecomposition_dimPart sX).eq_of_mem (hfst d₂ d₂' t₂)
      (hz ▸ hfst d₁ d₁' t₁)
    have he' : d₂' = d₁' := (isClopenDecomposition_dimPart sX').eq_of_mem (hsnd d₂ d₂' t₂)
      (hz ▸ hsnd d₁ d₁' t₁)
    subst he he'
    exact hne rfl

end Diagonal

/-! ### `[Δ_X] ⊗ [Δ_{X'}] = [Δ_{X × X'}]` -/

section Tensor

variable [IsProper sX] [IsProper sX']

/-- The map `X_d × X'_{d'} ⟶ (X × X')_{d+d'}` is a closed immersion. -/
instance (d d' : ℕ) : IsClosedImmersion (partProdHom k sX sX' d d') :=
  inferInstanceAs (IsClosedImmersion (partProdHomOfEq k sX sX' (rfl : d + d' = d + d')))

/-- The class of the diagonal of the piece `X_d × X'_{d'}`, read in the block `(d + d', d + d')`
of `Corr⁰(X × X', X × X')`. -/
def diagonalPieceBlock (d d' : ℕ) : Corr k (prodBase sX sX') (prodBase sX sX') (0 + 0) :=
  DirectSum.lof ℚ ℕ _ (d + d') (DirectSum.lof ℚ ℕ _ (d + d')
    ((1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
      (prodBase (partBase (prodBase sX sX') (d + d')) (partBase (prodBase sX sX') (d + d')))
      (partProdHom k sX sX' d d' ≫ graphMorphism (partBase (prodBase sX sX') (d + d'))
        (partBase (prodBase sX sX') (d + d')) (𝟙 _) (Category.id_comp _))
      (((d + d' : ℕ) : ℤ) - (0 + 0)))))

omit [IsProper sX] [IsProper sX'] in
/-- The diagonal of `P` lies over the base as `P`. -/
theorem graphMorphism_comp_prodBase {S P : Scheme.{u}} (sP : P ⟶ S) :
    graphMorphism sP sP (𝟙 P) (Category.id_comp _) ≫ prodBase sP sP = sP := by
  rw [prodBase, ← Category.assoc, graphMorphism_fst, Category.id_comp]

/-- The map `(X_d × X'_{d'}) × (X_e × X'_{e'}) ⟶ (X × X')_{d+d'} × (X × X')_{e+e'}` is a closed
immersion. -/
instance (d d' e e' : ℕ) : IsClosedImmersion (tensorBlockHom k sX sX' sX sX' d d' e e') := by
  have : IsOpenImmersion (tensorBlockHom k sX sX' sX sX' d d' e e') := by
    unfold tensorBlockHom; infer_instance
  exact IsClosedImmersion.of_isPreimmersion _
    (tensorBlockHom k sX sX' sX sX' d d' e e').isClosedMap.isClosed_range

omit [IsSeparated sX] [IsSeparated sX'] [IsProper sX] [IsProper sX'] in
/-- The product of the diagonals of `X_d` and `X'_{d'}`, embedded in the block of the fourfold
product, is the diagonal of the piece `X_d × X'_{d'}` of `(X × X')_{d+d'}`. -/
theorem tensorEmbedding_graphMorphism_tensorBlockHom (d d' : ℕ) :
    tensorEmbedding (partBase sX d) (partBase sX' d') (partBase sX d) (partBase sX' d')
        (graphMorphism (partBase sX d) (partBase sX d) (𝟙 _) (Category.id_comp _))
        (graphMorphism (partBase sX' d') (partBase sX' d') (𝟙 _) (Category.id_comp _))
        (graphMorphism_comp_prodBase _) (graphMorphism_comp_prodBase _) ≫
        tensorBlockHom k sX sX' sX sX' d d' d d' =
      partProdHom k sX sX' d d' ≫ graphMorphism (partBase (prodBase sX sX') (d + d'))
        (partBase (prodBase sX sX') (d + d')) (𝟙 _) (Category.id_comp _) := by
  have h : ∀ g : (Limits.pullback (prodBase (partBase sX d) (partBase sX' d'))
        (prodBase (partBase sX d) (partBase sX' d')) : Scheme.{u}) ⟶ _,
      (g = Limits.pullback.fst _ _ ∨ g = Limits.pullback.snd _ _) →
      tensorEmbedding (partBase sX d) (partBase sX' d') (partBase sX d) (partBase sX' d')
        (graphMorphism (partBase sX d) (partBase sX d) (𝟙 _) (Category.id_comp _))
        (graphMorphism (partBase sX' d') (partBase sX' d') (𝟙 _) (Category.id_comp _))
        (graphMorphism_comp_prodBase _) (graphMorphism_comp_prodBase _) ≫ g = 𝟙 _ := by
    rintro g (rfl | rfl) <;> apply Limits.pullback.hom_ext <;> simp [tensorEmbedding, tensorLift]
  apply Limits.pullback.hom_ext
  · rw [Category.assoc, Category.assoc, Limits.pullback.lift_fst, Limits.pullback.lift_fst,
      Category.comp_id, ← Category.assoc, h _ (Or.inl rfl), Category.id_comp]
  · rw [Category.assoc, Category.assoc, Limits.pullback.lift_snd, Limits.pullback.lift_snd,
      Category.comp_id, ← Category.assoc, h _ (Or.inr rfl), Category.id_comp]

/-- The tensor product of the diagonal blocks of `X_d` and `X'_{d'}` is the diagonal of the piece
`X_d × X'_{d'}`. -/
theorem tensor_diagonalBlock (d d' : ℕ) :
    tensor k sX sX' sX sX' (canonicalDiagonalClassFamily k) 0 0 (diagonalBlock k sX d)
        (diagonalBlock k sX' d') = diagonalPieceBlock k sX sX' d d' := by
  have hq : graphMorphism (partBase sX d) (partBase sX d) (𝟙 _) (Category.id_comp _) ≫
      prodBase (partBase sX d) (partBase sX d) = partBase sX d := graphMorphism_comp_prodBase _
  have hq' : graphMorphism (partBase sX' d') (partBase sX' d') (𝟙 _) (Category.id_comp _) ≫
      prodBase (partBase sX' d') (partBase sX' d') = partBase sX' d' :=
    graphMorphism_comp_prodBase _
  have := isClosedImmersion_tensorEmbedding (partBase sX d) (partBase sX' d') (partBase sX d)
    (partBase sX' d') _ _ hq hq'
  rw [diagonalBlock, diagonalBlock, tensor_lof_lof, graphCorrespondence, graphCorrespondence,
    tensorBlock_closedSubscheme k (partBase sX d) (partBase sX' d') (partBase sX d)
      (partBase sX' d') (relativeDimension_partBase sX d) (relativeDimension_partBase sX' d')
      (relativeDimension_partBase sX d) (relativeDimension_partBase sX' d') 0 0 _ _ hq hq'
      (relativeDimension_partBase sX d) (relativeDimension_partBase sX' d') (by simp) (by simp),
    one_mul, tensorBlockInclusion_tmul, diagonalPieceBlock]
  refine congrArg (DirectSum.lof ℚ ℕ _ (d + d')) (congrArg (DirectSum.lof ℚ ℕ _ (d + d'))
    (congrArg (TensorProduct.tmul ℤ (1 : ℚ)) ?_))
  rw [← QuotientAddGroup.mk'_apply, properChowPushforward_mk, QuotientAddGroup.mk'_apply,
    properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp]
  congr 2
  exact tensorEmbedding_graphMorphism_tensorBlockHom k sX sX' d d'

/-- The block `n` of `[Δ_{X × X'}]` is the sum of the diagonals of the pieces `X_d × X'_{d'}`,
`d + d' = n`. -/
theorem corrCongr_diagonalBlock_prodBase {D D' : Finset ℕ}
    (hD : ∀ d, (dimPart sX d : Set X).Nonempty → d ∈ D)
    (hD' : ∀ d, (dimPart sX' d : Set X').Nonempty → d ∈ D') (n : ℕ) :
    corrCongr k (prodBase sX sX') (prodBase sX sX') (add_zero 0).symm
        (diagonalBlock k (prodBase sX sX') n) =
      ∑ p ∈ (D ×ˢ D').filter (fun p ↦ p.1 + p.2 = n), diagonalPieceBlock k sX sX' p.1 p.2 := by
  rw [diagonalBlock, corrCongr_lof_lof, graphCorrespondence, correspondenceCongr_tmul,
    chowGroupDegreeEquiv_mk_cycleAssociatedToClosedSubscheme,
    ← sum_cycle_partProdHomOfEq_graphMorphism k sX sX' hD hD' n, ← Finset.sum_subtype_eq_sum_filter,
    QuotientAddGroup.mk_sum, TensorProduct.tmul_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl ?_
  rintro ⟨⟨d, d'⟩, h⟩ -
  subst h
  rw [diagonalPieceBlock]
  rfl

omit [IsSeparated sX] [IsSeparated sX'] [IsProper sX] [IsProper sX'] in
/-- A nonempty part `(X × X')_n` has `n = d + d'` for nonempty parts `X_d` and `X'_{d'}`. -/
theorem mem_image_of_nonempty_dimPart_prodBase {D D' : Finset ℕ}
    (hD : ∀ d, (dimPart sX d : Set X).Nonempty → d ∈ D)
    (hD' : ∀ d, (dimPart sX' d : Set X').Nonempty → d ∈ D') (n : ℕ)
    (hn : (dimPart (prodBase sX sX') n : Set (Limits.pullback sX sX' : Scheme.{u})).Nonempty) :
    n ∈ (D ×ˢ D').image fun p ↦ p.1 + p.2 := by
  obtain ⟨z, hz⟩ := hn
  obtain ⟨d, d', -, hn, -, hd, hd'⟩ := exists_partProdMap_eq_of_mem k sX sX' z hz
  exact Finset.mem_image.2 ⟨(d, d'), Finset.mem_product.2 ⟨hD _ ⟨_, hd⟩, hD' _ ⟨_, hd'⟩⟩, hn⟩

/-- `[Δ_X] ⊗ [Δ_{X'}]` is the sum of the diagonals of the pieces `X_d × X'_{d'}`. -/
theorem tensor_diagonalCorr_eq_sum {D D' : Finset ℕ}
    (hD : ∀ d, (dimPart sX d : Set X).Nonempty → d ∈ D)
    (hD' : ∀ d, (dimPart sX' d : Set X').Nonempty → d ∈ D') :
    tensor k sX sX' sX sX' (canonicalDiagonalClassFamily k) 0 0 (diagonalCorr k sX)
        (diagonalCorr k sX') = ∑ p ∈ D ×ˢ D', diagonalPieceBlock k sX sX' p.1 p.2 := by
  rw [diagonalCorr_eq_sum k sX hD, diagonalCorr_eq_sum k sX' hD', Finset.sum_product']
  simp only [map_sum, LinearMap.sum_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun d _ ↦ Finset.sum_congr rfl fun d' _ ↦
    tensor_diagonalBlock k sX sX' d d'

set_option synthInstance.maxHeartbeats 200000 in
-- instance search in the sums of correspondences over `prodBase sX sX'` is slow
/-- `[Δ_{X × X'}]` is the sum of the diagonals of the pieces `X_d × X'_{d'}`. -/
theorem corrCongr_diagonalCorr_prodBase_eq_sum {D D' : Finset ℕ}
    (hD : ∀ d, (dimPart sX d : Set X).Nonempty → d ∈ D)
    (hD' : ∀ d, (dimPart sX' d : Set X').Nonempty → d ∈ D') :
    corrCongr k (prodBase sX sX') (prodBase sX sX') (add_zero 0).symm
        (diagonalCorr k (prodBase sX sX')) =
      ∑ p ∈ D ×ˢ D', diagonalPieceBlock k sX sX' p.1 p.2 := by
  rw [diagonalCorr_eq_sum k (prodBase sX sX')
    (mem_image_of_nonempty_dimPart_prodBase k sX sX' hD hD'), map_sum,
    ← Finset.sum_fiberwise_of_maps_to (s := D ×ˢ D') (t := (D ×ˢ D').image fun p ↦ p.1 + p.2)
      (g := fun p ↦ p.1 + p.2) fun p hp ↦ Finset.mem_image_of_mem _ hp]
  exact Finset.sum_congr rfl fun n _ ↦ corrCongr_diagonalBlock_prodBase k sX sX' hD hD' n

/-- **`𝟙 ⊗ 𝟙 = 𝟙` for correspondences** (Stacks 0FG7): for smooth proper `X` and `X'` over `k`,
the tensor product of the diagonal classes is the diagonal class of the product,
`[Δ_X] ⊗ [Δ_{X'}] = [Δ_{X × X'}]` in `Corr⁰(X × X', X × X')`, up to the identification of degrees
`0 + 0 = 0`. -/
theorem tensor_diagonalCorr :
    tensor k sX sX' sX sX' (canonicalDiagonalClassFamily k) 0 0 (diagonalCorr k sX)
        (diagonalCorr k sX') =
      corrCongr k (prodBase sX sX') (prodBase sX sX') (add_zero 0).symm
        (diagonalCorr k (prodBase sX sX')) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace sX'
  have hD : ∀ d, (dimPart sX d : Set X).Nonempty →
      d ∈ (finite_setOf_nonempty_dimPart sX).toFinset :=
    fun d hd ↦ (finite_setOf_nonempty_dimPart sX).mem_toFinset.2 hd
  have hD' : ∀ d, (dimPart sX' d : Set X').Nonempty →
      d ∈ (finite_setOf_nonempty_dimPart sX').toFinset :=
    fun d hd ↦ (finite_setOf_nonempty_dimPart sX').mem_toFinset.2 hd
  exact (tensor_diagonalCorr_eq_sum k sX sX' hD hD').trans
    (corrCongr_diagonalCorr_prodBase_eq_sum k sX sX' hD hD').symm

end Tensor

end Stacks.WeilCohomology

end
