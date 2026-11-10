module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TensorDiagonal

/-!
# The tensor product of two graphs is the graph of the product

For morphisms `f : Y ⟶ X` and `g : Y' ⟶ X'` of smooth proper schemes over a field `k`, the
tensor product of correspondences (Stacks 0FG7) of the graph classes is the graph class of the
product:

  `[Γ_f] ⊗ [Γ_g] = [Γ_{f × g}]`  in  `Corr⁰(X × X', Y × Y')`.

This generalizes `Stacks.WeilCohomology.tensor_diagonalCorr`, the case of two identities, and the
proof follows it. On the parts of constant dimension, the `(d, e)` block of `[Γ_f]` is the class
of the closed subscheme `Γ_f ∩ (X_d × Y_e)`, whose source is the open subscheme `Y_e ∩ f⁻¹(X_d)` of
`Y_e`, and `[A] ⊗ [A'] = [A ×_k A']` (`Stacks.WeilCohomology.tensorBlock_closedSubscheme`). The
product of the pieces `Y_e ∩ f⁻¹(X_d)` and `Y'_{e'} ∩ g⁻¹(X'_{d'})` is an open piece of
`(Y × Y')_{e+e'} ∩ (f × g)⁻¹((X × X')_{d+d'})`, these pieces cover it and are disjoint, and on
each of them the graph of `f × g` is the product of the two graphs.

## Main results

* `Stacks.WeilCohomology.tensor_graphCorr`: `[Γ_f] ⊗ [Γ_g] = [Γ_{f × g}]`.

## References

* [Stacks Project, Tag 0FG7](https://stacks.math.columbia.edu/tag/0FG7)
* [Stacks Project, Tag 0FG1](https://stacks.math.columbia.edu/tag/0FG1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace Stacks.WeilCohomology

variable (k : Type u) [Field k] {X X' Y Y' : Scheme.{u}}
  (sX : X ⟶ (fieldChowSituation k).S) (sX' : X' ⟶ (fieldChowSituation k).S)
  (sY : Y ⟶ (fieldChowSituation k).S) (sY' : Y' ⟶ (fieldChowSituation k).S)
  [Smooth sX] [IsSeparated sX] [Smooth sX'] [IsSeparated sX']
  [Smooth sY] [IsSeparated sY] [Smooth sY'] [IsSeparated sY']
  (f : Y ⟶ X) (hf : f ≫ sX = sY) (g : Y' ⟶ X') (hg : g ≫ sX' = sY')


/-! ### Bookkeeping of finite sums -/

section Sums

variable {R M N P : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
  [AddCommMonoid P] [Module R M] [Module R N] [Module R P]

private lemma bilin_sum_sum (T : M →ₗ[R] N →ₗ[R] P) (D E D' E' : Finset ℕ) (x : ℕ → ℕ → M)
    (y : ℕ → ℕ → N) :
    T (∑ d ∈ D, ∑ e ∈ E, x d e) (∑ d ∈ D', ∑ e ∈ E', y d e) =
      ∑ q ∈ (D ×ˢ E) ×ˢ (D' ×ˢ E'), T (x q.1.1 q.1.2) (y q.2.1 q.2.2) := by
  have h₁ : T (∑ d ∈ D, ∑ e ∈ E, x d e) = ∑ p ∈ D ×ˢ E, T (x p.1 p.2) := by
    rw [← Finset.sum_product', map_sum]
  have h₂ : ∀ a, T a (∑ d ∈ D', ∑ e ∈ E', y d e) = ∑ q ∈ D' ×ˢ E', T a (y q.1 q.2) :=
    fun a ↦ by rw [← Finset.sum_product', map_sum]
  rw [h₁, LinearMap.sum_apply, Finset.sum_product (s := D ×ˢ E) (t := D' ×ˢ E')]
  exact Finset.sum_congr rfl fun p _ ↦ h₂ _

private lemma linearEquiv_sum_sum (L : M ≃ₗ[R] P) (N M' : Finset ℕ) (z : ℕ → ℕ → M) :
    L (∑ n ∈ N, ∑ m ∈ M', z n m) = ∑ n ∈ N, ∑ m ∈ M', L (z n m) := by
  simp only [map_sum]

private lemma sum_sum_filter_eq (S : Finset ((ℕ × ℕ) × (ℕ × ℕ))) (B : (ℕ × ℕ) × (ℕ × ℕ) → P)
    (N M' : Finset ℕ) (hN : ∀ q ∈ S, q.1.1 + q.2.1 ∈ N) (hM : ∀ q ∈ S, q.1.2 + q.2.2 ∈ M') :
    ∑ n ∈ N, ∑ m ∈ M', ∑ q ∈ S.filter (fun q ↦ q.1.1 + q.2.1 = n ∧ q.1.2 + q.2.2 = m), B q =
      ∑ q ∈ S, B q := by
  rw [← Finset.sum_product' (f := fun n m ↦
      ∑ q ∈ S.filter (fun q ↦ q.1.1 + q.2.1 = n ∧ q.1.2 + q.2.2 = m), B q)]
  rw [← Finset.sum_fiberwise_of_maps_to (s := S) (t := N ×ˢ M')
    (g := fun q ↦ (q.1.1 + q.2.1, q.1.2 + q.2.2))
    (fun q hq ↦ Finset.mem_product.2 ⟨hN q hq, hM q hq⟩) B]
  refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr ?_ fun _ _ ↦ rfl
  ext q
  simp [Prod.ext_iff]

end Sums

/-! ### The pieces of the graph -/

section Pieces

/-- The open subscheme `Y_e ∩ f⁻¹(X_d)` of `Y_e`, the source of the `(d, e)` block of `[Γ_f]`. -/
abbrev graphPieceOpens (d e : ℕ) : (dimPart sY e).toScheme.Opens :=
  ((dimPart sY e).ι ≫ f) ⁻¹ᵁ dimPart sX d

/-- The structure morphism of `Y_e ∩ f⁻¹(X_d)`. -/
abbrev graphPieceBase (d e : ℕ) :
    (graphPieceOpens k sX sY f d e).toScheme ⟶ (fieldChowSituation k).S :=
  (graphPieceOpens k sX sY f d e).ι ≫ partBase sY e

omit [IsSeparated sX] [IsSeparated sY] in
/-- The graph piece `Y_e ∩ f⁻¹(X_d) ⟶ X_d ×_k Y_e` followed by the structure morphism of
`X_d ×_k Y_e` is the structure morphism of `Y_e ∩ f⁻¹(X_d)`. -/
theorem graphPiece_comp_prodBase (d e : ℕ) :
    graphPiece k sX sY f hf d e ≫ prodBase (partBase sX d) (partBase sY e) =
      graphPieceBase k sX sY f d e :=
  graphPiece_prodBase k sX sY f hf d e

/-- The piece `Y_e ∩ f⁻¹(X_d)` is smooth over `k`. -/
instance (d e : ℕ) : Smooth (graphPieceBase k sX sY f d e) := by
  unfold graphPieceBase
  infer_instance

omit [IsSeparated sX] [IsSeparated sY] in
/-- The piece `Y_e ∩ f⁻¹(X_d)` has relative dimension `e` over `k`. -/
theorem relativeDimension_graphPieceBase (d e : ℕ) :
    RelativeDimension (graphPieceBase k sX sY f d e) e :=
  RelativeDimension.comp_isOpenImmersion _ _ (relativeDimension_partBase sY e)

/-- The inclusion of `Y_e ∩ f⁻¹(X_d)` into `Y`. -/
abbrev tensorGraphPieceι (d e : ℕ) : (graphPieceOpens k sX sY f d e).toScheme ⟶ Y :=
  (graphPieceOpens k sX sY f d e).ι ≫ (dimPart sY e).ι

omit [IsSeparated sX] [IsSeparated sY] in
/-- The inclusion of `Y_e ∩ f⁻¹(X_d)` into `Y` commutes with the structure morphisms. -/
theorem tensorGraphPieceι_comp (d e : ℕ) :
    tensorGraphPieceι k sX sY f d e ≫ sY = graphPieceBase k sX sY f d e := by
  simp [tensorGraphPieceι, graphPieceBase, partBase]

/-- The product of two pieces `(Y_e ∩ f⁻¹X_d) ×_k (Y'_{e'} ∩ g⁻¹X'_{d'}) ⟶ Y ×_k Y'`, an open
immersion. -/
abbrev graphPieceProdMap (d e d' e' : ℕ) :
    (Limits.pullback (graphPieceBase k sX sY f d e) (graphPieceBase k sX' sY' g d' e') :
      Scheme.{u}) ⟶ Limits.pullback sY sY' :=
  Limits.pullback.map _ _ sY sY' (tensorGraphPieceι k sX sY f d e)
    (tensorGraphPieceι k sX' sY' g d' e') (𝟙 _)
    ((tensorGraphPieceι_comp k sX sY f d e).trans (Category.comp_id _).symm)
    ((tensorGraphPieceι_comp k sX' sY' g d' e').trans (Category.comp_id _).symm)

/-- The product of two pieces is an open immersion into `Y ×_k Y'`. -/
instance (d e d' e' : ℕ) : IsOpenImmersion (graphPieceProdMap k sX sX' sY sY' f g d e d' e') :=
  MorphismProperty.pullbackMap (P := @IsOpenImmersion) inferInstance inferInstance
    (tensorGraphPieceι_comp k sX sY f d e).symm (tensorGraphPieceι_comp k sX' sY' g d' e').symm

end Pieces

/-! ### The pieces of the graph of the product -/

section ProductPieces

/-- The product morphism `f × g : Y ×_k Y' ⟶ X ×_k X'`. -/
abbrev graphProdHom : Limits.pullback sY sY' ⟶ Limits.pullback sX sX' :=
  prodHom sX sX' sY sY' f g hf hg

omit [Smooth sX] [IsSeparated sX] [Smooth sX'] [IsSeparated sX'] [Smooth sY] [IsSeparated sY]
    [Smooth sY'] [IsSeparated sY'] in
/-- The product morphism `f × g` commutes with the structure morphisms of `X ×_k X'` and
`Y ×_k Y'`. -/
theorem graphProdHom_comp_prodBase :
    graphProdHom k sX sX' sY sY' f hf g hg ≫ prodBase sX sX' = prodBase sY sY' :=
  prodHom_comp_prodBase _ _ _ _ _ _ _ _

omit [IsSeparated sX] [IsSeparated sY] in
/-- A point of `Y_e ∩ f⁻¹(X_d)` maps into `X_d`. -/
theorem tensorGraphPieceι_mem (d e : ℕ) (w : (graphPieceOpens k sX sY f d e).toScheme) :
    f (tensorGraphPieceι k sX sY f d e w) ∈ dimPart sX d := by
  have hw : ((dimPart sY e).ι ≫ f) ((graphPieceOpens k sX sY f d e).ι w) ∈ dimPart sX d := w.2
  rwa [Scheme.Hom.comp_apply] at hw

omit [IsSeparated sX] [IsSeparated sY] in
/-- A point of `Y_e ∩ f⁻¹(X_d)` maps into `Y_e`. -/
theorem tensorGraphPieceι_mem_dimPart (d e : ℕ) (w : (graphPieceOpens k sX sY f d e).toScheme) :
    tensorGraphPieceι k sX sY f d e w ∈ dimPart sY e := by
  rw [tensorGraphPieceι, Scheme.Hom.comp_apply]
  exact ((graphPieceOpens k sX sY f d e).ι w).2

omit [IsSeparated sX] [IsSeparated sX'] [IsSeparated sY] [IsSeparated sY'] in
/-- The product of two pieces, followed by the structure morphism of `Y ×_k Y'`, is the structure
morphism of the product of the pieces. -/
theorem graphPieceProdMap_comp_prodBase (d e d' e' : ℕ) :
    graphPieceProdMap k sX sX' sY sY' f g d e d' e' ≫ prodBase sY sY' =
      prodBase (graphPieceBase k sX sY f d e) (graphPieceBase k sX' sY' g d' e') := by
  rw [prodBase, Limits.pullback.lift_fst_assoc, prodBase, Category.assoc,
    tensorGraphPieceι_comp]

omit [IsSeparated sX] [IsSeparated sX'] [IsSeparated sY] [IsSeparated sY'] in
/-- The product of two pieces lies in the part `(Y × Y')_{e+e'}`. -/
theorem graphPieceProdMap_mem_dimPart (d e d' e' : ℕ)
    (t : (Limits.pullback (graphPieceBase k sX sY f d e) (graphPieceBase k sX' sY' g d' e') :
      Scheme.{u})) :
    graphPieceProdMap k sX sX' sY sY' f g d e d' e' t ∈ dimPart (prodBase sY sY') (e + e') := by
  refine range_subset_dimPart (prodBase sY sY') _ ?_ (Set.mem_range_self t)
  rw [Nat.add_comm]
  exact relativeDimension_of_eq (graphPieceProdMap_comp_prodBase k sX sX' sY sY' f g d e d' e').symm
    (relativeDimension_prodBase k _ _ (relativeDimension_graphPieceBase k sX sY f d e)
      (relativeDimension_graphPieceBase k sX' sY' g d' e'))

omit [IsSeparated sX] [IsSeparated sX'] [IsSeparated sY] [IsSeparated sY'] in
/-- Under `f × g` the product of two pieces maps into the part `(X × X')_{d+d'}`. -/
theorem graphProdHom_graphPieceProdMap_mem_dimPart (d e d' e' : ℕ)
    (t : (Limits.pullback (graphPieceBase k sX sY f d e) (graphPieceBase k sX' sY' g d' e') :
      Scheme.{u})) :
    graphProdHom k sX sX' sY sY' f hf g hg (graphPieceProdMap k sX sX' sY sY' f g d e d' e' t) ∈
      dimPart (prodBase sX sX') (d + d') := by
  refine range_partProdMap_subset k sX sX' d d' (mem_range_partProdMap k sX sX' _ ?_ ?_)
  · rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
      Limits.pullback.lift_fst, Limits.pullback.lift_fst_assoc, Scheme.Hom.comp_apply,
      Scheme.Hom.comp_apply]
    exact tensorGraphPieceι_mem k sX sY f d e _
  · rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
      Limits.pullback.lift_snd, Limits.pullback.lift_snd_assoc, Scheme.Hom.comp_apply,
      Scheme.Hom.comp_apply]
    exact tensorGraphPieceι_mem k sX' sY' g d' e' _

omit [IsSeparated sX] [IsSeparated sX'] [IsSeparated sY] [IsSeparated sY'] in
/-- The first projection of the image of a point of the product of two pieces is the image of its
first coordinate in `Y`. -/
theorem fst_graphPieceProdMap (d e d' e' : ℕ)
    (t : (Limits.pullback (graphPieceBase k sX sY f d e) (graphPieceBase k sX' sY' g d' e') :
      Scheme.{u})) :
    Limits.pullback.fst sY sY' (graphPieceProdMap k sX sX' sY sY' f g d e d' e' t) =
      tensorGraphPieceι k sX sY f d e
        (Limits.pullback.fst (graphPieceBase k sX sY f d e)
          (graphPieceBase k sX' sY' g d' e') t) := by
  rw [← Scheme.Hom.comp_apply, Limits.pullback.lift_fst, Scheme.Hom.comp_apply]

omit [IsSeparated sX] [IsSeparated sX'] [IsSeparated sY] [IsSeparated sY'] in
/-- The second projection of the image of a point of the product of two pieces is the image of its
second coordinate in `Y'`. -/
theorem snd_graphPieceProdMap (d e d' e' : ℕ)
    (t : (Limits.pullback (graphPieceBase k sX sY f d e) (graphPieceBase k sX' sY' g d' e') :
      Scheme.{u})) :
    Limits.pullback.snd sY sY' (graphPieceProdMap k sX sX' sY sY' f g d e d' e' t) =
      tensorGraphPieceι k sX' sY' g d' e'
        (Limits.pullback.snd (graphPieceBase k sX sY f d e)
          (graphPieceBase k sX' sY' g d' e') t) := by
  rw [← Scheme.Hom.comp_apply, Limits.pullback.lift_snd, Scheme.Hom.comp_apply]

omit [IsSeparated sX] [IsSeparated sY] in
/-- A point of `Y` in `Y_e` mapping into `X_d` lies in the piece `Y_e ∩ f⁻¹(X_d)`. -/
theorem mem_range_graphPieceι (d e : ℕ) {y : Y} (he : y ∈ dimPart sY e)
    (hd : f y ∈ dimPart sX d) : y ∈ Set.range (tensorGraphPieceι k sX sY f d e) :=
  ⟨⟨⟨y, he⟩, hd⟩, rfl⟩

omit [Smooth sX] [IsSeparated sX] [Smooth sX'] [IsSeparated sX'] [Smooth sY] [IsSeparated sY]
    [Smooth sY'] [IsSeparated sY'] in
/-- The first projection of `(f × g)(z)` is `f` applied to the first projection of `z`. -/
theorem fst_graphProdHom (z : (Limits.pullback sY sY' : Scheme.{u})) :
    Limits.pullback.fst sX sX' (graphProdHom k sX sX' sY sY' f hf g hg z) =
      f (Limits.pullback.fst sY sY' z) := by
  rw [← Scheme.Hom.comp_apply, Limits.pullback.lift_fst, Scheme.Hom.comp_apply]

omit [Smooth sX] [IsSeparated sX] [Smooth sX'] [IsSeparated sX'] [Smooth sY] [IsSeparated sY]
    [Smooth sY'] [IsSeparated sY'] in
/-- The second projection of `(f × g)(z)` is `g` applied to the second projection of `z`. -/
theorem snd_graphProdHom (z : (Limits.pullback sY sY' : Scheme.{u})) :
    Limits.pullback.snd sX sX' (graphProdHom k sX sX' sY sY' f hf g hg z) =
      g (Limits.pullback.snd sY sY' z) := by
  rw [← Scheme.Hom.comp_apply, Limits.pullback.lift_snd, Scheme.Hom.comp_apply]

/-- If `(f × g)(z)` lies in `(X × X')_n`, then `n = d + d'` for the parts `X_d` and `X'_{d'}`
containing `f` of the first and `g` of the second coordinate of `z`. -/
private lemma exists_add_eq_of_graphProdHom_mem (k : Type u) [Field k] {X X' Y Y' : Scheme.{u}}
    (sX : X ⟶ (fieldChowSituation k).S) (sX' : X' ⟶ (fieldChowSituation k).S)
    (sY : Y ⟶ (fieldChowSituation k).S) (sY' : Y' ⟶ (fieldChowSituation k).S)
    [Smooth sX] [Smooth sX'] (f : Y ⟶ X) (hf : f ≫ sX = sY) (g : Y' ⟶ X') (hg : g ≫ sX' = sY')
    (z : (Limits.pullback sY sY' : Scheme.{u})) (n : ℕ)
    (hz : graphProdHom k sX sX' sY sY' f hf g hg z ∈ dimPart (prodBase sX sX') n) :
    ∃ d d' : ℕ, f (Limits.pullback.fst sY sY' z) ∈ dimPart sX d ∧
      g (Limits.pullback.snd sY sY' z) ∈ dimPart sX' d' ∧ d + d' = n := by
  obtain ⟨d, hd⟩ :=
    (isClopenDecomposition_dimPart sX).exists_mem (f (Limits.pullback.fst sY sY' z))
  obtain ⟨d', hd'⟩ :=
    (isClopenDecomposition_dimPart sX').exists_mem (g (Limits.pullback.snd sY sY' z))
  exact ⟨d, d', hd, hd', (isClopenDecomposition_dimPart (prodBase sX sX')).eq_of_mem
    (range_partProdMap_subset k sX sX' d d' (mem_range_partProdMap k sX sX' _
      ((fst_graphProdHom k sX sX' sY sY' f hf g hg z).symm ▸ hd)
      ((snd_graphProdHom k sX sX' sY sY' f hf g hg z).symm ▸ hd'))) hz⟩

/-- The product of the pieces `Y_e ∩ f⁻¹(X_d)` and `Y'_{e'} ∩ g⁻¹(X'_{d'})` as an open piece of
`(Y × Y')_m ∩ (f × g)⁻¹((X × X')_n)`, for `d + d' = n` and `e + e' = m`. -/
def graphPieceProdHom (d e d' e' : ℕ) {n m : ℕ} (hn : d + d' = n) (hm : e + e' = m) :
    (Limits.pullback (graphPieceBase k sX sY f d e) (graphPieceBase k sX' sY' g d' e') :
      Scheme.{u}) ⟶
      (graphPieceOpens k (prodBase sX sX') (prodBase sY sY')
        (graphProdHom k sX sX' sY sY' f hf g hg) n m).toScheme :=
  IsOpenImmersion.lift (tensorGraphPieceι k (prodBase sX sX') (prodBase sY sY')
      (graphProdHom k sX sX' sY sY' f hf g hg) n m)
    (graphPieceProdMap k sX sX' sY sY' f g d e d' e') (by
      rintro _ ⟨t, rfl⟩
      have hz := graphPieceProdMap_mem_dimPart k sX sX' sY sY' f g d e d' e' t
      have hw := graphProdHom_graphPieceProdMap_mem_dimPart k sX sX' sY sY' f hf g hg d e d' e' t
      subst hn hm
      exact ⟨⟨⟨_, hz⟩, hw⟩, rfl⟩)

omit [IsSeparated sX] [IsSeparated sX'] [IsSeparated sY] [IsSeparated sY'] in
/-- `graphPieceProdHom` followed by the inclusion into `Y ×_k Y'` is the product of the two
pieces. -/
@[reassoc (attr := simp)]
theorem graphPieceProdHom_ι (d e d' e' : ℕ) {n m : ℕ} (hn : d + d' = n) (hm : e + e' = m) :
    graphPieceProdHom k sX sX' sY sY' f hf g hg d e d' e' hn hm ≫
        tensorGraphPieceι k (prodBase sX sX') (prodBase sY sY')
          (graphProdHom k sX sX' sY sY' f hf g hg) n m =
      graphPieceProdMap k sX sX' sY sY' f g d e d' e' :=
  IsOpenImmersion.lift_fac _ _ _

omit [IsSeparated sX] [IsSeparated sX'] [IsSeparated sY] [IsSeparated sY'] in
/-- `graphPieceProdHom` followed by the two inclusions into `(Y × Y')_m` and `Y ×_k Y'` is the
product of the two pieces. -/
@[reassoc (attr := simp)]
theorem graphPieceProdHom_ι_ι (d e d' e' : ℕ) {n m : ℕ} (hn : d + d' = n) (hm : e + e' = m) :
    graphPieceProdHom k sX sX' sY sY' f hf g hg d e d' e' hn hm ≫
        (graphPieceOpens k (prodBase sX sX') (prodBase sY sY')
          (graphProdHom k sX sX' sY sY' f hf g hg) n m).ι ≫ (dimPart (prodBase sY sY') m).ι =
      graphPieceProdMap k sX sX' sY sY' f g d e d' e' :=
  graphPieceProdHom_ι k sX sX' sY sY' f hf g hg d e d' e' hn hm

/-- `graphPieceProdHom` is an open immersion. -/
instance (d e d' e' : ℕ) {n m : ℕ} (hn : d + d' = n) (hm : e + e' = m) :
    IsOpenImmersion (graphPieceProdHom k sX sX' sY sY' f hf g hg d e d' e' hn hm) := by
  have : IsOpenImmersion (graphPieceProdHom k sX sX' sY sY' f hf g hg d e d' e' hn hm ≫
      tensorGraphPieceι k (prodBase sX sX') (prodBase sY sY')
        (graphProdHom k sX sX' sY sY' f hf g hg) n m) := by
    rw [graphPieceProdHom_ι]
    infer_instance
  exact IsOpenImmersion.of_comp _ (tensorGraphPieceι k (prodBase sX sX') (prodBase sY sY')
    (graphProdHom k sX sX' sY sY' f hf g hg) n m)

variable [IsProper sX] [IsProper sX'] [IsProper sY] [IsProper sY']

omit [IsSeparated sX] [IsSeparated sX'] [IsSeparated sY] [IsSeparated sY']
  [IsProper sX] [IsProper sX'] [IsProper sY] [IsProper sY'] in
/-- **On a product of pieces, the graph of `f × g` is the product of the graphs**: the closed
subscheme `(Γ_f ∩ (X_d × Y_e)) ×_k (Γ_g ∩ (X'_{d'} × Y'_{e'}))` of the fourfold product, read in
the block `(X × X')_{d+d'} × (Y × Y')_{e+e'}`, is the restriction of `Γ_{f×g}` to the open piece
of its source given by the product of the two pieces. -/
theorem graphPieceProdHom_graphPiece (d e d' e' : ℕ) :
    graphPieceProdHom k sX sX' sY sY' f hf g hg d e d' e' rfl rfl ≫
        graphPiece k (prodBase sX sX') (prodBase sY sY') (graphProdHom k sX sX' sY sY' f hf g hg)
          (graphProdHom_comp_prodBase k sX sX' sY sY' f hf g hg) (d + d') (e + e') =
      tensorEmbedding (partBase sX d) (partBase sX' d') (partBase sY e) (partBase sY' e')
          (graphPiece k sX sY f hf d e) (graphPiece k sX' sY' g hg d' e')
          (graphPiece_comp_prodBase k sX sY f hf d e)
          (graphPiece_comp_prodBase k sX' sY' g hg d' e') ≫
        tensorBlockHom k sX sX' sY sY' d d' e e' := by
  apply Limits.pullback.hom_ext
  · rw [← cancel_mono (dimPart (prodBase sX sX') (d + d')).ι]
    apply Limits.pullback.hom_ext <;>
      simp only [Category.assoc, graphPiece_fst_assoc, morphismRestrict_ι,
        graphPieceProdHom_ι_ι_assoc, Limits.pullback.lift_fst, Limits.pullback.lift_fst_assoc,
        Limits.pullback.lift_snd, Limits.pullback.lift_snd_assoc, partProdHom_ι_assoc,
        tensorEmbedding_fst_fst_assoc, tensorEmbedding_fst_snd_assoc]
  · rw [← cancel_mono (dimPart (prodBase sY sY') (e + e')).ι]
    apply Limits.pullback.hom_ext <;>
      simp only [Category.assoc, graphPiece_snd_assoc, graphPieceProdHom_ι_ι,
        Limits.pullback.lift_fst, Limits.pullback.lift_snd, partProdHom_ι_assoc,
        tensorEmbedding_snd_fst_assoc, tensorEmbedding_snd_snd_assoc]

/-- `tensorBlockHom` is a closed immersion. -/
instance (d d' e e' : ℕ) : IsClosedImmersion (tensorBlockHom k sX sX' sY sY' d d' e e') := by
  have : IsOpenImmersion (tensorBlockHom k sX sX' sY sY' d d' e e') := by
    unfold tensorBlockHom
    infer_instance
  exact IsClosedImmersion.of_isPreimmersion _
    (tensorBlockHom k sX sX' sY sY' d d' e e').isClosedMap.isClosed_range

/-- The restriction of the graph of `f × g` to the product of two pieces is a closed immersion. -/
instance (d e d' e' : ℕ) {n m : ℕ} (hn : d + d' = n) (hm : e + e' = m) :
    IsClosedImmersion (graphPieceProdHom k sX sX' sY sY' f hf g hg d e d' e' hn hm ≫
      graphPiece k (prodBase sX sX') (prodBase sY sY') (graphProdHom k sX sX' sY sY' f hf g hg)
        (graphProdHom_comp_prodBase k sX sX' sY sY' f hf g hg) n m) := by
  subst hn hm
  have := isClosedImmersion_tensorEmbedding (partBase sX d) (partBase sX' d') (partBase sY e)
    (partBase sY' e') (graphPiece k sX sY f hf d e) (graphPiece k sX' sY' g hg d' e')
    (graphPiece_comp_prodBase k sX sY f hf d e) (graphPiece_comp_prodBase k sX' sY' g hg d' e')
  rw [graphPieceProdHom_graphPiece]
  infer_instance

/-- The quadruples `((d, e), (d', e'))` with `d + d' = n`, `e + e' = m` and `d ∈ D`, `e ∈ E`,
`d' ∈ D'`, `e' ∈ E'`. -/
abbrev graphPieceQuads (D E D' E' : Finset ℕ) (n m : ℕ) :
    Finset {q : (ℕ × ℕ) × (ℕ × ℕ) // q.1.1 + q.2.1 = n ∧ q.1.2 + q.2.2 = m} :=
  ((D ×ˢ E) ×ˢ (D' ×ˢ E')).subtype fun q ↦ q.1.1 + q.2.1 = n ∧ q.1.2 + q.2.2 = m

/-- **The graph of `f × g` over the parts `(X × X')_n` and `(Y × Y')_m` is the sum of the products
of the pieces of the graphs of `f` and `g`.** -/
theorem sum_cycle_graphPieceProdHom {D E D' E' : Finset ℕ}
    (hD : ∀ d, (f ⁻¹ᵁ dimPart sX d : Set Y).Nonempty → d ∈ D)
    (hE : ∀ e, (dimPart sY e : Set Y).Nonempty → e ∈ E)
    (hD' : ∀ d, (g ⁻¹ᵁ dimPart sX' d : Set Y').Nonempty → d ∈ D')
    (hE' : ∀ e, (dimPart sY' e : Set Y').Nonempty → e ∈ E') (n m : ℕ) (j : ℤ) :
    ∑ i ∈ graphPieceQuads D E D' E' n m,
        cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase (partBase (prodBase sX sX') n) (partBase (prodBase sY sY') m))
          (graphPieceProdHom k sX sX' sY sY' f hf g hg i.1.1.1 i.1.1.2 i.1.2.1 i.1.2.2 i.2.1 i.2.2 ≫
            graphPiece k (prodBase sX sX') (prodBase sY sY')
              (graphProdHom k sX sX' sY sY' f hf g hg)
              (graphProdHom_comp_prodBase k sX sX' sY sY' f hf g hg) n m) j =
      cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (prodBase (partBase (prodBase sX sX') n) (partBase (prodBase sY sY') m))
        (graphPiece k (prodBase sX sX') (prodBase sY sY') (graphProdHom k sX sX' sY sY' f hf g hg)
          (graphProdHom_comp_prodBase k sX sX' sY sY' f hf g hg) n m) j := by
  refine cycleAssociatedToClosedSubscheme_eq_sum_of_isOpenImmersion
    (ι := {q : (ℕ × ℕ) × (ℕ × ℕ) // q.1.1 + q.2.1 = n ∧ q.1.2 + q.2.2 = m})
    (F := fun i ↦ (Limits.pullback (graphPieceBase k sX sY f i.1.1.1 i.1.1.2)
      (graphPieceBase k sX' sY' g i.1.2.1 i.1.2.2) : Scheme.{u}))
    _ _ (graphPieceQuads D E D' E' n m)
    (fun i ↦ graphPieceProdHom k sX sX' sY sY' f hf g hg _ _ _ _ i.2.1 i.2.2) ?_ ?_ j
  · intro w
    set z := tensorGraphPieceι k (prodBase sX sX') (prodBase sY sY')
      (graphProdHom k sX sX' sY sY' f hf g hg) n m w
    have hzm := tensorGraphPieceι_mem_dimPart k (prodBase sX sX') (prodBase sY sY')
      (graphProdHom k sX sX' sY sY' f hf g hg) n m w
    have hzn := tensorGraphPieceι_mem k (prodBase sX sX') (prodBase sY sY')
      (graphProdHom k sX sX' sY sY' f hf g hg) n m w
    obtain ⟨e, he⟩ := (isClopenDecomposition_dimPart sY).exists_mem (Limits.pullback.fst sY sY' z)
    obtain ⟨e', he'⟩ :=
      (isClopenDecomposition_dimPart sY').exists_mem (Limits.pullback.snd sY sY' z)
    obtain ⟨d, d', hd, hd', hn⟩ :=
      exists_add_eq_of_graphProdHom_mem k sX sX' sY sY' f hf g hg z n hzn
    have hm : e + e' = m := (isClopenDecomposition_dimPart (prodBase sY sY')).eq_of_mem
      (range_partProdMap_subset k sY sY' e e' (mem_range_partProdMap k sY sY' z he he')) hzm
    obtain ⟨t, ht⟩ : z ∈ Set.range (graphPieceProdMap k sX sX' sY sY' f g d e d' e') := by
      rw [Scheme.Pullback.range_map (f' := sY) (g' := sY') (i₁ := tensorGraphPieceι k sX sY f d e)
        (i₂ := tensorGraphPieceι k sX' sY' g d' e') (i₃ := 𝟙 _)
        (e₁ := (Category.comp_id _).trans (tensorGraphPieceι_comp k sX sY f d e).symm)
        (e₂ := (Category.comp_id _).trans (tensorGraphPieceι_comp k sX' sY' g d' e').symm)]
      exact ⟨mem_range_graphPieceι k sX sY f d e he hd,
        mem_range_graphPieceι k sX' sY' g d' e' he' hd'⟩
    refine ⟨⟨((d, e), (d', e')), hn, hm⟩, ?_, t, ?_⟩
    · exact Finset.mem_subtype.2 (Finset.mem_product.2 ⟨Finset.mem_product.2
        ⟨hD d ⟨_, hd⟩, hE e ⟨_, he⟩⟩, Finset.mem_product.2 ⟨hD' d' ⟨_, hd'⟩, hE' e' ⟨_, he'⟩⟩⟩)
    · apply (tensorGraphPieceι k (prodBase sX sX') (prodBase sY sY')
        (graphProdHom k sX sX' sY sY' f hf g hg) n m).isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, graphPieceProdHom_ι, ht]
  · rintro ⟨⟨⟨d₁, e₁⟩, ⟨d₁', e₁'⟩⟩, h₁⟩ - ⟨⟨⟨d₂, e₂⟩, ⟨d₂', e₂'⟩⟩, h₂⟩ - hne
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨t₁, rfl⟩ ⟨t₂, ht₂⟩
    have hz := congrArg (tensorGraphPieceι k (prodBase sX sX') (prodBase sY sY')
      (graphProdHom k sX sX' sY sY' f hf g hg) n m) ht₂
    simp only [← Scheme.Hom.comp_apply, graphPieceProdHom_ι] at hz
    have hfst := congrArg (Limits.pullback.fst sY sY') hz
    have hsnd := congrArg (Limits.pullback.snd sY sY') hz
    rw [fst_graphPieceProdMap, fst_graphPieceProdMap] at hfst
    rw [snd_graphPieceProdMap, snd_graphPieceProdMap] at hsnd
    have he : e₂ = e₁ := (isClopenDecomposition_dimPart sY).eq_of_mem
      (tensorGraphPieceι_mem_dimPart k sX sY f d₂ e₂ _)
      (hfst ▸ tensorGraphPieceι_mem_dimPart k sX sY f d₁ e₁ _)
    have he' : e₂' = e₁' := (isClopenDecomposition_dimPart sY').eq_of_mem
      (tensorGraphPieceι_mem_dimPart k sX' sY' g d₂' e₂' _)
      (hsnd ▸ tensorGraphPieceι_mem_dimPart k sX' sY' g d₁' e₁' _)
    have hd : d₂ = d₁ := (isClopenDecomposition_dimPart sX).eq_of_mem
      (tensorGraphPieceι_mem k sX sY f d₂ e₂ _) (hfst ▸ tensorGraphPieceι_mem k sX sY f d₁ e₁ _)
    have hd' : d₂' = d₁' := (isClopenDecomposition_dimPart sX').eq_of_mem
      (tensorGraphPieceι_mem k sX' sY' g d₂' e₂' _)
      (hsnd ▸ tensorGraphPieceι_mem k sX' sY' g d₁' e₁' _)
    subst he he' hd hd'
    exact hne rfl

/-- The product of the `(d, e)` piece of `Γ_f` and the `(d', e')` piece of `Γ_g`, as a class in
the block `(d + d', e + e')` of `Corr⁰(X × X', Y × Y')`. -/
def graphProdPieceBlock (d e d' e' : ℕ) : Corr k (prodBase sX sX') (prodBase sY sY') (0 + 0) :=
  DirectSum.lof ℚ ℕ _ (d + d') (DirectSum.lof ℚ ℕ _ (e + e')
    ((1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
      (prodBase (partBase (prodBase sX sX') (d + d')) (partBase (prodBase sY sY') (e + e')))
      (graphPieceProdHom k sX sX' sY sY' f hf g hg d e d' e' rfl rfl ≫
        graphPiece k (prodBase sX sX') (prodBase sY sY') (graphProdHom k sX sX' sY sY' f hf g hg)
          (graphProdHom_comp_prodBase k sX sX' sY sY' f hf g hg) (d + d') (e + e'))
      (((e + e' : ℕ) : ℤ) - (0 + 0)))))

/-- The tensor product of the `(d, e)` block of `[Γ_f]` and the `(d', e')` block of `[Γ_g]`. -/
theorem tensor_graphBlock (d e d' e' : ℕ) :
    tensor k sX sX' sY sY' (canonicalDiagonalClassFamily k) 0 0
        (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e (graphBlock k sX sY f hf d e)))
        (DirectSum.lof ℚ ℕ _ d' (DirectSum.lof ℚ ℕ _ e' (graphBlock k sX' sY' g hg d' e'))) =
      graphProdPieceBlock k sX sX' sY sY' f hf g hg d e d' e' := by
  have := isClosedImmersion_tensorEmbedding (partBase sX d) (partBase sX' d') (partBase sY e)
    (partBase sY' e') (graphPiece k sX sY f hf d e) (graphPiece k sX' sY' g hg d' e')
    (graphPiece_comp_prodBase k sX sY f hf d e) (graphPiece_comp_prodBase k sX' sY' g hg d' e')
  rw [tensor_lof_lof, graphBlock, graphBlock,
    tensorBlock_closedSubscheme k (partBase sX d) (partBase sX' d') (partBase sY e)
      (partBase sY' e') (relativeDimension_partBase sX d) (relativeDimension_partBase sX' d')
      (relativeDimension_partBase sY e) (relativeDimension_partBase sY' e') 0 0 _ _
      (graphPiece_comp_prodBase k sX sY f hf d e) (graphPiece_comp_prodBase k sX' sY' g hg d' e')
      (relativeDimension_graphPieceBase k sX sY f d e)
      (relativeDimension_graphPieceBase k sX' sY' g d' e') (by simp) (by simp),
    one_mul, tensorBlockInclusion_tmul, graphProdPieceBlock]
  refine congrArg (DirectSum.lof ℚ ℕ _ (d + d')) (congrArg (DirectSum.lof ℚ ℕ _ (e + e'))
    (congrArg (TensorProduct.tmul ℤ (1 : ℚ)) ?_))
  rw [← QuotientAddGroup.mk'_apply, properChowPushforward_mk, QuotientAddGroup.mk'_apply,
    properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp]
  congr 2
  exact (graphPieceProdHom_graphPiece k sX sX' sY sY' f hf g hg d e d' e').symm

/-- The block `(n, m)` of `[Γ_{f × g}]` is the sum of the products of the pieces of `Γ_f` and
`Γ_g` over the quadruples `((d, e), (d', e'))` with `d + d' = n` and `e + e' = m`. -/
theorem corrCongr_graphBlock_graphProdHom {D E D' E' : Finset ℕ}
    (hD : ∀ d, (f ⁻¹ᵁ dimPart sX d : Set Y).Nonempty → d ∈ D)
    (hE : ∀ e, (dimPart sY e : Set Y).Nonempty → e ∈ E)
    (hD' : ∀ d, (g ⁻¹ᵁ dimPart sX' d : Set Y').Nonempty → d ∈ D')
    (hE' : ∀ e, (dimPart sY' e : Set Y').Nonempty → e ∈ E') (n m : ℕ) :
    corrCongr k (prodBase sX sX') (prodBase sY sY') (add_zero 0).symm
        (DirectSum.lof ℚ ℕ _ n (DirectSum.lof ℚ ℕ _ m
          (graphBlock k (prodBase sX sX') (prodBase sY sY') (graphProdHom k sX sX' sY sY' f hf g hg)
            (graphProdHom_comp_prodBase k sX sX' sY sY' f hf g hg) n m))) =
      ∑ q ∈ ((D ×ˢ E) ×ˢ (D' ×ˢ E')).filter (fun q ↦ q.1.1 + q.2.1 = n ∧ q.1.2 + q.2.2 = m),
        graphProdPieceBlock k sX sX' sY sY' f hf g hg q.1.1 q.1.2 q.2.1 q.2.2 := by
  rw [graphBlock, corrCongr_lof_lof, correspondenceCongr_tmul,
    chowGroupDegreeEquiv_mk_cycleAssociatedToClosedSubscheme,
    ← sum_cycle_graphPieceProdHom k sX sX' sY sY' f hf g hg hD hE hD' hE' n m,
    ← Finset.sum_subtype_eq_sum_filter, QuotientAddGroup.mk_sum, TensorProduct.tmul_sum, map_sum,
    map_sum]
  refine Finset.sum_congr rfl ?_
  rintro ⟨⟨⟨d, e⟩, ⟨d', e'⟩⟩, hn, hm⟩ -
  dsimp only at hn hm
  subst hn hm
  rfl

omit [IsSeparated sX] [IsSeparated sX'] [Smooth sY] [IsSeparated sY] [Smooth sY'] [IsSeparated sY']
    [IsProper sX] [IsProper sX'] [IsProper sY] [IsProper sY'] in
/-- A part `(X × X')_n` met by `(f × g)(Y × Y')` has `n = d + d'` for parts `X_d` and `X'_{d'}`
met by `f(Y)` and `g(Y')`. -/
theorem mem_image_of_nonempty_preimage_dimPart_prodBase {D D' : Finset ℕ}
    (hD : ∀ d, (f ⁻¹ᵁ dimPart sX d : Set Y).Nonempty → d ∈ D)
    (hD' : ∀ d, (g ⁻¹ᵁ dimPart sX' d : Set Y').Nonempty → d ∈ D') (n : ℕ)
    (hn : (graphProdHom k sX sX' sY sY' f hf g hg ⁻¹ᵁ dimPart (prodBase sX sX') n :
      Set (Limits.pullback sY sY' : Scheme.{u})).Nonempty) :
    n ∈ (D ×ˢ D').image fun p ↦ p.1 + p.2 := by
  obtain ⟨z, hz⟩ := hn
  obtain ⟨d, d', hd, hd', hn⟩ := exists_add_eq_of_graphProdHom_mem k sX sX' sY sY' f hf g hg z n hz
  exact Finset.mem_image.2 ⟨(d, d'), Finset.mem_product.2 ⟨hD _ ⟨_, hd⟩, hD' _ ⟨_, hd'⟩⟩, hn⟩

/-- `[Γ_f] ⊗ [Γ_g]` is the sum of the products of the pieces of the two graphs. -/
theorem tensor_graphCorr_eq_sum {D E D' E' : Finset ℕ}
    (hD : ∀ d, (f ⁻¹ᵁ dimPart sX d : Set Y).Nonempty → d ∈ D)
    (hE : ∀ e, (dimPart sY e : Set Y).Nonempty → e ∈ E)
    (hD' : ∀ d, (g ⁻¹ᵁ dimPart sX' d : Set Y').Nonempty → d ∈ D')
    (hE' : ∀ e, (dimPart sY' e : Set Y').Nonempty → e ∈ E') :
    tensor k sX sX' sY sY' (canonicalDiagonalClassFamily k) 0 0 (graphCorr k sX sY f hf)
        (graphCorr k sX' sY' g hg) =
      ∑ q ∈ (D ×ˢ E) ×ˢ (D' ×ˢ E'),
        graphProdPieceBlock k sX sX' sY sY' f hf g hg q.1.1 q.1.2 q.2.1 q.2.2 := by
  rw [graphCorr_eq_sum k sX sY f hf hD hE, graphCorr_eq_sum k sX' sY' g hg hD' hE',
    bilin_sum_sum]
  exact Finset.sum_congr rfl fun q _ ↦ tensor_graphBlock k sX sX' sY sY' f hf g hg _ _ _ _

/-- `[Γ_{f × g}]` is the sum of the products of the pieces of the two graphs. -/
theorem corrCongr_graphCorr_graphProdHom_eq_sum {D E D' E' : Finset ℕ}
    (hD : ∀ d, (f ⁻¹ᵁ dimPart sX d : Set Y).Nonempty → d ∈ D)
    (hE : ∀ e, (dimPart sY e : Set Y).Nonempty → e ∈ E)
    (hD' : ∀ d, (g ⁻¹ᵁ dimPart sX' d : Set Y').Nonempty → d ∈ D')
    (hE' : ∀ e, (dimPart sY' e : Set Y').Nonempty → e ∈ E') :
    corrCongr k (prodBase sX sX') (prodBase sY sY') (add_zero 0).symm
        (graphCorr k (prodBase sX sX') (prodBase sY sY') (graphProdHom k sX sX' sY sY' f hf g hg)
          (graphProdHom_comp_prodBase k sX sX' sY sY' f hf g hg)) =
      ∑ q ∈ (D ×ˢ E) ×ˢ (D' ×ˢ E'),
        graphProdPieceBlock k sX sX' sY sY' f hf g hg q.1.1 q.1.2 q.2.1 q.2.2 := by
  rw [graphCorr_eq_sum k (prodBase sX sX') (prodBase sY sY') _ _
      (mem_image_of_nonempty_preimage_dimPart_prodBase k sX sX' sY sY' f hf g hg hD hD')
      (mem_image_of_nonempty_dimPart_prodBase k sY sY' hE hE'), linearEquiv_sum_sum]
  simp only [corrCongr_graphBlock_graphProdHom k sX sX' sY sY' f hf g hg hD hE hD' hE']
  exact sum_sum_filter_eq _ _ _ _ (fun q hq ↦ Finset.mem_image.2 ⟨(q.1.1, q.2.1),
    Finset.mem_product.2 ⟨(Finset.mem_product.1 (Finset.mem_product.1 hq).1).1,
      (Finset.mem_product.1 (Finset.mem_product.1 hq).2).1⟩, rfl⟩)
    (fun q hq ↦ Finset.mem_image.2 ⟨(q.1.2, q.2.2),
    Finset.mem_product.2 ⟨(Finset.mem_product.1 (Finset.mem_product.1 hq).1).2,
      (Finset.mem_product.1 (Finset.mem_product.1 hq).2).2⟩, rfl⟩)

/-- **The tensor product of two graphs is the graph of the product** (Stacks 0FG7, 0FG1): for
morphisms `f : Y ⟶ X` and `g : Y' ⟶ X'` of smooth proper schemes over `k`, of mixed dimension,
`[Γ_f] ⊗ [Γ_g] = [Γ_{f × g}]` in `Corr⁰(X × X', Y × Y')`, up to the identification of degrees
`0 + 0 = 0`. -/
theorem tensor_graphCorr :
    tensor k sX sX' sY sY' (canonicalDiagonalClassFamily k) 0 0 (graphCorr k sX sY f hf)
        (graphCorr k sX' sY' g hg) =
      corrCongr k (prodBase sX sX') (prodBase sY sY') (add_zero 0).symm
        (graphCorr k (prodBase sX sX') (prodBase sY sY') (graphProdHom k sX sX' sY sY' f hf g hg)
          (graphProdHom_comp_prodBase k sX sX' sY sY' f hf g hg)) := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have : CompactSpace Y' := QuasiCompact.compactSpace_of_compactSpace sY'
  obtain ⟨D, hD⟩ : ∃ D : Finset ℕ, ∀ d, (f ⁻¹ᵁ dimPart sX d : Set Y).Nonempty → d ∈ D :=
    ⟨_, fun d hd ↦ (finite_setOf_nonempty_preimage_dimPart k sX f).mem_toFinset.2 hd⟩
  obtain ⟨E, hE⟩ : ∃ E : Finset ℕ, ∀ e, (dimPart sY e : Set Y).Nonempty → e ∈ E :=
    ⟨_, fun e he ↦ (finite_setOf_nonempty_dimPart sY).mem_toFinset.2 he⟩
  obtain ⟨D', hD'⟩ : ∃ D' : Finset ℕ, ∀ d, (g ⁻¹ᵁ dimPart sX' d : Set Y').Nonempty → d ∈ D' :=
    ⟨_, fun d hd ↦ (finite_setOf_nonempty_preimage_dimPart k sX' g).mem_toFinset.2 hd⟩
  obtain ⟨E', hE'⟩ : ∃ E' : Finset ℕ, ∀ e, (dimPart sY' e : Set Y').Nonempty → e ∈ E' :=
    ⟨_, fun e he ↦ (finite_setOf_nonempty_dimPart sY').mem_toFinset.2 he⟩
  rw [tensor_graphCorr_eq_sum k sX sX' sY sY' f hf g hg hD hE hD' hE',
    corrCongr_graphCorr_graphProdHom_eq_sum k sX sX' sY sY' f hf g hg hD hE hD' hE']

end ProductPieces

end Stacks.WeilCohomology

end
