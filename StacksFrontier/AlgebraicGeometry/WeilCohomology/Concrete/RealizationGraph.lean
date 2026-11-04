module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RealizationFunctor
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# The realization of the graph of a morphism is the pullback

Let `W` be data (D0)–(D3) of Section 45.9 (Tag 0FHA) satisfying (A), (B) and (C), with coefficient
field of characteristic zero, and let `G` be the functor of the proof of Stacks 0FHL on
correspondences of degree zero (`Stacks.WeilCohomology.WeilData.corrFunctor`). For a morphism
`g : Q ⟶ P` of smooth projective schemes over `k`, the graph `[Γ_g] ∈ Corr⁰(P, Q)` acts by the
pullback, `G([Γ_g]) = g^*`: this is what makes `H^*(X) = G(h(X))` an identification of functors.

On a block, `[Γ_g] ∩ (P_d × Q_e)` is the graph of `g` restricted to the open and closed piece
`Q_e ∩ g⁻¹(P_d)` of `Q_e`, whose cycle class acts, by Stacks 0FHG and the trace equation, as
`a ↦ (piece ⊂ Q_e)_! (g|^* a)`; summing over the blocks, the pieces form a finite disjoint cover
of `Q` by open and closed subschemes, and Stacks 0FHJ gives `g^*`.

## Main results

* `Stacks.WeilCohomology.WeilData.corrMap_graphCorr`: `G([Γ_g]) = g^*`.

## References

* [Stacks Project, Tag 0FHL](https://stacks.math.columbia.edu/tag/0FHL)
* [Stacks Project, Tag 0FHG](https://stacks.math.columbia.edu/tag/0FHG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow

universe u w

namespace Stacks.WeilCohomology

namespace SmoothProjectiveScheme

variable {k : Type u} [Field k] {P Q : (SmoothProjectiveScheme k).FullSubcategory} (g : Q ⟶ P)
  (d e : ℕ)

/-- The open subscheme `Q_e ∩ g⁻¹(P_d)` of `Q_e`. -/
abbrev graphPieceOpen : (part Q e).obj.left.Opens :=
  ((dimPart Q.obj.hom e).ι ≫ g.hom.left) ⁻¹ᵁ dimPart P.obj.hom d

/-- The open subscheme `Q_e ∩ g⁻¹(P_d)` of `Q_e` is closed as well as open. -/
theorem isClopen_graphPieceOpen : IsClopen (graphPieceOpen g d e : Set (part Q e).obj.left) :=
  ((isClopenDecomposition_dimPart P.obj.hom).isClopen d).preimage
    ((dimPart Q.obj.hom e).ι ≫ g.hom.left).continuous

/-- The piece `Q_e ∩ g⁻¹(P_d)`, a smooth projective scheme. -/
abbrev graphPieceObj : (SmoothProjectiveScheme k).FullSubcategory :=
  clopenObj (part Q e) (graphPieceOpen g d e) (isClopen_graphPieceOpen g d e)

/-- The inclusion of the piece into `Q_e`. -/
abbrev graphPieceIncl : graphPieceObj g d e ⟶ part Q e :=
  clopenι (part Q e) (graphPieceOpen g d e) (isClopen_graphPieceOpen g d e)

/-- The inclusion of the piece `Q_e ∩ g⁻¹(P_d)` into `Q_e` is a closed immersion. -/
instance : IsClosedImmersion (graphPieceIncl g d e).hom.left :=
  isClosedImmersion_ι_of_isClopen (isClopen_graphPieceOpen g d e)

/-- The restriction `Q_e ∩ g⁻¹(P_d) ⟶ P_d` of `g`. -/
def graphPieceMap : graphPieceObj g d e ⟶ part P d :=
  ObjectProperty.homMk (Over.homMk (U := (graphPieceObj g d e).obj) (V := (part P d).obj)
    (((dimPart Q.obj.hom e).ι ≫ g.hom.left) ∣_ dimPart P.obj.hom d) (by
      change (((dimPart Q.obj.hom e).ι ≫ g.hom.left) ∣_ dimPart P.obj.hom d) ≫
          (dimPart P.obj.hom d).ι ≫ P.obj.hom =
        (graphPieceOpen g d e).ι ≫ (dimPart Q.obj.hom e).ι ≫ Q.obj.hom
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Category.assoc, Over.w g.hom]
      rfl))

/-- The graph `Q_e ∩ g⁻¹(P_d) ⟶ P_d × Q_e` of the restriction of `g` is a closed immersion. -/
instance : IsClosedImmersion (prodLift (graphPieceMap g d e) (graphPieceIncl g d e)).hom.left :=
  isClosedImmersion_graphPartMorphism P.obj.hom (partBase Q.obj.hom e)
    ((dimPart Q.obj.hom e).ι ≫ g.hom.left) (by rw [Category.assoc, Over.w g.hom])
    ((isClopenDecomposition_dimPart P.obj.hom).isClopen d)

/-- The inclusion of the piece `Q_e ∩ g⁻¹(P_d)` into `Q` is an open immersion. -/
instance : IsOpenImmersion (graphPieceIncl g d e ≫ partι Q e).hom.left :=
  inferInstanceAs (IsOpenImmersion ((graphPieceIncl g d e).hom.left ≫ (partι Q e).hom.left))

/-- The inclusion of the piece `Q_e ∩ g⁻¹(P_d)` into `Q` is a closed immersion. -/
instance : IsClosedImmersion (graphPieceIncl g d e ≫ partι Q e).hom.left :=
  inferInstanceAs (IsClosedImmersion ((graphPieceIncl g d e).hom.left ≫ (partι Q e).hom.left))

/-- A nonempty piece is nonempty and equidimensional of dimension `e`. -/
theorem isNonemptyEquidimensional_graphPieceObj (h : Nonempty (graphPieceObj g d e).obj.left) :
    IsNonemptyEquidimensional (graphPieceObj g d e) e :=
  ⟨h, RelativeDimension.comp_isOpenImmersion (graphPieceOpen g d e).ι _
    (relativeDimension_partBase Q.obj.hom e)⟩

/-- The restriction of `g` to the piece, followed by `P_d ⟶ P`, is the inclusion of the piece into
`Q` followed by `g`. -/
theorem graphPieceMap_comp_partι :
    graphPieceMap g d e ≫ partι P d = graphPieceIncl g d e ≫ partι Q e ≫ g :=
  hom_ext_left (morphismRestrict_ι _ _)

/-- A point of `Q` in the image of the piece `Q_e ∩ g⁻¹(P_d)` lies in `Q_e` and maps into `P_d`. -/
theorem mem_range_graphPiece {q : Q.obj.left}
    (hq : q ∈ Set.range (graphPieceIncl g d e ≫ partι Q e).hom.left) :
    q ∈ Set.range (partι Q e).hom.left ∧ g.hom.left q ∈ Set.range (partι P d).hom.left := by
  obtain ⟨t, rfl⟩ := hq
  refine ⟨⟨(graphPieceIncl g d e).hom.left t, rfl⟩, ⟨(graphPieceMap g d e).hom.left t, ?_⟩⟩
  rw [← comp_hom_left_apply, graphPieceMap_comp_partι]
  rfl

omit d e in
/-- The pieces `Q_e ∩ g⁻¹(P_d)` cover `Q`. -/
theorem cover_graphPiece (q : Q.obj.left) :
    ∃ p ∈ partSupport P ×ˢ partSupport Q,
      q ∈ Set.range (graphPieceIncl g p.1 p.2 ≫ partι Q p.2).hom.left := by
  obtain ⟨e, he, y, rfl⟩ := exists_mem_partSupport Q q
  obtain ⟨d, hd, hgy⟩ := exists_mem_partSupport P (g.hom.left ((partι Q e).hom.left y))
  rw [range_partι] at hgy
  refine ⟨(d, e), Finset.mem_product.2 ⟨hd, he⟩, ?_⟩
  rw [range_comp_hom_left]
  exact ⟨y, mem_range_clopenι (isClopen_graphPieceOpen g d e) hgy, rfl⟩

omit d e in
/-- The pieces `Q_e ∩ g⁻¹(P_d)` are pairwise disjoint. -/
theorem disjoint_graphPiece : ∀ s ∈ partSupport P ×ˢ partSupport Q,
    ∀ t ∈ partSupport P ×ˢ partSupport Q, s ≠ t →
      Disjoint (Set.range (graphPieceIncl g s.1 s.2 ≫ partι Q s.2).hom.left)
        (Set.range (graphPieceIncl g t.1 t.2 ≫ partι Q t.2).hom.left) := by
  intro s _ t _ hst
  refine Set.disjoint_left.2 fun q hs ht ↦ ?_
  obtain ⟨hs₁, hs₂⟩ := mem_range_graphPiece g s.1 s.2 hs
  obtain ⟨ht₁, ht₂⟩ := mem_range_graphPiece g t.1 t.2 ht
  by_cases he : s.2 = t.2
  · exact Set.disjoint_left.1 (disjoint_range_partι P fun h ↦ hst (Prod.ext h he)) hs₂ ht₂
  · exact Set.disjoint_left.1 (disjoint_range_partι Q he) hs₁ ht₁

end SmoothProjectiveScheme

namespace WeilData

open SmoothProjectiveScheme

variable {k : Type u} [Field k] {F : Type w} [Field F] [CharZero F] {W : WeilData k F}
  (hA : W.PoincareDuality) (hB : W.Kunneth) (hC : W.CycleClassAxiom hA.perfectPairing)

/-- The correspondence `[Γ] ∈ Corr⁰(X, Y)` of the graph `Γ = (γ, ι) : T ⟶ X × Y`. -/
def graphClassCorr {X Y T : (SmoothProjectiveScheme k).FullSubcategory} (γ : T ⟶ X) (ι : T ⟶ Y)
    [IsClosedImmersion (prodLift γ ι).hom.left] (e : ℕ) :
    Correspondence (fieldChowSituation k) X.obj.hom Y.obj.hom e 0 :=
  (1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
    (prod X Y).obj.hom (prodLift γ ι).hom.left ((e : ℤ) - 0))

/-- The `(d, e)` block of `[Γ_g]`, read on the parts, is the class of the graph of the restriction
of `g` to the piece. -/
theorem blockEquiv_graphBlock {P Q : (SmoothProjectiveScheme k).FullSubcategory} (g : Q ⟶ P)
    (d e : ℕ) :
    blockEquiv P Q d e 0 (graphBlock k P.obj.hom Q.obj.hom g.hom.left (Over.w g.hom) d e) =
      graphClassCorr (graphPieceMap g d e) (graphPieceIncl g d e) e :=
  rfl

/-- **The class of the graph of `γ : T ⟶ X` and an open and closed immersion `ι : T ⟶ Y`** acts
as `ι_! ∘ γ^*`, by Stacks 0FHG and the trace equation. -/
theorem blockAct_corrClass_graph {X Y T : (SmoothProjectiveScheme k).FullSubcategory} {d e : ℕ}
    (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y e)
    (hT : IsNonemptyEquidimensional T e) (γ : T ⟶ X) (ι : T ⟶ Y) [IsOpenImmersion ι.hom.left]
    [IsClosedImmersion ι.hom.left] [IsClosedImmersion (prodLift γ ι).hom.left] (n : ℤ) :
    W.blockAct hA.perfectPairing hX hY (W.corrClass X Y e 0 d (graphClassCorr γ ι e)) n =
      extendDeg hA hB hC ι n ∘ₗ W.pullDeg γ n := by
  have hz : ∀ v : W.H (prod X Y),
      W.traceProj (prod X Y) (d + e) (isNonemptyEquidimensional_prod hX hY)
        (W.corrClass X Y e 0 d (graphClassCorr γ ι e) * v) =
        W.traceProj T e hT (W.pull (prodLift γ ι) v) :=
    traceProj_corrClass_closedSubscheme hA hB hC hX hY hT (prodLift γ ι)
  refine LinearMap.ext fun a ↦ (eq_of_traceProj_mul_eq hA.perfectPairing hY fun b ↦ ?_)
  rw [blockAct_graph hA.perfectPairing hX hY hT γ ι hz a b,
    LinearMap.comp_apply, coe_extendDeg,
    traceProj_extendByZero_mul (hA := hA) (hB := hB) (hC := hC) ι hY hT, coe_pullDeg]

/-- **The action of the `(d, e)` block of `[Γ_g]`**: `(piece ⊂ Q)_! ∘ (piece ⟶ Q ⟶ P)^*`. -/
theorem blockMap_graphBlock {P Q : (SmoothProjectiveScheme k).FullSubcategory} (g : Q ⟶ P) (d e : ℕ)
    (n : ℤ) :
    blockMap hA hB hC P Q d e 0 n
        (blockEquiv P Q d e 0 (graphBlock k P.obj.hom Q.obj.hom g.hom.left (Over.w g.hom) d e)) =
      extendDeg hA hB hC (graphPieceIncl g d e ≫ partι Q e) n ∘ₗ
        W.pullDeg (graphPieceIncl g d e ≫ partι Q e ≫ g) n := by
  by_cases hT : Nonempty (graphPieceObj g d e).obj.left
  · obtain ⟨t⟩ := hT
    have hP : Nonempty (part P d).obj.left := ⟨(graphPieceMap g d e).hom.left t⟩
    have hQ : Nonempty (part Q e).obj.left := ⟨(graphPieceIncl g d e).hom.left t⟩
    rw [blockMap_of_nonempty hA hB hC n hP hQ, blockEquiv_graphBlock,
      blockAct_corrClass_graph hA hB hC (isNonemptyEquidimensional_part P hP)
        (isNonemptyEquidimensional_part Q hQ) (isNonemptyEquidimensional_graphPieceObj g d e ⟨t⟩)]
    refine LinearMap.ext fun a ↦ Subtype.ext ?_
    simp only [LinearMap.comp_apply, coe_extendDeg, coe_pullDeg]
    rw [extendByZero_comp (hA := hA) (hB := hB) (hC := hC), pull_pull, graphPieceMap_comp_partι]
  · have : IsEmpty (graphPieceObj g d e).obj.left := not_nonempty_iff.1 hT
    have := subsingleton_of_isEmpty hB.kunnethIsomorphism hC.pullback hC.mul hC.point
      (graphPieceObj g d e)
    have h0 : graphBlock k P.obj.hom Q.obj.hom g.hom.left (Over.w g.hom) d e = 0 :=
      graphBlock_eq_zero k P.obj.hom Q.obj.hom g.hom.left (Over.w g.hom)
        fun y hy hgy ↦ hT ⟨⟨⟨y, hy⟩, hgy⟩⟩
    rw [h0, map_zero (blockEquiv P Q d e 0), map_zero (blockMap hA hB hC P Q d e 0 n)]
    refine LinearMap.ext fun a ↦ ?_
    rw [LinearMap.comp_apply, Subsingleton.elim (W.pullDeg _ n a) 0, map_zero]
    rfl

/-- **`G([Γ_g]) = g^*`**: the graph of a morphism `g : Q ⟶ P` of smooth projective schemes acts on
cohomology by the pullback. -/
theorem corrMap_graphCorr (P Q : (SmoothProjectiveScheme k).FullSubcategory) (g : Q ⟶ P) (n : ℤ) :
    corrMap hA hB hC P Q 0 n (graphCorr k P.obj.hom Q.obj.hom g.hom.left (Over.w g.hom)) =
      W.pullDeg g n := by
  rw [graphCorr_eq_sum k P.obj.hom Q.obj.hom g.hom.left (Over.w g.hom) (D := partSupport P)
      (E := partSupport Q)
      (fun d ⟨y, hy⟩ ↦ mem_partSupport.2 ⟨_, hy⟩) (fun e he ↦ mem_partSupport.2 he),
    map_sum (corrMap hA hB hC P Q 0 n)]
  simp_rw [map_sum (corrMap hA hB hC P Q 0 n), corrMap_lof_lof, blockMap_graphBlock]
  refine LinearMap.ext fun a ↦ Subtype.ext ?_
  simp only [LinearMap.sum_apply, Submodule.coe_sum, LinearMap.comp_apply, coe_extendDeg,
    coe_pullDeg]
  rw [← Finset.sum_product' (partSupport P) (partSupport Q)
    (fun d e ↦ extendByZero hA hB hC (graphPieceIncl g d e ≫ partι Q e)
      (W.pull (graphPieceIncl g d e ≫ partι Q e ≫ g) (a : W.H P)))]
  refine (Finset.sum_congr rfl fun p _ ↦ ?_).trans (sum_extendByZero_pull (hA := hA) (hB := hB)
    (hC := hC) (partSupport P ×ˢ partSupport Q)
    (fun p ↦ graphPieceIncl g p.1 p.2 ≫ partι Q p.2) (cover_graphPiece g)
    (disjoint_graphPiece g) (W.pull g (a : W.H P)))
  rw [pull_pull, Category.assoc]

end WeilData

end Stacks.WeilCohomology

end
