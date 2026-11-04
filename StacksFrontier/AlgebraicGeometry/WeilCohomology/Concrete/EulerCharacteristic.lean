module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DiagonalDualBasis
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DiagonalSelfIntersection
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ZeroCycleTraceDegree
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Euler characteristic of a Weil cohomology theory

Let `H^*` be data (D0)–(D3) of Section 45.9 (Tag 0FHA) satisfying (A), (B) and (C)
(`Stacks.WeilCohomology.WeilData`), with `F` of characteristic zero, and let `X` be a nonempty
smooth projective scheme over `k`, equidimensional of dimension `d`. **Stacks 0FHS** asserts

  `∑_i (-1)^i dim_F H^i(X) = deg(Δ · Δ) = deg(c_d(𝒯_{X/k}))`.

The right-hand equality is a statement about Chow groups alone, proved in
`StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DiagonalSelfIntersection`. This file proves
the left-hand equality, following the source:

* `deg([Δ] · [Δ]) = ∫_{X × X} γ([Δ] · [Δ])` by Stacks 0FHR on `X × X`,
  `= ∫_{X × X} γ([Δ]) ∪ γ([Δ])` by (C)(c), and `= ∫_X Δ^*γ([Δ])` since `γ([Δ]) = Δ_*1` (Stacks
  0FHG) and by the trace equation of the pushforward (Stacks 0FHB)
  (`codimensionDegree_diag_mul_diag_eq_traceProj`);
* by Remark 0FHD, `Δ^*` after the Künneth isomorphism is the cup product, so `∫_X Δ^*γ([Δ])` is the
  sum over the Künneth components of `γ([Δ])` of the traces of their products; only those of
  bidegree `(i, 2d - i)` contribute, and writing `γ([Δ])_{(i, 2d-i)} = ∑_j e_{i,j} ⊗ e'_{2d-i,j}`
  for a basis `e` of `H^i(X)`, Stacks 0FHH gives
  `∑_j ∫_X e_{i,j} ∪ e'_{2d-i,j} = (-1)^i dim H^i(X)`
  (`traceProj_mulMapGrade_diagonalKunnethPreimage`, `traceProj_pull_diag_eq_finsum`).

The sum `∑_i (-1)^i dim_F H^i(X)` is over all `i ∈ ℤ`; that it has finite support is part of the
result, since a degree `i` with `H^i(X) ≠ 0` contributes a nonzero Künneth component of `γ([Δ])`.

## Main results

* `Stacks.WeilCohomology.WeilData.finsum_negOnePow_finrank_eq_codimensionDegree_diag_mul_diag`:
  **Stacks 0FHS**.

## References

* [Stacks Project, Tag 0FHS](https://stacks.math.columbia.edu/tag/0FHS)
* [Stacks Project, Tag 0FHR](https://stacks.math.columbia.edu/tag/0FHR)
* [Stacks Project, Tag 0FHH](https://stacks.math.columbia.edu/tag/0FHH)
* [Stacks Project, Tag 0FHG](https://stacks.math.columbia.edu/tag/0FHG)
* [Stacks Project, Tag 0FHD](https://stacks.math.columbia.edu/tag/0FHD)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Chow TensorProduct

universe u w

namespace Stacks.WeilCohomology.WeilData

variable {k : Type u} [Field k] {F : Type w} [Field F] {W : WeilData k F}

open SmoothProjectiveScheme

section Trace

variable [CharZero F] (hA : W.PoincareDuality) (hB : W.Kunneth)
  (hC : W.CycleClassAxiom hA.perfectPairing) {X : (SmoothProjectiveScheme k).FullSubcategory}
  {d : ℕ} (hX : IsNonemptyEquidimensional X d)

include hA hB hC in
/-- **`deg([Δ] · [Δ]) = ∫_X Δ^*γ([Δ])`.** By Stacks 0FHR on `X × X`, axiom (C)(c), and
`γ([Δ]) = Δ_*1` (Stacks 0FHG) with the trace equation of the pushforward. -/
theorem codimensionDegree_diag_mul_diag_eq_traceProj :
    ((codimensionDegree (prod X X) (d + d)
        (codimensionIntersectionProduct k (prod X X).obj.hom d d
          (closedSubschemeClass (prod X X).obj.hom (diag X).hom.left d)
          (closedSubschemeClass (prod X X).obj.hom (diag X).hom.left d)) : ℤ) : F) =
      W.traceProj X d hX (W.pull (diag X)
        (W.twCoord (prod X X) (2 * (d : ℤ)) d (W.cycleClass (prod X X) d
          (closedSubschemeClass (prod X X).obj.hom (diag X).hom.left d)) : W.H (prod X X))) := by
  set hP := isNonemptyEquidimensional_prod hX hX
  have h0 := trace_cycleClass_eq_codimensionDegree hA hB hC hP
    (codimensionIntersectionProduct k (prod X X).obj.hom d d
      (closedSubschemeClass (prod X X).obj.hom (diag X).hom.left d)
      (closedSubschemeClass (prod X X).obj.hom (diag X).hom.left d))
  rw [← h0]
  have hm := hC.mul (prod X X) d d (closedSubschemeClass (prod X X).obj.hom (diag X).hom.left d)
    (closedSubschemeClass (prod X X).obj.hom (diag X).hom.left d)
  show W.trace (prod X X) (d + d) hP (W.cycleClass (prod X X) ((d : ℤ) + d) _) = _
  rw [hm, trace_eq_traceProj]
  show W.traceProj (prod X X) (d + d) hP
    (W.twCoord (prod X X) (2 * ((d : ℤ) + d)) ((d : ℤ) + d) _ : W.H (prod X X)) = _
  rw [twCoord_cupTw, coe_cup]
  -- `γ([Δ]) = Δ_*1`, so `γ([Δ])` represents the trace pairing through the diagonal
  have hγ := W.cycleClass_diagonal_eq_pushforward_one hA hB hC hX hP
  have hG := traceProj_pull_diag hA.perfectPairing hX
    (W.twCoord (prod X X) (2 * (d : ℤ)) d (W.cycleClass (prod X X) d
      (closedSubschemeClass (prod X X).obj.hom (diag X).hom.left d))).2
  rw [hG, hγ]

end Trace

section Sum

variable (W) (X : (SmoothProjectiveScheme k).FullSubcategory)

/-- The multiplication `H^*(X) ⊗_F H^*(X) ⟶ H^*(X)`. -/
def mulMap : W.H X ⊗[F] W.H X →ₗ[F] W.H X :=
  TensorProduct.lift (LinearMap.mul F (W.H X))

/-- **Remark 0FHD**: pulling back along the diagonal after the Künneth map is the cup product. -/
theorem pull_diag_kunnethMap (x : W.H X ⊗[F] W.H X) :
    W.pull (diag X) (W.kunnethMap X X x) = W.mulMap X x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rw [kunnethMap_tmul, pull_diag_mul]; rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

/-- The multiplication on the summand `H^p(X) ⊗_F H^q(X)`. -/
def mulMapGrade (pq : ℤ × ℤ) : W.grade X pq.1 ⊗[F] W.grade X pq.2 →ₗ[F] W.H X :=
  TensorProduct.lift ((LinearMap.mul F (W.H X)).compl₁₂ (W.grade X pq.1).subtype
    (W.grade X pq.2).subtype)

/-- The multiplication is the sum of the multiplications on the bidegree summands. -/
theorem mulMap_eq_toModule :
    W.mulMap X = (DirectSum.toModule F (ℤ × ℤ) _ (W.mulMapGrade X)).comp
      (bidegreeEquiv X).toLinearMap := by
  refine TensorProduct.ext' fun u v ↦ ?_
  induction u using DirectSum.Decomposition.inductionOn (W.grade X) with
  | zero => simp
  | add u u' hu hu' => rw [TensorProduct.add_tmul, map_add, map_add, hu, hu']
  | @homogeneous p u =>
    induction v using DirectSum.Decomposition.inductionOn (W.grade X) with
    | zero => simp
    | add v v' hv hv' => rw [TensorProduct.tmul_add, map_add, map_add, hv, hv']
    | @homogeneous q v =>
      rw [LinearMap.comp_apply, LinearEquiv.coe_coe, bidegreeEquiv_tmul_of_mem X u.2 v.2,
        DirectSum.toModule_lof]
      rfl

open scoped Classical in
/-- The multiplication of `x ∈ H^*(X) ⊗_F H^*(X)` is the sum over the bidegrees `(p, q)` in which
`x` has a nonzero component of the multiplications of those components. -/
theorem mulMap_eq_sum (x : W.H X ⊗[F] W.H X) :
    W.mulMap X x = ∑ pq ∈ (bidegreeEquiv X x).support,
      W.mulMapGrade X pq (bidegreeEquiv X x pq) := by
  rw [mulMap_eq_toModule, LinearMap.comp_apply, LinearEquiv.coe_coe]
  conv_lhs => rw [← DirectSum.sum_support_of (bidegreeEquiv X x)]
  rw [map_sum]
  refine Finset.sum_congr rfl fun pq _ ↦ ?_
  rw [← DirectSum.lof_eq_of F, DirectSum.toModule_lof]

variable {W X} {d : ℕ} (hX : IsNonemptyEquidimensional X d)

/-- On a summand `H^p(X) ⊗_F H^q(X)` with `p + q ≠ 2d`, the trace of the product vanishes. -/
theorem traceProj_mulMapGrade_of_ne (pq : ℤ × ℤ) (hpq : pq.1 + pq.2 ≠ 2 * (d : ℤ))
    (t : W.grade X pq.1 ⊗[F] W.grade X pq.2) :
    W.traceProj X d hX (W.mulMapGrade X pq t) = 0 := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul u v => exact W.traceProj_of_mem_ne X d hX (SetLike.GradedMul.mul_mem u.2 v.2) hpq
  | add t t' ht ht' => rw [map_add, map_add, ht, ht', add_zero]

variable [CharZero F] (hA : W.PoincareDuality) (hB : W.Kunneth)
  (hC : W.CycleClassAxiom hA.perfectPairing)

/-- The Künneth preimage `x ∈ H^*(X) ⊗_F H^*(X)` of the class `γ([Δ])` of the diagonal, read in
the coordinates of the twists. -/
def diagonalKunnethPreimage (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ) :
    W.H X ⊗[F] W.H X :=
  (LinearEquiv.ofBijective (W.kunnethMap X X) (hB.kunnethIsomorphism X X)).symm
    (W.twCoord (prod X X) (2 * (d : ℤ)) d (W.cycleClass (prod X X) d
      (closedSubschemeClass (prod X X).obj.hom (diag X).hom.left d)) : W.H (prod X X))

omit [CharZero F] in
/-- The Künneth image of `x` is `γ([Δ])`. -/
theorem kunnethMap_diagonalKunnethPreimage :
    W.kunnethMap X X (diagonalKunnethPreimage hB X d) =
      (W.twCoord (prod X X) (2 * (d : ℤ)) d (W.cycleClass (prod X X) d
        (closedSubschemeClass (prod X X).obj.hom (diag X).hom.left d)) : W.H (prod X X)) :=
  (LinearEquiv.ofBijective (W.kunnethMap X X) (hB.kunnethIsomorphism X X)).apply_symm_apply _

omit [CharZero F] in
include hX hC in
/-- **The trace of the `(i, 2d - i)` Künneth component of the diagonal is `(-1)^i β_i`**: writing
`γ([Δ])_{(i, 2d-i)} = ∑_j e_{i,j} ⊗ e'_{2d-i,j}` for a basis `e` of `H^i(X)`,
`∑_j ∫_X e_{i,j} ∪ e'_{2d-i,j} = ∑_j (-1)^i = (-1)^i dim_F H^i(X)` by Stacks 0FHH. -/
theorem traceProj_mulMapGrade_diagonalKunnethPreimage (i : ℤ) :
    W.traceProj X d hX (W.mulMapGrade X (i, 2 * d - i)
        (bidegreeComponent X i (2 * d - i) (diagonalKunnethPreimage hB X d))) =
      ((i.negOnePow : ℤ) : F) * (Module.finrank F (W.grade X i) : F) := by
  have := hA.finiteDimensionality X d hX i
  set e := Module.finBasis F (W.grade X i)
  have hcomp : bidegreeComponent X i (2 * d - i) (diagonalKunnethPreimage hB X d) =
      ∑ l, e l ⊗ₜ (W.twCoord X (2 * d - i) d
        (W.diagonalKunnethCoordinates hB.kunnethIsomorphism X d i e l)) := by
    rw [← kunnethComponent_kunnethMap X hB.kunnethIsomorphism, kunnethMap_diagonalKunnethPreimage,
      ← map_twCoord_kunnethComponentTw,
      kunnethComponentTw_diagonal_eq_sum (X := X) (d := d) hB.kunnethIsomorphism i e, map_sum]
    rfl
  rw [hcomp, map_sum, map_sum]
  have hterm : ∀ l, W.traceProj X d hX (W.mulMapGrade X (i, 2 * d - i)
      (e l ⊗ₜ (W.twCoord X (2 * d - i) d
        (W.diagonalKunnethCoordinates hB.kunnethIsomorphism X d i e l)))) =
      ((i.negOnePow : ℤ) : F) := fun l ↦ by
    have h := pairing_diagonalKunnethCoordinates hX hA hB hC i e l l
    rw [pairing_eq_traceProj, if_pos rfl, mul_one] at h
    exact h
  simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring


omit [CharZero F] in
/-- The `(p, q)` coordinate of the bidegree decomposition is the bidegree component. -/
theorem bidegreeEquiv_apply (x : W.H X ⊗[F] W.H X) (p q : ℤ) :
    bidegreeEquiv X x (p, q) = bidegreeComponent X p q x := by
  rw [bidegreeComponent, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rfl

include hX hB hC in
open scoped Classical in
/-- **`∫_X Δ^*γ([Δ]) = ∑_i (-1)^i dim_F H^i(X)`**, the sum having finite support. -/
theorem traceProj_pull_diag_eq_finsum :
    (Function.support fun i : ℤ ↦ (i.negOnePow : ℤ) * (Module.finrank F (W.grade X i) : ℤ)).Finite ∧
    W.traceProj X d hX (W.pull (diag X)
        (W.twCoord (prod X X) (2 * (d : ℤ)) d (W.cycleClass (prod X X) d
          (closedSubschemeClass (prod X X).obj.hom (diag X).hom.left d)) : W.H (prod X X))) =
      ((∑ᶠ i : ℤ, (i.negOnePow : ℤ) * (Module.finrank F (W.grade X i) : ℤ) : ℤ) : F) := by
  set x := diagonalKunnethPreimage hB X d
  set f : ℤ → ℤ := fun i ↦ (i.negOnePow : ℤ) * (Module.finrank F (W.grade X i) : ℤ) with hf
  set S := (bidegreeEquiv X x).support
  set T := (S.filter fun pq ↦ pq.1 + pq.2 = 2 * (d : ℤ)).image Prod.fst
  -- the terms of the expansion
  have hterm : ∀ pq ∈ S, W.traceProj X d hX (W.mulMapGrade X pq (bidegreeEquiv X x pq)) =
      if pq.1 + pq.2 = 2 * (d : ℤ) then ((f pq.1 : ℤ) : F) else 0 := by
    rintro ⟨p, q⟩ -
    split_ifs with h
    · obtain rfl : q = 2 * d - p := by simp only at h; omega
      rw [bidegreeEquiv_apply, traceProj_mulMapGrade_diagonalKunnethPreimage hX hA hB hC p, hf]
      push_cast
      rfl
    · exact traceProj_mulMapGrade_of_ne hX _ h _
  -- the support of `f` lies in `T`
  have hsupp : Function.support f ⊆ T := by
    intro i hi
    rw [Function.mem_support] at hi
    have hrank : (Module.finrank F (W.grade X i) : F) ≠ 0 := by
      rw [Nat.cast_ne_zero]
      intro h0
      exact hi (by rw [hf]; simp [h0])
    have hmem : (i, 2 * (d : ℤ) - i) ∈ S := by
      rw [DFinsupp.mem_support_iff]
      intro h0
      have h := traceProj_mulMapGrade_diagonalKunnethPreimage hX hA hB hC i
      rw [← bidegreeEquiv_apply, h0, map_zero, map_zero] at h
      exact hrank ((mul_eq_zero.mp h.symm).resolve_left (by
        rcases Int.units_eq_one_or (i.negOnePow) with h1 | h1 <;> simp [h1]))
    exact Finset.mem_image.mpr ⟨_, Finset.mem_filter.mpr ⟨hmem, by ring⟩, rfl⟩
  refine ⟨(T.finite_toSet).subset hsupp, ?_⟩
  rw [← kunnethMap_diagonalKunnethPreimage hB, pull_diag_kunnethMap, mulMap_eq_sum, map_sum,
    Finset.sum_congr rfl hterm, ← Finset.sum_filter, finsum_eq_sum_of_support_subset f
      (by simpa using hsupp), Int.cast_sum,
    Finset.sum_image (fun a ha b hb hab ↦ by
      rw [Finset.coe_filter] at ha hb
      exact Prod.ext hab (by have := ha.2; have := hb.2; simp only at *; omega))]


end Sum

/-! ### Stacks 0FHS -/

section Main

variable [CharZero F] (hA : W.PoincareDuality) (hB : W.Kunneth)
  (hC : W.CycleClassAxiom hA.perfectPairing) {X : (SmoothProjectiveScheme k).FullSubcategory}
  {d : ℕ} (hX : IsNonemptyEquidimensional X d)

include hA hB hC hX in
/-- **Stacks 0FHS.** Assume given (D0), (D1), (D2) and (D3) satisfying (A), (B) and (C), with `F`
of characteristic zero. Let `X` be a nonempty smooth projective scheme over `k`, equidimensional of
dimension `d`. Then

  `∑_i (-1)^i dim_F H^i(X) = deg(Δ · Δ) = deg(c_d(𝒯_{X/k}))`.

Here the sum runs over all `i ∈ ℤ` and has finite support (the first conclusion);
`Δ · Δ ∈ CH^{2d}(X × X)` is the intersection product of Stacks 0FC0
(`Stacks.Chow.codimensionIntersectionProduct`) of the class `[Δ] ∈ CH^d(X × X)` of the diagonal
with itself, and `deg : CH^{2d}(X × X) = CH_0(X × X) → ℤ` the degree of zero cycles
(`Stacks.WeilCohomology.codimensionDegree`, Stacks 0AZ1); `c_d(𝒯_{X/k}) ∈ A^d(X)` is the `d`-th
Chern class (Stacks 0ESW) of the tangent sheaf `𝒯_{X/k} = 𝓗om(Ω_{X/k}, 𝒪_X)`
(`Stacks.WeilCohomology.SmoothProjectiveScheme.tangentSheaf`), and its degree is that of the
zero cycle class `c_d(𝒯_{X/k}) ∩ [X]` (`Stacks.Chow.zeroDegree`).

The proof is the source's. On the right, `[Δ] · [Δ] = Δ_*(Δ^![Δ])` (Stacks 0FFE), `Δ_*` preserves
degrees, and `Δ^![Δ] = c_d(𝒩) ∩ [X]` for the normal sheaf `𝒩 = 𝒞_{Δ}^∨ = 𝒯_{X/k}` (Stacks 0FV9,
the excess intersection formula for the Gysin map, with the conormal sheaf of the diagonal
`Ω_{X/k}` by Stacks 08S2): `codimensionDegree_diag_mul_diag` and
`zeroDegree_regularImmersionGysin_diag`. On the left, `deg([Δ] · [Δ]) = ∫_{X × X} γ([Δ]) ∪ γ([Δ])`
by Stacks 0FHR and (C)(c), `= ∫_X Δ^*γ([Δ])` since `γ([Δ]) = Δ_*1` (Stacks 0FHG, 0FHB), and writing
`γ([Δ]) = ∑ e_{i,j} ⊗ e'_{2d-i,j}` (Stacks 0FHH) and using Remark 0FHD this is
`∑_{i,j} ∫_X e_{i,j} ∪ e'_{2d-i,j} = ∑_i (-1)^i dim_F H^i(X)`. -/
@[stacks 0FHS "the whole lemma: for (D0)-(D3) satisfying (A), (B), (C), F of characteristic 0, \
and X nonempty smooth projective over k, equidimensional of dimension d: the Euler characteristic \
∑_i (-1)^i dim_F H^i(X) (over all i ∈ ℤ, of finite support) equals deg(Δ·Δ) for the \
intersection product of Tag 0FC0 of the class of the diagonal with itself in CH^{2d}(X × X), \
which equals deg(c_d(T_{X/k}) ∩ [X]) for the tangent sheaf T_{X/k} = Hom(Ω_{X/k}, O_X)",
  sga "7 XVI 2.1" "partial"]
theorem finsum_negOnePow_finrank_eq_codimensionDegree_diag_mul_diag :
    (Function.support fun i : ℤ ↦ (i.negOnePow : ℤ) * (Module.finrank F (W.grade X i) : ℤ)).Finite ∧
    (∑ᶠ i : ℤ, (i.negOnePow : ℤ) * (Module.finrank F (W.grade X i) : ℤ)) =
      codimensionDegree (prod X X) (d + d)
        (codimensionIntersectionProduct k (prod X X).obj.hom d d
          (closedSubschemeClass (prod X X).obj.hom (diag X).hom.left d)
          (closedSubschemeClass (prod X X).obj.hom (diag X).hom.left d)) ∧
    codimensionDegree (prod X X) (d + d)
        (codimensionIntersectionProduct k (prod X X).obj.hom d d
          (closedSubschemeClass (prod X X).obj.hom (diag X).hom.left d)
          (closedSubschemeClass (prod X X).obj.hom (diag X).hom.left d)) =
      zeroDegree k X.obj.hom (sub_self _)
        (chowCohomologyCap (fieldChowSituation k) (gysinSystemOfInvertible _) X.obj.hom d
          (totalChernOfFiniteLocallyFree (fieldChowSituation k) X.obj.hom (tangentSheaf X) d) d
          (fundamentalChowClass (fieldChowSituation k) X.obj.hom d)) := by
  obtain ⟨hfin, h⟩ := traceProj_pull_diag_eq_finsum hX hA hB hC
  refine ⟨hfin, Int.cast_injective (α := F) ?_, ?_⟩
  · rw [← h, codimensionDegree_diag_mul_diag_eq_traceProj hA hB hC hX]
  · exact (codimensionDegree_diag_mul_diag hX.relativeDimension).trans
      (zeroDegree_regularImmersionGysin_diag hX.relativeDimension)

end Main

end Stacks.WeilCohomology.WeilData

end
