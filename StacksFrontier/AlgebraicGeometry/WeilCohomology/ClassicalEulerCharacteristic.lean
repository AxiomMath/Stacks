module

public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalDiagonalBasis
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalDiagonalSelfIntersection
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# The Euler characteristic of a classical Weil cohomology theory

Let `H^*` be a classical Weil cohomology theory over an algebraically closed field `k`, with cycle
class maps on the Chow groups of Chapter 42
(`Stacks.WeilCohomology.ChowClassicalWeilCohomologyTheory`), and `X` a smooth projective variety of
dimension `d`. Stacks 0FH0 asserts

  `∑_{i = 0}^{2d} (-1)^i dim_F H^i(X) = deg([Δ] · [Δ]) = deg(c_d(𝒯_X) ∩ [X])`.

The second equality is Chow-theoretic and is
`Stacks.WeilCohomology.degree_diagonal_mul_eq_degree_chernCap_tangentSheaf`. This
file proves the first, as the source does: `deg([Δ] · [Δ]) = ∫_{X × X} γ([Δ]) ∪ γ([Δ])` by Stacks
0FGW and axiom (C)(c), `γ([Δ]) = δ_*1`, so this is `∫_X δ^*γ([Δ])`; through the Künneth
decomposition `γ([Δ]) = ∑ e_{i,j} ⊗ e'_{2d-i,j}` the pullback along the diagonal is the cup
product, and Stacks 0FGZ evaluates `∑_{i,j} ∫_X e_{i,j} ∪ e'_{2d-i,j}` to `∑_i (-1)^i dim H^i(X)`.

## Main results

* `Stacks.WeilCohomology.PoincareDualityPushforwardSetup.lmap_pullback_comp_kunnethMap`:
  `δ^*(p^*a ∪ q^*b) = a ∪ b`.
* `ChowClassicalWeilCohomologyTheory.integration_cycleClass_eq_codimensionDegree`:
  Stacks 0FGW in the codimension grading, `∫_Z γ(β) = deg(β)` for `β ∈ CH^{dim Z}(Z)`.
* `ChowClassicalWeilCohomologyTheory.integration_kunnethMap_cup_diagonal`:
  the trace of the cup product of the Künneth coordinates of `γ([Δ])` is the Euler characteristic.
* `ChowClassicalWeilCohomologyTheory.eulerCharacteristic_eq_degree_diagonal_mul`:
  **Stacks 0FH0**, the equality on the left.
* **Stacks 0FH0**, both equalities:
  `ChowClassicalWeilCohomologyTheory.eulerCharacteristic_eq_degree_diagonal_mul_eq_degree_chernCap`

## Implementation notes

`X × X` is any smooth projective variety `P` with projections `p, q` exhibiting it as the fibre
product of `X` with itself over `k`, as in the Künneth axiom of Stacks 0FGV, and `[Δ]` is the class
of the closed subscheme cut out by the diagonal section `δ`, as in Stacks 0FGZ. The Euler
characteristic is an integer, and the equality is stated in `ℤ`; it is proved in `F`, which has
characteristic zero.

## References

* [Stacks Project, Tag 0FH0](https://stacks.math.columbia.edu/tag/0FH0)
* [Stacks Project, Tag 0FGW](https://stacks.math.columbia.edu/tag/0FGW)
* [Stacks Project, Tag 0FGZ](https://stacks.math.columbia.edu/tag/0FGZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry DifferentialGraded Stacks.Chow
open scoped DirectSum TensorProduct

universe u v w

namespace Stacks.WeilCohomology

variable {k : Type u} [Field k] [IsAlgClosed k] {F : Type v} [Field F] [CharZero F]

namespace PoincareDualityPushforwardSetup

variable (S : PoincareDualityPushforwardSetup.{u, v, w} k F)
  {X P : (SmoothProjective k).FullSubcategory} (p q : P ⟶ X) (δ : X ⟶ P)

/-- Pullback along a section of `p` undoes pullback along `p`. -/
theorem pullback_pullback_of_comp_eq_id {f : X ⟶ P} {g : P ⟶ X} (h : f ≫ g = 𝟙 X) (i : ℤ)
    (a : (S.H X).piece i) : S.pullback f i (S.pullback g i a) = a := by
  rw [← LinearMap.comp_apply, ← S.pullback_comp, h, S.pullback_id]
  rfl

/-- **Pullback along the diagonal of the Künneth map is the cup product.** For a common section
`δ` of `p` and `q`, `δ^*(p^*a ∪ q^*b) = a ∪ b`: pullback is multiplicative and `p ∘ δ = q ∘ δ =
id`. -/
theorem lmap_pullback_comp_kunnethMap (hδp : δ ≫ p = 𝟙 X) (hδq : δ ≫ q = 𝟙 X) :
    DirectSum.lmap (fun n ↦ S.pullback δ n) ∘ₗ
        Stacks.WeilCohomology.kunnethMap (S.H X) (S.H X) (S.H P) (fun i ↦ S.pullback p i)
          (fun j ↦ S.pullback q j) =
      Stacks.WeilCohomology.kunnethMap (S.H X) (S.H X) (S.H X) (fun _ ↦ LinearMap.id)
        (fun _ ↦ LinearMap.id) := by
  refine TensorProduct.ext' fun x y ↦ ?_
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [TensorProduct.add_tmul, map_add, hx, hx']
  | of i a =>
    induction y using DirectSum.induction_on with
    | zero => simp
    | add y y' hy hy' => simp only [TensorProduct.tmul_add, map_add, hy, hy']
    | of j b =>
      rw [← DirectSum.lof_eq_of F, ← DirectSum.lof_eq_of F, LinearMap.comp_apply,
        kunnethMap_lof_tmul_lof, kunnethMap_lof_tmul_lof, DirectSum.lmap_lof, S.pullback_mul,
        S.pullback_pullback_of_comp_eq_id hδp, S.pullback_pullback_of_comp_eq_id hδq]
      rfl

end PoincareDualityPushforwardSetup

namespace ChowClassicalWeilCohomologyTheory

variable (T : ChowClassicalWeilCohomologyTheory.{u, v, w} k F)
  {X P : (SmoothProjective k).FullSubcategory} (p q : P ⟶ X)
  (hpq : IsPullback p.hom.left q.hom.left X.obj.hom X.obj.hom) (δ : X ⟶ P)
  (hδp : δ ≫ p = 𝟙 X) (hδq : δ ≫ q = 𝟙 X)

omit [IsAlgClosed k] in
/-- Transport of the codimension does not change a class, heterogeneously. -/
theorem _root_.Stacks.WeilCohomology.codimensionChowGroupCongr_heq {Z : Scheme.{u}}
    (sZ : Z ⟶ (fieldChowSituation k).S) [Smooth sZ] {i j : ℤ} (h : i = j)
    (x : codimensionChowGroup k sZ i) : codimensionChowGroupCongr sZ h x ≍ x := by
  subst h
  rfl

/-- A tensor product with a vanishing graded piece of `H^*(X)` on the left is zero. -/
theorem tensor_eq_zero_of_bounded {i : ℤ} (hi : i < 0 ∨ 2 * (T.dimension X : ℤ) < i) {j : ℤ}
    (t : (T.H X).piece i ⊗[F] (T.H X).piece j) : t = 0 := by
  induction t using TensorProduct.inductionOn with
  | tmul a b => rw [T.bounded X i hi a, TensorProduct.zero_tmul]
  | add a b ha hb => rw [ha, hb, add_zero]

include hδq in
/-- **The trace of the cup product of the Künneth coordinates of `γ([Δ])` is the Euler
characteristic.** Write `γ([Δ]) = ∑_{i, j} e_{i,j} ⊗ e'_{2d-i,j}` through the inverse of the
Künneth isomorphism; then `∑_{i,j} ∫_X e_{i,j} ∪ e'_{2d-i,j} = ∑_i (-1)^i dim H^i(X)`, the
`i`-th term being `∑_j (-1)^i` by Stacks 0FGZ. -/
theorem integration_kunnethMap_cup_diagonal :
    haveI := SmoothProjective.isClosedImmersion_of_section p δ hδp
    ((T.integration X).toLinearMap ∘ₗ
        DirectSum.component F ℤ (T.H X).piece (2 * (T.dimension X : ℤ)))
      (Stacks.WeilCohomology.kunnethMap (T.H X) (T.H X) (T.H X) (fun _ ↦ LinearMap.id)
        (fun _ ↦ LinearMap.id)
        ((T.kunnethEquiv X X P p q hpq).symm
          (DirectSum.lof F ℤ (fun n ↦ (T.H P).piece n) (2 * (T.dimension X : ℤ))
            (T.cycleClass P (T.dimension X)
              (closedSubschemeClass ((SmoothProjective.toSchemeCat k).obj P).obj.hom
                δ.hom.left (T.dimension X)))))) =
      ∑ i ∈ Finset.range (2 * T.dimension X + 1),
        (-1 : F) ^ i * (Module.finrank F ((T.H X).piece (i : ℤ)) : F) := by
  have := SmoothProjective.isClosedImmersion_of_section p δ hδp
  classical
  set d := T.dimension X
  set A := T.H X
  set x := (T.kunnethEquiv X X P p q hpq).symm
    (DirectSum.lof F ℤ (fun n ↦ (T.H P).piece n) (2 * (d : ℤ))
      (T.cycleClass P d (closedSubschemeClass ((SmoothProjective.toSchemeCat k).obj P).obj.hom
        δ.hom.left d))) with hx
  set z := TensorProduct.directSum F F (fun n : ℤ ↦ A.piece n) (fun n : ℤ ↦ A.piece n) x with hz
  set tr := (T.integration X).toLinearMap ∘ₗ DirectSum.component F ℤ A.piece (2 * (d : ℤ))
  set ψ : ∀ ij : ℤ × ℤ, A.piece ij.1 ⊗[F] A.piece ij.2 →ₗ[F] F := fun ij ↦
    tr ∘ₗ (DirectSum.lof F ℤ A.piece (ij.1 + ij.2)) ∘ₗ
      TensorProduct.lift (((A.mul ij.1 ij.2).comp LinearMap.id).compl₂ LinearMap.id) with hψ
  have hsum : tr (Stacks.WeilCohomology.kunnethMap A A A (fun _ ↦ LinearMap.id)
      (fun _ ↦ LinearMap.id) x) = ∑ ij ∈ z.support, ψ ij (z ij) := by
    change tr (DirectSum.toModule F (ℤ × ℤ) _ _ z) = _
    conv_lhs => rw [← DirectSum.sum_support_of z]
    simp only [map_sum, ← DirectSum.lof_eq_of F, DirectSum.toModule_lof]
    rfl
  -- the summands off the antidiagonal `i + j = 2d` vanish
  have hψ_ne : ∀ ij : ℤ × ℤ, ij.1 + ij.2 ≠ 2 * (d : ℤ) → ∀ t, ψ ij t = 0 := by
    intro ij h t
    exact ExternallyGradedAlgebra.traceExtension_of_ne A d (T.integration X).toLinearMap h _
  -- the coordinates in degrees outside `[0, 2d]` vanish
  have hz_out : ∀ ij : ℤ × ℤ, (ij.1 < 0 ∨ 2 * (d : ℤ) < ij.1) → z ij = 0 :=
    fun ij h ↦ T.tensor_eq_zero_of_bounded h _
  -- the antidiagonal summand of degree `i` is `(-1)^i dim H^i(X)`, by Stacks 0FGZ
  have hval : ∀ i : ℕ, ψ ((i : ℤ), 2 * (d : ℤ) - i) (z ((i : ℤ), 2 * (d : ℤ) - i)) =
      (-1 : F) ^ i * (Module.finrank F (A.piece (i : ℤ)) : F) := by
    intro i
    have := T.finite X (i : ℤ)
    set e := Module.finBasis F (A.piece (i : ℤ))
    set t := z ((i : ℤ), 2 * (d : ℤ) - i)
    set e' : Fin (Module.finrank F (A.piece (i : ℤ))) → A.piece (2 * (d : ℤ) - i) :=
      fun j ↦ TensorProduct.equivFinsuppOfBasisLeft e t j
    have hdec : t = ∑ j, e j ⊗ₜ[F] e' j := by
      conv_lhs => rw [← (TensorProduct.equivFinsuppOfBasisLeft e).symm_apply_apply t]
      rw [TensorProduct.equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum_fintype]
      simp
    have h0FGZ := T.integration_mul_diagonalKunnethCoordinate p q hpq δ hδp hδq (i : ℤ) e e'
      (by rw [← hdec]; rfl)
    have hterm : ∀ j, ψ ((i : ℤ), 2 * (d : ℤ) - i) (e j ⊗ₜ[F] e' j) = gradedSign F i := by
      intro j
      change A.traceExtension d (T.integration X).toLinearMap _
        (A.mul _ _ (e j) (e' j)) = _
      rw [ExternallyGradedAlgebra.traceExtension_of_eq _ _ _ (by omega)]
      have h := h0FGZ j j
      rw [ite_eq_left rfl, mul_one] at h
      exact h
    rw [hdec, map_sum]
    simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      gradedSign, Int.natAbs_natCast]
    ring
  -- collect the antidiagonal summands
  rw [hsum, Finset.sum_congr rfl (fun i _ ↦ (hval i).symm)]
  have hinj : Set.InjOn (fun i : ℕ ↦ ((i : ℤ), 2 * (d : ℤ) - i))
      (Finset.range (2 * d + 1) : Set ℕ) := fun a _ b _ h ↦ by
    simpa using congrArg Prod.fst h
  rw [← Finset.sum_image (f := fun ij : ℤ × ℤ ↦ ψ ij (z ij)) hinj]
  calc ∑ ij ∈ z.support, ψ ij (z ij)
      = ∑ ij ∈ z.support ∪ (Finset.range (2 * d + 1)).image
          (fun i : ℕ ↦ ((i : ℤ), 2 * (d : ℤ) - i)), ψ ij (z ij) := by
        refine Finset.sum_subset Finset.subset_union_left fun ij _ hn ↦ ?_
        rw [DFinsupp.notMem_support_iff.mp hn, map_zero]
    _ = _ := by
        refine (Finset.sum_subset Finset.subset_union_right fun ij _ hn ↦ ?_).symm
        by_cases h : ij.1 + ij.2 = 2 * (d : ℤ)
        · have hout : ij.1 < 0 ∨ 2 * (d : ℤ) < ij.1 := by
            by_contra hc
            obtain ⟨hc₁, hc₂⟩ := not_or.mp hc
            refine hn (Finset.mem_image.mpr ⟨ij.1.toNat, ?_, ?_⟩)
            · rw [Finset.mem_range]
              omega
            · ext <;> simp <;> omega
          rw [hz_out ij hout, map_zero]
        · exact hψ_ne ij h _

/-- **The trace of the cycle class of a class of top codimension is its degree** (Stacks 0FGW in
the codimension grading): for a smooth projective variety `Z` of dimension `n` and
`β ∈ CH^n(Z)`, `∫_Z γ(β) = deg(β)`, the degree being `Stacks.WeilCohomology.codimensionDegree`. -/
theorem integration_cycleClass_eq_codimensionDegree (Z : (SmoothProjective k).FullSubcategory)
    (β : (chowCycleData k).group Z (T.dimension Z)) :
    T.integration Z (T.cycleClass Z (T.dimension Z) β) =
      (codimensionDegree ((SmoothProjective.toSchemeCat k).obj Z) (T.dimension Z) β : F) := by
  have hZ : RelativeDimension ((SmoothProjective.toSchemeCat k).obj Z).obj.hom (T.dimension Z) :=
    SmoothProjective.relativeDimension_hom Z (T.dimension_eq Z)
  have := (isClopenDecomposition_dimPart
    ((SmoothProjective.toSchemeCat k).obj Z).obj.hom).isProper_ι (T.dimension Z)
  obtain ⟨α, hα⟩ : ∃ α : chowGroup (fieldChowSituation k)
      (partBase ((SmoothProjective.toSchemeCat k).obj Z).obj.hom (T.dimension Z)) 0,
      α = chowGroupDegreeEquiv _ _ (sub_self ((T.dimension Z : ℕ) : ℤ)) (β (T.dimension Z)) :=
    ⟨_, rfl⟩
  have hβ : codimensionClassOfZeroCycle (X := (SmoothProjective.toSchemeCat k).obj Z) α = β := by
    funext e
    by_cases he : e = T.dimension Z
    · subst he
      rw [codimensionClassOfZeroCycle_self, hα]
      exact eq_of_heq ((chowGroupDegreeEquiv_heq _ _ _ _).trans (chowGroupDegreeEquiv_heq _ _ _ _))
    · have : IsEmpty (dimPart ((SmoothProjective.toSchemeCat k).obj Z).obj.hom e).toScheme :=
        isEmpty_dimPart_of_ne _ hZ he
      exact @Subsingleton.elim _ (subsingleton_chowGroup_of_isEmpty _ _ _) _ _
  rw [← hβ, integration_cycleClass_codimensionClassOfZeroCycle T Z α, codimensionDegree_apply,
    codimensionClassOfZeroCycle_self, Subsingleton.elim (genericPoint (fieldChowSituation k).S)
      default]
  congr 2
  exact eq_of_heq ((chowGroupDegreeEquiv_heq _ _ _ _).trans (chowGroupDegreeEquiv_heq _ _ _ _)).symm

/-- The trace of a class of codimension `n = dim Z`, written with `n` rather than `dim Z`. -/
theorem codimensionDegree_eq_integration_cycleClass (Z : (SmoothProjective k).FullSubcategory)
    {n : ℕ} (hn : T.dimension Z = n) (β : (chowCycleData k).group Z n) :
    (codimensionDegree ((SmoothProjective.toSchemeCat k).obj Z) n β : F) =
      T.integration Z (ExternallyGraded.degreeCast (R := F) (X := (T.H Z).piece)
        (by rw [hn]) (T.cycleClass Z n β)) := by
  subst hn
  exact (T.integration_cycleClass_eq_codimensionDegree Z β).symm

include hpq hδq in
/-- **Stacks Project, Tag 0FH0**, the equality on the left: for a classical Weil cohomology theory
`H^*` and a smooth projective variety `X` of dimension `d`,
`∑_{i = 0}^{2d} (-1)^i dim_F H^i(X) = deg([Δ] · [Δ])`.

The product `X × X` is a smooth projective variety `P` with projections `p, q : P ⟶ X`
exhibiting it as the fibre product over `k`, the diagonal is `δ : X ⟶ P` with
`δ ≫ p = δ ≫ q = 𝟙`, `[Δ] ∈ CH^d(P)` is the class of the closed subscheme `δ(X)`, `·` is the
intersection product of Chapter 42 and `deg` the degree of zero cycles on
`CH^{2d}(P) = CH_0(P)` (`Stacks.WeilCohomology.codimensionDegree`).

The proof is the source's: `deg([Δ] · [Δ]) = ∫_P γ([Δ] · [Δ])` (Stacks 0FGW), which is
`∫_P γ([Δ]) ∪ δ_*1 = ∫_X δ^*γ([Δ])` by axiom (C)(c) and `γ([Δ]) = δ_*1`; writing
`γ([Δ]) = ∑ e_{i,j} ⊗ e'_{2d-i,j}` through the Künneth isomorphism, `δ^*` is the cup product, and
`∑_{i,j} ∫_X e_{i,j} ∪ e'_{2d-i,j} = ∑_i (-1)^i dim H^i(X)` by Stacks 0FGZ. -/
@[stacks 0FH0 "the equality on the left: Σ (-1)^i dim H^i(X) = deg([Δ] · [Δ])"]
theorem eulerCharacteristic_eq_degree_diagonal_mul :
    haveI := SmoothProjective.isClosedImmersion_of_section p δ hδp
    ∑ i ∈ Finset.range (2 * T.dimension X + 1),
        (-1 : ℤ) ^ i * (Module.finrank F ((T.H X).piece (i : ℤ)) : ℤ) =
      codimensionDegree ((SmoothProjective.toSchemeCat k).obj P) (T.dimension X + T.dimension X)
        (codimensionChowGroupCongr _ (by push_cast; rfl)
          ((chowCycleData k).mul (T.dimension X) (T.dimension X)
            (closedSubschemeClass ((SmoothProjective.toSchemeCat k).obj P).obj.hom δ.hom.left
              (T.dimension X))
            (closedSubschemeClass ((SmoothProjective.toSchemeCat k).obj P).obj.hom δ.hom.left
              (T.dimension X)))) := by
  have := SmoothProjective.isClosedImmersion_of_section p δ hδp
  have hdim := T.dimension_eq_add p q hpq
  set Δ := closedSubschemeClass ((SmoothProjective.toSchemeCat k).obj P).obj.hom δ.hom.left
    (T.dimension X)
  apply Int.cast_injective (α := F)
  push_cast
  refine Eq.trans ?_ (T.codimensionDegree_eq_integration_cycleClass P hdim _).symm
  -- `∫_P γ([Δ] · [Δ]) = ∫_P γ([Δ]) ∪ δ_*1 = ∫_X δ^*γ([Δ])`, by (C)(c) and `γ([Δ]) = δ_*1`
  have hcup := T.cycleClass_mul P (T.dimension X) (T.dimension X) Δ Δ
  have hargs : T.cycleClass P ((T.dimension X + T.dimension X : ℕ) : ℤ)
      (codimensionChowGroupCongr _ (by push_cast; rfl)
        ((chowCycleData k).mul (T.dimension X) (T.dimension X) Δ Δ)) ≍
      (T.H P).mul (2 * (T.dimension X : ℤ)) (2 * (T.dimension P : ℤ) - 2 * (T.dimension X : ℤ))
        (T.cycleClass P (T.dimension X) Δ)
        (T.pushforward δ (2 * (T.dimension X : ℤ))
          (ExternallyGraded.degreeCast (R := F) (X := (T.H X).piece)
            (show (0 : ℤ) = 2 * (T.dimension X : ℤ) - 2 * (T.dimension X : ℤ) by ring)
            (T.H X).one)) := by
    refine (T.cycleClass_heq P (by push_cast; rfl) (codimensionChowGroupCongr_heq _ _ _)).trans ?_
    rw [hcup, ExternallyGradedAlgebra.evenCup, LinearMap.compr₂_apply]
    refine (ExternallyGraded.degreeCast_heq (R := F) _ _).trans ?_
    exact ExternallyGradedAlgebra.mul_congr_right_heq (by rw [hdim]; push_cast; ring) _
      (T.cycleClass_diagonal_heq p q hpq δ hδp)
  refine Eq.trans ?_ (((T.H P).traceExtension_self (T.dimension P) (T.integration P).toLinearMap
    _).symm.trans ((ExternallyGradedAlgebra.traceExtension_congr _ _ _
      (by rw [hdim]; push_cast; ring) ((ExternallyGraded.degreeCast_heq (R := F) _ _).trans
        hargs)).trans
      (T.toPoincareDualityPushforwardSetup.traceExtension_mul_pushforward_one δ _))).symm
  -- `∫_X δ^*γ([Δ])` through the Künneth decomposition of `γ([Δ])`
  refine (T.integration_kunnethMap_cup_diagonal p q hpq δ hδp hδq).symm.trans ?_
  have hK := LinearMap.congr_fun (T.toPoincareDualityPushforwardSetup.lmap_pullback_comp_kunnethMap
    p q δ hδp hδq) ((T.kunnethEquiv X X P p q hpq).symm
      (DirectSum.lof F ℤ (fun n ↦ (T.H P).piece n) (2 * (T.dimension X : ℤ))
        (T.cycleClass P (T.dimension X) Δ)))
  have h1 := (T.kunnethEquiv X X P p q hpq).apply_symm_apply
    (DirectSum.lof F ℤ (fun n ↦ (T.H P).piece n) (2 * (T.dimension X : ℤ))
      (T.cycleClass P (T.dimension X) Δ))
  exact congrArg ((T.integration X).toLinearMap ∘ₗ
    DirectSum.component F ℤ (T.H X).piece (2 * (T.dimension X : ℤ)))
      ((hK.symm.trans (congrArg (DirectSum.lmap fun n ↦ T.pullback δ n) h1)).trans
        (DirectSum.lmap_lof _ _ _))

include hpq hδq in
/-- **Stacks Project, Tag 0FH0.** Let `H^*` be a classical Weil cohomology theory (Stacks 0FGV)
and `X` a smooth projective variety of dimension `d`. Then
`∑_{i = 0}^{2d} (-1)^i dim_F H^i(X) = deg([Δ] · [Δ]) = deg(c_d(𝒯_X) ∩ [X])`.

The product `X × X` is a smooth projective variety `P` with projections `p, q : P ⟶ X`
exhibiting it as the fibre product over `k`, and the diagonal is `δ : X ⟶ P` with
`δ ≫ p = δ ≫ q = 𝟙`; `[Δ]`, the intersection product, the degree and `c_d(𝒯_X) ∩ -` are those of
`ChowClassicalWeilCohomologyTheory.eulerCharacteristic_eq_degree_diagonal_mul`
(the equality on the left) and
`Stacks.WeilCohomology.degree_diagonal_mul_eq_degree_chernCap_tangentSheaf`
(the equality on the right). -/
@[stacks 0FH0]
theorem eulerCharacteristic_eq_degree_diagonal_mul_eq_degree_chernCap :
    haveI := SmoothProjective.isClosedImmersion_of_section p δ hδp
    haveI := SmoothProjectiveScheme.isFiniteLocallyFreeOfRank_tangentSheaf
      ((SmoothProjective.toSchemeCat k).obj X)
      (SmoothProjective.relativeDimension_hom X (T.dimension_eq X))
    ∑ i ∈ Finset.range (2 * T.dimension X + 1),
        (-1 : ℤ) ^ i * (Module.finrank F ((T.H X).piece (i : ℤ)) : ℤ) =
      codimensionDegree ((SmoothProjective.toSchemeCat k).obj P) (T.dimension X + T.dimension X)
        (codimensionChowGroupCongr _ (by push_cast; rfl)
          ((chowCycleData k).mul (T.dimension X) (T.dimension X)
            (closedSubschemeClass ((SmoothProjective.toSchemeCat k).obj P).obj.hom δ.hom.left
              (T.dimension X))
            (closedSubschemeClass ((SmoothProjective.toSchemeCat k).obj P).obj.hom δ.hom.left
              (T.dimension X)))) ∧
    codimensionDegree ((SmoothProjective.toSchemeCat k).obj P) (T.dimension X + T.dimension X)
        (codimensionChowGroupCongr _ (by push_cast; rfl)
          ((chowCycleData k).mul (T.dimension X) (T.dimension X)
            (closedSubschemeClass ((SmoothProjective.toSchemeCat k).obj P).obj.hom δ.hom.left
              (T.dimension X))
            (closedSubschemeClass ((SmoothProjective.toSchemeCat k).obj P).obj.hom δ.hom.left
              (T.dimension X)))) =
      chowDegree (fieldChowSituation k) (fieldChowSituation_dimensionFunction k) X.obj.hom
        default (chowGroupDegreeEquiv _ _ (sub_self (T.dimension X : ℤ))
          (GenuineChern.chernCap (fieldChowSituation k) (T.dimension X) X.obj.hom
            (SmoothProjectiveScheme.tangentSheaf ((SmoothProjective.toSchemeCat k).obj X))
            (T.dimension X) (Fin.last (T.dimension X))
            (fundamentalChowClass (fieldChowSituation k) X.obj.hom (T.dimension X)))) :=
  ⟨T.eulerCharacteristic_eq_degree_diagonal_mul p q hpq δ hδp hδq,
    degree_diagonal_mul_eq_degree_chernCap_tangentSheaf X P (T.dimension_eq X) p q hpq
      δ hδp hδq⟩

end ChowClassicalWeilCohomologyTheory

end Stacks.WeilCohomology

end
