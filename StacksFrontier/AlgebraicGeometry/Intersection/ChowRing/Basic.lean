module

public import Mathlib.Algebra.DirectSum.Ring
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapDimensionVanishing
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Transport
public import StacksFrontier.AlgebraicGeometry.Intersection.ChowRing.Transversal
public import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.MovingCycles
public import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.RationalEquivalenceProduct
public import StacksFrontier.AlgebraicGeometry.Intersection.ProperIntersections.FlatPullbackCycleProduct
public import StacksFrontier.AlgebraicGeometry.Intersection.ProperIntersections.IntersectProperlyLinear
public import StacksFrontier.AlgebraicGeometry.Intersection.ReductionToDiagonal.SubvarietyProductAssociativity
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.CycleIntersectionProductComm
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Projective

/-!
# The Chow ring of a nonsingular projective variety

Let `X` be a nonsingular projective variety over an algebraically closed field. Section 43.21 of
the source (Tag 0B0G) defines the intersection product `CH_r(X) × CH_s(X) ⟶ CH_{r+s-dim X}(X)`
by moving one factor into proper position (Tag 0B1U) and multiplying representatives by the
product of cycles of Tag 0B08; this is well defined by Tag 0B1V. The product is commutative,
associative (Tag 0B1L) and has the unit `[X]`, and `CH^*(X) = ⨁_c CH_{dim X - c}(X)` is a
commutative ring.

## Main definitions

* `Stacks.Intersection.ChowRing.chowMulFun`, `Stacks.Intersection.ChowRing.chowMul`: the
  intersection product `CH_r(X) × CH_s(X) ⟶ CH_m(X)`, `r + s = dim X + m`.
* `Stacks.Intersection.ChowRing.ChowGrade`, `Stacks.Intersection.ChowRing`: the graded
  pieces `CH^c(X)` and the Chow ring `CH^*(X)`, with its `DirectSum.GCommRing` structure.

## Main results

* `Stacks.Intersection.ChowRing.torFormulaCycleIntersectionProduct_fundamentalCycle_right` and
  `..._left`: on cycles, `α · [X] = α = [X] · α`.
* `Stacks.Intersection.ChowRing.torFormulaCycleIntersectionProduct_assoc_of_intersectProperly`:
  Tag 0B1L for cycles, by trilinearity from the case of three closed subvarieties.
* `Stacks.Intersection.ChowRing.chowMulFun_mk`: the product of two classes is the class of the
  product of any two representatives which intersect properly.
* `Stacks.Intersection.ChowRing.chowMulFun_comm`, `Stacks.Intersection.ChowRing.chowMulFun_assoc`,
  `Stacks.Intersection.ChowRing.chowMulFun_fundamentalClass`: the product on Chow groups is
  commutative, associative and unital.

## Implementation notes

Associativity on Chow groups chooses a representative of the first class meeting properly the
second representative, the third, and every irreducible component of their intersection; this
uses the moving lemma for a finite family of cycles of varying dimensions.

## References

* [Stacks Project, Tag 0B0G](https://stacks.math.columbia.edu/tag/0B0G)
* [Stacks Project, Tag 0B08](https://stacks.math.columbia.edu/tag/0B08)
* [Stacks Project, Tag 0B1U](https://stacks.math.columbia.edu/tag/0B1U)
* [Stacks Project, Tag 0B1V](https://stacks.math.columbia.edu/tag/0B1V)
* [Stacks Project, Tag 0B1L](https://stacks.math.columbia.edu/tag/0B1L)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Chow AlgebraicGeometry.TorFormula

universe u

namespace Stacks.Intersection.ChowRing

/-- The product of two prime cycles is the product of their subvarieties. -/
private theorem torFormulaCycleIntersectionProduct_single_single {K : Type u} [Field K]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of K)) [DecidableEq X] [LocallyOfFiniteType sX]
    [IsLocallyNoetherian X] [CompactSpace X] (hX : IsRegular X) (k : ℤ) (x y : X) :
    torFormulaCycleIntersectionProduct (fieldChowSituation K) sX hX k
      (Function.locallyFinsuppWithin.single x 1) (Function.locallyFinsuppWithin.single y 1) =
        torFormulaSubvarietyProductTotal (fieldChowSituation K) sX hX k x y := by
  rw [torFormulaCycleIntersectionProduct, cycleIntersectionProduct_single_single, one_mul,
    one_smul]

/-! ### Associativity of the product of cycles -/

section Associativity

variable (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} (sX : X ⟶ Spec (.of K))
  [IsVariety K sX] (hX : IsRegular X)

omit [IsAlgClosed K] [IsVariety K sX] in
/-- The product of cycles, expanded over the components of both factors. -/
theorem torFormulaCycleIntersectionProduct_eq_sum_single [DecidableEq X] [CompactSpace X]
    [LocallyOfFiniteType sX] [IsLocallyNoetherian X] (k : ℤ) (α β : AlgebraicCycle X ℤ) :
    torFormulaCycleIntersectionProduct (fieldChowSituation K) sX hX k α β =
      ∑ x ∈ (finite_support_of_compactSpace α).toFinset,
        ∑ y ∈ (finite_support_of_compactSpace β).toFinset, (α x * β y) •
          torFormulaCycleIntersectionProduct (fieldChowSituation K) sX hX k
            (Function.locallyFinsuppWithin.single x 1)
            (Function.locallyFinsuppWithin.single y 1) := by
  rw [torFormulaCycleIntersectionProduct_eq_sum _ _ _ _ (finite_support_of_compactSpace α)
    (finite_support_of_compactSpace β)]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [torFormulaCycleIntersectionProduct_single_single sX hX]

/-- The product with a cycle, expanded over the components of the second factor. -/
theorem cycleIntersectionProduct_eq_sum_single_right [DecidableEq X] [CompactSpace X]
    (prod : X → X → AlgebraicCycle X ℤ) (P γ : AlgebraicCycle X ℤ) :
    cycleIntersectionProduct prod P γ =
      ∑ w ∈ (finite_support_of_compactSpace γ).toFinset,
        γ w • cycleIntersectionProduct prod P (Function.locallyFinsuppWithin.single w 1) := by
  refine (congrArg (fun z => cycleIntersectionProduct prod P z)
    (AlgebraicCycle.eq_sum_zsmul_single (finite_support_of_compactSpace γ))).trans ?_
  rw [cycleIntersectionProduct_sum_right]
  exact Finset.sum_congr rfl fun w _ => cycleIntersectionProduct_zsmul_right _ _
    (finite_support_of_compactSpace _) (finite_support_of_compactSpace _)

/-- The product with a cycle, expanded over the components of the first factor. -/
theorem cycleIntersectionProduct_eq_sum_single_left [DecidableEq X] [CompactSpace X]
    (prod : X → X → AlgebraicCycle X ℤ) (α P : AlgebraicCycle X ℤ) :
    cycleIntersectionProduct prod α P =
      ∑ u ∈ (finite_support_of_compactSpace α).toFinset,
        α u • cycleIntersectionProduct prod (Function.locallyFinsuppWithin.single u 1) P := by
  refine (congrArg (fun z => cycleIntersectionProduct prod z P)
    (AlgebraicCycle.eq_sum_zsmul_single (finite_support_of_compactSpace α))).trans ?_
  rw [cycleIntersectionProduct_sum_left]
  exact Finset.sum_congr rfl fun w _ => cycleIntersectionProduct_zsmul_left _ _
    (finite_support_of_compactSpace _) (finite_support_of_compactSpace _)

omit [IsAlgClosed K] in
/-- The dimension of the closure of a component of a `d`-cycle is `d`. -/
theorem topologicalKrullDim_closure_of_mem_support {d : ℕ}
    (α : CycleGroup (fieldChowSituation K) sX (d : ℤ)) {x : X} (hx : α.1 x ≠ 0) :
    topologicalKrullDim (closure ({x} : Set X)) = (d : WithBot ℕ∞) :=
  ExteriorProductProjections.topologicalKrullDim_closure_of_relativeDimension_eq K sX x d
    ((mem_cyclesOfDimension_iff_forall_point (fieldChowSituation K) sX _ α.1).1 α.2 x hx)

/-- Two components of properly intersecting cycles, of dimensions `r` and `s` on a space of
dimension `n`, meet in dimension at most `r + s - n`. -/
private theorem topologicalKrullDim_inter_add_le_of_intersectProperly {X : Scheme.{u}}
    {n r s : WithBot ℕ∞} (hn : topologicalKrullDim X = n) {α β : AlgebraicCycle X ℤ} {x y : X}
    (hαβ : AlgebraicCycle.IntersectProperly α β) (hx : α x ≠ 0) (hy : β y ≠ 0)
    (hxr : topologicalKrullDim (closure ({x} : Set X)) = r)
    (hys : topologicalKrullDim (closure ({y} : Set X)) = s) :
    topologicalKrullDim ↥(closure ({x} : Set X) ∩ closure ({y} : Set X)) + n ≤ r + s := by
  subst hn hxr hys
  exact AlgebraicCycle.IntersectProperly.of_ne_zero hαβ hx hy

/-- **Stacks 0B1L for cycles.** Let `α`, `β`, `γ` be an `r`-, an `s`- and a `t`-cycle on a
nonsingular variety `X` of dimension `n` which intersect properly pairwise and such that every
triple of their components satisfies `dim (U ∩ V ∩ W) ≤ r + s + t - 2n`. Then `α` and `β · γ`
intersect properly, `α · β` and `γ` intersect properly, and `(α · β) · γ = α · (β · γ)`. By
trilinearity this is Tag 0B1L for each triple of components. -/
theorem torFormulaCycleIntersectionProduct_assoc_of_intersectProperly (n r s t : ℕ)
    (hn : topologicalKrullDim X = (n : WithBot ℕ∞))
    (α : CycleGroup (fieldChowSituation K) sX (r : ℤ))
    (β : CycleGroup (fieldChowSituation K) sX (s : ℤ))
    (γ : CycleGroup (fieldChowSituation K) sX (t : ℤ))
    (hαβ : AlgebraicCycle.IntersectProperly α.1 β.1)
    (hβγ : AlgebraicCycle.IntersectProperly β.1 γ.1)
    (hαγ : AlgebraicCycle.IntersectProperly α.1 γ.1)
    (htriple : ∀ u v w : X, α.1 u ≠ 0 → β.1 v ≠ 0 → γ.1 w ≠ 0 →
      topologicalKrullDim
          (↥(closure ({u} : Set X) ∩ closure ({v} : Set X) ∩ closure ({w} : Set X))) +
        ((2 * n : ℕ) : WithBot ℕ∞) ≤ ((r + s + t : ℕ) : WithBot ℕ∞)) :
    letI : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
    AlgebraicCycle.IntersectProperly α.1
        (torFormulaCycleIntersectionProduct (fieldChowSituation K) sX hX ((s : ℤ) + t - n)
          β.1 γ.1) ∧
      AlgebraicCycle.IntersectProperly
        (torFormulaCycleIntersectionProduct (fieldChowSituation K) sX hX ((r : ℤ) + s - n)
          α.1 β.1) γ.1 ∧
      torFormulaCycleIntersectionProduct (fieldChowSituation K) sX hX ((r : ℤ) + s + t - 2 * n)
          (torFormulaCycleIntersectionProduct (fieldChowSituation K) sX hX ((r : ℤ) + s - n)
            α.1 β.1) γ.1 =
        torFormulaCycleIntersectionProduct (fieldChowSituation K) sX hX ((r : ℤ) + s + t - 2 * n)
          α.1 (torFormulaCycleIntersectionProduct (fieldChowSituation K) sX hX
            ((s : ℤ) + t - n) β.1 γ.1) := by
  classical
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  set Sα := (finite_support_of_compactSpace α.1).toFinset
  set Sβ := (finite_support_of_compactSpace β.1).toFinset
  set Sγ := (finite_support_of_compactSpace γ.1).toFinset
  have mα : ∀ {u}, u ∈ Sα → α.1 u ≠ 0 := fun h => (Set.Finite.mem_toFinset _).1 h
  have mβ : ∀ {u}, u ∈ Sβ → β.1 u ≠ 0 := fun h => (Set.Finite.mem_toFinset _).1 h
  have mγ : ∀ {u}, u ∈ Sγ → γ.1 u ≠ 0 := fun h => (Set.Finite.mem_toFinset _).1 h
  have key : ∀ u ∈ Sα, ∀ v ∈ Sβ, ∀ w ∈ Sγ,
      AlgebraicCycle.IntersectProperly (Function.locallyFinsuppWithin.single u (1 : ℤ))
          (torFormulaCycleIntersectionProduct (fieldChowSituation K) sX hX ((s : ℤ) + t - n)
            (Function.locallyFinsuppWithin.single v 1)
            (Function.locallyFinsuppWithin.single w 1)) ∧
        AlgebraicCycle.IntersectProperly
          (torFormulaCycleIntersectionProduct (fieldChowSituation K) sX hX ((r : ℤ) + s - n)
            (Function.locallyFinsuppWithin.single u 1)
            (Function.locallyFinsuppWithin.single v 1))
          (Function.locallyFinsuppWithin.single w (1 : ℤ)) ∧
        torFormulaCycleIntersectionProduct (fieldChowSituation K) sX hX ((r : ℤ) + s + t - 2 * n)
            (torFormulaCycleIntersectionProduct (fieldChowSituation K) sX hX ((r : ℤ) + s - n)
              (Function.locallyFinsuppWithin.single u 1)
              (Function.locallyFinsuppWithin.single v 1))
            (Function.locallyFinsuppWithin.single w 1) =
          torFormulaCycleIntersectionProduct (fieldChowSituation K) sX hX
            ((r : ℤ) + s + t - 2 * n) (Function.locallyFinsuppWithin.single u 1)
            (torFormulaCycleIntersectionProduct (fieldChowSituation K) sX hX ((s : ℤ) + t - n)
              (Function.locallyFinsuppWithin.single v 1)
              (Function.locallyFinsuppWithin.single w 1)) := by
    intro u hu v hv w hw
    have hu' := topologicalKrullDim_closure_of_mem_support K sX α (mα hu)
    have hv' := topologicalKrullDim_closure_of_mem_support K sX β (mβ hv)
    have hw' := topologicalKrullDim_closure_of_mem_support K sX γ (mγ hw)
    have huv := AlgebraicCycle.IntersectProperly.of_ne_zero hαβ (mα hu) (mβ hv)
    have hvw := AlgebraicCycle.IntersectProperly.of_ne_zero hβγ (mβ hv) (mγ hw)
    have huw := AlgebraicCycle.IntersectProperly.of_ne_zero hαγ (mα hu) (mγ hw)
    obtain ⟨h1, h2, h3⟩ :=
      Stacks.Intersection.ReductionToDiagonal.torFormulaCycleIntersectionProduct_assoc
      K sX hX u v w n r s t hn hu' hv' hw' huv hvw huw (htriple u v w (mα hu) (mβ hv) (mγ hw))
    have ePvw : torFormulaCycleIntersectionProduct (fieldChowSituation K) sX hX ((s : ℤ) + t - n)
        (Function.locallyFinsuppWithin.single v 1) (Function.locallyFinsuppWithin.single w 1) =
        torSubvarietyProductOfBound (fieldChowSituation K) sX hX ((s : ℤ) + t - n)
          (Stacks.Intersection.ReductionToDiagonal.torSupportBound_of_intersectProperly_of_eq K sX
            hX v w hn hv' hw' hvw) := by
      rw [torFormulaCycleIntersectionProduct_single_single sX hX,
        torFormulaSubvarietyProductTotal_eq_of_bound]
    have eQuv : torFormulaCycleIntersectionProduct (fieldChowSituation K) sX hX ((r : ℤ) + s - n)
        (Function.locallyFinsuppWithin.single u 1) (Function.locallyFinsuppWithin.single v 1) =
        torSubvarietyProductOfBound (fieldChowSituation K) sX hX ((r : ℤ) + s - n)
          (Stacks.Intersection.ReductionToDiagonal.torSupportBound_of_intersectProperly_of_eq K sX
            hX u v hn hu' hv' huv) := by
      rw [torFormulaCycleIntersectionProduct_single_single sX hX,
        torFormulaSubvarietyProductTotal_eq_of_bound]
    rw [ePvw, eQuv]
    exact ⟨h1, h2, h3.symm⟩
  have hβγ_exp := torFormulaCycleIntersectionProduct_eq_sum_single K sX hX ((s : ℤ) + t - n)
    β.1 γ.1
  have hαβ_exp := torFormulaCycleIntersectionProduct_eq_sum_single K sX hX ((r : ℤ) + s - n)
    α.1 β.1
  refine ⟨?_, ?_, ?_⟩
  · rw [hβγ_exp]
    refine AlgebraicCycle.intersectProperly_sum_right _ _ fun v hv =>
      AlgebraicCycle.intersectProperly_sum_right _ _ fun w hw =>
      AlgebraicCycle.intersectProperly_zsmul_right _ ?_
    intro W V hW hV
    have hW' : α.1 W.isIrreducible.genericPoint ≠ 0 := hW
    have hmem : W.isIrreducible.genericPoint ∈ Sα := (Set.Finite.mem_toFinset _).2 hW'
    refine (key _ hmem v hv w hw).1 W V ?_ hV
    simp
  · rw [hαβ_exp]
    refine AlgebraicCycle.intersectProperly_sum_left _ _ fun u hu =>
      AlgebraicCycle.intersectProperly_sum_left _ _ fun v hv =>
      AlgebraicCycle.intersectProperly_zsmul_left _ ?_
    intro W V hW hV
    have hV' : γ.1 V.isIrreducible.genericPoint ≠ 0 := hV
    have hmem : V.isIrreducible.genericPoint ∈ Sγ := (Set.Finite.mem_toFinset _).2 hV'
    refine (key u hu v hv _ hmem).2.1 W V hW ?_
    simp
  · rw [hαβ_exp, hβγ_exp, torFormulaCycleIntersectionProduct, cycleIntersectionProduct_sum_left,
      torFormulaCycleIntersectionProduct, cycleIntersectionProduct_sum_right]
    have hL : ∀ u ∈ Sα, cycleIntersectionProduct
        (torFormulaSubvarietyProductTotal (fieldChowSituation K) sX hX ((r : ℤ) + s + t - 2 * n))
        (∑ v ∈ Sβ, (α.1 u * β.1 v) •
          torFormulaCycleIntersectionProduct (fieldChowSituation K) sX hX ((r : ℤ) + s - n)
            (Function.locallyFinsuppWithin.single u 1) (Function.locallyFinsuppWithin.single v 1))
        γ.1 = ∑ v ∈ Sβ, ∑ w ∈ Sγ, (α.1 u * β.1 v * γ.1 w) •
          torFormulaCycleIntersectionProduct (fieldChowSituation K) sX hX ((r : ℤ) + s + t - 2 * n)
            (torFormulaCycleIntersectionProduct (fieldChowSituation K) sX hX ((r : ℤ) + s - n)
              (Function.locallyFinsuppWithin.single u 1) (Function.locallyFinsuppWithin.single v 1))
            (Function.locallyFinsuppWithin.single w 1) := by
      intro u _
      rw [cycleIntersectionProduct_sum_left]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [cycleIntersectionProduct_zsmul_left _ _ (finite_support_of_compactSpace _)
        (finite_support_of_compactSpace _), cycleIntersectionProduct_eq_sum_single_right,
        Finset.smul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [smul_smul]
      rfl
    have hR : ∀ v ∈ Sβ, cycleIntersectionProduct
        (torFormulaSubvarietyProductTotal (fieldChowSituation K) sX hX ((r : ℤ) + s + t - 2 * n))
        α.1 (∑ w ∈ Sγ, (β.1 v * γ.1 w) •
          torFormulaCycleIntersectionProduct (fieldChowSituation K) sX hX ((s : ℤ) + t - n)
            (Function.locallyFinsuppWithin.single v 1) (Function.locallyFinsuppWithin.single w 1))
        = ∑ w ∈ Sγ, ∑ u ∈ Sα, (α.1 u * β.1 v * γ.1 w) •
          torFormulaCycleIntersectionProduct (fieldChowSituation K) sX hX ((r : ℤ) + s + t - 2 * n)
            (Function.locallyFinsuppWithin.single u 1)
            (torFormulaCycleIntersectionProduct (fieldChowSituation K) sX hX ((s : ℤ) + t - n)
              (Function.locallyFinsuppWithin.single v 1)
              (Function.locallyFinsuppWithin.single w 1)) := by
      intro v _
      rw [cycleIntersectionProduct_sum_right]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [cycleIntersectionProduct_zsmul_right _ _ (finite_support_of_compactSpace _)
        (finite_support_of_compactSpace _), cycleIntersectionProduct_eq_sum_single_left,
        Finset.smul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [smul_smul]
      congr 1
      ring
    rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hR]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun w hw => Finset.sum_congr rfl fun u hu => ?_
    rw [(key u hu v hv w hw).2.2]

end Associativity

/-! ### Components of closed subsets -/

section Components

variable {T : Type*} [TopologicalSpace T] [TopologicalSpace.NoetherianSpace T] [QuasiSober T]

/-- In a Noetherian quasi-sober space a closed subset is covered by the closures of finitely many
of its points, namely the generic points of its irreducible components. -/
theorem exists_finset_closure_cover {S : Set T} (hS : IsClosed S) :
    ∃ F : Finset T, (∀ x ∈ F, closure ({x} : Set T) ⊆ S) ∧ S ⊆ ⋃ x ∈ F, closure ({x} : Set T) := by
  classical
  obtain ⟨A, hA, hSA⟩ := TopologicalSpace.NoetherianSpace.exists_finset_irreducible ⟨S, hS⟩
  refine ⟨A.attach.image fun k => (hA k).genericPoint, ?_, ?_⟩
  · intro x hx
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hx
    rw [(hA k).isGenericPoint_genericPoint k.1.isClosed]
    have hle : k.1 ≤ A.sup id := Finset.le_sup (f := id) k.2
    rw [← hSA] at hle
    exact hle
  · intro y hy
    have hy' : y ∈ ((A.sup id : TopologicalSpace.Closeds T) : Set T) := by
      rw [← hSA]; exact hy
    rw [TopologicalSpace.Closeds.coe_finset_sup, Finset.sup_set_eq_biUnion] at hy'
    obtain ⟨k, hk, hyk⟩ := Set.mem_iUnion₂.1 hy'
    refine Set.mem_iUnion₂.2 ⟨(hA ⟨k, hk⟩).genericPoint,
      Finset.mem_image.2 ⟨⟨k, hk⟩, Finset.mem_attach _ _, rfl⟩, ?_⟩
    rw [(hA ⟨k, hk⟩).isGenericPoint_genericPoint k.isClosed]
    exact hyk

omit [NoetherianSpace T] [QuasiSober T] in
/-- **The dimension count behind Tag 0B1L.** Let `X` have dimension `n`, let `U`, `V`, `W` have
dimensions `r`, `s`, `t` with `V` and `W` meeting properly, and let `V ∩ W` be covered by the
closed subsets `T_x`, each contained in `V ∩ W` and each meeting `U` properly. Then
`dim (U ∩ V ∩ W) + 2n ≤ r + s + t`. -/
theorem topologicalKrullDim_inter_inter_add_le [QuasiSober T] (n : WithBot ℕ∞)
    {U V W : Set T} (r s t : WithBot ℕ∞) (F : Finset T)
    (hcover : V ∩ W ⊆ ⋃ x ∈ F, closure ({x} : Set T))
    (hsub : ∀ x ∈ F, closure ({x} : Set T) ⊆ V ∩ W)
    (hU : IsClosed U) (hV : IsClosed V) (hW : IsClosed W)
    (hVW : topologicalKrullDim ↥(V ∩ W) + n ≤ s + t)
    (hUx : ∀ x ∈ F, topologicalKrullDim ↥(U ∩ closure ({x} : Set T)) + n ≤
      r + topologicalKrullDim (closure ({x} : Set T))) :
    topologicalKrullDim ↥(U ∩ V ∩ W) + (n + n) ≤ r + (s + t) := by
  classical
  set f : T → WithBot ℕ∞ := fun x => topologicalKrullDim ↥((U ∩ V ∩ W) ∩ closure ({x} : Set T))
  have hpiece : ∀ x ∈ F, f x + (n + n) ≤ r + (s + t) := by
    intro x hx
    calc f x + (n + n) ≤ topologicalKrullDim ↥(U ∩ closure ({x} : Set T)) + n + n := by
          rw [add_assoc]
          exact add_le_add (topologicalKrullDim_le_of_subset fun z hz => ⟨hz.1.1.1, hz.2⟩) le_rfl
      _ ≤ r + topologicalKrullDim (closure ({x} : Set T)) + n := add_le_add (hUx x hx) le_rfl
      _ ≤ r + (topologicalKrullDim ↥(V ∩ W) + n) := by
          rw [add_assoc]
          exact add_le_add le_rfl (add_le_add (topologicalKrullDim_le_of_subset (hsub x hx)) le_rfl)
      _ ≤ r + (s + t) := add_le_add le_rfl hVW
  have hle : topologicalKrullDim ↥(U ∩ V ∩ W) ≤ F.sup f :=
    topologicalKrullDim_le_of_subset_biUnion F ((hU.inter hV).inter hW)
      (fun _ => isClosed_closure) (fun z hz => hcover ⟨hz.1.2, hz.2⟩)
      fun x hx => Finset.le_sup (f := f) hx
  refine le_trans (add_le_add hle le_rfl) ?_
  rcases F.eq_empty_or_nonempty with hF | hF
  · rw [hF, Finset.sup_empty, WithBot.bot_add]
    exact bot_le
  · obtain ⟨x, hx, hxf⟩ := Finset.exists_mem_eq_sup F hF f
    rw [hxf]
    exact hpiece x hx

end Components

/-! ### The unit -/

section Unit

variable (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} (sX : X ⟶ Spec (.of K))
  [IsVariety K sX] (hX : IsRegular X)

/-- **The fundamental cycle is a unit for the product of cycles**: `α · [X] = α` for every
`r`-cycle `α` on a nonsingular variety `X` of dimension `n`. -/
theorem torFormulaCycleIntersectionProduct_fundamentalCycle_right (n : ℕ)
    (hn : topologicalKrullDim X = (n : WithBot ℕ∞)) (r : ℤ)
    (α : CycleGroup (fieldChowSituation K) sX r) :
    letI : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
    torFormulaCycleIntersectionProduct (fieldChowSituation K) sX hX r α.1
        (cycleAssociatedToClosedSubscheme (fieldChowSituation K) sX (𝟙 X) (n : ℤ)).1 = α.1 := by
  classical
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have hα : (Function.support α.1).Finite := finite_support_of_compactSpace α.1
  have hdim0 : topologicalKrullDim X = topologicalKrullDim X + ((0 : ℕ) : WithBot ℕ∞) := by
    simp
  have hprime : ∀ v ∈ hα.toFinset,
      torFormulaCycleIntersectionProduct (fieldChowSituation K) sX hX r
          (cycleAssociatedToClosedSubscheme (fieldChowSituation K) sX
            (integralComponentAt v).subschemeι r).1
          (cycleAssociatedToClosedSubscheme (fieldChowSituation K) sX (𝟙 X) (n : ℤ)).1 =
        (cycleAssociatedToClosedSubscheme (fieldChowSituation K) sX
          (integralComponentAt v).subschemeι r).1 := by
    intro v hv
    have hvd : relativeDimension (fieldChowSituation K).dimensionFunction sX v = r :=
      (mem_cyclesOfDimension_iff_forall_point (fieldChowSituation K) sX r α.1).1 α.2 v
        (hα.mem_toFinset.1 hv)
    obtain ⟨d, rfl⟩ : ∃ d : ℕ, r = (d : ℤ) :=
      ⟨r.toNat, by
        have := relativeDimension_nonneg (fieldChowSituation K) (fun _ _ => rfl) sX v
        omega⟩
    have hsupp : topologicalKrullDim ((integralComponentAt v).support : Set X) ≤
        (d : WithBot ℕ∞) := by
      rw [coe_support_integralComponentAt,
        ExteriorProductProjections.topologicalKrullDim_closure_of_relativeDimension_eq K sX v d
          hvd]
    have h := torFormulaCycleIntersectionProduct_comap_closedImmersion K sX sX sX (𝟙 X)
      (Category.id_comp sX) (𝟙 X) (Category.id_comp sX) hX n n 0 0 d hn hn hdim0 hdim0
      (integralComponentAt v) hsupp
    rw [Category.comp_id, Scheme.IdealSheafData.comap_id, Nat.add_zero] at h
    rw [h, properPushforward_id]
  rw [congrArg Subtype.val (cycle_eq_sum_zsmul_primeCycles α hα)]
  simp only [AddSubgroup.val_finsetSum, AddSubgroup.coe_zsmul]
  rw [torFormulaCycleIntersectionProduct, cycleIntersectionProduct_sum_left]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [cycleIntersectionProduct_zsmul_left _ _ (finite_support_of_compactSpace _)
    (finite_support_of_compactSpace _)]
  exact congrArg _ (hprime v hv)

/-- **The fundamental cycle is a unit for the product of cycles**: `[X] · α = α`. -/
theorem torFormulaCycleIntersectionProduct_fundamentalCycle_left (n : ℕ)
    (hn : topologicalKrullDim X = (n : WithBot ℕ∞)) (r : ℤ)
    (α : CycleGroup (fieldChowSituation K) sX r) :
    letI : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
    torFormulaCycleIntersectionProduct (fieldChowSituation K) sX hX r
        (cycleAssociatedToClosedSubscheme (fieldChowSituation K) sX (𝟙 X) (n : ℤ)).1 α.1 =
      α.1 := by
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  rw [torFormulaCycleIntersectionProduct_comm]
  exact torFormulaCycleIntersectionProduct_fundamentalCycle_right K sX hX n hn r α

end Unit

/-! ### The intersection product on Chow groups -/

section ChowProduct

variable (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} (sX : X ⟶ Spec (.of K))
  [IsProjectiveVariety K sX] (hX : IsRegular X)

/-! #### The product of representatives -/

/-- The product `α · β` of two cycles, as a cycle of dimension `m`. -/
def mulCycle (m : ℤ) (α β : AlgebraicCycle X ℤ) : CycleGroup (fieldChowSituation K) sX m :=
  letI : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
  ⟨torFormulaCycleIntersectionProduct (fieldChowSituation K) sX hX m α β,
    torFormulaCycleIntersectionProduct_mem_cyclesOfDimension (fieldChowSituation K) sX hX m α β⟩

omit [IsAlgClosed K] in
/-- The underlying cycle of `mulCycle` is the product of cycles. -/
@[simp]
theorem coe_mulCycle (m : ℤ) (α β : AlgebraicCycle X ℤ) :
    letI : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
    (mulCycle K sX hX m α β).1 =
      torFormulaCycleIntersectionProduct (fieldChowSituation K) sX hX m α β := rfl

omit [IsAlgClosed K] in
/-- `mulCycle` is additive in the first factor: subtraction. -/
theorem mulCycle_sub_left (m : ℤ) (α α' β : AlgebraicCycle X ℤ) :
    mulCycle K sX hX m (α - α') β = mulCycle K sX hX m α β - mulCycle K sX hX m α' β := by
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  exact Subtype.ext (map_sub (cycleIntersectionProductLeftHom
    (torFormulaSubvarietyProductTotal (fieldChowSituation K) sX hX m) β) α α')

omit [IsAlgClosed K] in
/-- `mulCycle` is additive in the first factor: addition. -/
theorem mulCycle_add_left (m : ℤ) (α α' β : AlgebraicCycle X ℤ) :
    mulCycle K sX hX m (α + α') β = mulCycle K sX hX m α β + mulCycle K sX hX m α' β := by
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  exact Subtype.ext (map_add (cycleIntersectionProductLeftHom
    (torFormulaSubvarietyProductTotal (fieldChowSituation K) sX hX m) β) α α')

omit [IsAlgClosed K] in
/-- `mulCycle` is commutative. -/
theorem mulCycle_comm (m : ℤ) (α β : AlgebraicCycle X ℤ) :
    mulCycle K sX hX m α β = mulCycle K sX hX m β α := by
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  exact Subtype.ext (torFormulaCycleIntersectionProduct_comm _ _ _ _ _ _)

variable {K sX hX}

/-- **Tag 0B1V, read on classes.** Two representatives of the same class which both meet `β`
properly have rationally equivalent products with `β`. -/
theorem mk_mulCycle_eq_of_rationallyEquivalent {n : ℕ}
    (hn : topologicalKrullDim X = (n : WithBot ℕ∞)) {r s m : ℤ} (hm : r + s = n + m)
    {α α' : CycleGroup (fieldChowSituation K) sX r} (β : CycleGroup (fieldChowSituation K) sX s)
    (hαα' : RationallyEquivalent (fieldChowSituation K) sX r α α')
    (hα : AlgebraicCycle.IntersectProperly α.1 β.1)
    (hα' : AlgebraicCycle.IntersectProperly α'.1 β.1) :
    QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation K) sX m)
        (mulCycle K sX hX m α.1 β.1) =
      QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation K) sX m)
        (mulCycle K sX hX m α'.1 β.1) := by
  obtain rfl : m = r + s - n := by omega
  rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_iff_sub_mem,
    ← mulCycle_sub_left]
  exact torFormulaCycleIntersectionProduct_mem_rationalEquivalences K sX hX hn (α - α') β
    (AlgebraicCycle.intersectProperly_sub_left hα hα') hαα'

/-- Two rationally equivalent cycles both meeting `α` properly have rationally
equivalent products with `α`. -/
theorem mk_mulCycle_eq_of_rationallyEquivalent_right {n : ℕ}
    (hn : topologicalKrullDim X = (n : WithBot ℕ∞)) {r s m : ℤ} (hm : r + s = n + m)
    (α : CycleGroup (fieldChowSituation K) sX r) {β β' : CycleGroup (fieldChowSituation K) sX s}
    (hββ' : RationallyEquivalent (fieldChowSituation K) sX s β β')
    (hβ : AlgebraicCycle.IntersectProperly α.1 β.1)
    (hβ' : AlgebraicCycle.IntersectProperly α.1 β'.1) :
    QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation K) sX m)
        (mulCycle K sX hX m α.1 β.1) =
      QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation K) sX m)
        (mulCycle K sX hX m α.1 β'.1) := by
  rw [mulCycle_comm, mulCycle_comm K sX hX m α.1 β'.1]
  exact mk_mulCycle_eq_of_rationallyEquivalent hn (by omega) α hββ'
    (Stacks.Intersection.ReductionToDiagonal.cycle_intersectProperly_symm hβ)
    (Stacks.Intersection.ReductionToDiagonal.cycle_intersectProperly_symm hβ')

variable (K sX hX)

/-- **Stacks 0B0G: the intersection product on Chow groups**
`CH_r(X) × CH_s(X) ⟶ CH_m(X)`, `r + s = dim X + m`. Represent the second class by a cycle `β`
and the first by a cycle `α` meeting `β` properly, which Tag 0B1U provides, and take the class of
`α · β`; by Tag 0B1V this does not depend on the choices
(`chowMul_mk`). -/
def chowMulFun (m : ℤ) {r s : ℤ} (a : chowGroup (fieldChowSituation K) sX r)
    (b : chowGroup (fieldChowSituation K) sX s) : chowGroup (fieldChowSituation K) sX m :=
  QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation K) sX m)
    (mulCycle K sX hX m
      (exists_rationallyEquivalent_forall_intersectProperly K sX hX
        (QuotientAddGroup.mk_surjective a).choose _
        (fun _ : Unit => (QuotientAddGroup.mk_surjective b).choose)).choose.1
      (QuotientAddGroup.mk_surjective b).choose.1)

variable {K sX hX}

/-- **The product of classes is the class of the product of representatives meeting properly.**
For cycles `α` and `β` which intersect properly, `[α] · [β] = [α · β]`. -/
theorem chowMulFun_mk {n : ℕ} (hn : topologicalKrullDim X = (n : WithBot ℕ∞)) {r s m : ℤ}
    (hm : r + s = n + m) (α : CycleGroup (fieldChowSituation K) sX r)
    (β : CycleGroup (fieldChowSituation K) sX s)
    (hαβ : AlgebraicCycle.IntersectProperly α.1 β.1) :
    chowMulFun K sX hX m (QuotientAddGroup.mk' _ α) (QuotientAddGroup.mk' _ β) =
      QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation K) sX m)
        (mulCycle K sX hX m α.1 β.1) := by
  set a := QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation K) sX r) α
  set b := QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation K) sX s) β
  set α₀ := (QuotientAddGroup.mk_surjective a).choose with hα₀
  set β₀ := (QuotientAddGroup.mk_surjective b).choose with hβ₀
  have hα₀a : QuotientAddGroup.mk' _ α₀ = a := (QuotientAddGroup.mk_surjective a).choose_spec
  have hβ₀b : QuotientAddGroup.mk' _ β₀ = b := (QuotientAddGroup.mk_surjective b).choose_spec
  obtain ⟨hα₁, hα₁β⟩ := (exists_rationallyEquivalent_forall_intersectProperly K sX hX α₀ _
    (fun _ : Unit => β₀)).choose_spec
  set α₁ := (exists_rationallyEquivalent_forall_intersectProperly K sX hX α₀ _
    (fun _ : Unit => β₀)).choose with hα₁def
  change QuotientAddGroup.mk' _ (mulCycle K sX hX m α₁.1 β₀.1) = _
  obtain ⟨γ, hγ, hγβ⟩ :=
    exists_rationallyEquivalent_forall_intersectProperly K sX hX α _ (![β, β₀])
  have hγβ' : AlgebraicCycle.IntersectProperly γ.1 β.1 := hγβ 0
  have hγβ₀ : AlgebraicCycle.IntersectProperly γ.1 β₀.1 := hγβ 1
  have hα₀α : RationallyEquivalent (fieldChowSituation K) sX r α₀ α :=
    (QuotientAddGroup.eq_iff_sub_mem).1 hα₀a
  have hβ₀β : RationallyEquivalent (fieldChowSituation K) sX s β₀ β :=
    (QuotientAddGroup.eq_iff_sub_mem).1 hβ₀b
  have hα₁γ : RationallyEquivalent (fieldChowSituation K) sX r α₁ γ := by
    change α₁ - γ ∈ _
    have : α₁ - γ = (α₁ - α₀) + (α₀ - α) - (γ - α) := by abel
    rw [this]
    exact sub_mem (add_mem hα₁ hα₀α) hγ
  have hγα : RationallyEquivalent (fieldChowSituation K) sX r γ α := hγ
  rw [mk_mulCycle_eq_of_rationallyEquivalent hn hm β₀ hα₁γ (hα₁β ()) hγβ₀,
    mk_mulCycle_eq_of_rationallyEquivalent_right hn hm γ hβ₀β hγβ₀ hγβ',
    mk_mulCycle_eq_of_rationallyEquivalent hn hm β hγα hγβ' hαβ]

include hX in
/-- Every class has a representative meeting finitely many given cycles properly: Tag 0B1U. -/
theorem exists_mk_eq_intersectProperly {r : ℤ} (a : chowGroup (fieldChowSituation K) sX r)
    {ι : Type*} [Finite ι] {s : ι → ℤ} (β : ∀ i, CycleGroup (fieldChowSituation K) sX (s i)) :
    ∃ α : CycleGroup (fieldChowSituation K) sX r,
      QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation K) sX r) α = a ∧
        ∀ i, AlgebraicCycle.IntersectProperly α.1 (β i).1 := by
  obtain ⟨α₀, rfl⟩ := QuotientAddGroup.mk'_surjective _ a
  obtain ⟨α, hα, hαβ⟩ := exists_rationallyEquivalent_forall_intersectProperly K sX hX α₀ _ β
  exact ⟨α, (QuotientAddGroup.eq_iff_sub_mem).2 hα, hαβ⟩

/-- The intersection product on Chow groups is additive in the first factor. -/
theorem chowMulFun_add_left {n : ℕ} (hn : topologicalKrullDim X = (n : WithBot ℕ∞))
    {r s m : ℤ} (hm : r + s = n + m) (a₁ a₂ : chowGroup (fieldChowSituation K) sX r)
    (b : chowGroup (fieldChowSituation K) sX s) :
    chowMulFun K sX hX m (a₁ + a₂) b = chowMulFun K sX hX m a₁ b + chowMulFun K sX hX m a₂ b := by
  obtain ⟨β, rfl⟩ := QuotientAddGroup.mk'_surjective _ b
  obtain ⟨α₁, rfl, h₁⟩ := exists_mk_eq_intersectProperly (hX := hX) a₁ (fun _ : Unit => β)
  obtain ⟨α₂, rfl, h₂⟩ := exists_mk_eq_intersectProperly (hX := hX) a₂ (fun _ : Unit => β)
  rw [← map_add,
    chowMulFun_mk hn hm _ _ (AlgebraicCycle.intersectProperly_add_left (h₁ ()) (h₂ ())),
    chowMulFun_mk hn hm _ _ (h₁ ()), chowMulFun_mk hn hm _ _ (h₂ ()), ← map_add]
  exact congrArg _ (mulCycle_add_left K sX hX m α₁.1 α₂.1 β.1)

/-- The intersection product on Chow groups is commutative. -/
theorem chowMulFun_comm {n : ℕ} (hn : topologicalKrullDim X = (n : WithBot ℕ∞))
    {r s m : ℤ} (hm : r + s = n + m) (a : chowGroup (fieldChowSituation K) sX r)
    (b : chowGroup (fieldChowSituation K) sX s) :
    chowMulFun K sX hX m a b = chowMulFun K sX hX m b a := by
  obtain ⟨β, rfl⟩ := QuotientAddGroup.mk'_surjective _ b
  obtain ⟨α, rfl, h⟩ := exists_mk_eq_intersectProperly (hX := hX) a (fun _ : Unit => β)
  rw [chowMulFun_mk hn hm _ _ (h ()), chowMulFun_mk hn (by omega) _ _
    (Stacks.Intersection.ReductionToDiagonal.cycle_intersectProperly_symm (h ())),
    mulCycle_comm]

/-- The intersection product on Chow groups is additive in the second factor. -/
theorem chowMulFun_add_right {n : ℕ} (hn : topologicalKrullDim X = (n : WithBot ℕ∞))
    {r s m : ℤ} (hm : r + s = n + m) (a : chowGroup (fieldChowSituation K) sX r)
    (b₁ b₂ : chowGroup (fieldChowSituation K) sX s) :
    chowMulFun K sX hX m a (b₁ + b₂) = chowMulFun K sX hX m a b₁ + chowMulFun K sX hX m a b₂ := by
  rw [chowMulFun_comm hn hm, chowMulFun_add_left hn (by omega), chowMulFun_comm hn (by omega) b₁,
    chowMulFun_comm hn (by omega) b₂]

variable (K sX hX)

/-- **Stacks 0B0G: the intersection product** `CH_r(X) × CH_s(X) ⟶ CH_m(X)` on the Chow groups
of a nonsingular projective variety `X` of dimension `n`, for `r + s = n + m`, as a biadditive
map. -/
def chowMul {n : ℕ} (hn : topologicalKrullDim X = (n : WithBot ℕ∞)) {r s m : ℤ}
    (hm : r + s = n + m) :
    chowGroup (fieldChowSituation K) sX r →+ chowGroup (fieldChowSituation K) sX s →+
      chowGroup (fieldChowSituation K) sX m :=
  AddMonoidHom.mk' (fun a => AddMonoidHom.mk' (chowMulFun K sX hX m a)
      (chowMulFun_add_right hn hm a))
    fun a₁ a₂ => AddMonoidHom.ext fun b => chowMulFun_add_left hn hm a₁ a₂ b

variable {K sX hX}

/-- `chowMul` applied to two classes is `chowMulFun`. -/
@[simp]
theorem chowMul_apply {n : ℕ} (hn : topologicalKrullDim X = (n : WithBot ℕ∞)) {r s m : ℤ}
    (hm : r + s = n + m) (a : chowGroup (fieldChowSituation K) sX r)
    (b : chowGroup (fieldChowSituation K) sX s) :
    chowMul K sX hX hn hm a b = chowMulFun K sX hX m a b := rfl

omit [IsAlgClosed K] in
/-- **Cycles with disjoint components have zero product.** -/
theorem torFormulaCycleIntersectionProduct_eq_zero_of_disjoint {n : ℕ}
    (hn : topologicalKrullDim X = (n : WithBot ℕ∞)) (m : ℤ) {α β : AlgebraicCycle X ℤ}
    (h : ∀ x y : X, α x ≠ 0 → β y ≠ 0 → closure ({x} : Set X) ∩ closure ({y} : Set X) = ∅) :
    letI : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
    torFormulaCycleIntersectionProduct (fieldChowSituation K) sX hX m α β = 0 := by
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  rw [torFormulaCycleIntersectionProduct_eq_sum _ _ _ _ (finite_support_of_compactSpace α)
    (finite_support_of_compactSpace β)]
  refine Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun y hy => ?_
  rw [ReductionToDiagonal.torFormulaSubvarietyProductTotal_eq_zero_of_inter_eq_empty
    K sX hX hn m (h x y ((Set.Finite.mem_toFinset _).1 hx) ((Set.Finite.mem_toFinset _).1 hy)),
    smul_zero]

omit [IsAlgClosed K] in
/-- Two cycles meeting properly in negative expected dimension have disjoint components. -/
theorem inter_eq_empty_of_intersectProperly {n : ℕ} (hn : topologicalKrullDim X = (n : WithBot ℕ∞))
    {r s : ℕ} (hrs : r + s < n) (α : CycleGroup (fieldChowSituation K) sX (r : ℤ))
    (β : CycleGroup (fieldChowSituation K) sX (s : ℤ))
    (hαβ : AlgebraicCycle.IntersectProperly α.1 β.1) {x y : X} (hx : α.1 x ≠ 0)
    (hy : β.1 y ≠ 0) : closure ({x} : Set X) ∩ closure ({y} : Set X) = ∅ := by
  have hxy := topologicalKrullDim_inter_add_le_of_intersectProperly hn hαβ hx hy
    (topologicalKrullDim_closure_of_mem_support K sX α hx)
    (topologicalKrullDim_closure_of_mem_support K sX β hy)
  by_contra hne
  have hne' : Nonempty ↥(closure ({x} : Set X) ∩ closure ({y} : Set X)) :=
    Set.nonempty_coe_sort.2 (Set.nonempty_iff_ne_empty.2 hne)
  have hbot : topologicalKrullDim ↥(closure ({x} : Set X) ∩ closure ({y} : Set X)) ≠ ⊥ := by
    intro h0
    exact (not_isEmpty_iff.2 hne') ((topologicalKrullDim_eq_bot_iff_isEmpty _).1 h0)
  obtain ⟨c, hc⟩ := WithBot.ne_bot_iff_exists.1 hbot
  rw [← hc] at hxy
  have : ((c + n : ℕ∞) : WithBot ℕ∞) ≤ ((r + s : ℕ) : WithBot ℕ∞) := by
    push_cast at hxy ⊢; exact hxy
  have h' : c + n ≤ (r + s : ℕ) := by exact_mod_cast this
  have h'' : (n : ℕ∞) ≤ (r + s : ℕ) := le_trans le_add_self h'
  have : n ≤ r + s := by exact_mod_cast h''
  omega

omit [IsAlgClosed K] in
/-- **The product of two cycles is supported on the intersections of their components.** -/
theorem exists_mem_closure_inter_of_torFormulaCycleIntersectionProduct_ne_zero {n : ℕ}
    (hn : topologicalKrullDim X = (n : WithBot ℕ∞)) (m : ℤ) {α β : AlgebraicCycle X ℤ}
    {z : X}
    (hz : letI : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
      torFormulaCycleIntersectionProduct (fieldChowSituation K) sX hX m α β z ≠ 0) :
    ∃ x y : X, α x ≠ 0 ∧ β y ≠ 0 ∧ z ∈ closure ({x} : Set X) ∩ closure ({y} : Set X) := by
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  rw [torFormulaCycleIntersectionProduct, cycleIntersectionProduct_apply _
    (finite_support_of_compactSpace α) (finite_support_of_compactSpace β)] at hz
  obtain ⟨x, hx, hx'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
  obtain ⟨y, hy, hy'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx'
  refine ⟨x, y, (Set.Finite.mem_toFinset _).1 hx, (Set.Finite.mem_toFinset _).1 hy, ?_⟩
  by_contra hxy
  exact hy' (by rw [torFormulaSubvarietyProductTotal_apply_eq_zero_of_notMem_inter
    (fieldChowSituation K) sX hX m x y n hn.le hxy, mul_zero])

/-! #### The unit -/

omit [IsAlgClosed K] in
/-- The fundamental cycle `[X]` meets every cycle properly. -/
theorem intersectProperly_fundamentalCycle_left {n : ℕ}
    (_hn : topologicalKrullDim X = (n : WithBot ℕ∞)) (β : AlgebraicCycle X ℤ) :
    AlgebraicCycle.IntersectProperly
      (cycleAssociatedToClosedSubscheme (fieldChowSituation K) sX (𝟙 X) (n : ℤ)).1 β := by
  have : IsIntegral X := IsVariety.toIsIntegral (k := K) (f := sX)
  intro W V hW _
  have hWgen : W.isIrreducible.genericPoint = (𝟙 X : X ⟶ X).base (genericPoint X) := by
    by_contra hne
    exact hW (cycleAssociatedToClosedSubscheme_isIntegral_apply_of_ne (fieldChowSituation K) sX
      (𝟙 X) _ hne)
  have hWset : (W : Set X) = Set.univ := by
    rw [CycleFlatPullback.coe_eq_closure_genericPoint W, hWgen]
    exact genericPoint_spec X
  rw [AlgebraicGeometry.intersectProperly_iff, hWset, Set.univ_inter, add_comm]
  refine add_le_add_left (le_of_eq ?_) _
  exact (IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ X).isHomeomorph).symm

/-- **The unit of the Chow ring**: `[X] · a = a`. -/
theorem chowMulFun_fundamentalClass {n : ℕ} (hn : topologicalKrullDim X = (n : WithBot ℕ∞))
    {r : ℤ} (a : chowGroup (fieldChowSituation K) sX r) :
    chowMulFun K sX hX r (QuotientAddGroup.mk' _
      (cycleAssociatedToClosedSubscheme (fieldChowSituation K) sX (𝟙 X) (n : ℤ))) a = a := by
  obtain ⟨α, rfl⟩ := QuotientAddGroup.mk'_surjective _ a
  rw [chowMulFun_mk hn (by omega) _ _ (intersectProperly_fundamentalCycle_left (K := K) hn α.1)]
  congr 1
  exact Subtype.ext (torFormulaCycleIntersectionProduct_fundamentalCycle_left K sX hX n hn r α)

/-! #### Associativity -/

variable (K sX) in
/-- The prime cycle `[closure {x}]`, in the dimension of `closure {x}`. -/
def primeCycle [DecidableEq X] (x : X) :
    CycleGroup (fieldChowSituation K) sX
      (relativeDimension (fieldChowSituation K).dimensionFunction sX x) :=
  ⟨Function.locallyFinsuppWithin.single x 1, by
    refine (mem_cyclesOfDimension_iff_forall_point _ _ _ _).2 fun y hy => ?_
    by_cases h : y = x
    · rw [h]
    · exact absurd (by rw [Function.locallyFinsuppWithin.single_apply, ite_eq_right h]) hy⟩

/-- `0 · b = 0` on Chow groups. -/
theorem chowMulFun_zero_left {n : ℕ} (hn : topologicalKrullDim X = (n : WithBot ℕ∞))
    {r s m : ℤ} (hm : r + s = n + m) (b : chowGroup (fieldChowSituation K) sX s) :
    chowMulFun K sX hX m (0 : chowGroup (fieldChowSituation K) sX r) b = 0 := by
  have h := chowMulFun_add_left (hX := hX) hn hm 0 0 b
  rw [add_zero] at h
  exact (add_eq_left.1 h.symm)

/-- `a · 0 = 0` on Chow groups. -/
theorem chowMulFun_zero_right {n : ℕ} (hn : topologicalKrullDim X = (n : WithBot ℕ∞))
    {r s m : ℤ} (hm : r + s = n + m) (a : chowGroup (fieldChowSituation K) sX r) :
    chowMulFun K sX hX m a (0 : chowGroup (fieldChowSituation K) sX s) = 0 := by
  rw [chowMulFun_comm hn hm, chowMulFun_zero_left hn (by omega)]

/-- **Associativity of the intersection product on Chow groups**: `(a · b) · c = a · (b · c)`
(Tag 0B1L). -/
theorem chowMulFun_assoc {n : ℕ} (hn : topologicalKrullDim X = (n : WithBot ℕ∞))
    {r s t m₁ m₂ m : ℤ} (h₁ : r + s = n + m₁) (h₂ : s + t = n + m₂) (h : m₁ + t = n + m)
    (a : chowGroup (fieldChowSituation K) sX r) (b : chowGroup (fieldChowSituation K) sX s)
    (c : chowGroup (fieldChowSituation K) sX t) :
    chowMulFun K sX hX m (chowMulFun K sX hX m₁ a b) c =
      chowMulFun K sX hX m a (chowMulFun K sX hX m₂ b c) := by
  classical
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsNoetherian X := ⟨⟩
  have : JacobsonSpace (fieldChowSituation K).S :=
    inferInstanceAs (JacobsonSpace (Spec (CommRingCat.of K)))
  have hneg : ∀ {k : ℤ}, k < 0 → ∀ x : chowGroup (fieldChowSituation K) sX k, x = 0 :=
    fun hk x => Stacks.Chow.chowGroup_eq_zero_of_neg (fieldChowSituation K) (fun _ _ => rfl) sX
      hk x
  by_cases hr : r < 0
  · rw [hneg hr a, chowMulFun_zero_left hn h₁, chowMulFun_zero_left hn h,
      chowMulFun_zero_left hn (by omega)]
  by_cases hs : s < 0
  · rw [hneg hs b, chowMulFun_zero_right hn h₁, chowMulFun_zero_left hn h,
      chowMulFun_zero_left hn h₂, chowMulFun_zero_right hn (by omega)]
  by_cases ht : t < 0
  · rw [hneg ht c, chowMulFun_zero_right hn h, chowMulFun_zero_right hn h₂,
      chowMulFun_zero_right hn (by omega)]
  obtain ⟨r', rfl⟩ : ∃ r' : ℕ, r = r' := ⟨r.toNat, by omega⟩
  obtain ⟨s', rfl⟩ : ∃ s' : ℕ, s = s' := ⟨s.toNat, by omega⟩
  obtain ⟨t', rfl⟩ : ∃ t' : ℕ, t = t' := ⟨t.toNat, by omega⟩
  obtain rfl : m₁ = (r' : ℤ) + s' - n := by omega
  obtain rfl : m₂ = (s' : ℤ) + t' - n := by omega
  obtain rfl : m = (r' : ℤ) + s' + t' - 2 * n := by omega
  obtain ⟨γ, rfl⟩ := QuotientAddGroup.mk'_surjective _ c
  obtain ⟨β, rfl, hβ⟩ := exists_mk_eq_intersectProperly (hX := hX) b (fun _ : Unit => γ)
  have hβγ : AlgebraicCycle.IntersectProperly β.1 γ.1 := hβ ()
  set Sβ := (finite_support_of_compactSpace β.1).toFinset
  set Sγ := (finite_support_of_compactSpace γ.1).toFinset
  choose F hFsub hFcover using fun v w : X =>
    exists_finset_closure_cover (isClosed_closure.inter isClosed_closure :
      IsClosed (closure ({v} : Set X) ∩ closure ({w} : Set X)))
  set G : Finset X := Sβ ∪ Sγ ∪ (Sβ ×ˢ Sγ).biUnion fun p => F p.1 p.2
  obtain ⟨α, rfl, hα⟩ := exists_mk_eq_intersectProperly (hX := hX) a
    (fun x : G => primeCycle K sX x.1)
  have hαx : ∀ x ∈ G, AlgebraicCycle.IntersectProperly α.1
      (Function.locallyFinsuppWithin.single x (1 : ℤ)) := fun x hx => hα ⟨x, hx⟩
  have hαβ : AlgebraicCycle.IntersectProperly α.1 β.1 :=
    AlgebraicCycle.intersectProperly_of_forall_single fun v hv => hαx v (by
      simp only [G, Finset.mem_union]
      exact Or.inl (Or.inl ((Set.Finite.mem_toFinset _).2 hv)))
  have hαγ : AlgebraicCycle.IntersectProperly α.1 γ.1 :=
    AlgebraicCycle.intersectProperly_of_forall_single fun w hw => hαx w (by
      simp only [G, Finset.mem_union]
      exact Or.inl (Or.inr ((Set.Finite.mem_toFinset _).2 hw)))
  have htriple : ∀ u v w : X, α.1 u ≠ 0 → β.1 v ≠ 0 → γ.1 w ≠ 0 →
      topologicalKrullDim
          (↥(closure ({u} : Set X) ∩ closure ({v} : Set X) ∩ closure ({w} : Set X))) +
        ((2 * n : ℕ) : WithBot ℕ∞) ≤ ((r' + s' + t' : ℕ) : WithBot ℕ∞) := by
    intro u v w hu hv hw
    have hu' := topologicalKrullDim_closure_of_mem_support K sX α hu
    have hv' := topologicalKrullDim_closure_of_mem_support K sX β hv
    have hw' := topologicalKrullDim_closure_of_mem_support K sX γ hw
    have hvw := topologicalKrullDim_inter_add_le_of_intersectProperly hn hβγ hv hw hv' hw'
    have key := topologicalKrullDim_inter_inter_add_le (U := closure ({u} : Set X))
      (n : WithBot ℕ∞) (r' : WithBot ℕ∞)
      (s' : WithBot ℕ∞) (t' : WithBot ℕ∞) (F v w) (hFcover v w) (hFsub v w) isClosed_closure
      isClosed_closure isClosed_closure hvw (fun x hx => by
        have hxG : x ∈ G := by
          simp only [G, Finset.mem_union, Finset.mem_biUnion, Finset.mem_product]
          exact Or.inr ⟨(v, w), ⟨(Set.Finite.mem_toFinset _).2 hv,
            (Set.Finite.mem_toFinset _).2 hw⟩, hx⟩
        exact topologicalKrullDim_inter_add_le_of_intersectProperly hn (hαx x hxG) hu
          (by rw [Function.locallyFinsuppWithin.single_apply, ite_eq_left rfl]; exact one_ne_zero)
          hu' rfl)
    convert key using 2 <;> push_cast <;> ring
  obtain ⟨hA1, hA2, hA3⟩ := torFormulaCycleIntersectionProduct_assoc_of_intersectProperly K sX hX
    n r' s' t' hn α β γ hαβ hβγ hαγ htriple
  rw [chowMulFun_mk hn h₁ α β hαβ, chowMulFun_mk hn h₂ β γ hβγ,
    chowMulFun_mk hn (by omega) (mulCycle K sX hX _ α.1 β.1) γ hA2,
    chowMulFun_mk hn (by omega) α (mulCycle K sX hX _ β.1 γ.1) hA1]
  exact congrArg _ (Subtype.ext hA3)

/-- **The unit of the Chow ring**, in any degree equal to `dim X`: `[X] · a = a`. -/
theorem chowMulFun_fundamentalClass_of_eq {n : ℕ} (hn : topologicalKrullDim X = (n : WithBot ℕ∞))
    {k r : ℤ} (hk : k = n) (a : chowGroup (fieldChowSituation K) sX r) :
    chowMulFun K sX hX r (QuotientAddGroup.mk' _
      (cycleAssociatedToClosedSubscheme (fieldChowSituation K) sX (𝟙 X) k)) a = a := by
  subst hk
  exact chowMulFun_fundamentalClass hn a

/-- Changing the degree a product is formed in, along an equality of degrees, is a heterogeneous
equality. -/
theorem chowMulFun_heq {m m' : ℤ} (h : m = m') {r s : ℤ}
    (a : chowGroup (fieldChowSituation K) sX r) (b : chowGroup (fieldChowSituation K) sX s) :
    HEq (chowMulFun K sX hX m a b) (chowMulFun K sX hX m' a b) := by
  subst h; rfl

/-- The product does not depend on how the degrees of its arguments are spelled. -/
theorem chowMulFun_congr_heq {m r r' s s' : ℤ} (hr : r = r') (hs : s = s')
    {a : chowGroup (fieldChowSituation K) sX r} {a' : chowGroup (fieldChowSituation K) sX r'}
    {b : chowGroup (fieldChowSituation K) sX s} {b' : chowGroup (fieldChowSituation K) sX s'}
    (ha : a ≍ a') (hb : b ≍ b') :
    chowMulFun K sX hX m a b = chowMulFun K sX hX m a' b' := by
  subst hr hs
  rw [eq_of_heq ha, eq_of_heq hb]

end ChowProduct

/-! ### The Chow ring -/

section ChowRing

variable (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} (sX : X ⟶ Spec (.of K))
  [IsProjectiveVariety K sX] (hX : IsRegular X) (n : ℕ)
  (hn : topologicalKrullDim X = (n : WithBot ℕ∞))

/-- The Chow group `CH^c(X) = CH_{n - c}(X)` of cycles of codimension `c` on a variety of
dimension `n` (Chow Homology, Section 0FE2), the `c`-th graded piece of the Chow ring. -/
abbrev ChowGrade (_hX : IsRegular X) (_hn : topologicalKrullDim X = (n : WithBot ℕ∞)) (c : ℕ) :
    Type u :=
  chowGroup (fieldChowSituation K) sX ((n : ℤ) - c)

/-- The unit of the Chow ring: the class `[X] ∈ CH^0(X)`. -/
instance : GradedMonoid.GOne (ChowGrade K sX n hX hn) where
  one := QuotientAddGroup.mk' _
    (cycleAssociatedToClosedSubscheme (fieldChowSituation K) sX (𝟙 X) ((n : ℤ) - (0 : ℕ)))

/-- The graded multiplication `CH^i(X) × CH^j(X) ⟶ CH^{i+j}(X)`: the intersection product. -/
instance : GradedMonoid.GMul (ChowGrade K sX n hX hn) where
  mul {i j} a b := chowMulFun K sX hX ((n : ℤ) - ((i + j : ℕ) : ℤ)) a b

omit [IsAlgClosed K] in
/-- The unit of the Chow ring is the class of `X`. -/
theorem chowGrade_one_def :
    (GradedMonoid.GOne.one : ChowGrade K sX n hX hn 0) = QuotientAddGroup.mk' _
      (cycleAssociatedToClosedSubscheme (fieldChowSituation K) sX (𝟙 X) ((n : ℤ) - (0 : ℕ))) :=
  rfl

/-- The graded multiplication of the Chow ring is the intersection product. -/
theorem chowGrade_mul_def {i j : ℕ} (a : ChowGrade K sX n hX hn i)
    (b : ChowGrade K sX n hX hn j) :
    GradedMonoid.GMul.mul a b = chowMulFun K sX hX ((n : ℤ) - ((i + j : ℕ) : ℤ)) a b :=
  rfl

/-- The graded pieces of the Chow ring form a graded commutative monoid. -/
instance : GradedMonoid.GCommMonoid (ChowGrade K sX n hX hn) where
  one_mul a := by
    obtain ⟨i, a⟩ := a
    refine Sigma.ext (zero_add i) ?_
    change HEq (chowMulFun K sX hX ((n : ℤ) - ((0 + i : ℕ) : ℤ)) _ a) a
    have h₁ : ((n : ℤ) - ((0 + i : ℕ) : ℤ)) = n - i := by push_cast; ring
    have h₂ : ((n : ℤ) - ((0 : ℕ) : ℤ)) = n := by push_cast; ring
    refine (chowMulFun_heq h₁ _ _).trans (heq_of_eq ?_)
    exact chowMulFun_fundamentalClass_of_eq hn h₂ a
  mul_one a := by
    obtain ⟨i, a⟩ := a
    refine Sigma.ext (add_zero i) ?_
    change HEq (chowMulFun K sX hX ((n : ℤ) - ((i + 0 : ℕ) : ℤ)) a _) a
    have h₁ : ((n : ℤ) - ((i + 0 : ℕ) : ℤ)) = n - i := by push_cast; ring
    have h₂ : ((n : ℤ) - ((0 : ℕ) : ℤ)) = n := by push_cast; ring
    refine (chowMulFun_heq h₁ _ _).trans (heq_of_eq ?_)
    rw [chowMulFun_comm hn (by simp only [GradedMonoid.fst_one]; push_cast; ring)]
    exact chowMulFun_fundamentalClass_of_eq hn h₂ a
  mul_assoc a b c := by
    obtain ⟨i, a⟩ := a
    obtain ⟨j, b⟩ := b
    obtain ⟨k, c⟩ := c
    refine Sigma.ext (add_assoc i j k) ?_
    change HEq (chowMulFun K sX hX ((n : ℤ) - ((i + j + k : ℕ) : ℤ))
      (chowMulFun K sX hX ((n : ℤ) - ((i + j : ℕ) : ℤ)) a b) c)
      (chowMulFun K sX hX ((n : ℤ) - ((i + (j + k) : ℕ) : ℤ)) a
        (chowMulFun K sX hX ((n : ℤ) - ((j + k : ℕ) : ℤ)) b c))
    refine (heq_of_eq (chowMulFun_assoc hn (by push_cast; ring) (by push_cast; ring)
      (by push_cast; ring) a b c)).trans (chowMulFun_heq (by push_cast; ring) _ _)
  mul_comm a b := by
    obtain ⟨i, a⟩ := a
    obtain ⟨j, b⟩ := b
    refine Sigma.ext (add_comm i j) ?_
    change HEq (chowMulFun K sX hX ((n : ℤ) - ((i + j : ℕ) : ℤ)) a b)
      (chowMulFun K sX hX ((n : ℤ) - ((j + i : ℕ) : ℤ)) b a)
    rw [chowMulFun_comm hn (by push_cast; ring)]
    exact chowMulFun_heq (by push_cast; ring) _ _

/-- The graded pieces of the Chow ring form a graded commutative ring. -/
instance : DirectSum.GCommRing (ChowGrade K sX n hX hn) where
  mul_zero {i j} a := chowMulFun_zero_right hn (by push_cast; ring) a
  zero_mul {i j} b := chowMulFun_zero_left hn (by push_cast; ring) b
  mul_add {i j} a b c := chowMulFun_add_right hn (by push_cast; ring) a b c
  add_mul {i j} a b c := chowMulFun_add_left hn (by push_cast; ring) a b c
  natCast m := m • GradedMonoid.GOne.one
  natCast_zero := zero_smul _ _
  natCast_succ m := succ_nsmul _ m
  intCast m := m • GradedMonoid.GOne.one
  intCast_ofNat m := natCast_zsmul _ m
  intCast_negSucc_ofNat m := negSucc_zsmul _ m

/-- **Stacks 0B0G: the Chow ring** `CH^*(X) = ⨁_c CH^c(X)` of a nonsingular projective variety
`X` of dimension `n`, with the intersection product. It is a commutative ring with unit
`[X] ∈ CH^0(X)`. -/
abbrev _root_.Stacks.Intersection.ChowRing : Type u := DirectSum ℕ (ChowGrade K sX n hX hn)

end ChowRing

end Stacks.Intersection.ChowRing

end
