module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Intersection.ProperIntersections.Defs
public import StacksFrontier.Topology.Dimension.SpecializingSurjection

/-!
# A cycle with a coefficient-one component

Let `α` be an algebraic cycle with finitely many components on a scheme and let `ξ` be a point
at which its coefficient is `1`. Then

`α = [closure {ξ}] + ∑ m_j [W_j]`

where the `W_j` are the closures of the other points of the support of `α`, each occurring with
a nonzero coefficient. This is the bookkeeping behind the displayed conclusion
`C · X = [Z] + ∑ m_j [Z_j]` of Stacks 0B0E: once the coefficient of the intersection product at
the generic point of `Z` is known to be one — which is what the étale multiplicity computation
and the local form of Stacks 0B1J give — the rest of the product is automatically a finite
integer combination of prime cycles of subvarieties distinct from `Z`, and each of them occurs in
the support of the product, hence inside `C ∩ X`.

## Main results

* `AlgebraicGeometry.AlgebraicCycle.exists_finset_eq_single_add_sum`: the decomposition, indexed
  by the points of the support.
* `AlgebraicGeometry.AlgebraicCycle.exists_finset_irreducibleCloseds_eq_single_add_sum`: the
  decomposition indexed by closed subvarieties, which is the form the display of Stacks 0B0E
  takes.
* `AlgebraicGeometry.AlgebraicCycle.intersectProperly_single_genericPoint`: proper intersection
  of two closed subvarieties is proper intersection of their prime cycles.

## Implementation notes

A prime cycle `[W]` is `Function.locallyFinsuppWithin.single` at the generic point of `W` with
coefficient one; no new definition is introduced for it, because that is how the library's
intersection-product lemmas already write it (see
`AlgebraicGeometry.TorFormula.torFormulaCycleIntersectionProduct_apply_eq_one`).

The index set is a `Finset`, so the convention that the subvarieties of the sum are pairwise
distinct is part of the statement, and the clause `m W ≠ 0` makes the convention that the
multiplicities are nonzero part of it too. The subvariety-indexed form needs the ambient space to
be sober, which a scheme is: the passage between a point and the irreducible closed subset it is
the generic point of is a bijection, so the `Finset` of points can be transported.

The decomposition says nothing about the dimensions of the `W_j`; those come from the cycle `α`
being a cycle in a fixed dimension, which is a property of the intersection product and not of
this bookkeeping.

## References

* [Stacks Project, Tag 0B0E](https://stacks.math.columbia.edu/tag/0B0E)
* [Stacks Project, Tag 0AZ9](https://stacks.math.columbia.edu/tag/0AZ9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicCycle

variable {X : Scheme.{u}}

/-- The value at `y` of a finite integer combination of prime cycles: the coefficient at `y`
when `y` is one of the points indexing the combination, and zero otherwise. -/
private theorem sum_zsmul_single_apply [DecidableEq X] (S : Finset X) (c : X → ℤ) (y : X) :
    (∑ x ∈ S, c x • Function.locallyFinsuppWithin.single x (1 : ℤ) : AlgebraicCycle X ℤ) y =
      if y ∈ S then c y else 0 := by
  classical
  simp only [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply,
    Function.locallyFinsuppWithin.coe_zsmul, Pi.smul_apply,
    Function.locallyFinsuppWithin.coe_single, Pi.single_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero]
  exact Finset.sum_ite_eq S y c

/-- The value at `y` of the prime cycle of `x`. -/
private theorem single_one_apply [DecidableEq X] (x y : X) :
    (Function.locallyFinsuppWithin.single x (1 : ℤ) : AlgebraicCycle X ℤ) y =
      if y = x then (1 : ℤ) else 0 := by
  simp only [Function.locallyFinsuppWithin.coe_single, Pi.single_apply]

/-- **A cycle with finitely many components and coefficient one at `ξ` is the prime cycle of `ξ`
plus an integer combination of the prime cycles of the other points of its support.** -/
public theorem exists_finset_eq_single_add_sum [DecidableEq X] (α : AlgebraicCycle X ℤ)
    (hα : (Function.support α).Finite) {ξ : X} (hξ : α ξ = 1) :
    ∃ S : Finset X, (↑S : Set X) ⊆ Function.support α ∧ ξ ∉ S ∧ (∀ x ∈ S, α x ≠ 0) ∧
      α = Function.locallyFinsuppWithin.single ξ (1 : ℤ) +
        ∑ x ∈ S, α x • Function.locallyFinsuppWithin.single x (1 : ℤ) := by
  classical
  refine ⟨hα.toFinset.erase ξ, fun x hx => hα.mem_toFinset.mp (Finset.mem_of_mem_erase hx),
    Finset.notMem_erase _ _,
    fun x hx => hα.mem_toFinset.mp (Finset.mem_of_mem_erase hx), ?_⟩
  refine Function.locallyFinsuppWithin.ext fun y => ?_
  rw [Function.locallyFinsuppWithin.coe_add, Pi.add_apply, sum_zsmul_single_apply,
    single_one_apply]
  by_cases hyξ : y = ξ
  · subst hyξ
    rw [if_pos rfl, if_neg (Finset.notMem_erase y _), add_zero, hξ]
  · rw [if_neg hyξ, zero_add]
    by_cases hy : α y = 0
    · rw [if_neg fun h => (hα.mem_toFinset.mp (Finset.mem_of_mem_erase h)) hy, hy]
    · rw [if_pos (Finset.mem_erase.mpr ⟨hyξ, hα.mem_toFinset.mpr hy⟩)]

/-! ### The decomposition indexed by closed subvarieties -/

/-- The generic point of the closure of a point is that point: a generic point of an irreducible
closed subset of a sober space is unique. -/
@[ega "I 1.1.14" "(ii)", ega "I 2.1.5" "partial"]
public theorem genericPoint_closureSingleton (x : X) :
    (IrreducibleCloseds.closureSingleton x).isIrreducible.genericPoint = x :=
  (IsIrreducible.isGenericPoint_genericPoint
      (IrreducibleCloseds.closureSingleton x).isIrreducible
      (IrreducibleCloseds.closureSingleton x).isClosed').eq isGenericPoint_closure

/-- An irreducible closed subset is the closure of its generic point. -/
public theorem closureSingleton_genericPoint (W : IrreducibleCloseds X) :
    IrreducibleCloseds.closureSingleton W.isIrreducible.genericPoint = W :=
  IrreducibleCloseds.ext (by
    rw [IrreducibleCloseds.coe_closureSingleton]
    exact W.isIrreducible.closure_genericPoint W.isClosed')

/-- **The decomposition `α = [Z] + ∑ m_j [W_j]` indexed by closed subvarieties.** Let `α` be a
cycle with finitely many components and let `Z` be a closed subvariety whose coefficient in `α`
is one. Then `α` is the prime cycle of `Z` plus a finite integer combination of prime cycles of
closed subvarieties distinct from `Z`, each with a nonzero coefficient and each with its generic
point in the support of `α`.

This is the display of Stacks 0B0E read off a coefficient-one statement. -/
public theorem exists_finset_irreducibleCloseds_eq_single_add_sum [DecidableEq X]
    (α : AlgebraicCycle X ℤ) (hα : (Function.support α).Finite) (Z : IrreducibleCloseds X)
    (hZ : α Z.isIrreducible.genericPoint = 1) :
    ∃ (S : Finset (IrreducibleCloseds X)) (m : IrreducibleCloseds X → ℤ),
      α = Function.locallyFinsuppWithin.single Z.isIrreducible.genericPoint (1 : ℤ) +
          ∑ W ∈ S, m W • Function.locallyFinsuppWithin.single
            W.isIrreducible.genericPoint (1 : ℤ) ∧
        Z ∉ S ∧ (∀ W ∈ S, m W ≠ 0) ∧
        ∀ W ∈ S, W.isIrreducible.genericPoint ∈ Function.support α := by
  classical
  obtain ⟨T, hTsub, hTξ, hTne, hTeq⟩ := exists_finset_eq_single_add_sum α hα hZ
  have hpoint : ∀ x : X, ∀ W : IrreducibleCloseds X,
      IrreducibleCloseds.closureSingleton x = W → W.isIrreducible.genericPoint = x :=
    fun x _ h => h ▸ genericPoint_closureSingleton x
  have hinj : ∀ x ∈ T, ∀ y ∈ T,
      IrreducibleCloseds.closureSingleton x = IrreducibleCloseds.closureSingleton y → x = y :=
    fun x _ y _ h => (hpoint x _ h).symm.trans (hpoint y _ rfl)
  have hmem : ∀ W ∈ T.image IrreducibleCloseds.closureSingleton,
      W.isIrreducible.genericPoint ∈ T := by
    intro W hW
    obtain ⟨x, hxT, hx⟩ := Finset.mem_image.mp hW
    exact hpoint x W hx ▸ hxT
  refine ⟨T.image IrreducibleCloseds.closureSingleton,
    fun W => α W.isIrreducible.genericPoint, ?_, ?_, ?_, ?_⟩
  · conv_lhs => rw [hTeq]
    congr 1
    rw [Finset.sum_image hinj]
    exact Finset.sum_congr rfl fun x _ => by simp only [genericPoint_closureSingleton]
  · exact fun hZS => hTξ (hmem Z hZS)
  · exact fun W hW => hTne _ (hmem W hW)
  · exact fun W hW => hTsub (hmem W hW)

/-- **Proper intersection of two closed subvarieties is proper intersection of their prime
cycles.** The only component occurring in the prime cycle of a closed subvariety is that
subvariety itself, so the componentwise criterion of Tag 0AZQ for the two prime cycles reduces to
the dimension criterion for the two subvarieties.

This is what turns the proper intersection of `C` and `X` constructed in the proof of Stacks
0B0E, which is a statement about the two subvarieties, into the hypothesis the intersection
product of Section 0B08 takes, which is a statement about the two cycles. -/
public theorem intersectProperly_single_genericPoint [DecidableEq X] {C D : IrreducibleCloseds X}
    (h : AlgebraicGeometry.IntersectProperly C D) :
    AlgebraicGeometry.AlgebraicCycle.IntersectProperly
      (Function.locallyFinsuppWithin.single C.isIrreducible.genericPoint (1 : ℤ))
      (Function.locallyFinsuppWithin.single D.isIrreducible.genericPoint (1 : ℤ)) := by
  have key : ∀ W E : IrreducibleCloseds X,
      (Function.locallyFinsuppWithin.single E.isIrreducible.genericPoint (1 : ℤ) :
        AlgebraicCycle X ℤ) W.isIrreducible.genericPoint ≠ 0 → W = E := by
    intro W E hW
    have hWE : W.isIrreducible.genericPoint = E.isIrreducible.genericPoint := by
      by_contra hne
      simp [hne] at hW
    rw [← closureSingleton_genericPoint W, hWE, closureSingleton_genericPoint E]
  intro W V hW hV
  rw [key W C hW, key V D hV]
  exact h

end AlgebraicGeometry.AlgebraicCycle

end
