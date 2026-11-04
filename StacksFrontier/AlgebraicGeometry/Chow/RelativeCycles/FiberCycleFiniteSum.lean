module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.BaseChangeSubintegral

/-!
# A cycle on a fibre of a quasi-compact morphism is a finite sum of points

A cycle in this library is a *locally* finite formal sum: `Stacks.Chow.FiberCycleGroup f s r` sits
inside `AlgebraicGeometry.AlgebraicCycle (f.fiber s) ℤ`, which is
`Function.locallyFinsupp (f.fiber s) ℤ`, and local finiteness alone does not let one write such a
cycle as a `Finset`-indexed sum. Over a *fibre* of a quasi-compact morphism it does: the fibre is
a compact space, so the support of the cycle is finite and the cycle is the finite sum of its
singleton components.

This is the finiteness step with which the integral case of
[Tag 0H59](https://stacks.math.columbia.edu/tag/0H59) opens: writing the member `α_η` of a
relative `r`-cycle at the generic point of the base as `∑ᵢ nᵢ [Yᵢ]`. In Tag 0H59 `f` is of finite
type, hence quasi-compact.

## Main definitions

* `Stacks.Chow.fiberCycleSingle` — the cycle `[x]` on a fibre, for `x` a point of relative
  dimension `r`: the point `x` with coefficient one.
* `Stacks.Chow.fiberCycleComponent` — the singleton component of a given cycle at a point: the
  cycle `[x]` when `x` carries a nonzero coefficient, and `0` otherwise.

## Main results

* `Stacks.Chow.finite_support_fiberCycle` — the support of a cycle on a fibre of a quasi-compact
  morphism is finite.
* `Stacks.Chow.relativeDimension_of_fiberCycle_apply_ne_zero` — a point carrying a nonzero
  coefficient of an `r`-cycle on a fibre has relative dimension `r`.
* `Stacks.Chow.coe_fiberCycle_eq_sum_single` — the decomposition at the level of coefficients:
  the underlying algebraic cycle is a `Finset`-indexed sum of singleton indicator functions.
* `Stacks.Chow.fiberCycle_eq_sum_fiberCycleComponent` — **the decomposition**: a cycle on a fibre
  of a quasi-compact morphism is the sum, over its finite support, of its coefficients times its
  singleton components, as an identity in `Stacks.Chow.FiberCycleGroup`.
* `Stacks.Chow.exists_finset_fiberCycle_eq_sum_fiberCycleSingle` — the same read as an existence
  statement: there are a finite set of points, each of relative dimension `r`, and integer
  coefficients, with the cycle equal to the corresponding finite sum of `[x]`'s.

## Implementation notes

The finiteness comes from `Function.LocallyFiniteSupport.finite_inter_support_of_isCompact`
applied with `W = Set.univ`; the compactness of the fibre is the Mathlib instance
`CompactSpace (f.fiber s)` for `[QuasiCompact f]`, so `QuasiCompact f` is the only hypothesis
added beyond those needed to speak of `Stacks.Chow.FiberCycleGroup` at all. On `X` itself the
support of a cycle is only locally finite, so the statements here are about one fibre.

`Function.locallyFinsuppWithin.single` carries a `DecidableEq` instance argument. Decidability of
equality on the points of a scheme is not available, so the definitions below are classical, and
the lemmas describing `Stacks.Chow.fiberCycleSingle` are split into the value at the point and
the value away from it rather than stated with an `if`, so that no `Decidable` instance appears
in any statement.

## What is not done here

The decomposition is of the *cycle*, into singleton components indexed by points. It is not
turned into a decomposition into `Stacks.Chow.HilbertCycleDatum`s or into closed subschemes of
the ambient scheme `X`: that step — taking the closure in `X` of the integral closed subscheme of
the fibre cut out by a point of the support, and feeding the result to generic flatness — is part
of the integral case of Tag 0H59 and is not carried out here. In particular
`Stacks.Chow.fiberCycleSingle` is *not* identified with
`Stacks.Chow.cycleAssociatedToClosedSubscheme` of the reduced closure of `{x}`; that the two
agree, i.e. that the component multiplicity of a reduced closure at its own generic point is one,
is a separate statement and is not proved here.

## References

* [Stacks Project, Lemma 0H59](https://stacks.math.columbia.edu/tag/0H59)
* [Stacks Project, Section 0H4U](https://stacks.math.columbia.edu/tag/0H4U)
* [Stacks Project, Definition 02QR](https://stacks.math.columbia.edu/tag/02QR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (s : S) (r : ℕ)

/-! ### Finiteness of the support -/

/-- The support of a cycle on a fibre of a quasi-compact morphism is finite. -/
theorem finite_support_fiberCycle [QuasiCompact f] (c : FiberCycleGroup f s r) :
    (Function.support (c : AlgebraicCycle (f.fiber s) ℤ)).Finite := by
  simpa using (c : AlgebraicCycle (f.fiber s) ℤ).locallyFiniteSupport
    |>.finite_inter_support_of_isCompact (W := Set.univ) isCompact_univ

/-- A point carrying a nonzero coefficient of an `r`-cycle on a fibre has relative dimension `r`
over the residue field of the base point. -/
theorem relativeDimension_of_fiberCycle_apply_ne_zero (c : FiberCycleGroup f s r)
    {x : f.fiber s} (hx : (c : AlgebraicCycle (f.fiber s) ℤ) x ≠ 0) :
    relativeDimension (fieldChowSituation (S.residueField s)).dimensionFunction
      (f.fiberToSpecResidueField s) x = (r : ℤ) :=
  of_not_not fun h ↦ hx (fiberCycleGroup_apply_eq_zero f s r c x h)

/-! ### The singleton cycles -/

/-- The cycle `[x]` on a fibre: the point `x`, which must have relative dimension `r`, with
coefficient one. -/
def fiberCycleSingle (x : f.fiber s)
    (hx : relativeDimension (fieldChowSituation (S.residueField s)).dimensionFunction
      (f.fiberToSpecResidueField s) x = (r : ℤ)) :
    FiberCycleGroup f s r := by
  classical
  haveI : LocallyOfFiniteType (f.fiberToSpecResidueField s) := by
    change LocallyOfFiniteType (pullback.snd f (S.fromSpecResidueField s))
    infer_instance
  refine ⟨Function.locallyFinsuppWithin.single x 1, ?_⟩
  rw [mem_cyclesOfDimension_iff_forall_point]
  intro y hy
  have hyx : y = x := by
    by_contra h
    simp only [Function.locallyFinsuppWithin.single_apply, h, ite_false, ne_eq,
      not_true_eq_false] at hy
  exact hyx ▸ hx

/-- The underlying algebraic cycle of `Stacks.Chow.fiberCycleSingle` is the singleton indicator
at the chosen point. -/
theorem coe_fiberCycleSingle (x : f.fiber s)
    (hx : relativeDimension (fieldChowSituation (S.residueField s)).dimensionFunction
      (f.fiberToSpecResidueField s) x = (r : ℤ)) :
    letI := Classical.decEq (f.fiber s)
    (fiberCycleSingle f s r x hx : AlgebraicCycle (f.fiber s) ℤ) =
      Function.locallyFinsuppWithin.single x 1 :=
  rfl

/-- The cycle `[x]` has coefficient one at `x`. -/
theorem fiberCycleSingle_apply_self (x : f.fiber s)
    (hx : relativeDimension (fieldChowSituation (S.residueField s)).dimensionFunction
      (f.fiberToSpecResidueField s) x = (r : ℤ)) :
    (fiberCycleSingle f s r x hx : AlgebraicCycle (f.fiber s) ℤ) x = 1 := by
  classical
  rw [coe_fiberCycleSingle]
  simp only [Function.locallyFinsuppWithin.single_apply, ite_true]

/-- The cycle `[x]` has coefficient zero away from `x`. -/
theorem fiberCycleSingle_apply_of_ne (x y : f.fiber s)
    (hx : relativeDimension (fieldChowSituation (S.residueField s)).dimensionFunction
      (f.fiberToSpecResidueField s) x = (r : ℤ)) (hyx : y ≠ x) :
    (fiberCycleSingle f s r x hx : AlgebraicCycle (f.fiber s) ℤ) y = 0 := by
  classical
  rw [coe_fiberCycleSingle]
  simp only [Function.locallyFinsuppWithin.single_apply, hyx, ite_false]

/-- The singleton component of a cycle on a fibre at a point: the cycle `[x]` when `x` carries a
nonzero coefficient, and zero otherwise. -/
def fiberCycleComponent (c : FiberCycleGroup f s r) (x : f.fiber s) : FiberCycleGroup f s r := by
  classical
  exact if hx : (c : AlgebraicCycle (f.fiber s) ℤ) x ≠ 0 then
    fiberCycleSingle f s r x (relativeDimension_of_fiberCycle_apply_ne_zero f s r c hx) else 0

/-- At a point carrying a nonzero coefficient the singleton component is the cycle `[x]`. -/
theorem fiberCycleComponent_of_apply_ne_zero (c : FiberCycleGroup f s r) {x : f.fiber s}
    (hx : (c : AlgebraicCycle (f.fiber s) ℤ) x ≠ 0) :
    fiberCycleComponent f s r c x =
      fiberCycleSingle f s r x (relativeDimension_of_fiberCycle_apply_ne_zero f s r c hx) :=
  dif_pos hx

/-- Where the coefficient vanishes the singleton component is zero. -/
theorem fiberCycleComponent_of_apply_eq_zero (c : FiberCycleGroup f s r) {x : f.fiber s}
    (hx : (c : AlgebraicCycle (f.fiber s) ℤ) x = 0) :
    fiberCycleComponent f s r c x = 0 :=
  dif_neg (not_not.2 hx)

/-! ### The decomposition -/

/-- The decomposition of a cycle on a fibre of a quasi-compact morphism at the level of
coefficients: the underlying algebraic cycle is the finite sum, over its support, of the
singleton indicator functions weighted by its own coefficients. -/
theorem coe_fiberCycle_eq_sum_single [QuasiCompact f] (c : FiberCycleGroup f s r) :
    letI := Classical.decEq (f.fiber s)
    (c : AlgebraicCycle (f.fiber s) ℤ) =
      ∑ x ∈ (finite_support_fiberCycle f s r c).toFinset,
        Function.locallyFinsuppWithin.single x ((c : AlgebraicCycle (f.fiber s) ℤ) x) := by
  classical
  exact (Function.locallyFinsuppWithin.sum_apply_smul_single_eq_self_on_univ
    (finite_support_fiberCycle f s r c)).symm

/-- A singleton indicator with an integer weight is that multiple of the singleton indicator
with weight one. -/
theorem single_eq_zsmul_single_one {T : Type u} [TopologicalSpace T] [DecidableEq T]
    (x : T) (n : ℤ) :
    (Function.locallyFinsuppWithin.single x n : Function.locallyFinsupp T ℤ) =
      n • (Function.locallyFinsuppWithin.single x (1 : ℤ) : Function.locallyFinsupp T ℤ) := by
  refine Function.locallyFinsuppWithin.ext fun y ↦ ?_
  by_cases hy : y = x <;>
    simp only [Function.locallyFinsuppWithin.coe_zsmul, Pi.smul_apply,
      Function.locallyFinsuppWithin.single_apply, hy, ite_true, ite_false, smul_eq_mul, mul_one,
      mul_zero]

/-- A point of the finite support of a cycle on a fibre carries a nonzero coefficient. -/
private theorem apply_ne_zero_of_mem_toFinset_support [QuasiCompact f] (c : FiberCycleGroup f s r)
    {x : f.fiber s} (hx : x ∈ (finite_support_fiberCycle f s r c).toFinset) :
    (c : AlgebraicCycle (f.fiber s) ℤ) x ≠ 0 := by
  simpa using hx

/-- **A cycle on a fibre of a quasi-compact morphism is a finite sum of points.** It is the sum,
over its finite support, of its coefficient at each point times the singleton component there.
This is the step `α_η = ∑ᵢ nᵢ [Yᵢ]` with which the integral case of Tag 0H59 begins. -/
theorem fiberCycle_eq_sum_fiberCycleComponent [QuasiCompact f] (c : FiberCycleGroup f s r) :
    c = ∑ x ∈ (finite_support_fiberCycle f s r c).toFinset,
      (c : AlgebraicCycle (f.fiber s) ℤ) x • fiberCycleComponent f s r c x := by
  classical
  apply Subtype.ext
  refine (Function.locallyFinsuppWithin.sum_apply_smul_single_eq_self_on_univ
    (finite_support_fiberCycle f s r c)).symm.trans ?_
  rw [AddSubgroup.val_finsetSum]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  rw [fiberCycleComponent_of_apply_ne_zero f s r c
      (apply_ne_zero_of_mem_toFinset_support f s r c hx), AddSubgroupClass.coe_zsmul,
    coe_fiberCycleSingle, single_eq_zsmul_single_one]

/-- **The decomposition of a cycle on a fibre, as an existence statement.** There are a finite
set of points of the fibre, each of relative dimension `r`, and integer coefficients, such that
the cycle is the corresponding finite sum of the cycles `[x]`. -/
theorem exists_finset_fiberCycle_eq_sum_fiberCycleSingle [QuasiCompact f]
    (c : FiberCycleGroup f s r) :
    ∃ (A : Finset (f.fiber s))
      (hA : ∀ x ∈ A, relativeDimension (fieldChowSituation (S.residueField s)).dimensionFunction
        (f.fiberToSpecResidueField s) x = (r : ℤ)) (n : f.fiber s → ℤ),
      c = ∑ x ∈ A.attach, n x.1 • fiberCycleSingle f s r x.1 (hA x.1 x.2) := by
  classical
  have hmem {x} := apply_ne_zero_of_mem_toFinset_support f s r c (x := x)
  refine ⟨(finite_support_fiberCycle f s r c).toFinset,
    fun x hx ↦ relativeDimension_of_fiberCycle_apply_ne_zero f s r c (hmem hx),
    fun x ↦ (c : AlgebraicCycle (f.fiber s) ℤ) x, ?_⟩
  refine (fiberCycle_eq_sum_fiberCycleComponent f s r c).trans ?_
  rw [← Finset.sum_attach]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [fiberCycleComponent_of_apply_ne_zero f s r c (hmem x.2)]

end Stacks.Chow

end
