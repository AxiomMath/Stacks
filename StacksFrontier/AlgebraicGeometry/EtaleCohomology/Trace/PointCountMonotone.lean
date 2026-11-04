module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ConstantSheafCurve
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs

/-!
# Point counts over extensions are monotone along divisibility

Let `X` be a quasi-compact scheme locally of finite type over a finite field `k`. Its number of
points over the extension of degree `n` of `k` is
`N n = ∑_{x ∈ |X|, deg x ∣ n} deg x` (`Stacks.EtaleCohomology.natCard_fieldValuedPoints`). A
closed point of degree dividing `m` has degree dividing `m n`, so `N m ≤ N (m n)`. In terms of
points, `X(k_m) ⊆ X(k_{mn})`. This is one of the two properties of the point counts used in
part (4) of Tag 03V8 (`Stacks.EtaleCohomology.norm_curveEigenvalue_lt`, hypothesis `hmono`).

## Main results

* `Stacks.EtaleCohomology.pointCountSum_le_pointCountSum_mul`: `N m ≤ N (m n)` for `n ≠ 0`.
* `Stacks.EtaleCohomology.infinite_closedPoints_of_isCurve`: a curve over a field has infinitely
  many closed points.
* `Stacks.EtaleCohomology.exists_lt_pointCountSum`: on a curve the point counts are unbounded, the
  other property used in part (4) of Tag 03V8 (hypothesis `hunbdd`).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.EtaleCohomology

variable {k : Type u} [Field k] [Finite k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

section

variable [LocallyOfFiniteType f] [QuasiCompact f]

/-- The sum `∑_{x ∈ |X|, deg x ∣ n} deg x`, the number of points of `X` over the extension of
degree `n` of `k` when `n ≥ 1`. -/
def pointCountSum (n : ℕ) : ℕ :=
  ∑ x ∈ (closedPointsDegreeLE f n).filter fun x => residueDegree f x.1 ∣ n, residueDegree f x.1

/-- A closed point of degree at most `m` dividing `m` lies in the index set of `N m`. -/
private theorem mem_filter_closedPointsDegreeLE {m : ℕ} {x : closedPoints X}
    (hle : residueDegree f x.1 ≤ m) (hdvd : residueDegree f x.1 ∣ m) :
    x ∈ (closedPointsDegreeLE f m).filter fun x => residueDegree f x.1 ∣ m := by
  rw [Finset.mem_filter, closedPointsDegreeLE, Set.Finite.mem_toFinset]
  exact ⟨hle, hdvd⟩

/-- **Point counts grow along divisibility**: `N m ≤ N (m n)` for `n ≠ 0`. -/
theorem pointCountSum_le_pointCountSum_mul (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    pointCountSum f m ≤ pointCountSum f (m * n) := by
  classical
  refine Finset.sum_le_sum_of_subset fun x hx => ?_
  rw [Finset.mem_filter, closedPointsDegreeLE, Set.Finite.mem_toFinset] at hx
  exact mem_filter_closedPointsDegreeLE f
    (hx.1.trans (Nat.le_mul_of_pos_right m (Nat.pos_of_ne_zero hn))) (dvd_mul_of_dvd_left hx.2 n)

end

omit [Finite k] in
/-- **A curve over a field has infinitely many closed points.** -/
theorem infinite_closedPoints_of_isCurve [IsCurve k f] : (closedPoints X).Infinite := by
  intro hfin
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have hclosed : IsClosed (closedPoints X) := by
    rw [← Set.biUnion_of_singleton (closedPoints X)]
    exact hfin.isClosed_biUnion fun x hx => hx
  have huniv : closedPoints X = Set.univ := by
    have := closure_closedPoints (X := X)
    rwa [hclosed.closure_eq] at this
  have hη : IsClosed ({genericPoint X} : Set X) :=
    (huniv ▸ Set.mem_univ _ : genericPoint X ∈ closedPoints X)
  have hsub : Subsingleton X := by
    have hmem (x : X) : x ∈ ({genericPoint X} : Set X) := by
      rw [← hη.closure_eq, (genericPoint_spec X).def]; exact Set.mem_univ x
    exact ⟨fun x y => (hmem x).trans (hmem y).symm⟩
  have h1 := IsCurve.topologicalKrullDim_eq_one (k := k) f
  have : Subsingleton (TopologicalSpace.IrreducibleCloseds X) := ⟨fun A B => by
    obtain ⟨a, ha⟩ := A.isIrreducible.nonempty
    obtain ⟨b, hb⟩ := B.isIrreducible.nonempty
    ext x
    exact ⟨fun _ => Subsingleton.elim b x ▸ hb, fun _ => Subsingleton.elim a x ▸ ha⟩⟩
  have : Nonempty (TopologicalSpace.IrreducibleCloseds X) :=
    ⟨⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩⟩
  have h0 : topologicalKrullDim X = 0 := Order.krullDim_eq_zero
  exact zero_ne_one (h0.symm.trans h1)

variable [IsCurve k f] in
/-- **The point counts of a curve are unbounded**: for every `C` there is an `m ≠ 0` with
`C < N m`. -/
theorem exists_lt_pointCountSum (C : ℕ) : ∃ m : ℕ, m ≠ 0 ∧ C < pointCountSum f m := by
  classical
  have hinf : (Set.univ : Set (closedPoints X)).Infinite := by
    rw [Set.infinite_univ_iff]
    exact (infinite_closedPoints_of_isCurve f).to_subtype
  obtain ⟨T, hT⟩ := hinf.exists_subset_card_eq (C + 1)
  set m := ∏ x ∈ T, residueDegree f x.1 with hm
  have hpos : ∀ x : closedPoints X, 0 < residueDegree f x.1 := fun x =>
    residueDegree_pos f x.1 x.2
  have hm0 : m ≠ 0 := Finset.prod_ne_zero_iff.2 fun x _ => (hpos x).ne'
  refine ⟨m, hm0, ?_⟩
  have hdvd : ∀ x ∈ T, residueDegree f x.1 ∣ m := fun x hx => Finset.dvd_prod_of_mem _ hx
  have hsub : T ⊆ (closedPointsDegreeLE f m).filter fun x => residueDegree f x.1 ∣ m := fun x hx =>
    mem_filter_closedPointsDegreeLE f (Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) (hdvd x hx))
      (hdvd x hx)
  calc C < C + 1 := Nat.lt_succ_self C
    _ = ∑ x ∈ T, 1 := by rw [Finset.sum_const, smul_eq_mul, mul_one, hT.2]
    _ ≤ ∑ x ∈ T, residueDegree f x.1 := Finset.sum_le_sum fun x _ => hpos x
    _ ≤ pointCountSum f m := Finset.sum_le_sum_of_subset hsub

end Stacks.EtaleCohomology

end
