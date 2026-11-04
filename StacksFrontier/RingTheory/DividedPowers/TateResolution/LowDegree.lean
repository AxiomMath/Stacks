module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.ChosenPresentation
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.DegreeZeroStage

/-!
# Low degrees come from a truncated family of variables

Let `T` and `T'` be indexed presentations and `e` a degree-wise map of their index families.
If `e` is surjective in every degree below `m` and has a degree-wise retraction, then every
element of degree `m` of the algebra of `T'` is the comparison of an element of degree `m` of
the algebra of `T`.

## Main results

* `DividedPowers.TateResolution.IndexedPresentation.generator_eq_gen` — the structure's own
  variable at an index is the prescribed variable at the transported index.
* `DividedPowers.TateResolution.IndexedPresentation.exists_mem_grade_comparison_eq` — an element
  of degree `m` of the target is the comparison of an element of degree `m` of the source.

## References

* [Stacks Project, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w

namespace IndexedPresentation

variable {R : Type u} {P : Type v} [CommRing R] [CommRing P] [Algebra R P]
  {idx idx' : ℕ → Type (max u v w)}

/-- The variable of the underlying presentation at an index of its own family is the prescribed
variable at the index transported along `indexEquiv`. -/
public theorem generator_eq_gen (T : IndexedPresentation.{u, v, w} R P idx)
    (j : Σ n : ℕ, T.polynomial.indices n) :
    T.polynomial.generator j = T.gen (T.indexEquiv.symm j) :=
  (congrArg T.polynomial.generator (T.indexEquiv.apply_symm_apply j)).symm

/-- A variable of the target of degree at most `m` is the comparison of a variable of the
source, when the degree-wise map of index families is surjective below `m`. -/
public theorem generator_mem_comparison_range (T : IndexedPresentation.{u, v, w} R P idx)
    (T' : IndexedPresentation.{u, v, w} R P idx') (e : ∀ n : ℕ, idx n → idx' n) {m : ℕ}
    (hsurj : ∀ n : ℕ, n < m → ∀ y : idx' n, ∃ x : idx n, e n x = y)
    (j : Σ n : ℕ, T'.polynomial.indices n) (hj : j.1 < m) :
    ∃ g : T.A, T.comparison T' e g = T'.polynomial.generator j := by
  obtain ⟨z, hz⟩ := hsurj (T'.indexEquiv.symm j).1
    (by rw [T'.indexEquiv_symm_fst]; exact hj) (T'.indexEquiv.symm j).2
  refine ⟨T.gen ⟨(T'.indexEquiv.symm j).1, z⟩, ?_⟩
  rw [T.comparison_gen T' e ⟨(T'.indexEquiv.symm j).1, z⟩, hz]
  exact (T'.generator_eq_gen j).symm

/-- A finite variable stage of the target all of whose variables have degree at most `m` lies in
the image of the comparison, when the degree-wise map of index families is surjective below `m`
and has a degree-wise retraction. -/
public theorem finiteVariableStage_le_comparison_range
    (T : IndexedPresentation.{u, v, w} R P idx) (T' : IndexedPresentation.{u, v, w} R P idx')
    (e : ∀ n : ℕ, idx n → idx' n) (ρ : ∀ n : ℕ, idx' n → Option (idx n))
    (hρ : ∀ (n : ℕ) (x : idx n), ρ n (e n x) = some x) {m : ℕ}
    (hsurj : ∀ n : ℕ, n < m → ∀ y : idx' n, ∃ x : idx n, e n x = y)
    (S : Finset (Σ n : ℕ, T'.polynomial.indices n)) (hS : ∀ j ∈ S, j.1 < m) :
    finiteVariableStage T'.gamma T'.coefficient T'.polynomial.generator S ≤
      (T.comparison T' e).range.toSubring := by
  obtain ⟨r, hr, hrg⟩ := T.exists_comparison_retraction T' e ρ hρ
  refine Subring.closure_le.mpr ?_
  rintro y (⟨p, hp⟩ | ⟨j, hjS, hy⟩)
  · exact ⟨T.coefficient p, hp ▸ T.comparison_coefficient T' e p⟩
  · obtain ⟨g, hg⟩ := T.generator_mem_comparison_range T' e hsurj j (hS j hjS)
    rcases hy with rfl | ⟨n, rfl⟩
    · exact ⟨g, hg⟩
    · by_cases hpos : T'.polynomial.generator j ∈ positiveEvenPart T'.grade
      · have hgpos : g ∈ positiveEvenPart T.grade := by
          have hrpos := T'.mem_positiveEvenPart_of_mem T r hrg hpos
          rwa [← hg, hr g] at hrpos
        exact ⟨T.gamma.dpow n g, hg ▸ (T.comparison_dpow T' e n g hgpos).symm⟩
      · exact ⟨0, by rw [map_zero, T'.gamma.dpow_null hpos]⟩

/-- **An element of degree `m` of the target is the comparison of an element of degree `m` of
the source**, as soon as the degree-wise map of index families is surjective in every degree
below `m` and has a degree-wise retraction. -/
public theorem exists_mem_grade_comparison_eq (T : IndexedPresentation.{u, v, w} R P idx)
    (T' : IndexedPresentation.{u, v, w} R P idx') (e : ∀ n : ℕ, idx n → idx' n)
    (ρ : ∀ n : ℕ, idx' n → Option (idx n)) (hρ : ∀ (n : ℕ) (x : idx n), ρ n (e n x) = some x)
    {m : ℕ} (hsurj : ∀ n : ℕ, n < m → ∀ y : idx' n, ∃ x : idx n, e n x = y)
    (x : T'.A) (hx : x ∈ T'.grade m) :
    ∃ y : T.A, y ∈ T.grade m ∧ T.comparison T' e y = x := by
  obtain ⟨r, hr, hrg⟩ := T.exists_comparison_retraction T' e ρ hρ
  have hle : T'.grade m ≤ Subalgebra.toSubmodule (T.comparison T' e).range := by
    rw [← iSup_inf_finiteVariableStageSubmodule T'.gamma T'.coefficient
      T'.polynomial.generator T'.polynomial.finite_support m]
    refine iSup_le fun S => le_trans
      (inf_finiteVariableStageSubmodule_le_filter T'.polynomial m S)
      (le_trans inf_le_right fun z hz => ?_)
    exact T.finiteVariableStage_le_comparison_range T' e ρ hρ hsurj _
      (fun j hj => (Finset.mem_filter.mp hj).2) hz
  obtain ⟨y, hy : T.comparison T' e y = x⟩ := Subalgebra.mem_carrier.mp (hle hx)
  exact ⟨r x, hrg m x hx, by rw [← hy, hr y]⟩

end IndexedPresentation

end DividedPowers.TateResolution

end
