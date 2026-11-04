module

public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.Basic

/-!
# Reindexing an admissible sequence along an equality of lengths

A sequence indexed by `Fin m` may be read as a sequence indexed by `Fin n` whenever
`n = m`. This reindexing leaves the spans of initial segments and admissibility untouched,
which is what lets the determinant of a module be compared with the determinant of another
module of the same length.

## Main results

* `Module.FiniteLength.spanBefore_cast` and `Module.FiniteLength.spanBefore_eq_cast` are the
  two orientations of the statement that `spanBefore` is unchanged by reindexing.
* `Module.FiniteLength.admissible_cast` reindexes an admissible sequence.

## References

* [Stacks Project, Tag 02P6](https://stacks.math.columbia.edu/tag/02P6)
-/

@[expose] public section

noncomputable section

namespace Module.FiniteLength

universe u v

/-- Reindexing a sequence along an equality of lengths does not change the span of the
entries preceding an index. -/
public lemma spanBefore_cast {R : Type u} {M : Type v} [Ring R] [AddCommGroup M]
    [Module R M] {n m : ℕ} (h : n = m) (e : Fin m → M) (i : Fin n) :
    spanBefore (R := R) (fun j : Fin n => e (Fin.cast h j)) i =
      spanBefore (R := R) e (Fin.cast h i) := by
  have himage : e '' Set.Iio (Fin.cast h i) =
      (fun j : Fin n => e (Fin.cast h j)) '' Set.Iio i := by
    ext y
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨Fin.cast h.symm j, by simpa [Fin.lt_def] using hj, by simp⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨Fin.cast h j, by simpa using hj, rfl⟩
  simp only [spanBefore, himage]

/-- `spanBefore_cast` with the equality of lengths oriented the other way. -/
public lemma spanBefore_eq_cast {R : Type u} {M : Type v} [Ring R] [AddCommGroup M]
    [Module R M] {m n : ℕ} (h : m = n) (e : Fin m → M) (i : Fin m) :
    spanBefore (R := R) e i =
      spanBefore (R := R) (fun j : Fin n => e (Fin.cast h.symm j)) (Fin.cast h i) :=
  (spanBefore_cast h.symm e (Fin.cast h i)).symm

/-- Membership in the span of the preceding entries is preserved by reindexing. -/
public lemma spanBefore_cast_mem {R : Type u} {M : Type v} [Ring R] [AddCommGroup M]
    [Module R M] {n m : ℕ} (h : n = m) (e : Fin m → M) (i : Fin m) (x : M) :
    x ∈ spanBefore (R := R) e i ↔
      x ∈ spanBefore (R := R) (fun j : Fin n => e (Fin.cast h j))
        (Fin.cast h.symm i) := by
  have hs := spanBefore_cast (R := R) h e (Fin.cast h.symm i)
  rw [hs, Fin.cast_cast, Fin.cast_eq_self]

/-- Reindexing an admissible sequence along an equality of lengths gives an admissible
sequence. -/
public lemma admissible_cast {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] {n m : ℕ}
    (h : n = m) (e : Fin m → M) (he : IsAdmissibleSequence (R := R) e) :
    IsAdmissibleSequence (R := R) (fun i : Fin n => e (Fin.cast h i)) := by
  intro i r hr
  rw [spanBefore_cast (R := R) h e i]
  exact he (Fin.cast h i) r hr

end Module.FiniteLength

end
