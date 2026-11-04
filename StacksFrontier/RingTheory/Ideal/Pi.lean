module

public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Ideal.Basic

/-!
# Finite generation of a product of ideals

The ideal `Ideal.pi I` of a product of rings cut out by a family of ideals `I i` of the factors
is finitely generated as soon as the index type is finite and every `I i` is.

## Main results

* `Ideal.fg_pi`: a product of finitely generated ideals over a finite index type is finitely
  generated.

## Implementation notes

The generating set is the union over `i` of the images under `Pi.single i` of generating sets of
the `I i`. That it generates uses the decomposition `x = ∑ i, Pi.single i (x i)` of an element of
a product over a finite index type, together with the multiplicativity of `Pi.single i`, which
turns a representation of `x i` by the chosen generators of `I i` into one of `Pi.single i (x i)`.
-/

@[expose] public section

namespace Ideal

/-- A product of finitely generated ideals, indexed by a finite type, is finitely generated. -/
theorem fg_pi {ι : Type*} [Finite ι] {R : ι → Type*} [∀ i, CommRing (R i)]
    (I : ∀ i, Ideal (R i)) (h : ∀ i, (I i).FG) : (Ideal.pi I).FG := by
  classical
  cases nonempty_fintype ι
  choose s hs using h
  set T : Finset (∀ i, R i) := Finset.univ.biUnion fun i ↦ (s i).image (Pi.single i) with hT
  have hmemT : ∀ x, x ∈ T ↔ ∃ i, ∃ y ∈ s i, Pi.single i y = x := by simp [hT]
  refine ⟨T, le_antisymm ?_ ?_⟩
  · rw [Ideal.span_le]
    intro x hx
    obtain ⟨i, y, hy, rfl⟩ := (hmemT x).mp hx
    intro j
    rcases eq_or_ne j i with rfl | hji
    · simpa using (hs j ▸ Ideal.subset_span hy : y ∈ I j)
    · simp [Pi.single_eq_of_ne hji]
  · intro x hx
    rw [← Finset.univ_sum_single x]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.mp (hs i ▸ hx i :
      x i ∈ Ideal.span ((s i : Set (R i))))
    have hsum : Pi.single i (x i) = ∑ y ∈ s i, Pi.single i (f y • y) := by
      rw [← hf]
      exact map_sum (AddMonoidHom.single (fun i ↦ R i) i) _ _
    rw [hsum]
    refine Submodule.sum_mem _ fun y hy ↦ ?_
    have hy' : Pi.single i (f y • y) = Pi.single i (f y) * Pi.single i y := by
      simp [smul_eq_mul, Pi.single_mul]
    rw [hy']
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ((hmemT _).mpr ⟨i, y, hy, rfl⟩))

end Ideal
