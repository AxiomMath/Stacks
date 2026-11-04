module

public import StacksFrontier.RingTheory.Depth.Criteria

/-!
# Positive depth and regular elements

A finite module has positive depth along an ideal exactly when some element of the ideal acts
regularly on it. Both directions are read off the two branches of `Module.depth`: when the ideal
acts surjectively Nakayama's lemma produces a regular element of the shape `1 - r`, and otherwise
a length-one regular sequence is exactly a regular element of the ideal.

## Main results

* `Module.exists_mem_isSMulRegular_of_depth_ne_zero`: a nonzero depth along an ideal yields a
  regular element in that ideal.

## Implementation notes

It lives in a module whose only import is `StacksFrontier.RingTheory.Depth.Criteria`, which
supplies `Module.depth_eq_iSup_isWeaklyRegular_length`, so that every module using it can import
it cheaply.

The companion `Module.one_le_depth_iff_exists_isSMulRegular`, the positive-depth criterion, is
stated in `StacksFrontier/RingTheory/Depth/Nakayama.lean` and is not repeated here.

## References

* [Stacks Project, Tag 00LK](https://stacks.math.columbia.edu/tag/00LK)
-/

@[expose] public section

open RingTheory.Sequence

/-- A finite module of nonzero depth along an ideal has a regular element in that ideal. -/
public lemma Module.exists_mem_isSMulRegular_of_depth_ne_zero
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
    (I : Ideal R) (h : Module.depth R I M ≠ 0) :
    ∃ x ∈ I, IsSMulRegular M x := by
  by_contra hc
  refine h (le_zero_iff.mp ?_)
  rw [Module.depth_eq_iSup_isWeaklyRegular_length]
  refine iSup₂_le fun rs hrs => ?_
  match rs with
  | [] => simp
  | a :: t =>
    exact absurd ((RingTheory.Sequence.isWeaklyRegular_cons_iff M a t).mp hrs.2).1 fun hreg =>
      hc ⟨a, hrs.1 a (List.mem_cons_self ..), hreg⟩

end
