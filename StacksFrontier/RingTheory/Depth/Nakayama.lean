module

public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Nakayama
public import StacksFrontier.RingTheory.Depth.Defs.Defs

/-!
# Nakayama's lemma for the maximal ideal of a local ring

For a nonzero finite module `M` over a local ring `(R, 𝔪)` one has `𝔪 • M ≠ M`.

## Main results

* `Module.maximalIdeal_smul_top_ne_top`: `𝔪 • M ≠ M` for a nonzero finite module `M` over a
  local ring `(R, 𝔪)`.
* `Module.one_le_depth_iff_exists_isSMulRegular`: for a finite module `M`, the depth of `M`
  along `I` is at least one exactly when some element of `I` acts regularly on `M`.

## References

* [Stacks Project, Tag 00LI](https://stacks.math.columbia.edu/tag/00LI)
-/

@[expose] public section

/-- Nakayama's lemma: the maximal ideal of a local ring does not saturate a nonzero finite
module. -/
public theorem Module.maximalIdeal_smul_top_ne_top {R : Type*} [CommRing R] [IsLocalRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M] :
    IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ :=
  .symm <| Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator <| by
    rw [IsLocalRing.jacobson_eq_maximalIdeal _
      (mt Module.annihilator_eq_top_iff.mp (not_subsingleton M))]

/-- For a finite module `M`, the depth of `M` along `I` is at least one exactly when some
element of `I` is a nonzerodivisor on `M`. -/
public lemma Module.one_le_depth_iff_exists_isSMulRegular {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] (I : Ideal R) :
    1 ≤ Module.depth R I M ↔ ∃ x ∈ I, IsSMulRegular M x := by
  rw [Module.depth]
  split_ifs with h
  · refine iff_of_true le_top ?_
    obtain ⟨r, hr, hzero⟩ :=
      Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I ⊤
        Module.Finite.fg_top h.ge
    refine ⟨1 - r, by simpa using (Ideal.neg_mem_iff _).mpr hr, fun a b hab => ?_⟩
    simpa [sub_smul, hzero a trivial, hzero b trivial] using hab
  · constructor
    · intro hle
      by_contra hc
      push Not at hc
      refine absurd hle (not_le.mpr (lt_of_le_of_lt (iSup₂_le ?_) zero_lt_one))
      rintro (_ | ⟨x, tl⟩) hrs
      · simp
      · exact absurd
          ((RingTheory.Sequence.isWeaklyRegular_cons_iff M x tl).mp
            ((RingTheory.Sequence.isRegular_iff M _).mp hrs.2).1).1
          (hc x (hrs.1 x List.mem_cons_self))
    · rintro ⟨x, hxI, hxreg⟩
      have hne : ⊤ ≠ Ideal.ofList [x] • (⊤ : Submodule R M) := fun heq =>
        h (top_le_iff.mp (heq.le.trans
          (Submodule.smul_mono_left (by simpa [Ideal.ofList] using hxI))))
      exact (by simp : (1 : ℕ∞) = (([x] : List R).length : ℕ∞)).trans_le
        (le_iSup₂ (f := fun rs (_ : rs ∈ {rs : List R |
          (∀ r ∈ rs, r ∈ I) ∧ RingTheory.Sequence.IsRegular M rs}) => (rs.length : ℕ∞))
          [x] ⟨by simpa using hxI, (RingTheory.Sequence.isRegular_iff M [x]).mpr
            ⟨(RingTheory.Sequence.isWeaklyRegular_singleton_iff M x).mpr hxreg, hne⟩⟩)

end
