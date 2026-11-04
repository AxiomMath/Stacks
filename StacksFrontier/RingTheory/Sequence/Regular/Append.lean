module

public import Mathlib.RingTheory.Regular.RegularSequence
public import StacksCore.Tactic.StacksAttribute

/-!
# Concatenation of regular sequences

Let `f₁, …, fₙ` be a regular sequence in a ring `A` generating an ideal `I`, and let
`g₁, …, gₘ ∈ A` be elements whose images in `A ⧸ I` form a regular sequence. Then
`f₁, …, fₙ, g₁, …, gₘ` is a regular sequence in `A`.

## Main results

* `Stacks.RingTheory.Sequence.isRegular_append_iff`: `rs₁ ++ rs₂` is `M`-regular if and only if
  `rs₁` is weakly `M`-regular and `rs₂` is regular on `M ⧸ (rs₁) M`.
* `Stacks.RingTheory.Sequence.isRegular_append_of_isRegular_quotient`: Stacks 065K.

## References

* [Stacks Project, Tag 065K](https://stacks.math.columbia.edu/tag/065K)
-/

@[expose] public section

namespace Stacks.RingTheory.Sequence

open _root_.RingTheory.Sequence

variable {R : Type*} [CommRing R]

/-- A concatenation `rs₁ ++ rs₂` is `M`-regular if and only if `rs₁` is weakly `M`-regular and
`rs₂` is regular on `M ⧸ (rs₁) M`. -/
theorem isRegular_append_iff {M : Type*} [AddCommGroup M] [Module R M] (rs₁ rs₂ : List R) :
    IsRegular M (rs₁ ++ rs₂) ↔
      IsWeaklyRegular M rs₁ ∧ IsRegular (M ⧸ (Ideal.ofList rs₁ • ⊤ : Submodule R M)) rs₂ := by
  induction rs₁ generalizing M with
  | nil =>
    refine Iff.symm <| (and_iff_right (.nil R M)).trans ?_
    refine (Submodule.quotEquivOfEqBot _ ?_).isRegular_congr rs₂
    rw [Ideal.ofList_nil, Submodule.bot_smul]
  | cons r rs₁ ih =>
    rw [List.cons_append, isRegular_cons_iff, isWeaklyRegular_cons_iff, ih, ← and_assoc,
      ← (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M r rs₁).isRegular_congr rs₂]

/-- Let `f` be a regular sequence in `A` generating the ideal `I`, and let `g` be a list of
elements of `A` whose images in `A ⧸ I` form a regular sequence. Then `f ++ g` is a regular
sequence in `A`. -/
@[stacks 065K]
theorem isRegular_append_of_isRegular_quotient {A : Type*} [CommRing A] {I : Ideal A}
    {f g : List A} (hf : IsRegular A f) (hI : Ideal.ofList f = I)
    (hg : IsRegular (A ⧸ I) (g.map (Ideal.Quotient.mk I))) : IsRegular A (f ++ g) := by
  subst hI
  refine (isRegular_append_iff f g).mpr ⟨hf.toIsWeaklyRegular, ?_⟩
  refine ((Submodule.quotEquivOfEq _ _ (by rw [Ideal.smul_eq_mul, Ideal.mul_top])).isRegular_congr
    g).mpr ?_
  exact ((AddEquiv.refl _).isRegular_congr <| List.forall₂_map_right_iff.mpr <|
    List.forall₂_same.mpr fun r _ x => (algebraMap_smul (A ⧸ Ideal.ofList f) r x).symm).mpr hg

end Stacks.RingTheory.Sequence
