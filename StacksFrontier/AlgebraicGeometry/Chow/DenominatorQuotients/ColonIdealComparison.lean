module

public import StacksFrontier.AlgebraicGeometry.Chow.CartierDivisorsK.Basic
public import StacksFrontier.AlgebraicGeometry.DenominatorColonIdeal.Basic

/-!
# The denominator ideal of a section is the denominator ideal of its local ratio

The ideal of denominators of a meromorphic section `s` of an invertible `𝒪_X`-module `L` is
presented affine-locally by [Stacks, Tag 02P0]: over an affine open `V` on which `L` is trivial
and on which `s` is the ratio `a / b` of two sections of `𝒪_X` with `b` a nonzerodivisor, its
sections are the `g` with `g * a = b * u` for some `u`.
`Stacks.DenominatorColonIdeal.range_denominatorIdealι_app_eq` states that as an equality of the
image of the ideal inclusion on sections with that **set**, written out literally, and
`Stacks.ColonLocalization` works in the same shape deliberately: the colon ideal is not how the
geometric statement presents itself, and Mathlib's `Submodule.colon` has no localization result
at this pin.

The algebraic side of the same object is `Ideal.denominatorIdeal a b`, the colon ideal
`(b) : (a)`, which is what the length formula of [Stacks, Tag 02QH] is stated about. This file
is the one lemma joining the two, so that neither presentation has to be rewritten in terms of
the other: the set form stays where it is chosen, and the colon form stays where the lengths are
computed.

## Main results

* `Stacks.Chow.range_denominatorIdealι_app_eq_coe_denominatorIdeal` — the image of the ideal
  inclusion on the sections over a trivializing affine open is the denominator ideal of the
  local ratio.
* `Stacks.Chow.exists_affineOpen_denominatorIdeal_presentation` — such an affine open exists
  around every point of every open set.

## Implementation notes

The sections of the structure sheaf carry two spellings, `Stacks.DenominatorLocalRatio.oScalar`
at `RingCat` — where the module structures on the sections of a sheaf of `𝒪_X`-modules are
stated, and so where the ratio `a / b` is produced — and `Γ(X, V)` at `CommRingCat`, where
`Ideal.denominatorIdeal` is formed. They are the same type, so the equality is stated between a
`Set` of the former and the coercion of an `Ideal` of the latter without a transport.

## References

* [Stacks Project, Tag 02P0](https://stacks.math.columbia.edu/tag/02P0)
* [Stacks Project, Tag 02QH](https://stacks.math.columbia.edu/tag/02QH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.DenominatorIdeal Stacks.DenominatorColonIdeal Stacks.DenominatorLocalRatio

universe u

namespace Stacks.Chow

variable (X : Scheme.{u}) (L : SheafOfModules.{u} (O X)) (s : MeromorphicSection.{u, u} X.sheaf L)

/-- **The image of the denominator ideal on the sections over a trivializing affine open is the
denominator ideal of the local ratio.** This is
`Stacks.DenominatorColonIdeal.range_denominatorIdealι_app_eq`, whose right-hand side is the
literal set `{g | ∃ u, g * a = b * u}`, compared with the denominator ideal through
`Ideal.mem_denominatorIdeal_iff`, whose equation has the two factors in the other order. -/
theorem range_denominatorIdealι_app_eq_coe_denominatorIdeal
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (O X).property L)
    {V : Opens X} (hV : IsAffineOpen V)
    (θ : Stacks.SheafDescent.Trivialization X.presheaf L.val V)
    {b : oScalar X V} (hb : b ∈ nonZeroDivisors Γ(X, V)) {a : oScalar X V}
    (hbt : (toK X L).val.app (op V) (a • oTrivBasis X L θ) =
      (sectionMap X L s).val.app (op V) b) :
    Set.range (ConcreteCategory.hom ((denominatorIdealι X L s).val.app (op V))) =
      (Ideal.denominatorIdeal (R := Γ(X, V)) a b : Set Γ(X, V)) := by
  rw [range_denominatorIdealι_app_eq X L s hL hV θ hb hbt]
  refine Set.eq_of_subset_of_subset (fun g hg => ?_) (fun g hg => ?_)
  · obtain ⟨v, hv⟩ := hg
    refine SetLike.mem_coe.mpr ((Ideal.mem_denominatorIdeal_iff (R := Γ(X, V))).mpr ⟨v, ?_⟩)
    exact hv.trans (oScalar_mul_comm X V b v)
  · obtain ⟨y, hy⟩ :=
      (Ideal.mem_denominatorIdeal_iff (R := Γ(X, V))).mp (SetLike.mem_coe.mp hg)
    exact ⟨y, hy.trans (oScalar_mul_comm X V y b)⟩

/-- **Around every point of every open set there is an affine open on which the denominator
ideal is the denominator ideal of a ratio of sections.** The affine open and the ratio come from
`Stacks.DenominatorColonIdeal.exists_affineOpen_colon_presentation`; only the presentation of
the colon ideal is changed. -/
theorem exists_affineOpen_denominatorIdeal_presentation
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (O X).property L)
    (W : Opens X) (x : X) (hx : x ∈ W) :
    ∃ V : Opens X, V ≤ W ∧ x ∈ V ∧ IsAffineOpen V ∧
      ∃ b : oScalar X V, b ∈ nonZeroDivisors Γ(X, V) ∧ ∃ a : oScalar X V,
        Set.range (ConcreteCategory.hom ((denominatorIdealι X L s).val.app (op V))) =
          (Ideal.denominatorIdeal (R := Γ(X, V)) a b : Set Γ(X, V)) := by
  obtain ⟨V, hVW, hxV, hVaff, ⟨θ⟩, b, hb, t, hbt⟩ :=
    Stacks.DenominatorLocalRatio.exists_affineOpen_denominator X L s hL W x hx
  obtain ⟨a, hat⟩ := exists_smul_oTrivBasis X L θ t
  rw [hat] at hbt
  exact ⟨V, hVW, hxV, hVaff, b, hb, a,
    range_denominatorIdealι_app_eq_coe_denominatorIdeal X L s hL hVaff θ hb hbt⟩

end Stacks.Chow

end
