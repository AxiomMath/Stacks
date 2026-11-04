module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.Topology.GDelta.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Ideal sheaves containing a nonzerodivisor have nowhere dense support

Let `X` be a scheme and `I` an ideal sheaf on `X`, given in the affine-local interface
`AlgebraicGeometry.Scheme.IdealSheafData`.  If on every affine open `U` the ideal `I(U)`
contains a nonzerodivisor of `Γ(X, U)`, then the support of `I` is nowhere dense.

## Main results

* `Stacks.IdealSheafSupport.one_eq_zero_of_subset_zeroLocus`: an affine open whose points all lie
  in the zero locus of a family of sections containing a nonzerodivisor has the zero ring as its
  ring of sections.
* `Stacks.IdealSheafSupport.eq_bot_of_subset_zeroLocus`: consequently such an affine open is
  empty.
* `Stacks.IdealSheafSupport.isNowhereDense_support`: an ideal sheaf whose ideal at every affine
  open contains a nonzerodivisor has nowhere dense support.
* `Stacks.IdealSheafSupport.isNowhereDense_support_of_le`: the same conclusion when the
  nonzerodivisor condition holds for a smaller ideal sheaf.
* `Stacks.IdealSheafSupport.isNowhereDense_support_ofIdeals_of_le`: the same conclusion for
  `Scheme.IdealSheafData.ofIdeals F`, given an ideal sheaf satisfying the condition whose ideals
  lie below `F`.
* `Stacks.IdealSheafSupport.exists_isClosed_isNowhereDense_of_subset_support`: a subset of such a
  support lies in a closed nowhere dense set.

## References

* [Stacks Project, Tag 02P0](https://stacks.math.columbia.edu/tag/02P0)
* [Stacks Project, Tag 03HP](https://stacks.math.columbia.edu/tag/03HP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.IdealSheafSupport

variable {X : Scheme.{u}}

/-- If every point of an affine open `U` lies in the zero locus of a family `s` of sections
containing a nonzerodivisor, then `Γ(X, U)` is the zero ring. -/
lemma one_eq_zero_of_subset_zeroLocus (U : X.affineOpens) {s : Set Γ(X, U)} {b : Γ(X, U)}
    (hbs : b ∈ s) (hb : b ∈ nonZeroDivisors Γ(X, U))
    (hsub : (U.1 : Set X) ⊆ X.zeroLocus (U := U.1) s) :
    (1 : Γ(X, U)) = 0 := by
  have hbot : X.basicOpen b = ⊥ := le_bot_iff.mp fun y hy =>
    absurd hy ((X.mem_zeroLocus_iff s y).mp (hsub (X.basicOpen_le b hy)) b hbs)
  obtain ⟨n, hn⟩ :=
    (Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact U.2.isCompact b).mpr hbot
  exact (mem_nonZeroDivisors_iff.mp (pow_mem hb n)).1 1 (by rw [hn, zero_mul])

/-- If every point of an affine open `U` lies in the zero locus of a family `s` of sections
containing a nonzerodivisor, then `U` is empty. -/
lemma eq_bot_of_subset_zeroLocus (U : X.affineOpens) {s : Set Γ(X, U)} {b : Γ(X, U)}
    (hbs : b ∈ s) (hb : b ∈ nonZeroDivisors Γ(X, U))
    (hsub : (U.1 : Set X) ⊆ X.zeroLocus (U := U.1) s) :
    U.1 = ⊥ :=
  calc U.1 = X.basicOpen (1 : Γ(X, U.1)) := X.basicOpen_one.symm
    _ = X.basicOpen (0 : Γ(X, U.1)) := by rw [one_eq_zero_of_subset_zeroLocus U hbs hb hsub]
    _ = ⊥ := X.basicOpen_zero U.1

/-- An ideal sheaf whose ideal at every affine open contains a nonzerodivisor has nowhere dense
support. -/
theorem isNowhereDense_support (I : X.IdealSheafData)
    (h : ∀ U : X.affineOpens, ∃ b ∈ I.ideal U, b ∈ nonZeroDivisors Γ(X, U)) :
    IsNowhereDense (I.support : Set X) := by
  have hcl : IsClosed (I.support : Set X) := I.isClosed_supportSet
  rw [hcl.isNowhereDense_iff, Set.eq_empty_iff_forall_notMem]
  intro x hx
  obtain ⟨-, ⟨V, hV, rfl⟩, hxV, hVsub⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx isOpen_interior
  obtain ⟨b, hbI, hb⟩ := h ⟨V, hV⟩
  have hVbot : V = ⊥ := eq_bot_of_subset_zeroLocus ⟨V, hV⟩ hbI hb fun y hy =>
    I.supportSet_subset_zeroLocus ⟨V, hV⟩ (interior_subset (hVsub hy))
  rwa [hVbot, Opens.coe_bot] at hxV

/-- If `J ≤ I` and the ideal of `J` at every affine open contains a nonzerodivisor, then the
support of `I` is nowhere dense. -/
theorem isNowhereDense_support_of_le {J I : X.IdealSheafData} (hJI : J ≤ I)
    (h : ∀ U : X.affineOpens, ∃ b ∈ J.ideal U, b ∈ nonZeroDivisors Γ(X, U)) :
    IsNowhereDense (I.support : Set X) :=
  (isNowhereDense_support J h).mono (Scheme.IdealSheafData.support_antitone hJI)

/-- If `J` is an ideal sheaf with `J.ideal ≤ F` whose ideal at every affine open contains a
nonzerodivisor, then the support of `Scheme.IdealSheafData.ofIdeals F` is nowhere dense. -/
theorem isNowhereDense_support_ofIdeals_of_le {F : ∀ U : X.affineOpens, Ideal Γ(X, U)}
    {J : X.IdealSheafData} (hJ : J.ideal ≤ F)
    (h : ∀ U : X.affineOpens, ∃ b ∈ J.ideal U, b ∈ nonZeroDivisors Γ(X, U)) :
    IsNowhereDense ((Scheme.IdealSheafData.ofIdeals F).support : Set X) :=
  isNowhereDense_support_of_le (Scheme.IdealSheafData.le_ofIdeals_iff.mpr hJ) h

/-- If the ideal of `I` at every affine open contains a nonzerodivisor, then every subset of the
support of `I` lies in a closed nowhere dense set. -/
@[ega "IV 21.10.5" "special case"]
theorem exists_isClosed_isNowhereDense_of_subset_support {I : X.IdealSheafData}
    (h : ∀ U : X.affineOpens, ∃ b ∈ I.ideal U, b ∈ nonZeroDivisors Γ(X, U))
    {S : Set X} (hS : S ⊆ (I.support : Set X)) :
    ∃ T : Set X, IsClosed T ∧ IsNowhereDense T ∧ S ⊆ T :=
  ⟨(I.support : Set X), I.isClosed_supportSet, isNowhereDense_support I h, hS⟩

end Stacks.IdealSheafSupport

end
