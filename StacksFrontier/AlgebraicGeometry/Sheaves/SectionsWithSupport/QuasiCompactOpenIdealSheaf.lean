module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.FittingIdeals

/-!
# Quasi-compact opens and ideal sheaves of finite type

On a quasi-compact scheme, the complement of the support of a quasi-coherent ideal sheaf of
finite type is a quasi-compact open.

## Main results

* `AlgebraicGeometry.isCompact_compl_zeroLocus_inter_of_fg`: inside an affine open, the
  complement of the zero locus of a finitely generated ideal is quasi-compact.
* `AlgebraicGeometry.isCompact_of_forall_isCompact_inter_affineOpens`: on a quasi-compact
  scheme, an open is quasi-compact as soon as its intersection with every affine open is.
* `AlgebraicGeometry.isCompact_of_isFiniteType_of_support_eq_compl`: the complement of the
  support of a finite type ideal sheaf on a quasi-compact scheme is quasi-compact.

## References

* [Stacks Project, Tag 01PH](https://stacks.math.columbia.edu/tag/01PH)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

add_to_stacks 01PH "retrocompact iff quasi-compact"
  QuasiSeparatedSpace.isRetrocompact_iff_isCompact
add_to_stacks 01PH "quasi-compact iff finite union of affine opens"
  AlgebraicGeometry.isCompact_iff_finite_and_eq_biUnion_affineOpens
add_to_ega "I 1.1.10" "more general"
  AlgebraicGeometry.isCompact_iff_finite_and_eq_biUnion_affineOpens
add_to_ega "IV 1.8.1" AlgebraicGeometry.isCompact_iff_finite_and_eq_biUnion_affineOpens

/-- Inside an affine open `U`, the complement of the zero locus of a finitely generated ideal
of `Γ(X, U)` is quasi-compact. -/
theorem isCompact_compl_zeroLocus_inter_of_fg {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (K : Ideal Γ(X, U)) (hK : K.FG) :
    IsCompact ((X.zeroLocus (U := U) (K : Set Γ(X, U)))ᶜ ∩ U) := by
  obtain ⟨s, -, rfl⟩ := hK
  rw [X.zeroLocus_span, X.zeroLocus_def]
  simp only [Set.compl_iInter, compl_compl]
  convert s.finite_toSet.isCompact_biUnion
    (fun f _ ↦ isCompact_basicOpen X hU.isCompact f) using 1
  ext x
  simp only [Set.mem_inter_iff, Set.mem_iUnion, exists_prop]
  refine ⟨fun h ↦ h.1, fun h ↦ ⟨h, ?_⟩⟩
  obtain ⟨f, -, hx⟩ := h
  exact X.basicOpen_le f hx

/-- On a quasi-compact scheme an open subset is quasi-compact as soon as its intersection with
every affine open is. -/
theorem isCompact_of_forall_isCompact_inter_affineOpens {X : Scheme.{u}} [CompactSpace X]
    (U : X.Opens) (hU : ∀ V : X.affineOpens, IsCompact ((U : Set X) ∩ (V : Set X))) :
    IsCompact (U : Set X) := by
  obtain ⟨s, hs, hcover⟩ :=
    (isCompact_iff_finite_and_eq_biUnion_affineOpens (X := X) (U := ⊤)).mp isCompact_univ
  have hUcover : (U : Set X) = ⋃ V ∈ s, (U : Set X) ∩ (V : Set X) := by
    refine Set.ext fun x ↦ ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
    · have hxV : x ∈ ⋃ V ∈ s, (V : Set X) := by
        have hxTop : x ∈ (⊤ : X.Opens) := Set.mem_univ x
        rw [hcover] at hxTop
        simpa only [Opens.mem_iSup, Set.mem_iUnion, SetLike.mem_coe] using hxTop
      obtain ⟨V, hV, hxV⟩ := Set.mem_iUnion₂.mp hxV
      exact Set.mem_iUnion₂.mpr ⟨V, hV, hx, hxV⟩
    · obtain ⟨V, -, hx⟩ := Set.mem_iUnion₂.mp hx
      exact hx.1
  rw [hUcover]
  exact hs.isCompact_biUnion fun V _ ↦ hU V

/-- On a quasi-compact scheme, the complement of the support of a quasi-coherent ideal sheaf of
finite type is a quasi-compact open. -/
theorem isCompact_of_isFiniteType_of_support_eq_compl {X : Scheme.{u}} [CompactSpace X]
    (U : X.Opens) (I : X.IdealSheafData) (hI : Scheme.IdealSheafData.IsFiniteType I)
    (hIU : (I.support : Set X) = (U : Set X)ᶜ) : IsCompact (U : Set X) := by
  refine isCompact_of_forall_isCompact_inter_affineOpens U fun V ↦ ?_
  have hset : (U : Set X) ∩ (V : Set X) =
      (X.zeroLocus (U := V.1) (I.ideal V : Set Γ(X, V.1)))ᶜ ∩ (V : Set X) := by
    refine Set.ext fun x ↦ ?_
    by_cases hxV : x ∈ (V : Set X)
    · have hxSupport : x ∈ (I.support : Set X) ↔
          x ∈ X.zeroLocus (U := V.1) (I.ideal V : Set Γ(X, V.1)) :=
        I.mem_support_iff_of_mem hxV
      have hxU : x ∈ (U : Set X) ↔ x ∉ (I.support : Set X) := by
        rw [hIU]
        simp
      rw [Set.mem_inter_iff, Set.mem_inter_iff, hxU, hxSupport]
      simp [hxV]
    · simp [hxV]
  rw [hset]
  exact isCompact_compl_zeroLocus_inter_of_fg V.2 (I.ideal V) (hI V)

end AlgebraicGeometry

end
