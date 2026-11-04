module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.LocallyConstant.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Bounded
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.LowerSemicontinuity
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UpperSemicontinuity

/-!
# Local constancy of the dimension of the fibres of a proper flat morphism

For a proper, flat morphism of finite presentation the dimension of the fibres is a locally
constant function on the base.

This is immediate from the two semicontinuities: flatness and finite presentation give lower
semicontinuity (Tag 0D4H) and properness gives upper semicontinuity (Tag 0D4I), so each level set
is the intersection of two open sets. For a finite level `n` these are the loci where the function
exceeds `n - 1` and where it is below `n + 1`; the level `⊥` is the locus below `0`, and the level
`⊤` is empty because the fibres of a proper morphism have finite dimension.

## Main results

* `AlgebraicGeometry.isLocallyConstant_fiberDimension` is **Stacks Tag 0D4J**.

## Implementation notes

That the level `⊤` is empty is the only part not formally contained in the two semicontinuities:
it is Tag 0A3V applied over an affine open neighbourhood of the given point of the base, together
with the base-change formula of Tag 05F8 to transfer the resulting bound back.

## References

* [Stacks Project, Tag 0D4J](https://stacks.math.columbia.edu/tag/0D4J)
* [Stacks Project, Tag 0D4H](https://stacks.math.columbia.edu/tag/0D4H)
* [Stacks Project, Tag 0D4I](https://stacks.math.columbia.edu/tag/0D4I)
* [Stacks Project, Tag 0A3V](https://stacks.math.columbia.edu/tag/0A3V)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- An element of `WithBot ℕ∞` equals the natural number `n` exactly when it lies strictly between
`n - 1` — read as `⊥` when `n` is zero — and `n + 1`. -/
public lemma eq_natCast_iff_lt_lt (n : ℕ) (x : WithBot ℕ∞) :
    x = (n : WithBot ℕ∞) ↔
      (if n = 0 then (⊥ : WithBot ℕ∞) else ((n - 1 : ℕ) : WithBot ℕ∞)) < x ∧
        x < ((n + 1 : ℕ) : WithBot ℕ∞) := by
  cases n with
  | zero =>
    cases x with
    | bot => simp
    | coe x =>
      cases x with
      | top => exact ⟨fun h ↦ (WithTop.top_ne_coe (WithBot.coe_eq_coe.mp h)).elim,
          fun h ↦ ((not_lt_of_ge le_top) h.2).elim⟩
      | coe m => simp [WithBot.coe_natCast]
  | succ n =>
    cases x with
    | bot =>
      simpa [WithBot.coe_natCast] using
        (WithBot.bot_ne_coe : (⊥ : WithBot ℕ∞) ≠ (↑((n + 1 : ℕ) : ℕ∞)))
    | coe x =>
      cases x with
      | top => exact ⟨fun h ↦ (WithTop.top_ne_coe (WithBot.coe_eq_coe.mp h)).elim,
          fun h ↦ ((not_lt_of_ge le_top) h.2).elim⟩
      | coe m => simp [WithBot.coe_natCast]; norm_cast; omega

/-- The fibres of a proper morphism have finite dimension: over an affine open neighbourhood of a
point of the base the dimensions of the fibres are bounded by Tag 0A3V, and the base-change
formula identifies them with the dimensions of the fibres of the original morphism. -/
private lemma fiberDimension_ne_top {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (y : Y) :
    f.fiberDimension y ≠ ⊤ := by
  obtain ⟨_, ⟨V : Y.Opens, hV, rfl⟩, hyV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have : IsAffine V.toScheme := hV
  have : CompactSpace V := isCompact_iff_compactSpace.mp hV.isCompact
  obtain ⟨n, hn⟩ := exists_topologicalKrullDim_fiber_le (pullback.snd f V.ι)
  have hlocal : (pullback.snd f V.ι).fiberDimension ⟨y, hyV⟩ ≤ (n : WithBot ℕ∞) := hn ⟨y, hyV⟩
  rw [Scheme.Hom.fiberDimension_pullback_snd] at hlocal
  have hdim : f.fiberDimension y ≤ (n : WithBot ℕ∞) := hlocal
  exact ne_of_lt (lt_of_le_of_lt hdim (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)))

/-- **Stacks Project, Tag 0D4J.** The dimension-of-fibres function of a proper, flat morphism of
schemes of finite presentation is locally constant. -/
@[stacks 0D4J,
  ega "IV 14.2.5" "flat fin. pres. case",
  ega "IV 13.2.12" "(ii), special case",
  sga "3 VIB 4.3" "special case"]
public theorem isLocallyConstant_fiberDimension {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    [Flat f] (hfp : FinitePresentation f) : IsLocallyConstant f.fiberDimension := by
  have hlower := lowerSemicontinuous_fiberDimension f hfp
  have hupper := upperSemicontinuous_fiberDimension f
  refine IsLocallyConstant.iff_isOpen_fiber.mpr fun d ↦ ?_
  cases d with
  | bot =>
    have hbot : f.fiberDimension ⁻¹' {⊥} = f.fiberDimension ⁻¹' Set.Iio (0 : WithBot ℕ∞) := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_Iio]
      exact (WithBot.lt_zero_iff_eq_bot _).symm
    rw [hbot]
    exact hupper.isOpen_preimage (0 : WithBot ℕ∞)
  | coe d =>
    cases d with
    | top =>
      have htop : f.fiberDimension ⁻¹' {((⊤ : ℕ∞) : WithBot ℕ∞)} = ∅ := by
        ext y
        simp [fiberDimension_ne_top f y]
      rw [htop]
      exact isOpen_empty
    | coe n =>
      have hcut : f.fiberDimension ⁻¹' {(n : WithBot ℕ∞)} =
          f.fiberDimension ⁻¹' Set.Ioi
              (if n = 0 then (⊥ : WithBot ℕ∞) else ((n - 1 : ℕ) : WithBot ℕ∞)) ∩
            f.fiberDimension ⁻¹' Set.Iio ((n + 1 : ℕ) : WithBot ℕ∞) := by
        ext y
        simpa only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_Ioi,
          Set.mem_Iio] using eq_natCast_iff_lt_lt n (f.fiberDimension y)
      show IsOpen (f.fiberDimension ⁻¹' {(n : WithBot ℕ∞)})
      rw [hcut]
      exact (hlower.isOpen_preimage _).inter (hupper.isOpen_preimage _)

end AlgebraicGeometry

end
