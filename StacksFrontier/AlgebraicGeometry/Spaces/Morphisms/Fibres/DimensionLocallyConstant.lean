module

public import Mathlib.Topology.LocallyConstant.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.DimensionLowerSemicontinuity
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.DimensionUpperSemicontinuity
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.LocallyConstant

/-!
# Local constancy of the fibre dimension of a proper flat morphism

The fibre-dimension function of a proper flat morphism of algebraic spaces over a scheme `S` of
finite presentation is locally constant on the points of its target.

## Main results

* `AlgebraicGeometry.Space.isLocallyConstant_fiberDimension` is **Stacks 0D4R**.

## Implementation notes

A function into `WithBot ℕ∞` which is both lower and upper semicontinuous is locally constant,
because each of its fibres is cut out by two strict inequalities: the fibre over `⊥` is the
sublevel set below `0`, the fibre over `⊤` is empty since the morphism is of finite type, and the
fibre over a natural number `n` is the intersection of the superlevel set above `n - 1` — read as
`⊥` when `n` is zero — with the sublevel set below `n + 1`. Lower semicontinuity is Stacks 0D4P
and upper semicontinuity is Stacks 0D4Q.

## References

* [Stacks Project, Tag 0D4R](https://stacks.math.columbia.edu/tag/0D4R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 0D4R.** The fibre-dimension function of a proper flat morphism of algebraic spaces
over `S` of finite presentation is locally constant on the points of its target. -/
@[stacks 0D4R, ega "IV 14.2.5" "flat fin. pres. case"]
theorem isLocallyConstant_fiberDimension (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hProper : IsProper B S hS f)
    (hFlat : IsFlat B S hS f) (hFP : IsFinitePresentation B S hS f) :
    IsLocallyConstant (fiberDimension B S hS f) := by
  have hlower := lowerSemicontinuous_fiberDimension B S hS hX hY f hFlat hFP
  have hupper := upperSemicontinuous_fiberDimension B S hS hX hY f hProper
  refine IsLocallyConstant.iff_isOpen_fiber.mpr fun d ↦ ?_
  cases d with
  | bot =>
    have hbot : (fiberDimension B S hS f) ⁻¹' {⊥} =
        (fiberDimension B S hS f) ⁻¹' Set.Iio (0 : WithBot ℕ∞) := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_Iio]
      exact (WithBot.lt_zero_iff_eq_bot _).symm
    rw [hbot]
    exact hupper.isOpen_preimage (0 : WithBot ℕ∞)
  | coe d =>
    cases d with
    | top =>
      have htop : (fiberDimension B S hS f) ⁻¹' {((⊤ : ℕ∞) : WithBot ℕ∞)} = ∅ := by
        ext y
        simp [fiberDimension_ne_top B S hS f hX hY hProper.2.1 y]
      rw [htop]
      exact isOpen_empty
    | coe n =>
      have hcut : (fiberDimension B S hS f) ⁻¹' {(n : WithBot ℕ∞)} =
          (fiberDimension B S hS f) ⁻¹' Set.Ioi
              (if n = 0 then (⊥ : WithBot ℕ∞) else ((n - 1 : ℕ) : WithBot ℕ∞)) ∩
            (fiberDimension B S hS f) ⁻¹' Set.Iio ((n + 1 : ℕ) : WithBot ℕ∞) := by
        ext y
        simpa only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_Ioi,
          Set.mem_Iio] using eq_natCast_iff_lt_lt n (fiberDimension B S hS f y)
      show IsOpen ((fiberDimension B S hS f) ⁻¹' {(n : WithBot ℕ∞)})
      rw [hcut]
      exact (hlower.isOpen_preimage _).inter (hupper.isOpen_preimage _)

end AlgebraicGeometry.Space

end
