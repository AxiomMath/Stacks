module

public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FlatSource
public import StacksFrontier.AlgebraicGeometry.Picard.SmoothCurveLocalDimension
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
public import StacksFrontier.RingTheory.CohenMacaulay.Witnesses
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cohen–Macaulay local rings along a smooth morphism

Let `f : X ⟶ Y` be a smooth morphism of locally Noetherian schemes and let `x ∈ X`. The map of
local rings `𝒪_{Y, f x} ⟶ 𝒪_{X, x}` is a flat local homomorphism whose closed fibre is the local
ring of the fibre `X_{f x}` at `x`, a regular local ring because `X_{f x}` is smooth over the
residue field `κ(f x)`. A regular local ring is Cohen–Macaulay, so the flat local criterion for
Cohen–Macaulayness (Stacks 045J) shows that `𝒪_{X, x}` is Cohen–Macaulay as soon as `𝒪_{Y, f x}`
is.

## Main results

* `AlgebraicGeometry.isCohenMacaulayLocalRing_stalk_of_smooth` — if `𝒪_{Y, f x}` is
  Cohen–Macaulay then so is `𝒪_{X, x}`.

## References

* [Stacks Project, Tag 045J](https://stacks.math.columbia.edu/tag/045J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- For a smooth morphism `f : X ⟶ Y` of locally Noetherian schemes and `x ∈ X`, if the local
ring `𝒪_{Y, f x}` is Cohen–Macaulay then so is `𝒪_{X, x}`. -/
@[ega "IV 6.3.5" "(ii), special case", ega "IV 7.3.11" "(ii), special case"]
theorem isCohenMacaulayLocalRing_stalk_of_smooth {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (x : X)
    (h : IsCohenMacaulayLocalRing (Y.presheaf.stalk (f x))) :
    IsCohenMacaulayLocalRing (X.presheaf.stalk x) := by
  let A := Y.presheaf.stalk (f x)
  let B := X.presheaf.stalk x
  let _ : Algebra A B := (f.stalkMap x).hom.toAlgebra
  have : IsLocalHom (algebraMap A B) := by
    rw [RingHom.algebraMap_toAlgebra]
    infer_instance
  have : Module.Flat A B := Flat.stalkMap f x
  have := isLocallyNoetherian_fiber f (f x)
  have hsmooth : Smooth (f.fiberToSpecResidueField (f x)) :=
    inferInstanceAs (Smooth (pullback.snd f (Y.fromSpecResidueField (f x))))
  have : IsRegularLocalRing ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) :=
    IsRegular.isRegularLocalRing_stalk
      (@isRegular_of_smooth_over_field (IsLocalRing.ResidueField (Y.presheaf.stalk (f x)))
        inferInstance (f.fiber (f x)) (f.fiberToSpecResidueField (f x)) hsmooth) _
  let I : Ideal B := (IsLocalRing.maximalIdeal A).map (algebraMap A B)
  let Q := B ⧸ I
  let e : Q ≃+* (f.fiber (f x)).presheaf.stalk (f.asFiber x) := quotientStalkEquivFiberStalk f x
  have hQsurj : Function.Surjective (algebraMap B Q) := Ideal.Quotient.mk_surjective
  have : Nontrivial Q := ⟨0, 1, fun h => by simpa using congrArg e h⟩
  have : IsLocalRing Q := IsLocalRing.of_surjective' (Ideal.Quotient.mk I) hQsurj
  have hQdepth : (Module.depth B (IsLocalRing.maximalIdeal B) Q : WithBot ℕ∞) =
      ringKrullDim Q := by
    rw [Module.depth_eq_depth_self_of_surjective_algebraMap (A := B) (B := Q) hQsurj]
    exact (isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay Q).mp
      ((isCohenMacaulayLocalRing_iff_of_ringEquiv e).mpr
        (IsRegularLocalRing.isCohenMacaulayLocalRing _))
  exact (isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay B).mpr
    ((Module.isMaximalCohenMacaulay_self_iff_of_flat A B).mpr
      ⟨(isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay A).mp h, hQdepth⟩)

end AlgebraicGeometry

end
