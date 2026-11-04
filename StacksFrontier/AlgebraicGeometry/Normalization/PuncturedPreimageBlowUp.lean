module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.IsomorphismOffCenter.Basic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NormalMorphism.BaseFieldExtension
public import StacksFrontier.AlgebraicGeometry.Normalization.ComplementSpecialFiber

/-!
# Blowing up a closed point in the special fibre preserves normality off that fibre

Let `Y` be a normal scheme over a local ring `B` and let `y` be a closed point of `Y` lying over
the closed point of `Spec B`. Blowing up `Y` at the reduced closed subscheme `{y}` does not change
the part of `Y` lying over the punctured spectrum of `B`, because `y` is not in that part. Hence
the complement of the special fibre of the blown-up scheme is again normal.

## Main results

* `AlgebraicGeometry.isNormal_complementSpecialFiber_blowUpToBase_vanishingIdeal`: the complement
  of the special fibre of the blowup of a normal scheme at a closed point of its special fibre is
  normal.

## Implementation notes

The complement of the special fibre of the composite `blowUpToBase I ≫ g` is by definition the
preimage of the punctured spectrum, and taking preimages along a composite is taking preimages
twice. So the scheme in question is the restriction of the blowup over the open
`g ⁻¹ᵁ Stacks.Divisors.puncturedSpectrum B` of `Y`. That open misses `y`, since `g` sends `y` to
the closed point of `Spec B`, which the punctured spectrum omits; the support of the vanishing
ideal of `{y}` being `{y}`, Tag 02OS makes the blowup an isomorphism over that open. Normality is
then inherited from the open subscheme of `Y` by Tag 033J and transported along the isomorphism.

## References

* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 033J](https://stacks.math.columbia.edu/tag/033J)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The part of `Y` lying over the punctured spectrum of a local base misses a point mapping to
the closed point, hence avoids the support of that point's vanishing ideal. -/
private theorem subset_compl_support_vanishingIdeal
    {B : Type u} [CommRing B] [IsLocalRing B] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of B)) (y : Y) (hy : IsClosed ({y} : Set Y))
    (hgy : g y = IsLocalRing.closedPoint B) :
    ((g ⁻¹ᵁ Stacks.Divisors.puncturedSpectrum B : Y.Opens) : Set Y) ⊆
      ((Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)).support : Set Y)ᶜ := by
  intro z hz
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
  intro hzy
  have hzy' : z = y := hzy
  have hgz : g z ∈ Stacks.Divisors.puncturedSpectrum B := hz
  rw [hzy', hgy] at hgz
  exact hgz rfl

/-- Let `Y` be a normal scheme over a local ring `B` and let `y` be a closed point of `Y` over the
closed point of `Spec B`. The complement of the special fibre of the blowup of `Y` at `y` is
normal, the blowup being an isomorphism there. -/
public theorem isNormal_complementSpecialFiber_blowUpToBase_vanishingIdeal
    {B : Type u} [CommRing B] [IsLocalRing B] {Y : Scheme.{u}} [IsNormal Y]
    (g : Y ⟶ Spec (.of B)) (y : Y) (hy : IsClosed ({y} : Set Y))
    (hgy : g y = IsLocalRing.closedPoint B) :
    IsNormal (AlgebraicGeometry.SemistableReduction.complementSpecialFiber
      (AlgebraicGeometry.blowUpToBase
          (Scheme.IdealSheafData.vanishingIdeal
            (⟨{y}, hy⟩ : TopologicalSpace.Closeds Y)) ≫ g)) := by
  have hiso : IsIso (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
      (⟨{y}, hy⟩ : Closeds Y)) ∣_ (g ⁻¹ᵁ Stacks.Divisors.puncturedSpectrum B)) :=
    isIso_blowUpToBase_restrict_of_subset_compl_support _ _
      (subset_compl_support_vanishingIdeal g y hy hgy)
  exact isNormal_of_iso (@asIso _ _ _ _ _ hiso)

end AlgebraicGeometry

end
