module

public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.FlatBaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The exceptional divisor commutes with flat base change

Let `g : X₁ ⟶ X₂` be a flat morphism of schemes and `I` a quasi-coherent ideal on `X₂`. By
Stacks tag 0805 (`AlgebraicGeometry.exists_isPullback_blowUpToBase_comap`) the blowup of `X₁` in
`I.comap g` is the base change along `g` of the blowup of `X₂` in `I`. This file lifts that
cartesian square to the exceptional divisors.

## Main results

* `AlgebraicGeometry.comap_exceptionalIdeal_of_isPullback`: in such a cartesian square the
  inverse image of the exceptional ideal is the exceptional ideal of the inverse-image centre.
* `AlgebraicGeometry.exists_isPullback_exceptionalDivisor_comap`: the exceptional divisor of the
  blowup of `X₁` in `I.comap g` sits in a cartesian square over that of the blowup of `X₂` in `I`.

## References

* [Stacks Project, Tag 0805](https://stacks.math.columbia.edu/tag/0805)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- In a cartesian square of blowups over a base change `g`, the inverse image of the exceptional
ideal along the comparison morphism of the blowups is the exceptional ideal of the inverse-image
centre. -/
theorem comap_exceptionalIdeal_of_isPullback {X₁ X₂ : Scheme.{u}} (I : X₂.IdealSheafData)
    (g : X₁ ⟶ X₂) {h : blowUp (I.comap g) ⟶ blowUp I}
    (hp : IsPullback (blowUpToBase (I.comap g)) h g (blowUpToBase I)) :
    (exceptionalIdeal I).comap h = exceptionalIdeal (I.comap g) :=
  calc (exceptionalIdeal I).comap h = I.comap (h ≫ blowUpToBase I) :=
        (Scheme.IdealSheafData.comap_comp I h (blowUpToBase I)).symm
    _ = I.comap (blowUpToBase (I.comap g) ≫ g) := by rw [hp.w]
    _ = exceptionalIdeal (I.comap g) :=
        Scheme.IdealSheafData.comap_comp I (blowUpToBase (I.comap g)) g

/-- **Stacks Project, Tag 0805 for the exceptional divisor.** For a flat `g : X₁ ⟶ X₂` and a
quasi-coherent ideal `I` on `X₂`, the exceptional divisor of the blowup of `X₁` in the inverse
image of `I` sits in a cartesian square over the exceptional divisor of the blowup of `X₂` in
`I`, above the cartesian square of the two blowup morphisms. -/
@[ega "IV 19.4.6" "(i), special case"]
theorem exists_isPullback_exceptionalDivisor_comap {X₁ X₂ : Scheme.{u}} (g : X₁ ⟶ X₂) [Flat g]
    (I : X₂.IdealSheafData) :
    ∃ (h : blowUp (I.comap g) ⟶ blowUp I)
      (e : exceptionalDivisor (I.comap g) ⟶ exceptionalDivisor I),
      IsPullback (blowUpToBase (I.comap g)) h g (blowUpToBase I) ∧
      IsPullback (exceptionalIdeal (I.comap g)).subschemeι e h
        (exceptionalIdeal I).subschemeι := by
  obtain ⟨h, hp⟩ := exists_isPullback_blowUpToBase_comap g I
  have hc := comap_exceptionalIdeal_of_isPullback I g hp
  have hle : exceptionalIdeal I ≤ (exceptionalIdeal (I.comap g)).map h := by
    rw [← hc]
    exact Scheme.IdealSheafData.le_map_comap _ _
  refine ⟨h, Scheme.IdealSheafData.subschemeMap _ _ h hle, hp,
    isPullback_of_isClosedImmersion _ _ _ _
      (Scheme.IdealSheafData.subschemeMap_subschemeι _ _ h hle).symm ?_⟩
  rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι]
  exact hc

end AlgebraicGeometry

end
