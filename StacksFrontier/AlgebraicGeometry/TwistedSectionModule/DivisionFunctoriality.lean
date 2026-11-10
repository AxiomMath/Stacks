module

public import StacksFrontier.AlgebraicGeometry.TwistedSectionModule.Functoriality
public import StacksFrontier.AlgebraicGeometry.TwistedSectionModule.MonoidalFunctor

/-!
# The divisions by the powers of a section are natural in the twisted module

Stacks Tag 01QJ asserts its comparison is functorial in `ℱ`, and Stacks Tag 0B5I's morphism
`M̃ ⟶ f_* ℱ` is asked to be a natural transformation in `ℱ`. The graded module of twisted
sections is covariant in `ℱ`
(`StacksFrontier/AlgebraicGeometry/TwistedSectionModule/Functoriality.lean`), and this file proves
that **every stage of the division machinery commutes with that covariance**: multiplication by
`s`, its iterates, the divisions by the powers of `s`, and the divisions obtained after a monoidal
functor.

This is the division-level half of the naturality in `ℱ`. The other half — the naturality of Tag
0B5L's map itself, out of the degree-zero localization — is the sibling
`StacksFrontier/AlgebraicGeometry/TwistedSectionModule/LocalizationFunctoriality.lean`, which takes
the results here as its hypothesis on numerators.

## Main results

* `Stacks.TwistedSections.shiftBySection_twistSectionsMap`: multiplication by `s` commutes with
  the map induced by `φ : F ⟶ F'`. The only input is
  `Stacks.TwistedSections.actMap_comp_twistPowMap`, the naturality of the action in the twisted
  object.
* `Stacks.TwistedSections.shiftPow_twistSectionsMap`: the same for the `k`-fold multiplication.
* `Stacks.TwistedSections.powerDivision_twistSectionsMap`: **the divisions are natural in the
  twisted module.** Since the divisions are defined as the inverse of a bijection, this is proved
  by applying that bijection to both sides.
* `Stacks.TwistedSections.mapTwistPow_naturality` and
  `Stacks.TwistedSections.mapTwistSections_twistSectionsMap`: carrying a twisted section along a
  monoidal functor `G` commutes with the covariance, by one naturality square of the oplax
  tensorator per copy of `L`.
* `Stacks.TwistedSections.monoidalDivision_twistSectionsMap`: **the divisions obtained through
  `G` are natural in the twisted module.**

## Implementation notes

`localizationLiftOfDegree`'s value on a fraction is the division of its numerator, so the
naturality square of the sibling file reduces to exactly `monoidalDivision_twistSectionsMap` below.
The induced map on the degree-zero localizations that the square's other side needs is the
covariance of `AlgebraicGeometry.ProjectiveSpectrum.Proj.GradedModuleDegreeZeroLocalization` in
the graded module, `Stacks.SheafOfModules.mapDegreeZeroLocalization`.

## References

* [Stacks Project, Tag 01QJ](https://stacks.math.columbia.edu/tag/01QJ)
* [Stacks Project, Tag 0B5I](https://stacks.math.columbia.edu/tag/0B5I)
* [Stacks Project, Tag 0B5L](https://stacks.math.columbia.edu/tag/0B5L)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory DirectSum
open Stacks.GradedSections (powSections sectionRing HasTrivialSelfBraiding)
open Stacks.TensorPowers (natTensorPow)

universe v₂ u₂ v u

namespace Stacks.TwistedSections

section Abstract

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {F F' L : C}


/-- **Multiplication by `s` is natural in the twisted module.** The map induced on twisted
sections by `φ : F ⟶ F'` is postcomposition with the whiskered `φ`, and the action whiskers on the
other side. -/
theorem shiftBySection_twistSectionsMap {d : ℕ} (s : powSections L d) (φ : F ⟶ F') {m : ℕ}
    (t : twistSections F L m) :
    shiftBySection s (twistSectionsMap φ m t) =
      twistSectionsMap φ (m + d) (shiftBySection s t) := by
  rw [shiftBySection_eq, shiftBySection_eq, twistSectionsMap, twistSectionsMap,
    actMap_comp_twistPowMap, Category.assoc]

/-- **The `k`-fold multiplication by `s` is natural in the twisted module.** -/
theorem shiftPow_twistSectionsMap {d : ℕ} (s : powSections L d) (φ : F ⟶ F') (k : ℕ)
    (u : twistSections F L 0) :
    shiftPow s k (twistSectionsMap φ 0 u) = twistSectionsMap φ (d * k) (shiftPow s k u) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [shiftPow_succ, shiftPow_succ, ih, shiftBySection_twistSectionsMap]
      rfl

variable [Preadditive C] [(tensorRight L).Additive]

/-- **The divisions by the powers of an invertible `s` are natural in the twisted module.**
Dividing the image of `t` and taking the image of the division of `t` agree: both have the same
product with `sᵏ`, and multiplication by `sᵏ` is injective. -/
theorem powerDivision_twistSectionsMap {d : ℕ} (s : powSections L d) [IsIso s] (φ : F ⟶ F')
    (k : ℕ) (t : twistSections F L (d * k)) :
    powerDivision s k (twistSectionsMap φ (d * k) t) =
      twistSectionsMap φ 0 (powerDivision s k t) := by
  refine (bijective_shiftPow (F := F') s k).injective ?_
  rw [shiftPow_powerDivision, shiftPow_twistSectionsMap, shiftPow_powerDivision]

end Abstract

section Monoidal

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  (G : C ⥤ D) [G.Monoidal] {F F' L : C}


/-- **The comparison `G(F ⊙ m) ⟶ (G F) ⊙ m` is natural in `F`.** One naturality square of the
oplax tensorator per copy of `L`. -/
theorem mapTwistPow_naturality (φ : F ⟶ F') (m : ℕ) :
    G.map (twistPowMap L φ m) ≫ mapTwistPow G F' L m =
      mapTwistPow G F L m ≫ twistPowMap (G.obj L) (G.map φ) m := by
  induction m with
  | zero => exact (Category.comp_id (G.map φ)).trans (Category.id_comp (G.map φ)).symm
  | succ m ih =>
      change G.map (twistPowMap L φ m ▷ L) ≫ (Functor.OplaxMonoidal.δ G (twistPow F' L m) L ≫
          mapTwistPow G F' L m ▷ G.obj L) =
        (Functor.OplaxMonoidal.δ G (twistPow F L m) L ≫ mapTwistPow G F L m ▷ G.obj L) ≫
          twistPowMap (G.obj L) (G.map φ) m ▷ G.obj L
      rw [← Category.assoc, ← Functor.OplaxMonoidal.δ_natural_left]
      simp only [Category.assoc]
      rw [← comp_whiskerRight, ih, comp_whiskerRight]

/-- **Carrying a twisted section along `G` is natural in the twisted module.** -/
theorem mapTwistSections_twistSectionsMap (φ : F ⟶ F') {m : ℕ} (t : twistSections F L m) :
    mapTwistSections G (twistSectionsMap φ m t) =
      twistSectionsMap (G.map φ) m (mapTwistSections G t) := by
  rw [mapTwistSections, mapTwistSections, twistSectionsMap, twistSectionsMap, Functor.map_comp]
  simp only [Category.assoc]
  rw [mapTwistPow_naturality]

variable [Preadditive C] [Preadditive D] [G.Additive]
  [(tensorRight (G.obj L)).Additive]

/-- **The divisions obtained through `G` are natural in the twisted module.** This is what the
naturality in `ℱ` of Stacks Tag 0B5L's map reduces to on numerators. -/
theorem monoidalDivision_twistSectionsMap {d : ℕ} (s : powSections L d)
    [IsIso (mapPowSections G s)] (φ : F ⟶ F') (n : ℕ) (t : twistSections F L (d * n)) :
    monoidalDivision G s n (twistSectionsMap φ (d * n) t) =
      twistSectionsMap (G.map φ) 0 (monoidalDivision G s n t) := by
  rw [monoidalDivision_apply, monoidalDivision_apply, mapTwistSections_twistSectionsMap,
    powerDivision_twistSectionsMap]

end Monoidal

end Stacks.TwistedSections

end
