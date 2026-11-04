module

public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningPushoutFullyFaithful
public import StacksFrontier.Deformation.Artin.RimSchlessinger

/-!
# Condition (RS) from the thickening-and-affine pushouts

Condition (RS) of Stacks 07WP asks that a category fibred in groupoids `𝒵` over the big fppf site
of `S` turn certain pushouts of spectra of local Artinian rings into equivalences of fibre
categories. Every such pushout is a pushout along a thickening and an affine morphism: a closed
immersion between spectra of local Artinian rings is surjective, the target having a single
point, and any morphism between affine schemes is affine. So (RS) is the special case of the
conclusion of Stacks 07WN in which all four schemes are spectra of local Artinian rings.

## Main results

* `Deformation.Artin.isThickening_of_isArtinianLocal`: a closed immersion between spectra of local
  Artinian rings is a thickening.
* `Deformation.Artin.satisfiesRS_of_forall_isEquivalence`: if the comparison functor is an
  equivalence for every pushout along a thickening and an affine morphism, condition (RS) holds.

## References

* [Stacks Project, Tag 07WP](https://stacks.math.columbia.edu/tag/07WP)
* [Stacks Project, Tag 07WN](https://stacks.math.columbia.edu/tag/07WN)
* [Stacks Project, Tag 07WQ](https://stacks.math.columbia.edu/tag/07WQ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u u₁ v₁

namespace Deformation.Artin

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The underlying space of the spectrum of a local Artinian ring has at most one point. -/
theorem subsingleton_of_isArtinianLocal {X : BigFppfOver B S hS} (hX : IsArtinianLocal B S hS X) :
    Subsingleton ((BigFppfOver.toScheme B S hS).obj X) := by
  obtain ⟨hA, hL, hR⟩ := hX
  set T := (BigFppfOver.toScheme B S hS).obj X
  have : Subsingleton (PrimeSpectrum Γ(T, ⊤)) := by
    refine ⟨fun p q => ?_⟩
    have hp : p.asIdeal = IsLocalRing.maximalIdeal _ :=
      IsLocalRing.eq_maximalIdeal inferInstance
    have hq : q.asIdeal = IsLocalRing.maximalIdeal _ :=
      IsLocalRing.eq_maximalIdeal inferInstance
    exact PrimeSpectrum.ext (hp.trans hq.symm)
  have hs : Subsingleton (Spec Γ(T, ⊤)) := this
  refine ⟨fun x y => (T.isoSpec.hom.homeomorph.injective) ?_⟩
  exact Subsingleton.elim _ _

/-- The spectrum of a local Artinian ring is nonempty. -/
theorem nonempty_of_isArtinianLocal {X : BigFppfOver B S hS} (hX : IsArtinianLocal B S hS X) :
    Nonempty ((BigFppfOver.toScheme B S hS).obj X) := by
  obtain ⟨hA, hL, hR⟩ := hX
  set T := (BigFppfOver.toScheme B S hS).obj X
  obtain ⟨p⟩ : Nonempty (PrimeSpectrum Γ(T, ⊤)) := inferInstance
  exact ⟨T.isoSpec.inv.base p⟩

/-- **A closed immersion between spectra of local Artinian rings is a thickening**: the target
has a single point and the source is nonempty. -/
theorem isThickening_of_isArtinianLocal {X X' : BigFppfOver B S hS}
    (hX : IsArtinianLocal B S hS X) (hX' : IsArtinianLocal B S hS X') (i : X ⟶ X')
    (hi : IsClosedImmersion ((BigFppfOver.toScheme B S hS).map i)) :
    Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map i) := by
  refine ⟨hi, fun y => ?_⟩
  obtain ⟨x⟩ := nonempty_of_isArtinianLocal hX
  have := subsingleton_of_isArtinianLocal hX'
  exact ⟨x, Subsingleton.elim _ _⟩

variable {𝒵 : Type u₁} [Category.{v₁} 𝒵] (p : 𝒵 ⥤ BigFppfOver B S hS)

/-- **Condition (RS) from the thickening-and-affine pushouts.** If, for every pushout square of
schemes over `S` along a thickening `i : X ⟶ X'` and an affine morphism `X ⟶ Y`, the functor of
fibre categories `𝒵_{Y'} ⟶ 𝒵_Y ×_{𝒵_X} 𝒵_{X'}` is an equivalence, then `𝒵` satisfies condition
(RS) of Stacks 07WP. -/
theorem satisfiesRS_of_forall_isEquivalence (hp : p.IsFiberedInGroupoids)
    (h : letI : p.IsFibered := hp.isFibered
      ∀ {X X' Y Y' : BigFppfOver B S hS} (i : X ⟶ X') (j : X ⟶ Y) (i' : X' ⟶ Y')
        (j' : Y ⟶ Y') (w : i ≫ i' = j ≫ j'),
        Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map i) →
        IsAffineHom ((BigFppfOver.toScheme B S hS).map j) →
        IsPushout ((BigFppfOver.toScheme B S hS).map i)
          ((BigFppfOver.toScheme B S hS).map j)
          ((BigFppfOver.toScheme B S hS).map i')
          ((BigFppfOver.toScheme B S hS).map j') →
        (fiberSquareComparison p (p.chosenPullbacks) j i j' i' w.symm).IsEquivalence) :
    SatisfiesRS B S hS p hp := by
  intro X X' Y Y' i j i' j' w hX hX' hY _ _ _ _ _ hi hpo
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj X) := hX.1
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj Y) := hY.1
  exact h i j i' j' w (isThickening_of_isArtinianLocal hX hX' i hi)
    (isAffineHom_of_isAffine _) hpo

end Deformation.Artin
