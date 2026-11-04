module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrum
public import StacksFrontier.AlgebraicGeometry.FormalSpace.WeakIdealPresentation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineSupplement

/-!
# The formal spectrum as a weak-ideal colimit presentation

A quotient system `AlgebraicGeometry.FormalSpace.QuotientSystem` for a topological ring `A`
presents its formal spectrum `AlgebraicGeometry.FormalSpace.formalSpectrum` as the colimit of the
spectra of the quotients of `A` by its weak ideals of definition, that is, as a
`AlgebraicGeometry.FormalSpace.WeakIdealColimitPresentation` in the sense of Stacks 0AIC.

## Main definitions

* `AlgebraicGeometry.FormalSpace.QuotientSystem.weakIdealColimitPresentation`: the weak-ideal
  colimit presentation of the formal spectrum of a quotient system.

## Main results

* `AlgebraicGeometry.FormalSpace.hasThickeningPresentation_formalSpectrum`: the formal spectrum
  of a weakly admissible topological ring has a presentation by affine thickenings, with no
  condition on the size of the site.
* `AlgebraicGeometry.FormalSpace.hasAllSurjectivePresentations_formalSpectrum`: condition (5)
  of Stacks 0AIC for a formal spectrum satisfying the set-theoretic condition of Stacks 0AIS.

## References

* [Stacks Project, Tag 0AIC](https://stacks.math.columbia.edu/tag/0AIC)
* [Stacks Project, Tag 0AIF](https://stacks.math.columbia.edu/tag/0AIF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : Type u} [CommRing A] [TopologicalSpace A]

/-- The weak-ideal colimit presentation, in the sense of Stacks 0AIC, of the formal spectrum of a
quotient system for `A`: the colimit of the spectra of the quotients of `A` by its weak ideals
of definition. -/
noncomputable def QuotientSystem.weakIdealColimitPresentation (D : QuotientSystem B S hS A) :
    WeakIdealColimitPresentation B S hS A (formalSpectrum D) where
  diagram := D.diagram
  quotientIso _ := Iso.refl _
  quotientIso_natural {J K} f := by
    change (BigAffineFppf.toScheme B S hS).map (D.transition (leOfHom f)) ≫ 𝟙 _ =
      𝟙 _ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (show K.1 ≤ J.1 from leOfHom f)))
    rw [Category.comp_id, Category.id_comp]
    rfl
  colimitIso := Iso.refl _

/-- **The formal spectrum of a weakly admissible topological ring over `S` has a presentation
by affine thickenings**, with no condition on the size of the site. -/
theorem hasThickeningPresentation_formalSpectrum [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A) (D : QuotientSystem B S hS A) :
    HasThickeningPresentation B S hS (formalSpectrum D) :=
  hasThickeningPresentation_of_weakIdealColimitPresentation B S hS A hA
    D.weakIdealColimitPresentation

/-- **Stacks 0AIC, condition (5), for a formal spectrum.** The formal spectrum of a weakly
admissible topological ring over `S` which satisfies the set-theoretic condition of Stacks
0AIS is an affine formal algebraic space all of whose presentations by affine thickenings have
surjective section-ring projections. -/
theorem hasAllSurjectivePresentations_formalSpectrum [IsTopologicalRing A]
    [IsLinearTopology A A] (hA : TopologicalRing.IsWeaklyAdmissible A)
    (D : QuotientSystem B S hS A)
    (hX : SatisfiesSetTheoreticCondition B S hS (formalSpectrum D)) :
    HasAllSurjectivePresentations B S hS (formalSpectrum D) :=
  hasAllSurjectivePresentations_of_weakIdealColimitPresentation B S hS A hA hX
    D.weakIdealColimitPresentation

end AlgebraicGeometry.FormalSpace

end
