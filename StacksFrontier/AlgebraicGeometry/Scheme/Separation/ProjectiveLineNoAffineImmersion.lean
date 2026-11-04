module

public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ProjectiveLineDegree
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineSections

/-!
# The projective line admits no immersion into an affine scheme

The projective line over a field admits no immersion into any affine scheme whatsoever: not an
open immersion, not a closed immersion, and not a locally closed immersion either.

## Main results

* `AlgebraicGeometry.not_isImmersion_to_affine_projectiveLine`: there is no immersion from the
  projective line over a field into an affine scheme.

## Implementation notes

An affine scheme is quasi-affine, and a quasi-compact locally closed subscheme of a quasi-affine
scheme is again quasi-affine. The projective line over a field is quasi-compact, so an immersion
of it into an affine scheme would make it quasi-affine, and the canonical morphism from a
quasi-affine scheme to the spectrum of its global sections is an open immersion, hence injective
on points. But the global sections of the projective line are just the constants, so that
spectrum is a single point, while the projective line has the two distinct points `0` and `∞`.

The hypothesis is immersion rather than open or closed immersion: those are stronger, so would
give a weaker statement. No finiteness, Noetherian or algebra hypothesis is placed on the target
either, since the argument needs none.

## References

* [Stacks Project, Tag 01KX](https://stacks.math.columbia.edu/tag/01KX)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The spectrum of the global sections of the projective line over a field is a single point:
those global sections are the constants. -/
lemma subsingleton_spec_globalSections_projectiveLine (k : Type u) [Field k] :
    Subsingleton (Spec Γ(projectiveLine k, ⊤)) := by
  have := isIso_constantsToGlobalSections k
  have hsurj : Function.Surjective (CommRingCat.Hom.hom
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (projectiveLine k ↘ Spec (.of k)).appTop)) :=
    (ConcreteCategory.bijective_of_isIso _).2
  have hinj := PrimeSpectrum.comap_injective_of_surjective _ hsurj
  exact ⟨fun a b ↦ hinj (Subsingleton.elim _ _)⟩

/-- The projective line over a field admits no immersion into any affine scheme. -/
@[stacks 01KX "projective_line_no_immersion_into_affine"]
theorem not_isImmersion_to_affine_projectiveLine
    (k : Type u) [Field k] (A : Scheme.{u}) [IsAffine A] (f : projectiveLine k ⟶ A) :
    ¬ IsImmersion f := by
  intro hf
  have : (projectiveLine k).IsQuasiAffine := Scheme.IsQuasiAffine.of_isImmersion f
  have hinj : Function.Injective (projectiveLine k).toSpecΓ.base :=
    (projectiveLine k).toSpecΓ.isOpenEmbedding.injective
  exact projectiveLineZero_ne_projectiveLineInfinity k
    (hinj ((subsingleton_spec_globalSections_projectiveLine k).elim _ _))

end AlgebraicGeometry

end
