module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Etale.FormallyEtaleScheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.FormallySmooth.Defs
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-!
# Formal étaleness is formal smoothness plus formal unramifiedness

A morphism of schemes is formally étale exactly when it is formally smooth and formally
unramified: the *unique* infinitesimal lifting property splits into existence of a filler and
uniqueness of a filler.

## Main results

* `AlgebraicGeometry.formallyEtale_iff_formallySmooth_and_formallyUnramified`: a morphism of
  schemes is formally étale if and only if it is formally smooth and formally unramified.

## Implementation notes

Formal unramifiedness is Mathlib's `AlgebraicGeometry.FormallyUnramified`, defined chart-wise on
coordinate rings; it is compared with uniqueness of fillers through
`AlgebraicGeometry.FormallyUnramified.of_hom_ext` and
`AlgebraicGeometry.FormallyUnramified.hom_ext`.

## References

* [Stacks Project, Tag 02H0](https://stacks.math.columbia.edu/tag/02H0)
* [Stacks Project, Tag 02HG](https://stacks.math.columbia.edu/tag/02HG)
* [Stacks Project, Tag 02HH](https://stacks.math.columbia.edu/tag/02HH)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A morphism of schemes is formally étale if and only if it is formally smooth and formally
unramified. -/
@[stacks 02HH, ega "IV 17.1.1" "étale ⟺ smooth+unram"]
theorem formallyEtale_iff_formallySmooth_and_formallyUnramified
    {X S : Scheme.{u}} (f : X ⟶ S) :
    FormallyEtale f ↔ (FormallySmooth f ∧ FormallyUnramified f) := by
  refine ⟨fun hf => ⟨?_, ?_⟩, ?_⟩
  · intro T T' hT hT' i hi g p hcomm
    obtain ⟨h, hh, -⟩ := hf i hi p g hcomm
    exact ⟨h, hh.2, hh.1⟩
  · refine FormallyUnramified.of_hom_ext f fun R T φ hφ hker g₁ g₂ hig hgf => ?_
    obtain ⟨h, -, huniq⟩ := hf (Spec.map φ)
      (Stacks.Smooth.isFirstOrderThickening_specMap φ hφ hker) (g₁ ≫ f) (Spec.map φ ≫ g₁)
      (by simp)
    exact (huniq g₁ ⟨rfl, rfl⟩).trans (huniq g₂ ⟨hig.symm, hgf.symm⟩).symm
  · rintro ⟨hsmooth, hunram⟩
    let : FormallyUnramified f := hunram
    intro T T' hT hT' i hi p g hcomm
    obtain ⟨h, hhf, hhi⟩ := hsmooth hT hT' i hi g p hcomm
    refine ⟨h, ⟨hhi, hhf⟩, fun h' hh' => ?_⟩
    have : IsClosedImmersion i := hi.1
    exact FormallyUnramified.hom_ext i ⟨2, by simpa using hi.2⟩ f
      (hh'.1.trans hhi.symm) (hh'.2.trans hhf.symm)

end AlgebraicGeometry

end
