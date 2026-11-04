module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.RefinementKillsClosure

/-!
# Two refinements of a proper model have a common refinement

`AlgebraicGeometry.Scheme.ZariskiRiemann.RefinementsCofiltered B` asks that two refinements
`Y₁ ⟶ Y` and `Y₂ ⟶ Y` of a proper model of `η = Spec (Frac B)` over `Spec B` be refined by one
model `Y₃`, with equal composites `Y₃ ⟶ Y`. This is the cospan property of the cofiltered category
of proper models, `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.isCofiltered`: `Y₃` is the
equalizer model (`ProperModel.eqLocus`) of the two composites out of the fibre product model
`Y₁ ×_{Spec B} Y₂` (`ProperModel.prod`).

## Main results

* `AlgebraicGeometry.Scheme.ZariskiRiemann.refinementsCofiltered` — **two refinements of a proper
  model have a common refinement**, for every domain `B`.

## References

* Travaux de Gabber sur l'uniformisation locale et la cohomologie étale des schémas
  quasi-excellents, Exposé XVIII-A (L. Illusie), last remark of §2, Astérisque 363–364 (2014)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.ZariskiRiemann

/-- **Two refinements of a proper model have a common refinement** with equal composites, for
every domain `B`: the cospan property of the cofiltered category of proper models. -/
theorem refinementsCofiltered (B : Type u) [CommRing B] [IsDomain B] :
    RefinementsCofiltered B := by
  intro M₁ M₂ M φ₁ φ₂
  obtain ⟨M₃, ψ₁, ψ₂, h⟩ :=
    IsCofiltered.cospan (C := ProperModel B) (show M₁ ⟶ M from φ₁) (show M₂ ⟶ M from φ₂)
  exact ⟨M₃, ψ₁, ψ₂, congrArg ProperModel.Refinement.π h⟩

end AlgebraicGeometry.Scheme.ZariskiRiemann

end
