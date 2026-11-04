module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.LiftsOfObjects.Smoothness.Criterion

/-!
# Smoothness of the first factor of a smooth composite

Let `φ : 𝓕 ⟶ 𝓖` be a morphism of deformation categories over `𝒞_Λ` and let `ψ : 𝓖 ⟶ 𝓗` be a
morphism into any category over `𝒞_Λ`. If `φ` is surjective on tangent spaces and the
composite `φ ⋙ ψ` is smooth, then `φ` is smooth.

## Main results

* `Deformation.isSmooth_of_differential_surjective_of_comp`: the criterion.

## Implementation notes

The target `𝓗` of the second morphism need not be a deformation category, nor even cofibered
in groupoids: it only has to receive the lifting arrows produced by smoothness of the
composite, and a based functor preserves the property of lying over a given morphism of the
base. This is why the proof goes through the existence-of-lifts half of
`Deformation.isSmooth_iff_differential_surjective_and_lifts` rather than through the
definition of smoothness: the definition asks for a comparison arrow in `𝓖`, which `ψ` cannot
reflect, whereas the criterion asks only for a lift in `𝓕`.

## References

* [Stacks Project, Tag 0E3R](https://stacks.math.columbia.edu/tag/0E3R)
-/

@[expose] public section

namespace Deformation

section
open CategoryTheory
universe u w u₁ v₁ u₂ v₂ u₃ v₃

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- **Stacks Project, Tag 0E3R.** A morphism of deformation categories is smooth if its
differential is surjective and its composite with another morphism is smooth. -/
@[stacks 0E3R]
public theorem isSmooth_of_differential_surjective_of_comp
    {𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
    {𝓖 : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
    {𝓗 : BasedCategory.{v₃, u₃} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
    (h𝓕 : IsDeformationCategory 𝓕.p)
    (h𝓖 : IsDeformationCategory 𝓖.p)
    (φ : BasedFunctor 𝓕 𝓖) (ψ : BasedFunctor 𝓖 𝓗)
    (hd : Function.Surjective
      (differential h𝓕.predeformation.cofibered
        h𝓖.predeformation.cofibered φ))
    (hsmooth : IsSmooth (BasedFunctor.comp φ ψ)) :
    IsSmooth φ := by
  rw [isSmooth_iff_differential_surjective_and_lifts h𝓕 h𝓖 φ]
  refine ⟨hd, ?_⟩
  intro B A f hf x hlift
  obtain ⟨y', g, hg⟩ := hlift
  have hψg : (𝓗.p).IsHomLift f (ψ.map g) :=
    BasedFunctor.preserves_isHomLift ψ f g
  have hsurj : Function.Surjective f.hom := hf.2.2.2.2.1
  obtain ⟨x', h, -, hh, -, -⟩ := hsmooth f hsurj (ψ.obj y') x.1 (ψ.map g) hψg
  exact ⟨x', h, hh⟩

end

end Deformation
