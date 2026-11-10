module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.CofiberedPresentation.Morphism
public import StacksFrontier.Deformation.Predeformation.Basic
public import StacksFrontier.Deformation.Smooth.EssentiallySurjective

/-!
# Equivalence of a smooth quotient presentation

If a smooth morphism from a set-valued functor into a category cofibered in groupoids over
`𝒞_Λ` is essentially surjective over the residue field, the canonical morphism from the
quotient of its groupoid in functors is an equivalence.

## Main results

* `Deformation.presentationMorphism_isEquivalence_of_isSmooth_of_fiber_essSurj`: the quotient
  morphism of a smooth, fibrewise essentially surjective presentation is an equivalence.

## References

* [Stacks Project, Tag 06L1](https://stacks.math.columbia.edu/tag/06L1)
-/

@[expose] public section

open CategoryTheory

universe u w u₁ v₁ uU

namespace Deformation

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type u₁} [Category.{v₁} F]
variable (p : F ⥤ ArtinianLocalAlgCat.{u, w, w} Λ k)
variable (U : ArtinianLocalAlgCat.{u, w, w} Λ k ⥤ Type uU)
variable (f : BasedFunctor
    (BasedCategory.ofFunctor (Functor.Elements.π U))
    (BasedCategory.ofFunctor p))

/-- The canonical quotient morphism associated to a smooth presentation is an equivalence if
the presentation is essentially surjective over the residue field. -/
@[stacks 06L1 "quotient_equivalence"]
theorem presentationMorphism_isEquivalence_of_isSmooth_of_fiber_essSurj
    (hp : IsCofiberedInGroupoids p)
    (hf : IsSmooth f)
    (h₀ : (fiberFunctor f (residueFieldObject Λ k)).EssSurj) :
    (presentationMorphism p U f.toFunctor f.w
      (presentationGroupoid p U f.toFunctor f.w hp)).1.IsEquivalence :=
  (presentationMorphism_isEquivalence_iff p U f.toFunctor f.w
      (presentationGroupoid p U f.toFunctor f.w hp) hp).2
    (essSurj_of_isSmooth_of_fiber_essSurj f hp hf h₀)

end Deformation

end
