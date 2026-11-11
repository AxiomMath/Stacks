module

public import StacksFrontier.Deformation.Smooth.FullyFaithful
public import StacksFrontier.Deformation.Smooth.Versal
public import StacksFrontier.Deformation.RimSchlessingerCategory.Prorepresentable

/-!
# Every object receives a morphism from a level of a versal formal object

Let `p : F ⥤ 𝒞_Λ` be a predeformation category and `ξ` a versal formal object of `F`
(Stacks 06HR): the associated morphism `h_R ⟶ F` from the cofibered set represented by the base
`R` of `ξ` is smooth. A smooth morphism of predeformation categories is essentially surjective
(Stacks 06HN), so every object `x` of `F` over an Artinian `A` is isomorphic to the value of the
associated morphism at some `R ⟶ A`, which is a pushforward of a level `ξ_n` along
`R / 𝔪^{n+1} ⟶ A`. Composing the canonical arrow `ξ_n ⟶ ξ^#(α)` with that isomorphism gives a
morphism `ξ_n ⟶ x`.

## Main results

* `Deformation.FormalObject.exists_level_hom_of_isVersal`: every object of a predeformation
  category receives a morphism from some level of a versal formal object.

## References

* [Stacks Project, Tag 06HR](https://stacks.math.columbia.edu/tag/06HR)
* [Stacks Project, Tag 06HN](https://stacks.math.columbia.edu/tag/06HN)
* [Stacks Project, Tag 06HC](https://stacks.math.columbia.edu/tag/06HC)
-/

@[expose] public section

namespace Deformation

open CategoryTheory

universe u w uF vF

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {F : Type uF} [Category.{vF} F] {p : F ⥤ ArtinianLocalAlgCat.{u, w, w} Λ k}

/-- **Every object of a predeformation category receives a morphism from a level of a versal
formal object.** If `ξ` is a versal formal object of a predeformation category `p : F ⥤ 𝒞_Λ`,
then for every object `x` of `F` there are `n` and a morphism `ξ_n ⟶ x`. -/
theorem FormalObject.exists_level_hom_of_isVersal (hp : IsPredeformationCategory p)
    (ξ : FormalObject p) (hξ : IsVersal hp.cofibered ξ) (x : F) :
    ∃ n, Nonempty (ξ.level n ⟶ x) := by
  let H := associatedMorphism hp.cofibered ξ (chosenPushforwardsOfCofibered p hp.cofibered)
  have hR : IsPredeformationCategory (CategoryOfElements.π (restrictedCoyoneda ξ.base)) :=
    (isPredeformationCategory_iff _).2 (restrictedCoyoneda_isPredeformationFunctor ξ.base)
  have : H.toBasedFunctor.toFunctor.EssSurj :=
    essSurj_of_isSmooth (𝓕 := BasedCategory.ofFunctor
      (CategoryOfElements.π (restrictedCoyoneda ξ.base))) (𝓖 := BasedCategory.ofFunctor p)
      hR hp H.toBasedFunctor (hξ _)
  let α := H.toBasedFunctor.toFunctor.objPreimage x
  exact ⟨H.level α, ⟨H.pointInclusion α ≫ (H.toBasedFunctor.toFunctor.objObjPreimageIso x).hom⟩⟩

end Deformation
