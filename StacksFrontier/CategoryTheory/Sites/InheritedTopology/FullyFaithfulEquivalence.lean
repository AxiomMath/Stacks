module

public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.EssentiallySurjective
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.FibrewiseEquivalence

/-! # When a fully faithful 1-morphism of stacks is an equivalence

Let `(𝒞, J)` be a site and let `F` be a fully faithful 1-morphism of stacks over `𝒞`. Then `F` is
an equivalence over `𝒞` exactly when every object of every fibre of the target is, locally on the
base, in the essential image of `F` on fibres. This is Stacks 046N.

That the condition is necessary is the easy direction: the counit of an equivalence over `𝒞` is
vertical, so it is already an isomorphism of the fibre, and the maximal sieve will do. That it is
sufficient is the content: the local preimages of an object of a fibre assemble into a descent
datum for the source, effective descent there produces a global preimage, and the `Mor`-sheaf
condition of the target identifies its image with the given object. Full faithfulness then upgrades
essential surjectivity on fibres to an equivalence over `𝒞`.

## Main results

* `CategoryTheory.Functor.isEquivalenceOver_iff_locallyEssSurjOnFibers`: **Stacks 046N**.

## Implementation notes

"Equivalence" is read as equivalence in the 2-category of fibred categories over `𝒞`,
`CategoryTheory.Functor.IsEquivalenceOver`: a quasi-inverse that is again strictly a functor over
`𝒞`, with vertical unit and counit. It is data, hence the `Nonempty`.

The source states condition (2) over a covering *family* `{fᵢ : Uᵢ → U}`; it is rendered here by
the covering *sieve* form `CategoryTheory.Functor.LocallyEssSurjOnFibers`, which is the form
Stacks 06DV and 05W9 already use in this library. The two agree: a covering family generates a
covering sieve, and if `fᵢ^* x` is in the essential image on fibres then so is
`(g ≫ fᵢ)^* x = g^* (fᵢ^* x)`, because a 1-morphism of fibred categories commutes with the chosen
pullbacks up to `CategoryTheory.Functor.mapPullbackFiberIso'`.
-/

@[expose] public section

namespace CategoryTheory.Functor

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒴 : Type u₃} [Category.{v₃} 𝒴]

/-- **Stacks 046N**. Let `(𝒞, J)` be a site, let `p : 𝒳 ⥤ 𝒞` and `q : 𝒴 ⥤ 𝒞` be stacks over `𝒞`
and let `F : 𝒳 ⥤ 𝒴` be a fully faithful 1-morphism of fibred categories over `𝒞`. Then the
following are equivalent:

1. `F` is an equivalence over `𝒞`;
2. for every object `U` of `𝒞` and every object `x` of the fibre of `𝒴` over `U` there is a
   covering sieve of `U` along each member `f` of which `f^* x` is in the essential image of the
   functor induced by `F` on the fibres over the source of `f`. -/
@[stacks 046N]
theorem isEquivalenceOver_iff_locallyEssSurjOnFibers
    {p : 𝒳 ⥤ 𝒞} {q : 𝒴 ⥤ 𝒞} {F : 𝒳 ⥤ 𝒴} {J : GrothendieckTopology 𝒞}
    (h₁ : p.IsStack J) (h₂ : q.IsStack J) (hF : IsFibredOneMorphism p q F)
    [F.Full] [F.Faithful] :
    Nonempty (IsEquivalenceOver p q F) ↔ LocallyEssSurjOnFibers h₂.isFibered hF.comp_eq J := by
  have hp : p.IsFibered := h₁.isFibered
  have hq : q.IsFibered := h₂.isFibered
  constructor
  · rintro ⟨E⟩
    intro U x
    refine ⟨⊤, J.top_mem U, ?_⟩
    intro V f _
    exact (fiber_essSurj_of_isEquivalenceOver hF.comp_eq E V).mem_essImage
      (pullbackFiber q x f)
  · intro hloc
    have hess : ∀ U : 𝒞, (Fiber.mapOfComp p q F hF.comp_eq U).EssSurj := by
      intro U
      refine ⟨fun x => ?_⟩
      obtain ⟨R, hR, hRess⟩ := hloc U x
      exact exists_iso_of_locally_essImage hF h₁.hasEffectiveDescent (h₂.isMorSheaf U) x hR hRess
    exact ⟨isEquivalenceOver_of_exists_vertical_iso hF.comp_eq
      (exists_vertical_iso_of_fiber_essSurj hF.comp_eq hess)⟩

end CategoryTheory.Functor
