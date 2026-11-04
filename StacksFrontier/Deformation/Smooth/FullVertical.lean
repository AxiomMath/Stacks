module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverComp
public import StacksFrontier.Deformation.Smooth.Basic

/-!
# A full morphism with vertical preimages of objects is smooth

Smoothness of a morphism `φ : 𝓕 ⟶ 𝓖` of categories cofibered in groupoids over `𝒞_Λ` asks, for
every surjection `f : B → A` of `𝒞_Λ` and every lifting problem `g : y ⟶ φ(x)` over `f`, for an
object `x'` of `𝓕`, an arrow `h : x' ⟶ x` over `f` and an arrow `a : φ(x') ⟶ y` over `𝟙 B` with
`φ(h) = a ∘ g`.

Two properties of `φ` already solve every such problem, with no reference to `f` at all:

* every object `y` of `𝓖` admits an object `x'` of `𝓕` together with an arrow `φ(x') ⟶ y`
  *vertical* over `𝒞_Λ` — this is the arrow `a`, and it fixes `x'`;
* `φ` is full — this produces `h` from `a ∘ g`, and `h` then lies over `f` because `φ` is a
  morphism *over* `𝒞_Λ`, so `a ∘ g` lying over `𝟙 B ∘ f = f` forces it.

This is the criterion by which a comparison of two `2`-fibre products which is an equivalence
"on the nose" — the comparison functors of
`CategoryTheory.TwoFibreProductOver.mapBase` and of a change of the factors of a product over
`𝒞_Λ` — is seen to be smooth: neither is a lifting statement, and neither needs the
Rim–Schlessinger condition.

An equivalence over `𝒞_Λ` in the sense of `StacksRepresentableCFG.EquivalenceOver` satisfies
both hypotheses, the vertical arrow being a component of its counit; this is
`Deformation.isSmooth_of_equivalenceOver`.

## Main results

* `Deformation.isSmooth_of_full_of_exists_vertical`: the criterion.
* `Deformation.isSmooth_of_equivalenceOver`: an equivalence over `𝒞_Λ` is smooth.

## References

* [Stacks Project, Tag 06HG](https://stacks.math.columbia.edu/tag/06HG)
-/

@[expose] public section

namespace Deformation

open CategoryTheory

universe u v w v₁ u₁ v₂ u₂

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- **A full morphism over `𝒞_Λ` all of whose targets receive a vertical arrow from the image of
some object is smooth.** Every lifting problem over a surjection is solved by the given vertical
arrow together with a preimage under fullness: the preimage lies over the right morphism of
`𝒞_Λ` because the morphism is over `𝒞_Λ`, so no property of the surjection is used. -/
theorem isSmooth_of_full_of_exists_vertical
    {𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, v, w} Λ k)}
    {𝓖 : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, v, w} Λ k)}
    (φ : BasedFunctor 𝓕 𝓖) [φ.toFunctor.Full]
    (hvert : ∀ y : 𝓖.obj, ∃ (x : 𝓕.obj) (a : φ.obj x ⟶ y),
      𝓖.p.IsHomLift (𝟙 (𝓖.p.obj y)) a) :
    IsSmooth φ := by
  intro B A f _ y x g hg
  obtain ⟨x', a, ha⟩ := hvert y
  have hB : 𝓖.p.obj y = B := IsHomLift.domain_eq 𝓖.p f g
  subst hB
  have := hg
  have := ha
  refine ⟨x', φ.toFunctor.preimage (a ≫ g), a, ?_, ha, φ.toFunctor.map_preimage _⟩
  refine (BasedFunctor.isHomLift_iff φ f (φ.toFunctor.preimage (a ≫ g))).mp ?_
  rw [φ.toFunctor.map_preimage (a ≫ g)]
  exact IsHomLift.comp_lift_id_left' 𝓖.p (𝓖.p.obj y) a f g

/-- **An equivalence of categories cofibered in groupoids over `𝒞_Λ` is smooth.** The vertical
arrow onto an object of the target is the component of the counit at it, which is vertical
because the counit is a `2`-cell over `𝒞_Λ`; fullness is fullness of an equivalence. -/
theorem isSmooth_of_equivalenceOver
    {𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, v, w} Λ k)}
    {𝓖 : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, v, w} Λ k)}
    (e : StacksRepresentableCFG.EquivalenceOver 𝓕.p 𝓖.p)
    (φ : BasedFunctor 𝓕 𝓖) (hφ : φ.toFunctor = e.hom.functor) :
    IsSmooth φ := by
  have hequiv : e.hom.functor.IsEquivalence := e.isEquivalence_hom_functor
  have hfull : φ.toFunctor.Full := by rw [hφ]; infer_instance
  refine isSmooth_of_full_of_exists_vertical φ (fun y => ?_)
  refine ⟨e.inv.functor.obj y,
    eqToHom (Functor.congr_obj hφ (e.inv.functor.obj y)) ≫ e.counitIso.hom.app y, ?_⟩
  have := e.isHomLift_counitIso_hom_app y
  infer_instance

end Deformation

end
