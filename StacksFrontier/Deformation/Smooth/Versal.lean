module

public import StacksFrontier.Deformation.Basic
public import StacksFrontier.Deformation.Cofibered
public import StacksFrontier.Deformation.Completed.Basic
public import StacksFrontier.Deformation.FormalObject.Associated
public import StacksFrontier.Deformation.FormalObject.Basic
public import StacksFrontier.Deformation.Smooth.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Versal formal objects

A versal formal object is one whose associated morphism is smooth.

## Main definitions

* `IsVersal` is versality of a formal object.

## Main results

* `isSmooth_of_iso`: smoothness of a morphism of categories over `𝒞_Λ` is invariant under
  isomorphism of morphisms.
* `associatedMorphism_pointInclusion_isHomLift`: the canonical arrow into the value of an
  associated morphism at an Artinian point lies over the chosen factorization of that point.

## Implementation notes

The associated morphism uses auxiliary choices of pushforwards. Versality asks for
smoothness for every such choice, so the property belongs to the formal object rather
than to a chosen presentation of its associated morphism. This abbreviated predicate
unfolds directly to the smoothness condition used by downstream lifting arguments.

## References

* [Stacks Project, Tag 06HR](https://stacks.math.columbia.edu/tag/06HR)
-/

@[expose] public section

namespace Deformation

/-! ### Versal formal objects -/

section
open CategoryTheory
universe u v w uF vF u₁ v₁ u₂ v₂


variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {F : Type uF} [Category.{vF} F] {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}

/-- Smoothness of a morphism of categories over `𝒞_Λ` is invariant under isomorphism of
morphisms: the lift produced for one is transported by the comparison 2-cell, which is
vertical. -/
public theorem isSmooth_of_iso
    {𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, v, w} Λ k)}
    {𝓖 : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, v, w} Λ k)}
    {φ ψ : BasedFunctor 𝓕 𝓖} (e : φ ≅ ψ) (hψ : IsSmooth ψ) : IsSmooth φ := by
  intro B A f hf y x g hg
  have : 𝓖.p.IsHomLift f g := hg
  have hg' : 𝓖.p.IsHomLift f (g ≫ e.hom.app x) := by
    have : 𝓖.p.IsHomLift (𝟙 A) (e.hom.app x) :=
      e.hom.isHomLift ((BasedFunctor.w_obj φ x).symm.trans
        (IsHomLift.codomain_eq 𝓖.p f g))
    exact inferInstance
  obtain ⟨x', h, a, hh, ha, hfac⟩ := hψ f hf y x (g ≫ e.hom.app x) hg'
  refine ⟨x', h, e.hom.app x' ≫ a, hh, ?_, ?_⟩
  · have : 𝓖.p.IsHomLift (𝟙 B) (e.hom.app x') :=
      e.hom.isHomLift (IsHomLift.domain_eq 𝓕.p f h)
    have : 𝓖.p.IsHomLift (𝟙 B) a := ha
    exact inferInstance
  · refine (cancel_mono (e.hom.app x)).1 ?_
    rw [e.hom.naturality h, hfac]
    simp [Category.assoc]

/-- The canonical arrow into the value of the associated morphism at an Artinian point of the
base lies over the chosen factorization of that point. -/
public theorem associatedMorphism_pointInclusion_isHomLift
    (η : FormalObject p) {P : ChosenPushforwards p} (H : AssociatedMorphism η P)
    (α : (restrictedCoyoneda η.base).Elements) :
    p.IsHomLift (H.factor α) (H.pointInclusion α) := by
  have h := ((P (H.factor α)).cocartesian
    ⟨η.level (H.level α), η.level_eq (H.level α)⟩).toIsHomLift
  rw [← H.pointInclusion_eq α] at h
  exact (IsHomLift.eqToHom_comp_lift_iff p (H.factor α)
    (H.pointInclusion α) (H.obj_eq α)).mp h

/-- A formal object is versal when its associated morphism from the represented
functor is smooth, independently of the auxiliary pushforward choices. -/
@[stacks 06HR,
  sga "7 VI 1.19" "(1)",
  sga "7 VI 1.9" "versal formal object"]
public abbrev IsVersal (hp : IsCofiberedInGroupoids p)
    (ξ : FormalObject p) : Prop := ∀ pushforwards : ChosenPushforwards p,
  IsSmooth (associatedMorphism hp ξ pushforwards).toBasedFunctor

end

end Deformation
