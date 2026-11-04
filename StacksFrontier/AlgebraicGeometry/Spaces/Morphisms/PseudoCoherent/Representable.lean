module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType

/-!
# Representable algebraic spaces and relative pseudo-coherence

Relative pseudo-coherence of an object of the derived category of an algebraic space `X`
over an algebraic space `Y` is defined, when `X` and `Y` are representable, by passing to
schemes representing them. This is legitimate because a scheme morphism representing a
morphism of representable algebraic spaces which is locally of finite type is itself
locally of finite type, which is what this file records.

## Main results

* `AlgebraicGeometry.Space.locallyOfFiniteType_of_represents`: any scheme morphism
  representing a morphism of representable algebraic spaces which is locally of finite
  type is locally of finite type: **Stacks 0CSW**.

## Implementation notes

A representation of a morphism `f : X ⟶ Y` of algebraic spaces by a morphism `f₀ : U ⟶ V`
of objects of the site is a pair of isomorphisms `yoneda.obj U ≅ X` and
`yoneda.obj V ≅ Y` making the evident square commute. Such a pair is in particular a
commuting square of étale charts: an isomorphism of presheaves is representable, and each
of its represented base changes is an isomorphism of objects of the site, whose underlying
scheme morphism is therefore an isomorphism and so étale. Local finite type of `f₀` is then
an instance of the defining chart condition of
`AlgebraicGeometry.Space.IsLocallyOfFiniteType`, so no separate algebraic-space hypothesis
on `X` or `Y` is needed: by Stacks 025Z a representable presheaf on the big fppf site is an
algebraic space, and the two isomorphisms transport that to `X` and `Y`.

## References

* [Stacks Project, Tag 0CSW](https://stacks.math.columbia.edu/tag/0CSW)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

/-- **Stacks 0CSW.** If a morphism `f` of algebraic spaces over `S` is locally of finite
type and a morphism `f₀` of objects of the site represents it, through isomorphisms
`yoneda.obj U ≅ X` and `yoneda.obj V ≅ Y`, then the scheme morphism underlying `f₀` is
locally of finite type. -/
@[stacks 0CSW "representing_locally_finite_type"]
theorem locallyOfFiniteType_of_represents (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f) (U V : BigFppfOver B S hS) (f₀ : U ⟶ V)
    (eX : yoneda.obj U ≅ X) (eY : yoneda.obj V ≅ Y)
    (hrep : yoneda.map f₀ ≫ eY.hom = eX.hom ≫ f) :
    LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map f₀) := by
  have hchart {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ G) :
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf e.hom := by
    refine ⟨Functor.relativelyRepresentable.of_isIso yoneda e.hom, ?_⟩
    intro A D g fst snd h
    have : IsIso (yoneda.map snd) := h.isIso_snd_of_isIso
    have : IsIso snd := Yoneda.fullyFaithful.isIso_of_isIso_map snd
    have : IsIso ((BigFppfOver.toScheme B S hS).map snd) :=
      Functor.map_isIso (BigFppfOver.toScheme B S hS) snd
    exact inferInstanceAs (Etale _)
  exact hf U V eX.hom eY.hom f₀ (hchart eX) (hchart eY) hrep

end AlgebraicGeometry.Space

end
