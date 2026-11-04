module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentFromSpaceBaseFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPushforward

/-!
# Faithfulness of the functor from the base to the groupoid

Let `(U, R, s, t, c)` be a groupoid in algebraic spaces, let `X` be an algebraic space and let
`φ : U ⟶ X` be an étale morphism with `t ≫ φ = s ≫ φ`.  The functor
`AlgebraicGeometry.Space.quasicoherentFromSpaceBase` sends a quasi-coherent `𝒪_X`-module `ℱ` to
`φ^*ℱ` with its canonical transition morphism.  A morphism of quasi-coherent modules on the
groupoid is a morphism of the underlying modules subject to a condition, and the underlying
morphism of the image of `ψ` is `φ^*ψ`, so the functor is faithful as soon as the inverse image
of modules along `φ` is.

## Main results

* `AlgebraicGeometry.Space.faithful_quasicoherentFromSpaceBase`: the functor is faithful as soon
  as `AlgebraicGeometry.Space.modulePullback` along `φ` is.
* `AlgebraicGeometry.Space.faithful_modulePullback_of_eq`: the faithfulness of the inverse image
  of modules along a surjective étale morphism whose source is *equal to* the algebraic space of
  a scheme of the site, rather than given as that space.
* `AlgebraicGeometry.Space.faithful_quasicoherentFromSpaceBase_of_surjective`: for a surjective
  étale `φ` out of a space of objects which is the algebraic space of a scheme of the site — the
  situation of Stacks 03M3 — the functor is faithful.

## References

* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The inverse image of modules along a surjective étale morphism whose source is identified
with the algebraic space of a scheme of the site is faithful.** -/
theorem faithful_modulePullback_of_eq {Y X : AlgebraicSpaces B S hS}
    {U : BigFppfOver B S hS} (hY : Y = schemeSpace U) (φ : Y ⟶ X)
    (hφet : IsEtale B S hS φ.hom)
    (hφsurj : (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ.hom) :
    (modulePullback B S hS φ).Faithful := by
  subst hY
  exact faithful_modulePullback B S hS U φ hφet hφsurj

variable {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)
  {X : AlgebraicSpaces B S hS}

/-- **The functor from the base to the groupoid is faithful as soon as the inverse image of
modules along `φ` is.** -/
theorem faithful_quasicoherentFromSpaceBase (φ : G.objects ⟶ X)
    (hφ : G.target ≫ φ = G.source ≫ φ)
    [(modulePullback B S hS φ).Faithful] :
    (quasicoherentFromSpaceBase B S hS G φ hφ).Faithful := by
  constructor
  intro M N g h hgh
  exact CategoryTheory.InducedCategory.hom_ext
    ((modulePullback B S hS φ).map_injective (congrArg QuasicoherentModule.Hom.hom hgh))

/-- **The functor from the base to the groupoid is faithful in the situation of Stacks 03M3.**
For a groupoid in algebraic spaces whose space of objects is the algebraic space of a scheme `U`
of the site, and a surjective étale `φ : U ⟶ X` with `t ≫ φ = s ≫ φ`, the functor
`ℱ ↦ (φ^*ℱ, α)` from quasi-coherent `𝒪_X`-modules to quasi-coherent modules on the groupoid is
faithful. -/
theorem faithful_quasicoherentFromSpaceBase_of_surjective {U : BigFppfOver B S hS}
    (hUobj : G.objects = schemeSpace U) (φ : G.objects ⟶ X)
    (hφet : IsEtale B S hS φ.hom)
    (hφsurj : (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ.hom)
    (hφ : G.target ≫ φ = G.source ≫ φ) :
    (quasicoherentFromSpaceBase B S hS G φ hφ).Faithful :=
  have := faithful_modulePullback_of_eq B S hS hUobj φ hφet hφsurj
  faithful_quasicoherentFromSpaceBase B S hS G φ hφ

end AlgebraicGeometry.Space

end
