module

public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# Base change for the relative Picard functor

Let `f : X ⟶ S` be a morphism of a chosen big fppf site. The relative Picard functor of `f`
sends an `S`-scheme `T` of the site to the Picard group of the base change `X ×_S T`, and then
takes the fppf sheafification. This file provides the base-change half of that construction:
the scheme `X ×_S T` and its functoriality in `T`.

The big site need not itself contain the fibre products `X ×_S T`; they are formed in the
category of all schemes, which is why `baseChange` lands in `Scheme` rather than in
`B.Schemes`.

## Main definitions

* `Stacks.PicardFunctor.baseChange` — the scheme `X ×_S T`.
* `Stacks.PicardFunctor.baseChangeMap` — the morphism `X ×_S T ⟶ X ×_S U` induced by a
  morphism `T ⟶ U` of `S`-schemes of the site.
* `Stacks.PicardFunctor.baseChangeSection` — the section of `X ×_S T ⟶ T` induced by a section
  of `X ⟶ S`.

## Implementation notes

The Picard functor itself is not constructed here: it requires the Picard group of a scheme
together with pullback of invertible modules along a morphism of schemes (Stacks Tag 0B8L,
pullback preserves invertibility). The abelian group of isomorphism classes of invertible
modules on a site is `Stacks.SheafOfModules.PicardGroup` (Stacks Tag 01CX).

The definition of the Picard functor as a sheafification (Tag 0B9L) and the split exactness of
the Picard sequence (Tag 0B9N) are not stated here.

## References

* [Stacks Project, Tag 0B9L](https://stacks.math.columbia.edu/tag/0B9L)
* [Stacks Project, Tag 0B9N](https://stacks.math.columbia.edu/tag/0B9N)
* [Stacks Project, Tag 021S](https://stacks.math.columbia.edu/tag/021S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.PicardFunctor

variable (B : BigFppfSite.{u}) {X S : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S)
  (f : B.obj hX ⟶ B.obj hS)

/-- The scheme obtained by base changing `X ⟶ S` to an object of the big fppf site over `S`. -/
abbrev baseChange (T : BigFppfOver B S hS) : Scheme.{u} :=
  pullback (B.inclusion.map f) (B.inclusion.map T.hom)

/-- The map of base changes induced by a morphism of `S`-schemes. -/
def baseChangeMap {T U : BigFppfOver B S hS} (g : T ⟶ U) :
    baseChange B hX hS f T ⟶ baseChange B hX hS f U :=
  pullback.map (B.inclusion.map f) (B.inclusion.map T.hom)
    (B.inclusion.map f) (B.inclusion.map U.hom)
    (𝟙 _) (B.inclusion.map g.left) (𝟙 _)
    (by simp)
    (by
      simp only [Category.comp_id, ← Functor.map_comp]
      exact congrArg (fun h ↦ B.inclusion.map h) (Over.w g).symm)

/-- The section of `X ×_S T ⟶ T` induced by a section of `X ⟶ S`. -/
def baseChangeSection (σ : S ⟶ X) (hσ : σ ≫ B.inclusion.map f = 𝟙 S)
    (T : BigFppfOver B S hS) :
    (BigFppfOver.toScheme B S hS).obj T ⟶ baseChange B hX hS f T :=
  pullback.lift (B.inclusion.map T.hom ≫ σ) (𝟙 _)
    (by
      change (T.hom.hom ≫ σ) ≫ f.hom = T.hom.hom
      rw [Category.assoc, show σ ≫ f.hom = 𝟙 S from hσ]
      exact Category.comp_id _)

/-- The section induced on a base change really is a section of the base-change projection. -/
@[simp]
theorem baseChangeSection_comp_snd (σ : S ⟶ X) (hσ : σ ≫ B.inclusion.map f = 𝟙 S)
    (T : BigFppfOver B S hS) :
    baseChangeSection B hX hS f σ hσ T ≫
        pullback.snd (B.inclusion.map f) (B.inclusion.map T.hom) =
      𝟙 _ :=
  pullback.lift_snd _ _ _

end Stacks.PicardFunctor

end
