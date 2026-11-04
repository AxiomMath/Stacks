module

public import StacksFrontier.AlgebraicGeometry.ProjTwistCompare.Twist

/-!
# Applying a further left adjoint to an inverse adjoint transpose

Let `adj₁ : L₁ ⊣ R₁` and `adj₂ : L₂ ⊣ R₂` be adjunctions, so that `L₁ ⋙ L₂ ⊣ R₂ ⋙ R₁`. A
morphism `g : X ⟶ R₁.obj Y` has an inverse adjoint transpose `θ : L₁.obj X ⟶ Y` along the first
adjunction, and `L₂.map θ` is then a morphism out of `(L₁ ⋙ L₂).obj X`. This file identifies it
as an inverse adjoint transpose along the composite adjunction: it is the transpose of `g`
followed by `R₁` applied to the unit of the second adjunction.

The geometric case this is written for is `L₁ = h^*` for a morphism of schemes `h` and
`L₂ = (-)|_V` the restriction to an open `V`, where it says that the restriction to `V` of the
comparison map `θ` of Tag 01MY is again an inverse adjoint transpose, of a morphism built from
the adjoint comparison `Stacks.AlgebraicGeometry.ProjTwistCompare.twistPushforwardMap`, which
does have a formula on sections. That is what makes the restriction of `θ` to a chart accessible
at all: `θ` itself has no formula on sections, and neither does its restriction, but both are
determined by a morphism that does.

## Main results

* `Stacks.AlgebraicGeometry.TwistChartLocality.map_homEquiv_symm`: **the identification.**
* `Stacks.AlgebraicGeometry.TwistChartLocality.restrictFunctor_map_twistTranspose`: the case of
  interest, the restriction to an open of the domain of definition of the transpose that Tag
  01MY's `θ n` is built from.

## Implementation notes

The proof is the triangle-free half of the adjunction calculus: apply the composite `homEquiv`
to both sides, expand it with `CategoryTheory.Adjunction.comp_unit_app`, and use naturality of
the unit of the second adjunction at `θ`. No triangle identity is needed.

`Stacks.AlgebraicGeometry.TwistChartLocality.restrictFunctor_map_twistTranspose` is stated with
the composite adjunction `(pullbackPushforwardAdjunction (mapHom 𝒜 ℬ ψ)).comp
(restrictAdjunction V.ι)` rather than with the adjunction of the composite morphism
`V.ι ≫ mapHom 𝒜 ℬ ψ`. The two left adjoints are isomorphic, but so are their right adjoints
only, so passing between them is a conjugation rather than a rewriting; keeping the composite
adjunction leaves that conjugation to the consumer, which is where the morphism it is applied
to is known.

It is also stated on the transpose rather than on `θ n` itself, which is that transpose followed
by `Stacks.AlgebraicGeometry.ProjTwistCompare.restrictFunctorIsoPullback` at `𝒪_{Proj ℬ}(n)`.
Writing it on `θ n` requires unfolding `twistMap`, and with the local reducibility attributes of
`Proj` in force the resulting definitional check exhausts the heartbeat budget; the final
isomorphism is left for the consumer to compose, which costs nothing.

## References

* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistCompare

namespace Stacks.AlgebraicGeometry.TwistChartLocality

/-! ### The abstract identification -/

section Abstract

variable {C D E : Type*} [Category C] [Category D] [Category E]
  {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : D ⥤ E} {R₂ : E ⥤ D}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

/-- **A further left adjoint applied to an inverse adjoint transpose is again one.** For
`g : X ⟶ R₁.obj Y`, the image under `L₂` of the transpose of `g` along `adj₁` is the transpose,
along the composite adjunction, of `g` followed by `R₁` applied to the unit of `adj₂`. -/
public theorem map_homEquiv_symm {X : C} {Y : D} (g : X ⟶ R₁.obj Y) :
    L₂.map ((adj₁.homEquiv X Y).symm g) =
      ((adj₁.comp adj₂).homEquiv X (L₂.obj Y)).symm
        (g ≫ R₁.map (adj₂.unit.app Y)) := by
  rw [Equiv.eq_symm_apply, Adjunction.comp_homEquiv]
  simp [Adjunction.homEquiv_unit, Adjunction.homEquiv_counit]

end Abstract

/-! ### The restriction of Tag 01MY's comparison map to an open -/

section Twist

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top

universe u w w'

variable {A B : Type u} {σ : Type w} {τ : Type w'}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

/-- **The restriction to an open of the inverse adjoint transpose that defines `θ n`.** Tag
01MY's comparison map is this transpose followed by the identification of restriction with
pullback, so this is the whole content of the restriction of `θ n` to an open of the domain of
definition: it is again an inverse adjoint transpose, along the composite of the
pullback--pushforward adjunction of `mapHom` with the restriction adjunction of the open, of the
adjoint comparison `Stacks.AlgebraicGeometry.ProjTwistCompare.twistPushforwardMap` followed by
the unit of that restriction adjunction. -/
public theorem restrictFunctor_map_twistTranspose (ψ : 𝒜 →+*ᵍ ℬ) (n : ℤ)
    (V : (mapDomain 𝒜 ℬ ψ).toScheme.Opens) :
    (Scheme.Modules.restrictFunctor V.ι).map
        (((Scheme.Modules.pullbackPushforwardAdjunction (mapHom 𝒜 ℬ ψ)).homEquiv
            (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf 𝒜 n) _).symm
          (twistPushforwardMap 𝒜 ℬ ψ n)) =
      (((Scheme.Modules.pullbackPushforwardAdjunction (mapHom 𝒜 ℬ ψ)).comp
            (Scheme.Modules.restrictAdjunction V.ι)).homEquiv
          (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf 𝒜 n) _).symm
        (twistPushforwardMap 𝒜 ℬ ψ n ≫
          (Scheme.Modules.pushforward (mapHom 𝒜 ℬ ψ)).map
            ((Scheme.Modules.restrictAdjunction V.ι).unit.app
              ((Scheme.Modules.restrictFunctor (mapDomain 𝒜 ℬ ψ).ι).obj
                (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf ℬ n)))) :=
  map_homEquiv_symm _ _ _

end Twist

end Stacks.AlgebraicGeometry.TwistChartLocality

end
