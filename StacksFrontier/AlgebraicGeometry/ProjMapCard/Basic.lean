module

public import StacksFrontier.AlgebraicGeometry.ProjMapData.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTwistCompare.Twist

/-!
# Tag 01MY part (2), stated on the bundle rather than on the morphism alone

Tag 01MY is a statement about a triple: the open `U(ψ) ⊆ Proj ℬ` on which a graded ring
homomorphism `ψ : 𝒜 →+*ᵍ ℬ` induces a morphism, that morphism `r_ψ : U(ψ) ⟶ Proj 𝒜`, and the
degree-preserving maps `θ n` on the twists. Its clause (2) — the inverse image of a standard
open, the square of degree-zero homogeneous localizations over that standard open, and the
uniqueness of the morphism those two pin down — mentions only the morphism.

`Stacks.AlgebraicGeometry.ProjTwistChain.mapHom_preimage_basicOpen`,
`Stacks.AlgebraicGeometry.ProjTwistChain.awayToSection_comp_appLE_mapHom` and
`Stacks.AlgebraicGeometry.ProjTwistChain.eq_mapHom` prove those three assertions about
`Stacks.AlgebraicGeometry.ProjTwistChain.mapHom` directly, which is the seam the source itself
uses: its proof opens "Clearly condition (2) uniquely determines the morphism of schemes and
the open subset `U(ψ)`", and only then determines `θ`. That split was forced while the bundle
did not exist. It does exist now, as
`Stacks.AlgebraicGeometry.ProjTwistCompare.projMapData`, and its underlying morphism is
`mapHom` by `rfl`. So the three assertions can be stated the way the source states them, as
assertions about the `hom` field of the canonical bundle, and this file does that. Nothing is
reproved: each statement is the corresponding `mapHom` statement, accepted at the bundle's
type.

## Main results

* `Stacks.AlgebraicGeometry.ProjMapCard.projMapData_basicOpen`: the inverse image of a
  standard open under the bundle's morphism.
* `Stacks.AlgebraicGeometry.ProjMapCard.projMapData_awayToSection`: the square of degree-zero
  homogeneous localizations over a standard open, for the bundle's morphism.
* `Stacks.AlgebraicGeometry.ProjMapCard.projMapData_hom_unique`: a morphism with those two
  properties is the bundle's morphism.

## Implementation notes

The side conditions of the two `Scheme.Hom.appLE`s are proofs of an inequality of opens, and
so are irrelevant: the statement below writes the inequality's proof through
`projMapData_basicOpen` where the `mapHom` statement writes it through
`mapHom_preimage_basicOpen`, and the two terms are definitionally equal because the inequality
is a proposition.

## References

* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistCompare

namespace Stacks.AlgebraicGeometry.ProjMapCard

universe u w w'

variable {A B : Type u} {σ : Type w} {τ : Type w'}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

/-- **Tag 01MY (2)**: the inverse image of a standard open of `Proj 𝒜` under the morphism of
the canonical bundle is the standard open of the image element. -/
public theorem projMapData_basicOpen (ψ : 𝒜 →+*ᵍ ℬ)
    (f : A) (d : ℕ) (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    (projMapData 𝒜 ℬ ψ).hom ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f =
      (mapDomain 𝒜 ℬ ψ).ι ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen ℬ (ψ f) :=
  mapHom_preimage_basicOpen 𝒜 ℬ ψ f d hf hd

/-- **Tag 01MY (2)**: on the standard open `D₊(ψ f)` of the domain of definition, the morphism
of the canonical bundle is the one induced by the map `𝒜_{(f)} → ℬ_{(ψ f)}` of degree-zero
homogeneous localizations. -/
public theorem projMapData_awayToSection (ψ : 𝒜 →+*ᵍ ℬ)
    (f : A) (d : ℕ) (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    AlgebraicGeometry.Proj.awayToSection 𝒜 f ≫
      Scheme.Hom.appLE (projMapData 𝒜 ℬ ψ).hom
        (AlgebraicGeometry.Proj.basicOpen 𝒜 f)
        ((mapDomain 𝒜 ℬ ψ).ι ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen ℬ (ψ f))
        (by rw [projMapData_basicOpen 𝒜 ℬ ψ f d hf hd]) =
    CommRingCat.ofHom (HomogeneousLocalization.Away.map ψ f) ≫
      AlgebraicGeometry.Proj.awayToSection ℬ (ψ f) ≫
        Scheme.Hom.appLE (mapDomain 𝒜 ℬ ψ).ι
          (AlgebraicGeometry.Proj.basicOpen ℬ (ψ f))
          ((mapDomain 𝒜 ℬ ψ).ι ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen ℬ (ψ f))
          le_rfl :=
  awayToSection_comp_appLE_mapHom 𝒜 ℬ ψ f d hf hd

/-- **Tag 01MY (2), uniqueness**: a morphism out of the domain of definition that has the
inverse images of standard opens of Tag 01MY (2), and that on each of them is induced by the
corresponding map of degree-zero homogeneous localizations, is the morphism of the canonical
bundle. -/
public theorem projMapData_hom_unique (ψ : 𝒜 →+*ᵍ ℬ)
    (h : (mapDomain 𝒜 ℬ ψ).toScheme ⟶ AlgebraicGeometry.Proj 𝒜)
    (hopen : ∀ (f : A) (d : ℕ), f ∈ 𝒜 d → 0 < d →
      h ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f =
        (mapDomain 𝒜 ℬ ψ).ι ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen ℬ (ψ f))
    (hlocal : ∀ (f : A) (d : ℕ) (hf : f ∈ 𝒜 d) (hd : 0 < d),
      AlgebraicGeometry.Proj.awayToSection 𝒜 f ≫
        Scheme.Hom.appLE h (AlgebraicGeometry.Proj.basicOpen 𝒜 f)
          ((mapDomain 𝒜 ℬ ψ).ι ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen ℬ (ψ f))
          (by rw [hopen f d hf hd]) =
      CommRingCat.ofHom (HomogeneousLocalization.Away.map ψ f) ≫
        AlgebraicGeometry.Proj.awayToSection ℬ (ψ f) ≫
          Scheme.Hom.appLE (mapDomain 𝒜 ℬ ψ).ι
            (AlgebraicGeometry.Proj.basicOpen ℬ (ψ f))
            ((mapDomain 𝒜 ℬ ψ).ι ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen ℬ (ψ f))
            le_rfl) :
    h = (projMapData 𝒜 ℬ ψ).hom :=
  eq_mapHom 𝒜 ℬ ψ h (fun f d hf hd => hopen f d hf hd) hlocal

end Stacks.AlgebraicGeometry.ProjMapCard

end
