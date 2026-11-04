module

public import StacksFrontier.AlgebraicGeometry.ProjTwistCompTwistMap.Generic

/-!
# Tag 01MY's comparison on twists, on a pulled-back section over an arbitrary open

`Stacks.AlgebraicGeometry.ProjTwistTheta.twistMap_pullbackSectionOn` computes `θ` on a
pulled-back section and leaves
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` standing in its right-hand side,
because trading that isomorphism for the unit of the pullback adjunction of the open immersion
asks for an open `T₁` of `Proj ℬ` with `ι ⁻¹ᵁ T₁ = mapHom ⁻¹ᵁ T`. The canonical such `T₁` is
`ι ''ᵁ (mapHom ⁻¹ᵁ T)`, and the identification is propositional. This file performs that trade,
with the identification carried by
`Stacks.AlgebraicGeometry.ProjTwistCompTwistMap.pullbackSectionAt`.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistCompTwistMap.twistMap_pullbackSectionAt`: **`θ n` carries a
  transported pulled-back section of the `n`-th twist on `Proj 𝒜` to the transported pulled-back
  section attached to `Stacks.AlgebraicGeometry.ProjTwistCompare.twistSection`.**

## References

* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01MZ](https://stacks.math.columbia.edu/tag/01MZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry HomogeneousIdeal HomogeneousLocalization TopologicalSpace CategoryTheory
open Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistCompare Stacks.AlgebraicGeometry.ProjTwistTheta
open Stacks.AlgebraicGeometry.PullbackUnit

namespace Stacks.AlgebraicGeometry.ProjTwistCompTwistMap

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top

universe u w w'

variable {A B : Type u} {σ : Type w} {τ : Type w'}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- The inverse image under the inclusion of the domain of definition of the image of an open is
that open. -/
public theorem ι_preimage_image (ψ : 𝒜 →+*ᵍ ℬ)
    (Z₀ : (mapDomain 𝒜 ℬ ψ).toScheme.Opens) :
    (mapDomain 𝒜 ℬ ψ).ι ⁻¹ᵁ ((mapDomain 𝒜 ℬ ψ).ι ''ᵁ Z₀) = Z₀ :=
  (mapDomain 𝒜 ℬ ψ).ι.preimage_image_eq Z₀

/-- **Tag 01MY's comparison map on the `n`-th twist, on a transported pulled-back section.**

The value is the transported pulled-back section, along the inclusion of the domain of
definition, attached to `Stacks.AlgebraicGeometry.ProjTwistCompare.twistSection` — the family of
homogeneous fractions obtained by applying `ψ` pointwise. -/
public theorem twistMap_pullbackSectionAt (ψ : 𝒜 →+*ᵍ ℬ) (n : ℤ)
    (T : (AlgebraicGeometry.Proj 𝒜).Opens)
    {V : (mapDomain 𝒜 ℬ ψ).toScheme.Opens} (h : mapHom 𝒜 ℬ ψ ⁻¹ᵁ T = V)
    (h' : (mapDomain 𝒜 ℬ ψ).ι ⁻¹ᵁ ((mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ T)) = V)
    (s : (twistingSheaf 𝒜 n).val.obj (op T)) :
    (twistMap 𝒜 ℬ ψ n).val.app (op V)
        (pullbackSectionAt (mapHom 𝒜 ℬ ψ) (twistingSheaf 𝒜 n) T V h s)
      = pullbackSectionAt (mapDomain 𝒜 ℬ ψ).ι (twistingSheaf ℬ n)
          ((mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ T)) V h'
          (twistSection 𝒜 ℬ ψ n T s) := by
  subst h
  refine Eq.trans ?_ (pullbackSectionAt_eq_restrictIso (mapDomain 𝒜 ℬ ψ).ι
    (twistingSheaf ℬ n) _ h' (twistSection 𝒜 ℬ ψ n T s)).symm
  refine Eq.trans (congrArg (fun z => (twistMap 𝒜 ℬ ψ n).val.app
    (op (mapHom 𝒜 ℬ ψ ⁻¹ᵁ T)) z)
      (pullbackSectionAt_rfl (mapHom 𝒜 ℬ ψ) (twistingSheaf 𝒜 n) T _ s)) ?_
  refine Eq.trans (twistMap_pullbackSectionOn 𝒜 ℬ ψ n T s) ?_
  exact congrArg (fun z =>
      ((Scheme.Modules.restrictFunctorIsoPullback (mapDomain 𝒜 ℬ ψ).ι).hom.app
        (twistingSheaf ℬ n)).val.app (op (mapHom 𝒜 ℬ ψ ⁻¹ᵁ T)) z)
    (restrictUnit_preimage_image (mapDomain 𝒜 ℬ ψ).ι (twistingSheaf ℬ n)
      (mapHom 𝒜 ℬ ψ ⁻¹ᵁ T) h' (twistSection 𝒜 ℬ ψ n T s)).symm

end Stacks.AlgebraicGeometry.ProjTwistCompTwistMap

end
