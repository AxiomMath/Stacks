module

public import StacksFrontier.AlgebraicGeometry.ProjTwistCompTwistMap.Opens

/-!
# The composition law for the fibre comparison, applied to a section, at free primes

The pointwise content of Tag 01MZ's assertion about the maps on all twists is
`Stacks.AlgebraicGeometry.TwistBaseChange.fibreMap_comp`, and the only thing standing between
that and the two sides of the assertion is that the two sides read the section at two
*propositionally* equal points of `Proj 𝒜`. This file combines the two inputs —
`fibreMap_comp` and
`Stacks.AlgebraicGeometry.ProjTwistCompFunctoriality.fibreMap_apply_congr` — into one statement
in which **all four primes are free arguments**, so no reading of a point through a domain of
definition occurs and nothing has to be transported.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistCompTwistMap.fibreMap_comp_apply`

## References

* [Stacks Project, Tag 01MZ](https://stacks.math.columbia.edu/tag/01MZ)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry HomogeneousIdeal HomogeneousLocalization TopologicalSpace CategoryTheory
open Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistCompare
open Stacks.AlgebraicGeometry.ProjTwistCompFunctoriality
open Stacks.AlgebraicGeometry.TwistBaseChange

namespace Stacks.AlgebraicGeometry.ProjTwistCompTwistMap

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top

universe u w w' w''

variable {A B C : Type u} {σ : Type w} {τ : Type w'} {υ : Type w''}
  [CommRing A] [CommRing B] [CommRing C]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  [SetLike υ C] [AddSubgroupClass υ C]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) (𝒞 : ℕ → υ) [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]

/-- **The composition law for the fibre comparison, applied to a section read at two
propositionally equal points.**

Both primes of `Proj 𝒜` are free arguments and so is the intermediate prime of `Proj ℬ`: the two
sides of Tag 01MZ's twist assertion read the section at
`basePoint 𝒜 𝒞 (ψ ∘ φ) w` and at `basePoint 𝒜 ℬ φ u`, which
`Stacks.AlgebraicGeometry.ProjTwistCompFunctoriality.basePoint_innerPt` identifies, and feeding
both in as free primes is what keeps that identification out of every type here.

The two ingredients are `Stacks.AlgebraicGeometry.TwistBaseChange.fibreMap_comp` and
`Stacks.AlgebraicGeometry.ProjTwistCompFunctoriality.fibreMap_apply_congr`. -/
public theorem fibreMap_comp_apply (φ : 𝒜 →+*ᵍ ℬ) (χ : ℬ →+*ᵍ 𝒞) (n : ℤ)
    (x x' : ProjectiveSpectrum 𝒜) (y : ProjectiveSpectrum ℬ) (z : ProjectiveSpectrum 𝒞)
    (hxx' : x = x')
    (hxy : x.asHomogeneousIdeal = y.asHomogeneousIdeal.comap φ)
    (hxy' : x'.asHomogeneousIdeal = y.asHomogeneousIdeal.comap φ)
    (hyz : y.asHomogeneousIdeal = z.asHomogeneousIdeal.comap χ)
    (hxz : x.asHomogeneousIdeal = z.asHomogeneousIdeal.comap (χ.comp φ))
    {T : (AlgebraicGeometry.Proj 𝒜).Opens}
    (a : (twistingSheaf 𝒜 n).val.obj (op T)) (hx : x ∈ T) (hx' : x' ∈ T) :
    fibreMap 𝒜 𝒞 (χ.comp φ) x z hxz (a.1 ⟨x, hx⟩)
      = fibreMap ℬ 𝒞 χ y z hyz (fibreMap 𝒜 ℬ φ x' y hxy' (a.1 ⟨x', hx'⟩)) := by
  refine Eq.trans (DFunLike.congr_fun
    (fibreMap_comp 𝒜 ℬ 𝒞 φ χ x y z hxy hyz hxz) (a.1 ⟨x, hx⟩)) ?_
  exact congrArg (fibreMap ℬ 𝒞 χ y z hyz)
    (fibreMap_apply_congr 𝒜 ℬ φ n a x x' hx hx' hxx' y hxy hxy')

end Stacks.AlgebraicGeometry.ProjTwistCompTwistMap

end
