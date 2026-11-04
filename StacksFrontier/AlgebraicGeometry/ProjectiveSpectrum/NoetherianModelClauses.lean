module

public import StacksFrontier.AlgebraicGeometry.ProjNoetherian.Basic

/-!
# The structural morphism of the projective spectrum of a Noetherian graded algebra

Let `A` be a graded algebra over a commutative ring `R`, nonnegatively graded by submodules
`𝒜 : ℕ → Submodule R A`.  Its projective spectrum carries the structural morphism
`Proj 𝒜 ⟶ Spec R`, the composite of `AlgebraicGeometry.Proj.toSpecZero` with the morphism of
affine spectra induced by `R → 𝒜 0`.  This file records which finiteness properties of that
morphism follow from `A` being a Noetherian ring, and which need a finiteness hypothesis over
`R` itself.

## Main results

* `quasiCompact_projToSpec`: the structural morphism is quasi-compact as soon as `A` is
  Noetherian.
* `isLocallyNoetherian_proj`: `Proj 𝒜` is locally Noetherian as soon as `A` is Noetherian.
* `locallyOfFiniteType_projToSpec`: the structural morphism is locally of finite type, for which
  `Algebra.FiniteType R (𝒜 0)` is needed as well.

## Implementation notes

The two statements that need only `IsNoetherianRing A` go through
`Stacks.AlgebraicGeometry.Proj.finiteType_of_isNoetherianRing`, which supplies
`Algebra.FiniteType (𝒜 0) A`, the hypothesis of Mathlib's instances for `Proj.toSpecZero`.

The finite-type statement is different in kind, and the difference is worth recording: it is a
statement about the morphism down to `Spec R`, so it needs `𝒜 0` to be of finite type over `R`,
and `IsNoetherianRing A` says nothing about that — a Noetherian graded algebra over a
non-Noetherian base need not have a degree-zero part of finite type over the base.  The
hypothesis is therefore carried separately, and the bridge from it to the morphism property is
explicit (`HasRingHomProperty.Spec_iff` and `RingHom.finiteType_algebraMap`): instance search
alone does not cross from `Algebra.FiniteType` to `RingHom.FiniteType` of the bundled
`CommRingCat` morphism.

## References

* [Stacks Project, Tag 0B5Q](https://stacks.math.columbia.edu/tag/0B5Q)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace Stacks.AlgebraicGeometry.Proj

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

/-- The projective spectrum of a Noetherian graded algebra is locally Noetherian. -/
public theorem isLocallyNoetherian_proj [IsNoetherianRing A] :
    IsLocallyNoetherian (AlgebraicGeometry.Proj 𝒜) := by
  have : IsNoetherian (AlgebraicGeometry.Proj 𝒜) := isNoetherian_proj 𝒜
  infer_instance

/-- The structural morphism `Proj 𝒜 ⟶ Spec R` of a Noetherian graded algebra is
quasi-compact. -/
public theorem quasiCompact_projToSpec [IsNoetherianRing A] :
    QuasiCompact (AlgebraicGeometry.Proj.toSpecZero 𝒜 ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (𝒜 0)))) := by
  have : Algebra.FiniteType (𝒜 0) A := finiteType_of_isNoetherianRing 𝒜
  infer_instance

/-- The structural morphism `Proj 𝒜 ⟶ Spec R` is locally of finite type when `A` is Noetherian
and the degree-zero part is of finite type over the base. -/
public theorem locallyOfFiniteType_projToSpec [IsNoetherianRing A]
    [Algebra.FiniteType R (𝒜 0)] :
    LocallyOfFiniteType (AlgebraicGeometry.Proj.toSpecZero 𝒜 ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (𝒜 0)))) := by
  have : Algebra.FiniteType (𝒜 0) A := finiteType_of_isNoetherianRing 𝒜
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R (𝒜 0)))) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2
      (RingHom.finiteType_algebraMap.2 inferInstance)
  infer_instance

end Stacks.AlgebraicGeometry.Proj

end
