module

public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.ProjNoetherian.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProjFiniteType.Twists

/-!
# The twists on the projective spectrum of a Noetherian graded ring are of finite presentation

Let `A` be a Noetherian commutative ring graded by a `SetLike` family `𝒜 : ℕ → σ`. Every twist
`𝒪(t)` of the structure sheaf on `Proj 𝒜` is then a module of finite presentation.

A Noetherian graded ring is a finite type algebra over its own degree-zero part, so `Proj 𝒜` is a
Noetherian scheme (Stacks tag 0B5Q) and the twist is quasi-coherent and of finite type
(`AlgebraicGeometry.ProjectiveSpectrum.Proj.isFiniteType_twistingSheaf`). On a locally Noetherian
scheme those two properties give finite presentation (Stacks tag 01XZ).

## Main results

* `AlgebraicGeometry.ProjectiveSpectrum.Proj.isFinitePresentation_twistingSheaf`: every twist on
  the projective spectrum of a Noetherian graded ring is of finite presentation.

## Implementation notes

This is the absolute case of the assertion of Stacks tag 0D4D about the twists on a relative
`Proj`, and it is the input the Noetherian-model argument of that tag needs over its Noetherian
model. It is not tagged, because the statement of the tag is the relative one and carries no
Noetherian hypothesis.

## References

* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 0B5Q](https://stacks.math.columbia.edu/tag/0B5Q)
* [Stacks Project, Tag 0D4D](https://stacks.math.columbia.edu/tag/0D4D)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u w

namespace AlgebraicGeometry.ProjectiveSpectrum.Proj

variable {A : Type u} {σ : Type w} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- **Every twist of the structure sheaf on the projective spectrum of a Noetherian graded ring is
a module of finite presentation.**

`Proj 𝒜` is a Noetherian scheme, the twist is quasi-coherent, and it is of finite type because a
Noetherian graded ring is of finite type over its degree-zero part; on a locally Noetherian scheme
a quasi-coherent module of finite type is of finite presentation.

This is the absolute case of the assertion of Stacks tag 0D4D, which is stated for a relative
`Proj` and assumes no Noetherian hypothesis; the attribute is therefore withheld. -/
public theorem isFinitePresentation_twistingSheaf [IsNoetherianRing A] (t : ℤ) :
    SheafOfModules.IsFinitePresentation.{u, u, u} (twistingSheaf 𝒜 t) := by
  have : Algebra.FiniteType (𝒜 0) A :=
    Stacks.AlgebraicGeometry.Proj.finiteType_of_isNoetherianRing 𝒜
  have : AlgebraicGeometry.IsNoetherian (Proj 𝒜) :=
    Stacks.AlgebraicGeometry.Proj.isNoetherian_proj 𝒜
  have h : SheafOfModules.IsQuasicoherent.{u, u, u} (twistingSheaf 𝒜 t) ∧
      SheafOfModules.IsFiniteType.{u, u, u} (twistingSheaf 𝒜 t) :=
    ⟨inferInstance, isFiniteType_twistingSheaf 𝒜 t⟩
  exact ((Stacks.AlgebraicGeometry.CoherenceCriteria.coherent_tfae (Proj 𝒜)
    (twistingSheaf 𝒜 t)).out 2 3).mp h

end AlgebraicGeometry.ProjectiveSpectrum.Proj

end
