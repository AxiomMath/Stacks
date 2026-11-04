module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwist
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistSectionRing
public import StacksFrontier.AlgebraicGeometry.GradedLocalization.ModuleMaps
public import StacksFrontier.AlgebraicGeometry.ProjStalkGlobalSections.GlobalSections

/-!
# Homogeneous elements as global sections of the twists on Proj

Let `S` be a commutative ring with a nonnegative grading `𝒮 : ℕ → σ`. A homogeneous element of
degree `n` determines a global section of the `n`-th twist `𝒪(n)` of the structure sheaf of
`Proj(S)`, whose value at every point is the fraction `a / 1`. That section is
`AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection`, an element of the group
`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistGlobalSections 𝒮 n`.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistSections.mem_twistGrading_zero`: a homogeneous element of
  degree `n` lies in the degree-zero piece of the `n`-th shift of the regular graded module.
* `Stacks.AlgebraicGeometry.ProjTwistSections.degreeSection_apply`: the value of the section at
  a point is `a / 1`.
* `Stacks.AlgebraicGeometry.ProjTwistSections.degreeSection_stalk`: its germ at a homogeneous
  prime is `a / 1`.

## Implementation notes

The twist `𝒪(n)` is the sheaf associated with the shifted graded module `S(n)`, whose degree-zero
piece is the degree-`n` piece of `S`, so the degree-`n` section map is
`Stacks.AlgebraicGeometry.ProjStalkGlobalSections.degreeZeroToGlobalSections` applied to the
shifted module, with `a ∈ 𝒮 n` read as `a ∈ (twistGrading 𝒮 n) 0`.

The degree is kept as a single free variable `n : ℕ` and the membership proof is produced once,
by `mem_twistGrading_zero`: the degree of a homogeneous element occurs inside the proofs carried
by the Proj constructions, so two syntactically different degrees cannot be related by rewriting.

The local transparency attributes are needed because the sheaf-of-modules index built by
composing the structure sheaf with the forgetful functor, and the one the twist is stated over,
are two spellings of one object; instance search and motive checks cross between them only when
those wrappers are reducible.

## References

* [Stacks Project, Tag 01MP](https://stacks.math.columbia.edu/tag/01MP)
* [Stacks Project, Tag 01M7](https://stacks.math.columbia.edu/tag/01M7)
* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite DirectSum
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjStalkGlobalSections
open Stacks.GradedLocalization

namespace Stacks.AlgebraicGeometry.ProjTwistSections

universe u w

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

omit [GradedRing 𝒮] in
/-- A homogeneous element of degree `n` lies in the degree-zero piece of the `n`-th shift of
the regular graded module. -/
public theorem mem_twistGrading_zero {n : ℕ} (a : 𝒮 n) :
    (a : S) ∈ twistGrading (S := S) 𝒮 (n : ℤ) 0 := by
  simp

/-- The value at a point of `Proj(S)` of the global section of `𝒪(n)` attached to a homogeneous
element `a` of degree `n` is the fraction `a / 1`. -/
public theorem degreeSection_apply (n : ℕ) (a : 𝒮 n)
    (x : (⊤ : Opens (ProjectiveSpectrum.top 𝒮))) :
    (AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection 𝒮 n a).1 x =
      LocalizedModule.mk (a : S) (1 : x.1.asHomogeneousIdeal.toIdeal.primeCompl) :=
  degreeZeroToGlobalSections_apply 𝒮 (twistGrading (S := S) 𝒮 (n : ℤ))
    ⟨(a : S), mem_twistGrading_zero 𝒮 a⟩ x

/-- The germ at a homogeneous prime of the global section of `𝒪(n)` attached to a homogeneous
element `a` of degree `n` is the fraction `a / 1`. -/
public theorem degreeSection_stalk (n : ℕ) (a : 𝒮 n) (x : ProjectiveSpectrum.top 𝒮) :
    ((associatedModuleSheafStalkEquiv 𝒮 (twistGrading (S := S) 𝒮 (n : ℤ)) x
      (associatedModuleSheafGerm 𝒮 (twistGrading (S := S) 𝒮 (n : ℤ)) x ⊤
        (show x ∈ (⊤ : Opens (ProjectiveSpectrum.top 𝒮)) from trivial)
        (AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection 𝒮 n a)) :
        degreeZeroModuleAt 𝒮 (twistGrading (S := S) 𝒮 (n : ℤ)) x) :
      ProjectiveSpectrum.Proj.ModuleFiber (M := S) 𝒮 x) =
        LocalizedModule.mk (a : S) (1 : x.asHomogeneousIdeal.toIdeal.primeCompl) :=
  degreeZeroToGlobalSections_stalk 𝒮 (twistGrading (S := S) 𝒮 (n : ℤ)) x
    ⟨(a : S), mem_twistGrading_zero 𝒮 a⟩

end Stacks.AlgebraicGeometry.ProjTwistSections

end
