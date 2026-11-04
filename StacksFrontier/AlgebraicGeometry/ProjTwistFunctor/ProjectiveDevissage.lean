module

public import StacksFrontier.AlgebraicGeometry.HighTwistDevissage.Cohomology
public import StacksFrontier.AlgebraicGeometry.ProjTwistFunctor.Projective

/-!
# Descending dévissage for the cohomology of twists on projective space over a ring

This is the companion of `StacksFrontier/AlgebraicGeometry/ProjTwistFunctor/Devissage.lean` on
projective space over a ring: the twisted descending-dévissage engine
`Stacks.HighTwistDevissage.exists_isZero_hgroup_twist_of_descending_devissage` instantiated at
`Stacks.AlgebraicGeometry.ProjTwistFunctor.projectiveTwistFunctor`, with hypotheses and
conclusion phrased in `AlgebraicGeometry.projectiveTwist`.

**It is a different statement from the `Proj 𝒜` one.** `AlgebraicGeometry.projectiveSpaceOverRing`
is a pullback presentation, not a `Proj` term; the two dévissage statements are therefore proved
separately from the shared tensor-functor infrastructure, and the tagged statements they serve —
[Stacks, Tag 01YS] assertion (4) and [Stacks, Tag 0B5Q] assertion (3) — rest on separate proofs.

## Main results

* `exists_isZero_hgroup_projectiveTwist_of_descending_devissage`, in the
  `Stacks.AlgebraicGeometry.ProjTwistFunctor` namespace.

## Implementation notes

As on the `Proj 𝒜` side, `CategoryTheory.HasSheafify` and
`CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective` for `AddCommGrpCat` on the site of
opens of `AlgebraicGeometry.projectiveSpaceOverRing n R` are found by instance search with no
local declaration, so only the injectives and the two derived
categories are carried.

No tag attribute is attached: this is an input to [Stacks, Tag 01YS] assertion (4) and not its
statement. What remains for that statement is the same list as on the `Proj` side — coherence as
the class `P`, the bound from a finite affine cover, the surjection from a finite direct sum of
twists, and flatness (equivalently invertibility) of the pulled-back twisting sheaf.

## References

* [Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ProjTwistFunctor

variable {R : Type u} [CommRing R]

/-- **Twisted descending dévissage on `ℙⁿ_R`.** The statement of
`Stacks.AlgebraicGeometry.ProjTwistFunctor.exists_isZero_hgroup_twist_of_descending_devissage`
with the twist of projective space over a ring in place of the twist on `Proj`. -/
theorem exists_isZero_hgroup_projectiveTwist_of_descending_devissage (n : ℕ)
    [EnoughInjectives
      (SheafOfModules.{u} (projectiveSpaceOverRing n (.of R)).ringCatSheaf)]
    [HasDerivedCategory
      (SheafOfModules.{u} (projectiveSpaceOverRing n (.of R)).ringCatSheaf)]
    [HasDerivedCategory AddCommGrpCat.{u}]
    (U : (projectiveSpaceOverRing n (.of R)).Opens)
    (P : SheafOfModules.{u} (projectiveSpaceOverRing n (.of R)).ringCatSheaf → Prop) (e : ℕ)
    (hbound : ∀ p : ℕ, e < p →
      ∀ F : SheafOfModules.{u} (projectiveSpaceOverRing n (.of R)).ringCatSheaf, P F → ∀ d : ℤ,
      IsZero (Hgroup (projectiveSpaceOverRing n (.of R)).ringCatSheaf U p
        (projectiveTwist n F d)))
    (step : ∀ F : SheafOfModules.{u} (projectiveSpaceOverRing n (.of R)).ringCatSheaf, P F →
      ∃ T : ShortComplex
          (SheafOfModules.{u} (projectiveSpaceOverRing n (.of R)).ringCatSheaf),
        T.X₃ = F ∧ P T.X₁ ∧
        (∀ d : ℤ, (T.map (projectiveTwistFunctor n d)).ShortExact) ∧
        ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → ∀ m : ℕ, 0 < m →
          IsZero (Hgroup (projectiveSpaceOverRing n (.of R)).ringCatSheaf U m
            (projectiveTwist n T.X₂ d)))
    (p : ℕ) (hp : 0 < p)
    (F : SheafOfModules.{u} (projectiveSpaceOverRing n (.of R)).ringCatSheaf) (hF : P F) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d →
      IsZero (Hgroup (projectiveSpaceOverRing n (.of R)).ringCatSheaf U p
        (projectiveTwist n F d)) :=
  Stacks.HighTwistDevissage.exists_isZero_hgroup_twist_of_descending_devissage
    (projectiveSpaceOverRing n (.of R)).ringCatSheaf U (projectiveTwistFunctor n) P e
    hbound step p hp F hF

end Stacks.AlgebraicGeometry.ProjTwistFunctor

end
