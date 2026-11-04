module

public import StacksFrontier.AlgebraicGeometry.HighTwistDevissage.Cohomology
public import StacksFrontier.AlgebraicGeometry.ProjTwistFunctor.Basic

/-!
# Descending dévissage for the cohomology of twists on `Proj 𝒜`

`Stacks.HighTwistDevissage.exists_isZero_hgroup_twist_of_descending_devissage` is the twisted
descending-dévissage engine: from a vanishing bound on all twists of a class `P` and a dévissage
sequence whose twists are short exact with eventually acyclic middle term, it concludes that
`Hᵖ(U, ℱ(d))` vanishes for all sufficiently large `d`. Its one unsupplied input was a twist
*functor*. This file supplies it, instantiating the engine at
`Stacks.AlgebraicGeometry.ProjTwistFunctor.twistFunctor`.

The statement is the shape of [Stacks, Tag 0B5Q] assertion (3): the hypotheses and the
conclusion are phrased entirely in
`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistSheafOfModules`, the repository's twist, with no
mention of the tensor-functor machinery — which is possible only because the functor's object map
*is* that twist, by `rfl`.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistFunctor.exists_isZero_hgroup_twist_of_descending_devissage`.

## Implementation notes

This is not [Stacks, Tag 0B5Q] assertion (3) itself and carries no tag attribute. What is still
owed to turn it into that statement is, precisely: `P` instantiated as coherence together with
the link between `SheafOfModules.IsCoherent` and `Proj` (Tags 01YR/0B5R); the bound `e` from a
finite affine cover (Tag 01XI); the surjection from a finite direct sum of twists which produces
the dévissage sequence (Tag 0B5Q assertion (1)); and short exactness of the twisted sequence,
which `shortExact_map_twistFunctor_of_preservesMonomorphisms` reduces to flatness of `𝒪(d)`.

The ambient hypotheses are carried as instance arguments rather than discharged:
`CategoryTheory.EnoughInjectives` on `𝒪_{Proj 𝒜}`-modules and the two
`CategoryTheory.HasDerivedCategory` instances are what the engine's long-exact-sequence
discharge needs, and they are not available on this site at this pin. By contrast,
`CategoryTheory.HasSheafify` and
`CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective` for `AddCommGrpCat` on the site of
opens of `Proj 𝒜` *are* found by instance search with no local declaration, so they are not
listed.

## References

* [Stacks Project, Tag 0B5Q](https://stacks.math.columbia.edu/tag/0B5Q)
* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u w

namespace Stacks.AlgebraicGeometry.ProjTwistFunctor

variable {S : Type u} [CommRing S] {σ : Type w} [SetLike σ S] [AddSubgroupClass σ S]

/-- **Twisted descending dévissage on `Proj 𝒜`.** If `Hᵖ(U, ℱ(d))` vanishes for every `ℱ` in a
class `P`, every `p > e` and every `d`, and every `ℱ` in `P` is the quotient term of a sequence
`0 → ℱ' → 𝒢 → ℱ → 0` with `ℱ'` again in `P`, all of whose twists are short exact and whose
middle term is eventually acyclic over `U` in positive degrees, then for each `p > 0` the group
`Hᵖ(U, ℱ(d))` vanishes for all sufficiently large `d`. -/
theorem exists_isZero_hgroup_twist_of_descending_devissage
    (𝒜 : ℕ → σ) [GradedRing 𝒜]
    [EnoughInjectives (SheafOfModules.{u} (projRingSheaf 𝒜))]
    [HasDerivedCategory (SheafOfModules.{u} (projRingSheaf 𝒜))]
    [HasDerivedCategory AddCommGrpCat.{u}]
    (U : Opens (ProjectiveSpectrum.top 𝒜))
    (P : SheafOfModules.{u} (projRingSheaf 𝒜) → Prop) (e : ℕ)
    (hbound : ∀ p : ℕ, e < p → ∀ F : SheafOfModules.{u} (projRingSheaf 𝒜), P F → ∀ d : ℤ,
      IsZero (Hgroup (projRingSheaf 𝒜) U p (twistSheafOfModules 𝒜 F d)))
    (step : ∀ F : SheafOfModules.{u} (projRingSheaf 𝒜), P F →
      ∃ T : ShortComplex (SheafOfModules.{u} (projRingSheaf 𝒜)), T.X₃ = F ∧ P T.X₁ ∧
        (∀ d : ℤ, (T.map (twistFunctor 𝒜 d)).ShortExact) ∧
        ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → ∀ m : ℕ, 0 < m →
          IsZero (Hgroup (projRingSheaf 𝒜) U m (twistSheafOfModules 𝒜 T.X₂ d)))
    (p : ℕ) (hp : 0 < p) (F : SheafOfModules.{u} (projRingSheaf 𝒜)) (hF : P F) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d →
      IsZero (Hgroup (projRingSheaf 𝒜) U p (twistSheafOfModules 𝒜 F d)) :=
  Stacks.HighTwistDevissage.exists_isZero_hgroup_twist_of_descending_devissage
    (projRingSheaf 𝒜) U (twistFunctor 𝒜) P e hbound step p hp F hF

end Stacks.AlgebraicGeometry.ProjTwistFunctor

end
