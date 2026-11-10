module

public import StacksFrontier.AlgebraicGeometry.ProjTwistFunctor.Devissage
public import StacksFrontier.AlgebraicGeometry.ProjTwistFunctor.ProjectiveDevissage
public import StacksFrontier.AlgebraicGeometry.TwistFlatness.Projective

/-!
# The twist dévissage with its short-exactness hypothesis discharged

`Stacks.AlgebraicGeometry.ProjTwistFunctor.exists_isZero_hgroup_twist_of_descending_devissage`
and its projective-space companion ask the dévissage sequence to satisfy

`∀ d : ℤ, (T.map (twistFunctor 𝒜 d)).ShortExact`,

which a consumer producing a short exact sequence `0 → ℱ' → 𝒢 → ℱ → 0` cannot supply directly:
it is a statement about every twist of the sequence, not about the sequence. This file replaces
that clause by plain `T.ShortExact` — on `ℙⁿ_R` with no hypothesis at all, and on `Proj 𝒜` under
the degree-one generation that makes the twist an equivalence.

## Main results

* `Stacks.AlgebraicGeometry.TwistFlatness.exists_isZero_hgroup_twist_of_descending_devissage`:
  the dévissage on `Proj 𝒜` for `𝒜` generated in degree one, with `T.ShortExact` as the
  hypothesis on the sequence.
* `exists_isZero_hgroup_projectiveTwist_of_descending_devissage`, in the same namespace: the
  same on `ℙⁿ_R`, with no hypothesis beyond `T.ShortExact`.

## Implementation notes

The two statements differ from their originals only in that one clause; everything else, including
the ambient `CategoryTheory.EnoughInjectives` and `CategoryTheory.HasDerivedCategory` instance
binders, is carried through unchanged, because those are what the engine's long-exact-sequence
discharge needs and they are not available on these sites in the library.

**These are still not the tagged statements.** On the `Proj 𝒜` side
Tag 0B5Q assertion (3) is stated for an arbitrary Noetherian graded ring, not one generated in
degree one, and the twist there is *not* invertible — the Stacks proof reduces to the degree-one
case through the Veronese subring, which is a separate step. On the `ℙⁿ_R` side the remaining
inputs are the bound from a finite affine cover (Tag 01XI), the
surjection from a finite direct sum of twists (Tag 0B5Q assertion (1)), and a theory of
`Hgroup`. No tag attribute is attached here.

## References

* [Stacks Project, Tag 0B5Q](https://stacks.math.columbia.edu/tag/0B5Q)
* [Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u w

namespace Stacks.AlgebraicGeometry.TwistFlatness

open Stacks.AlgebraicGeometry.ProjTwistFunctor

section Proj

variable {S : Type u} [CommRing S] {σ : Type w} [SetLike σ S] [AddSubgroupClass σ S]

/-- **Twisted descending dévissage on `Proj 𝒜` for `𝒜` generated in degree one.** The dévissage
sequence is asked only to be short exact: all of its twists then are, because the twist is an
equivalence. -/
theorem exists_isZero_hgroup_twist_of_descending_devissage
    (𝒜 : ℕ → σ) [GradedRing 𝒜]
    (hgen : Algebra.adjoin (𝒜 0) (Set.range fun f : 𝒜 1 => (f : S)) = ⊤)
    [EnoughInjectives (SheafOfModules.{u} (projRingSheaf 𝒜))]
    [HasDerivedCategory (SheafOfModules.{u} (projRingSheaf 𝒜))]
    [HasDerivedCategory AddCommGrpCat.{u}]
    (U : Opens (ProjectiveSpectrum.top 𝒜))
    (P : SheafOfModules.{u} (projRingSheaf 𝒜) → Prop) (e : ℕ)
    (hbound : ∀ p : ℕ, e < p → ∀ F : SheafOfModules.{u} (projRingSheaf 𝒜), P F → ∀ d : ℤ,
      IsZero (Hgroup (projRingSheaf 𝒜) U p (twistSheafOfModules 𝒜 F d)))
    (step : ∀ F : SheafOfModules.{u} (projRingSheaf 𝒜), P F →
      ∃ T : ShortComplex (SheafOfModules.{u} (projRingSheaf 𝒜)), T.X₃ = F ∧ P T.X₁ ∧
        T.ShortExact ∧
        ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → ∀ m : ℕ, 0 < m →
          IsZero (Hgroup (projRingSheaf 𝒜) U m (twistSheafOfModules 𝒜 T.X₂ d)))
    (p : ℕ) (hp : 0 < p) (F : SheafOfModules.{u} (projRingSheaf 𝒜)) (hF : P F) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d →
      IsZero (Hgroup (projRingSheaf 𝒜) U p (twistSheafOfModules 𝒜 F d)) :=
  ProjTwistFunctor.exists_isZero_hgroup_twist_of_descending_devissage
    𝒜 U P e hbound
    (fun F hF => by
      obtain ⟨T, hT₃, hT₁, hTse, hacyc⟩ := step F hF
      exact ⟨T, hT₃, hT₁,
        fun d => shortExact_map_twistFunctor_of_adjoin_degree_one 𝒜 hgen d hTse, hacyc⟩)
    p hp F hF

end Proj

section Projective

variable {R : Type u} [CommRing R]

/-- **Twisted descending dévissage on `ℙⁿ_R`**, with the dévissage sequence asked only to be
short exact. No hypothesis on `R`, `n` or the twists: the twist on `ℙⁿ_R` is unconditionally an
equivalence. -/
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
        T.X₃ = F ∧ P T.X₁ ∧ T.ShortExact ∧
        ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → ∀ m : ℕ, 0 < m →
          IsZero (Hgroup (projectiveSpaceOverRing n (.of R)).ringCatSheaf U m
            (projectiveTwist n T.X₂ d)))
    (p : ℕ) (hp : 0 < p)
    (F : SheafOfModules.{u} (projectiveSpaceOverRing n (.of R)).ringCatSheaf) (hF : P F) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d →
      IsZero (Hgroup (projectiveSpaceOverRing n (.of R)).ringCatSheaf U p
        (projectiveTwist n F d)) :=
  ProjTwistFunctor.exists_isZero_hgroup_projectiveTwist_of_descending_devissage
    n U P e hbound
    (fun F hF => by
      obtain ⟨T, hT₃, hT₁, hTse, hacyc⟩ := step F hF
      exact ⟨T, hT₃, hT₁, fun d => shortExact_map_projectiveTwistFunctor n d hTse, hacyc⟩)
    p hp F hF

end Projective

end Stacks.AlgebraicGeometry.TwistFlatness

end
