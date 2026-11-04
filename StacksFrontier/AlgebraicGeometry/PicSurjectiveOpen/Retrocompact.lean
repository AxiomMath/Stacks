module

public import StacksFrontier.AlgebraicGeometry.PicSurjectiveOpen.Basic
public import StacksFrontier.AlgebraicGeometry.PicSurjectiveOpen.IsolatingChart
public import StacksFrontier.AlgebraicGeometry.Variety.NoetherianDimensionOne.IsolatingFunction
public import StacksFrontier.Topology.Sheaves.Cohomology.Torsors.GeneratorsOfARankOneModule
import StacksCore.Tactic.StacksAttribute

/-!
# Clause (2) of Stacks Tag 09NA: `Pic(X) → Pic(U)` is surjective

Let `U` be a retrocompact open of a scheme `X` with discrete complement, along which the local
rings of `X` are Noetherian of Krull dimension at most one.  Then every invertible `𝒪_U`-module
is the pullback of an invertible `𝒪_X`-module.

This is clause (2) of [Stacks, Tag 09NA](https://stacks.math.columbia.edu/tag/09NA); clause (1),
that `U` is the nonvanishing locus of a global section of an invertible module, is
`AlgebraicGeometry.exists_isInvertible_nonvanishingOpen_eq`.  Surjectivity of a restriction map of
Picard groups is recorded, here as elsewhere in this repository (see the Tag 0C0U statement
`Stacks.PicSurjectiveFinite.exists_isInvertible_modulePullback_iso_of_isClosedImmersion_restrict`),
as the statement that every invertible module downstairs is a pullback.

## Main results

* `Stacks.PicSurjectiveOpen.exists_isInvertible_modulePullback_iso_of_isRetrocompact`: the
  statement above.

## The chart family

`Stacks.PicSurjectiveOpen.exists_isInvertible_modulePullback_iso` glues an invertible module on
`X` out of a family of opens of `X` which covers `X`, meets pairwise inside `U`, and over whose
preimages `N` is trivial.  The family used here is indexed by the disjoint union of the points of
`U` and the points of the complement:

* at a point of `U`, a trivializing open of `N`, pushed forward along the open immersion `U.ι`
  (so it lies inside `U` by `AlgebraicGeometry.Scheme.Hom.image_le_opensRange`, and its preimage
  is the open one started from by `AlgebraicGeometry.Scheme.Hom.preimage_image_eq`);
* at a point `y` outside `U`, the shrunk isolating chart of
  `Stacks.PicSurjectiveOpen.exists_generatorSections_of_isolating_chart`, applied to the chart
  that `AlgebraicGeometry.exists_isAffineOpen_isolating_point` produces from the dimension
  hypothesis.

Two members of the family meet inside `U` for the reason the tag gives: a chart of the second
kind meets the complement only in its own point, so two distinct such charts meet the complement
nowhere, and a chart of the first kind is inside `U` already.

## References

* [Stacks Project, Tag 09NA](https://stacks.math.columbia.edu/tag/09NA)
* [Stacks Project, Tag 0623](https://stacks.math.columbia.edu/tag/0623)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.SheafOfModules RingedSpaceModuleAdjunction

universe u

namespace Stacks.PicSurjectiveOpen

variable {X : Scheme.{u}} {U : X.Opens}

/-- An invertible module on a ringed space whose stalks are local rings has a generating section
on a neighbourhood of every point: it is finite locally free of rank one, which is what
`Stacks.Cohomology.Generators.exists_generator_section` consumes. -/
theorem exists_mem_nonempty_generatorSections (Z : Scheme.{u}) (L : Z.Modules)
    [IsInvertible Z.presheaf (structureSheafRing Z.toRingedSpace).property L] (z : Z) :
    ∃ W : Z.Opens, z ∈ W ∧ Nonempty (GeneratorSections Z.toRingedSpace L W) := by
  have : ∀ w : Z.toRingedSpace.carrier,
      IsLocalRing (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk
        Z.toRingedSpace w) := Z.isLocalRing
  have := Stacks.SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible L
  exact Stacks.Cohomology.Generators.exists_generator_section Z.toRingedSpace L z

variable (X U) in
/-- **Clause (2) of Stacks Tag 09NA.** For a retrocompact open `U` of a scheme `X` whose
complement is discrete and along which the local rings of `X` are Noetherian of Krull dimension
at most one, every invertible `𝒪_U`-module is the pullback of an invertible `𝒪_X`-module; that
is, `Pic(X) → Pic(U)` is surjective. -/
@[stacks 09NA "surjectivity of the restriction Pic(X) -> Pic(U)"]
theorem exists_isInvertible_modulePullback_iso_of_isRetrocompact
    (hU : IsRetrocompact (U : Set X)) [DiscreteTopology (Uᶜ : Set X)]
    (h_noetherian : ∀ x : X, x ∈ (U : Set X)ᶜ → IsNoetherianRing (X.presheaf.stalk x))
    (h_dimension : ∀ x : X, x ∈ (U : Set X)ᶜ → Ring.KrullDimLE 1 (X.presheaf.stalk x))
    (N : U.toScheme.Modules)
    [IsInvertible U.toScheme.presheaf
      (structureSheafRing U.toScheme.toRingedSpace).property N] :
    ∃ (L : X.Modules)
      (_ : IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property L),
      Nonempty ((modulePullback U.ι.toLRSHom.toShHom).obj L ≅ N) := by
  classical
  -- Trivializing opens of `N` at the points of `U`.
  choose Wu hWu hgenu using exists_mem_nonempty_generatorSections U.toScheme N
  -- Shrunk isolating charts at the points of the complement.
  have hcpl : ∀ y : ((U : Set X)ᶜ : Set X), ∃ V' : X.Opens, (y : X) ∈ V' ∧
      ((V' : Set X) ∩ (U : Set X)ᶜ ⊆ {(y : X)}) ∧
      Nonempty (GeneratorSections U.toScheme.toRingedSpace N (U.ι ⁻¹ᵁ V')) := by
    intro y
    obtain ⟨V, hVaff, hyV, hVC, f, hfz⟩ :=
      AlgebraicGeometry.exists_isAffineOpen_isolating_point X U hU h_noetherian h_dimension
        y.1 y.2
    have := h_noetherian y.1 y.2
    have := h_dimension y.1 y.2
    have hfU : V ⊓ U = X.basicOpen f := by
      refine TopologicalSpace.Opens.ext (Set.ext fun p => ?_)
      simp only [Opens.coe_inf, Set.mem_inter_iff, SetLike.mem_coe]
      refine ⟨fun ⟨hpV, hpU⟩ => ?_, fun hpb => ⟨X.basicOpen_le f hpb, ?_⟩⟩
      · by_contra hpb
        have hmem : p ∈ (V : Set X) \ (X.basicOpen f : Set X) := ⟨hpV, hpb⟩
        rw [hfz, Set.mem_singleton_iff] at hmem
        exact y.2 (hmem ▸ hpU)
      · by_contra hpU
        have hp : p = y := hVC.subset ⟨X.basicOpen_le f hpb, hpU⟩
        exact (hfz.superset (Set.mem_singleton _)).2 (hp ▸ hpb)
    obtain ⟨V', hyV', hV'V, hgen⟩ :=
      exists_generatorSections_of_isolating_chart N hVaff hyV y.2 f hfU
    exact ⟨V', hyV', fun p hp => hVC.subset ⟨hV'V hp.1, hp.2⟩, hgen⟩
  choose Vc hVc hVcIso hgenc using hcpl
  -- The chart family: a trivializing open at each point of `U`, a shrunk isolating chart at
  -- each point of the complement.
  refine exists_isInvertible_modulePullback_iso
    (W := Sum.elim (fun z : U.toScheme.carrier => U.ι ''ᵁ Wu z)
      (fun y : ((U : Set X)ᶜ : Set X) => Vc y)) (N := N) ?_ ?_ ?_
  · rintro (z | y)
    · show GeneratorSections U.toScheme.toRingedSpace N (U.ι ⁻¹ᵁ (U.ι ''ᵁ Wu z))
      rw [U.ι.preimage_image_eq (Wu z)]
      exact (hgenu z).some
    · exact (hgenc y).some
  · rintro (z | y) j hij
    · exact inf_le_left.trans (by simpa using U.ι.image_le_opensRange (Wu z))
    rcases j with z' | y'
    · exact inf_le_right.trans (by simpa using U.ι.image_le_opensRange (Wu z'))
    · intro p hp
      by_contra hpU
      have h1 := hVcIso y ⟨hp.1, hpU⟩
      have h2 := hVcIso y' ⟨hp.2, hpU⟩
      rw [Set.mem_singleton_iff] at h1 h2
      exact hij (congrArg Sum.inr (Subtype.ext (h1.symm.trans h2)))
  · intro p _
    by_cases hp : p ∈ U
    · exact Opens.mem_iSup.mpr ⟨Sum.inl ⟨p, hp⟩, ⟨⟨p, hp⟩, hWu ⟨p, hp⟩, rfl⟩⟩
    · exact Opens.mem_iSup.mpr ⟨Sum.inr ⟨p, hp⟩, hVc ⟨p, hp⟩⟩

end Stacks.PicSurjectiveOpen

end
