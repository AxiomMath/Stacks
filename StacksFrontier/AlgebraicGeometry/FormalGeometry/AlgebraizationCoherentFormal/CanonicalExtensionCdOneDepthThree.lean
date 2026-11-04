module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.CanonicalExtensionCdOneProIso
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.TorsionSubsheafCohomologyFinite

/-!
# [Stacks, Tag 0EJI]: canonical extension of a coherent formal module of depth three

Fix an algebraization situation: a Noetherian ring `A` with ideals `I ⊆ 𝔞`, `X = Spec(A)`,
`Y = V(I)`, `Z = V(𝔞)` and `U = X ∖ Z`. Let `(ℱₙ)` be an object of `Coh(U, I𝒪_U)`. Assume

1. `A` has a dualizing complex and `cd(A, I) = 1`, and
2. `(ℱₙ)` is pro-isomorphic to an inverse system `(ℱ''ₙ)` of coherent `𝒪_U`-modules with
   `depth(ℱ''_{n,y}) + δ^Y_Z(y) ≥ 3` for all `y ∈ U ∩ Y`.

Then `(ℱₙ)` extends canonically to `X` ([Stacks, Tag 0EIP]). This is [Stacks, Tag 0EJI], proved
here with no hypothesis beyond the source's.

## The proof

The three conditions of the criterion [Stacks, Tag 0EHH] are checked as in the source.

* (b), the limit topology on `limₙ H⁰(U, ℱₙ)` is `I`-adic, is the case `p = 0` of
  [Stacks, Tag 0EH7] (`Stacks.Algebraization.limitGlobalSections_topology_eq_adicModuleTopology`).
* (c) and the finiteness of `lim H¹(U, ℱ_N)` modulo `I` come from the pro-isomorphism: a
  transition map of `(ℱₙ)` factors through `ℱ''_m`, and the map into `ℱ''_m` out of a term of
  `(ℱₙ)`, being killed by a power of `I`, factors through the `I`-power torsion subsheaf of
  `ℱ''_m`, whose `H⁰` and `H¹` on `U` are finite `A`-modules by [Stacks, Tag 0BJY] in the form
  `Stacks.Algebraization.exists_torsionSubsheaf_finite` (the torsion subsheaf is supported on
  `Y`, which is where hypothesis (2) bounds the depth).
* (a), the Mittag-Leffler property, is the obstruction argument of the source,
  `Stacks.Algebraization.isMittagLefflerCategorical_globalSectionsSystem_of_cd_one`.

## Main results

* `Stacks.Algebraization.hasFiniteTorsionCohomology_of_depthThree` — the terms of `(ℱ''ₙ)` have
  finite torsion cohomology.
* `Stacks.Algebraization.canonicallyExtends_of_cd_one_of_proIso_depthThree` —
  [Stacks, Tag 0EJI].

## Implementation notes

The depth of a stalk is `Stacks.Algebraization.depthOfStalkOnOpen` and the pro-isomorphism is
`InverseSequence.ProIso`, both from `CanonicalExtensionDepthThree.lean`, where condition (c) of
[Stacks, Tag 0EHH] is proved.

## References

* [Stacks Project, Tag 0EJI](https://stacks.math.columbia.edu/tag/0EJI)
* [Stacks Project, Tag 0EHH](https://stacks.math.columbia.edu/tag/0EHH)
* [Stacks Project, Tag 0EIP](https://stacks.math.columbia.edu/tag/0EIP)
* [Stacks Project, Tag 0EH7](https://stacks.math.columbia.edu/tag/0EH7)
* [Stacks Project, Tag 0BJY](https://stacks.math.columbia.edu/tag/0BJY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

variable (S : AlgebraizationSituation.{u})

/-- Sections on `U` and the zeroth cohomology on `U` are isomorphic `A`-modules. -/
theorem finite_openSections_of_finite_openCohomology_zero (K : S.U.toScheme.Modules)
    (h : Module.Finite S.A ((openCohomologyFunctor S 0).obj K)) :
    Module.Finite S.A ((openSectionsFunctor S).obj K) :=
  have : Module.Finite S.A ((ModuleCat.restrictScalars (scalarMap S)).obj
      (((topSections S).rightDerived 0).obj K)) := h
  Module.Finite.equiv ((ModuleCat.restrictScalars (scalarMap S)).mapIso
    ((topSections S).rightDerivedZeroIsoSelf.app K)).toLinearEquiv

/-- **A coherent `𝒪_U`-module with `depth + δ^Y_Z ≥ 3` on `U ∩ Y` has finite torsion
cohomology**, when `A` has a dualizing complex. -/
theorem hasFiniteTorsionCohomology_of_depthThree
    (hdual : ∃ K : DerivedCategory (ModuleCat.{u} S.A), Dualizing.IsDualizingComplex K)
    (G : S.U.toScheme.Modules) [G.IsCoherent]
    (hdepth : ∀ (y : S.U.toScheme) (z : S.Y), S.U.ι.base y = S.Yι.base z →
      3 ≤ depthOfStalkOnOpen S G y + S.distanceToZ z) :
    HasFiniteTorsionCohomology S G := by
  intro k
  obtain ⟨K, ι, hfac, hfin⟩ := exists_torsionSubsheaf_finite S hdual G hdepth k
  exact ⟨K, ι, hfac, finite_openSections_of_finite_openCohomology_zero S K (hfin 0 (by omega)),
    hfin 1 le_rfl⟩

variable (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))

/-- **Stacks Project, Tag 0EJI.** In Situation 0EHC let `(ℱₙ)` be an object of
`Coh(U, I𝒪_U)`. Assume (1) `A` has a dualizing complex and `cd(A, I) = 1`, and (2) `(ℱₙ)` is
pro-isomorphic to an inverse system `(ℱ''ₙ)` of coherent `𝒪_U`-modules with
`depth(ℱ''_{n,y}) + δ^Y_Z(y) ≥ 3` for all `y ∈ U ∩ Y`. Then `(ℱₙ)` extends canonically to `X`.

A point of `U ∩ Y` is a point `y` of `U` together with a point `z` of `Y` with the same image in
`X`; the depth is that of the stalk over the local ring of `U` at `y`, and `δ^Y_Z` is evaluated
at `z`. -/
@[stacks 0EJI]
theorem canonicallyExtends_of_cd_one_of_proIso_depthThree
    (hdual : ∃ K : DerivedCategory (ModuleCat.{u} S.A), Dualizing.IsDualizingComplex K)
    (hcd : Stacks.LocalCohomology.cohomologicalDimension S.A S.I
      (IsNoetherian.noetherian S.I) = 1)
    (G : ℕᵒᵖ ⥤ S.U.toScheme.Modules) [∀ n : ℕᵒᵖ, (G.obj n).IsCoherent]
    (e : InverseSequence.ProIso F.obj G)
    (hdepth : ∀ n : ℕ, ∀ (y : S.U.toScheme) (z : S.Y), S.U.ι.base y = S.Yι.base z →
      3 ≤ depthOfStalkOnOpen S (G.obj (op n)) y + S.distanceToZ z) :
    CanonicallyExtends S F :=
  canonicallyExtends_of_proIso_of_torsionFinite S F hcd G e fun n =>
    hasFiniteTorsionCohomology_of_depthThree S hdual (G.obj (op n)) (hdepth n)

end Stacks.Algebraization

end
