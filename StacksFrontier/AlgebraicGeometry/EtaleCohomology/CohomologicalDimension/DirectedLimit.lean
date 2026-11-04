module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimensionLimits
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleColimitUnconditional
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleColimitPresentationAdjointForm
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleLimitLevelTransitionCoherence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtalePresentedSystem
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence

/-!
# Cohomological dimension of a directed limit of schemes

[Stacks, Tag 0F0R] (Étale Cohomology, Lemma 59.95.2): if `X = lim X_i` is a directed limit of a
system of quasi-compact and quasi-separated schemes with affine transition morphisms, then
`cd(X) ≤ max cd(X_i)`.

`AlgebraicGeometry.Scheme.etaleCohomologicalDimension_le_iSup_of_isLimit` states this with the
transport of vanishing supplied by Tags 0EYN and 09YQ as a hypothesis `h09YQ`. Here that
transport is proved on Mathlib's small étale sites, giving the lemma with no hypothesis beyond the
source's, for a directed set `I` and a diagram `D : Iᵒᵖ ⥤ Scheme`.

## Main results

* `AlgebraicGeometry.Scheme.subsingleton_sheafH_of_isLimit_of_forall_subsingleton` — the
  transport of vanishing: if `H^q(X_i, f_{i,*}𝓕)` vanishes at every level then `H^q(X, 𝓕)`
  vanishes. This is the hypothesis `h09YQ` of
  `AlgebraicGeometry.Scheme.etaleCohomologicalDimension_le_iSup_of_isLimit`.
* `AlgebraicGeometry.Scheme.etaleCohomologicalDimension_le_iSup_of_isLimit_of_isDirected` —
  the statement of Tag 0F0R, with no hypothesis beyond the source's.

## Implementation notes

The transport follows the two steps of the source. [Stacks, Tag 0EYN], second half, presents `𝓕` as
`colim f_i^{-1}f_{i,*}𝓕` with the counits as legs: in adjoint form this is
`Stacks.EtaleCohomology.AffineLimitCohomology.isDirectImageDescent_of_levelBaseChange`, and
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.isColimitPresentation_directImageSystem_iff`
reads it as the presentation predicate of [Stacks, Tag 09YQ]. That tag,
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.isCohomologyColimit_of_isLimit`, then says
every class on `X` comes from a level. Both are stated relative to a big étale site containing
the levels and the limit, a size device which
`AlgebraicGeometry.BigEtaleSite.exists_contains_of_small` supplies.

## References

* [Stacks Project, Tag 0F0R](https://stacks.math.columbia.edu/tag/0F0R)
* [Stacks Project, Tag 0EYN](https://stacks.math.columbia.edu/tag/0EYN)
* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

open Stacks.EtaleCohomology Stacks.EtaleCohomology.SmallEtaleLimitCohomology

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I] (D : Iᵒᵖ ⥤ Scheme.{u})
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)] [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
  [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)] {c : Cone D}

omit [IsDirected I (· ≤ ·)] [Nonempty I] [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
  [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)] in
/-- A big étale site containing every level of the system and the vertex of the cone. -/
theorem exists_bigEtaleSite_contains_levels_and_pt (c : Cone D) :
    ∃ B : BigEtaleSite.{u}, (∀ i, B.Contains (D.obj i)) ∧ B.Contains c.pt := by
  let S₀ : Set Scheme.{u} := Set.range D.obj ∪ {c.pt}
  have : Small.{u} S₀ := small_union _ _
  obtain ⟨B, hB⟩ := BigEtaleSite.exists_contains_of_small S₀
  exact ⟨B, fun i => hB _ (Or.inl ⟨i, rfl⟩), hB _ (Or.inr rfl)⟩

/-- **The étale cohomology of a sheaf on a directed limit vanishes in every degree in which that
of all its direct images to the levels vanishes.** Let `X = lim X_i` be a directed limit of
quasi-compact quasi-separated schemes with affine transition morphisms, `f_i : X ⟶ X_i` the
projections, and `𝓕` an abelian sheaf on `X_étale`. If `H^q(X_i, f_{i,*}𝓕) = 0` for every `i`,
then `H^q(X, 𝓕) = 0`: by Tag 0EYN the counits present `𝓕 = colim f_i^{-1}f_{i,*}𝓕`, so by
Tag 09YQ every class of `H^q(X, 𝓕)` is the image of a class at some level. -/
theorem subsingleton_sheafH_of_isLimit_of_forall_subsingleton (hc : IsLimit c)
    (𝓕 : Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (h : ∀ i : Iᵒᵖ, Subsingleton (Sheaf.H.{u + 1, u + 1}
      ((smallEtalePushforward (c.π.app i) AddCommGrpCat.{u + 1}).obj 𝓕) q)) :
    Subsingleton (Sheaf.H.{u + 1, u + 1} 𝓕 q) := by
  obtain ⟨B, hD, hX⟩ := exists_bigEtaleSite_contains_levels_and_pt D c
  have hpres : IsColimitPresentation (c := c) (directImageSystem D AddCommGrpCat.{u + 1} c 𝓕) 𝓕
      (coneDirectImageLeg 𝓕) :=
    (isColimitPresentation_directImageSystem_iff 𝓕).2
      (AffineLimitCohomology.isDirectImageDescent_of_levelBaseChange D c B hD hX hc 𝓕)
  have hE := isCohomologyColimit_of_isLimit D c B hD hX hc q
    (presentedSystemOfIsColimitPresentation _ 𝓕 _ hpres)
  refine subsingleton_of_forall_eq 0 fun z => ?_
  obtain ⟨i, w, hw⟩ := hE.exists_leg_eq z
  rw [← hw, @Subsingleton.elim _ (h i) w 0]
  exact map_zero _

/-- **Stacks Project, Tag 0F0R** (Étale Cohomology, Lemma 59.95.2). Let `X = lim X_i` be a
directed limit of a system of quasi-compact and quasi-separated schemes with affine transition
morphisms. Then `cd(X) ≤ max cd(X_i)`.

The directed system is the diagram `D : Iᵒᵖ ⥤ Scheme` over a directed set `I`, with affine
transition maps and quasi-compact quasi-separated values; the limit is the cone `c` with
`hc : IsLimit c`; the maximum over the index set is the supremum in the complete lattice `ℕ∞`,
attained because a directed set is nonempty. The instances on `c.pt` are what makes `cd(X)`
defined and are consequences of `hc`
(`AlgebraicGeometry.Scheme.compactSpace_of_isLimit'`,
`AlgebraicGeometry.Scheme.quasiSeparatedSpace_pt_of_isLimit`). -/
theorem etaleCohomologicalDimension_le_iSup_of_isLimit_of_isDirected
    [CompactSpace c.pt] [QuasiSeparatedSpace c.pt] (hc : IsLimit c) :
    etaleCohomologicalDimension c.pt ≤ ⨆ i : Iᵒᵖ, etaleCohomologicalDimension (D.obj i) := by
  refine etaleCohomologicalDimension_le c.pt _ fun 𝓕 h𝓕 q hq =>
    subsingleton_sheafH_of_isLimit_of_forall_subsingleton D hc 𝓕 q fun i => ?_
  have : IsAffineHom (c.π.app i) := isAffineHom_π_app' D c hc i
  exact isEtaleCohomologyBound_etaleCohomologicalDimension (D.obj i) _
    (torsionSheafProperty_smallEtaleDirectImageAb.{u + 1, u} (c.π.app i) 𝓕 h𝓕) q
    (lt_of_le_of_lt (le_iSup (fun j : Iᵒᵖ => etaleCohomologicalDimension (D.obj j)) i) hq)

end AlgebraicGeometry.Scheme

end
