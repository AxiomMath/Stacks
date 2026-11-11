module

public import StacksFrontier.AlgebraicGeometry.Stacks.AffineCoveringFamily
public import StacksFrontier.AlgebraicGeometry.Stacks.AssociatedSiteRefinement
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineSite
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Equivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FilteredColimits.FiniteCoproductsOfRepresentables
public import StacksCore.Tactic.StacksAttribute

/-!
# Finite affine refinements of coverings on the fppf site of a stack

Let `𝒳` be a category fibred in groupoids over the big fppf category of a scheme `S` contained in
a big fppf site `B`, with the fppf topology of **Stacks 06TP** on its total category. This file
proves that every covering sieve of an object of `𝒳` lying over an affine scheme is refined by a
*finite* covering family whose members again lie over affine schemes.

That assertion is condition (2) of **Stacks 0GN4** for the collection `B` of the proof of
**Stacks 0GQV**, namely the objects of the site lying over affine schemes, and it is the hypothesis
`HasFiniteCoverRefinementsFrom` of the criterion proved in the module
`FiniteCoveringCriterionOnALargeSite` of
`StacksDraft.CategoryTheory.Sites.Cohomology.FilteredColimits`.

## Main results

* `AlgebraicGeometry.BigFppfOver.exists_finite_affine_covering_refinement`: **Stacks 021P in the
  big fppf category over `S`** — a covering sieve of an object lying over an affine scheme is
  refined by a finite chosen covering family whose members lie over affine schemes.
* `AlgebraicGeometry.Stack.hasFiniteCoverRefinementsFrom_fppfTopology`: condition (2) of
  Stacks 0GN4 for the fppf site of `𝒳` and the objects lying over affine schemes.

## Implementation notes

The localization of Stacks 021P from `B.Schemes` to the big fppf category over `S` is not stated
anywhere in the library: `AlgebraicGeometry.exists_standardFppf_refinement` is about `B.Schemes`,
and the passage to the slice over `S` is performed inline inside the proof of
`AlgebraicGeometry.bigAffineFppfInclusion_isCocontinuous`. The first result below is that passage,
extracted and stated once, and it keeps the two facts the criterion needs and the standard-covering
predicate of **Stacks 021Q** does not record in the slice: finiteness of the index type and
affineness of the sources, read off `AlgebraicGeometry.IsStandardFppfCovering.finite_index` and
`AlgebraicGeometry.IsStandardFppfCovering.affine_source`.

Transporting the refinement up to `𝒳` is
`AlgebraicGeometry.Stack.exists_chosenCovering_le_of_mem_associatedTopology`, whose base-level
hypothesis is quantified over *every* object of the big fppf category over `S`, whereas Stacks 021P
needs the target to be affine. Rather than restate that transport — it is an existing result, and
its proof applies the hypothesis only at the image of the object being covered — the class of chosen
covering families fed to it is taken to be *conditional on affineness of the target*: for a
non-affine target the class holds of every family, and the tautological family of all arrows of the
given sieve discharges the hypothesis there. At the affine object the condition is then available
in full.

The resulting family is indexed by a finite type in `Type (u + 1)`, while
`Stacks.Cohomology.ColimitsOfCohomology.HasFiniteCoverRefinementsFrom` asks for an indexing by
`Fin n`; `Finite.equivFin` reindexes it, and the two generated sieves agree because
`CategoryTheory.Sieve.mem_ofArrows_iff` describes membership through an existential over the index
type.

## References

* [Stacks Project, Tag 021P](https://stacks.math.columbia.edu/tag/021P)
* [Stacks Project, Tag 021Q](https://stacks.math.columbia.edu/tag/021Q)
* [Stacks Project, Tag 06NU](https://stacks.math.columbia.edu/tag/06NU)
* [Stacks Project, Tag 06TP](https://stacks.math.columbia.edu/tag/06TP)
* [Stacks Project, Tag 0GN4](https://stacks.math.columbia.edu/tag/0GN4)
* [Stacks Project, Tag 0GQV](https://stacks.math.columbia.edu/tag/0GQV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.ColimitsOfCohomology

namespace AlgebraicGeometry

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 021P in the big fppf category over `S`.** A covering sieve of an object `U` of the big
fppf category over `S` whose underlying scheme is affine is refined by a chosen covering family
which is finite and whose members again lie over affine schemes.

This is `AlgebraicGeometry.exists_standardFppf_refinement` localized at `S`, the step performed
inline in the proof of `AlgebraicGeometry.bigAffineFppfInclusion_isCocontinuous`: a covering sieve
of the localized topology is by definition one whose image under `CategoryTheory.Sieve.overEquiv`
covers downstairs, the standard fppf covering refining that image is read back upstairs by
equipping each of its members with the composite structure morphism to `S`, and finiteness and
affineness are the fields `finite_index` and `affine_source` of **Stacks 021Q**. -/
theorem BigFppfOver.exists_finite_affine_covering_refinement
    {U : BigFppfOver B S hS} (hU : IsAffineOver B S hS U)
    {R : Sieve U} (hR : R ∈ BigFppfOver.topology B S hS U) :
    ∃ Q : PreZeroHypercover.{u + 1} U, Finite Q.I₀ ∧
      (∀ i, IsAffineOver B S hS (Q.X i)) ∧
      BigFppfOver.IsCovering B S hS ⟨U, Q⟩ ∧ Q.presieve₀ ≤ R.arrows := by
  have hRbase : (Sieve.overEquiv U) R ∈ B.topology ((BigFppfOver.forget B S hS).obj U) := by
    rwa [GrothendieckTopology.mem_over_iff] at hR
  have hTaff : IsAffine (B.inclusion.obj ((BigFppfOver.forget B S hS).obj U)) := hU
  obtain ⟨Q, hQcover, hQstd, hQle⟩ :=
    exists_standardFppf_refinement B (T := (BigFppfOver.forget B S hS).obj U)
      (R := Sieve.overEquiv U R) hRbase
  refine ⟨⟨Q.I₀, fun i => Over.mk (Q.f i ≫ U.hom), fun i => Over.homMk (Q.f i) rfl⟩,
    hQstd.finite_index, fun i => hQstd.affine_source i, hQcover, ?_⟩
  rw [PreZeroHypercover.presieve₀, Presieve.ofArrows_le_iff]
  exact fun i => (Sieve.overEquiv_iff R (Q.f i)).mp (hQle _ _ ⟨i⟩)

namespace Stack

variable (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))

/-- The class of covering families of the big fppf category over `S` which are finite with affine
sources and are chosen covering families — asked only of the families whose target is affine.

Making the class vacuous at a non-affine target is what lets
`AlgebraicGeometry.Stack.exists_chosenCovering_le_of_mem_associatedTopology`, whose base-level
hypothesis ranges over all objects, be applied with a base-level input that Stacks 021P supplies
only over affine schemes. -/
private def FiniteAffineCoveringOverAffine (E : Covering.{u + 1, u, u + 1} (BigFppfOver B S hS)) :
    Prop :=
  IsAffineOver B S hS E.1 →
    Finite E.2.I₀ ∧ (∀ i, IsAffineOver B S hS (E.2.X i)) ∧ BigFppfOver.IsCovering B S hS E

/-- Every covering sieve of the big fppf category over `S` contains a family of
`AlgebraicGeometry.Stack.FiniteAffineCoveringOverAffine`: over an affine target this is
Stacks 021P localized at `S`, and over any other target the class is vacuous, so the tautological
family of all arrows of the sieve will do. -/
private theorem exists_finiteAffineCoveringOverAffine
    ⦃U : BigFppfOver B S hS⦄ {R : Sieve U} (hR : R ∈ B.topology.over (B.obj hS) U) :
    ∃ Q : PreZeroHypercover.{u + 1} U,
      FiniteAffineCoveringOverAffine B S hS ⟨U, Q⟩ ∧ Q.presieve₀ ≤ R.arrows := by
  classical
  by_cases hU : IsAffineOver B S hS U
  · obtain ⟨Q, hfin, haff, hcov, hle⟩ :=
      BigFppfOver.exists_finite_affine_covering_refinement B S hS hU hR
    exact ⟨Q, fun _ => ⟨hfin, haff, hcov⟩, hle⟩
  · refine ⟨⟨Σ V : BigFppfOver B S hS, {g : V ⟶ U // R g}, fun i => i.1, fun i => i.2.1⟩,
      fun h => absurd h hU, ?_⟩
    rw [PreZeroHypercover.presieve₀, Presieve.ofArrows_le_iff]
    exact fun i => i.2.2

/-- **Condition (2) of Stacks 0GN4 for the fppf site of a category fibred in groupoids over the big
fppf category of `S`, at the objects lying over affine schemes.** Every covering sieve of an object
of `𝒳` lying over an affine scheme contains a finite covering family whose members again lie over
affine schemes.

This is the second of the four conditions the proof of **Stacks 0GQV** checks, the collection `B`
of that proof being the objects of the site lying over affine schemes; the source derives it from
**Stacks 021P**, and so does the proof here.

The refinement is produced downstairs by
`AlgebraicGeometry.BigFppfOver.exists_finite_affine_covering_refinement` and transported to `𝒳` by
`AlgebraicGeometry.Stack.exists_chosenCovering_le_of_mem_associatedTopology`; the transported
family covers because its image is a chosen covering family of the big fppf category over `S` and
because in a category fibred in groupoids every morphism is strongly cartesian over its image,
which is what the covering families of **Stacks 06NU** ask of its members. See the module
documentation for the two bookkeeping steps: restricting the base-level input to affine targets,
and reindexing a finite index type by `Fin n`.

The tag registers this one condition of the proof of **Stacks 0GQV** and nothing more: the
assertion of Stacks 0GN4 is that the four conditions suffice, which is
`Stacks.Cohomology.ColimitsOfCohomology.isIso_colimit_post_rightDerived_globalSections_of_covers`,
and the full assertions of Stacks 0GQV are
`AlgebraicGeometry.Stack.isIso_colimit_post_rightDerived_globalSections_fppf_of_isQuasiCompact`
and
`AlgebraicGeometry.Stack.isIso_colimit_post_rightDerived_globalSections_etale_of_isQuasiCompact`.
-/
@[stacks 0GQV "condition (2) of Stacks 0GN4 for the fppf site, from Stacks 021P"]
theorem hasFiniteCoverRefinementsFrom_fppfTopology
    {x : 𝒳.val.obj} (hx : IsAffineObject B S hS 𝒳.val.p x) :
    HasFiniteCoverRefinementsFrom (fppfTopology B S hS 𝒳)
      {y : 𝒳.val.obj | IsAffineObject B S hS 𝒳.val.p y} x := by
  classical
  intro T hT
  obtain ⟨E, hE, hEle⟩ := exists_chosenCovering_le_of_mem_associatedTopology B S hS 𝒳.val.p
    B.topology (FiniteAffineCoveringOverAffine B S hS)
    (fun _ _ hR => exists_finiteAffineCoveringOverAffine B S hS hR)
    𝒳.isFiberedInGroupoids T hT
  obtain ⟨hfin, haff, hcov⟩ := hE hx
  have hfin' : Finite E.I₀ := hfin
  let e : E.I₀ ≃ Fin (Nat.card E.I₀) := Finite.equivFin E.I₀
  have hsieve : Sieve.ofArrows (fun i => E.X (e.symm i)) (fun i => E.f (e.symm i)) =
      Sieve.ofArrows E.X E.f := by
    ext W g
    rw [Sieve.mem_ofArrows_iff, Sieve.mem_ofArrows_iff]
    exact ⟨fun ⟨i, a, h⟩ => ⟨e.symm i, a, h⟩,
      fun ⟨i, a, h⟩ => ⟨e i, by rw [e.symm_apply_apply]; exact ⟨a, h⟩⟩⟩
  have hup : Sieve.ofArrows E.X E.f ∈ fppfTopology B S hS 𝒳 x := by
    rw [fppfTopology, associatedTopology, Functor.inheritedTopology_eq]
    refine Precoverage.generate_mem_toGrothendieck
      ⟨fun _ q _ => Functor.IsFiberedInGroupoids.isStronglyCartesian
        𝒳.isFiberedInGroupoids q, ?_⟩
    rw [GrothendieckTopology.mem_toPrecoverage_iff, Presieve.map_ofArrows]
    have hBcover : Sieve.ofArrows (fun i => 𝒳.val.p.obj (E.X i))
        (fun i => 𝒳.val.p.map (E.f i)) ∈
          (B.topology.over (B.obj hS)) (𝒳.val.p.obj x) := by
      rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
      have hpre : ((E.map 𝒳.val.p).map (BigFppfOver.forget B S hS)).presieve₀ ∈
          B.precoverage ((BigFppfOver.forget B S hS).obj (𝒳.val.p.obj x)) :=
        ⟨(E.map 𝒳.val.p).map (BigFppfOver.forget B S hS), rfl, hcov⟩
      simpa [PreZeroHypercover.presieve₀, PreZeroHypercover.map] using
        Precoverage.generate_mem_toGrothendieck hpre
    exact hBcover
  refine ⟨Nat.card E.I₀, fun i => E.X (e.symm i), fun i => E.f (e.symm i),
    fun i => haff (e.symm i), ?_, ?_⟩
  · rwa [hsieve]
  · rwa [hsieve, Sieve.ofArrows, Sieve.generate_le_iff]

end Stack

end AlgebraicGeometry

end
