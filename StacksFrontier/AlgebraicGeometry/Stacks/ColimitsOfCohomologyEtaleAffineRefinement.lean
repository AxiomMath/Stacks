module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AssociatedSiteRefinement
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineSite
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.ChosenEtaleAffineRefinement
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.FilteredColimits.FiniteCoproductsOfRepresentables

/-!
# Finite affine refinements of coverings on the étale site of a stack

Let `𝒳` be a category fibred in groupoids over the big fppf category of a scheme `S` contained in
a big fppf site `B`, with the **étale** topology of **Stacks 06TP** on its total category — the
one it inherits from the big étale topology `AlgebraicGeometry.etaleTopology` of **Stacks 03FF**
localized at `S`. This file proves that every covering sieve of an object of `𝒳` lying over an
affine scheme is refined by a *finite* covering family whose members again lie over affine
schemes.

That assertion is condition (2) of **Stacks 0GN4** for the collection `B` of the proof of
**Stacks 0GQV**, namely the objects of the site lying over affine schemes, and it is the
hypothesis `HasFiniteCoverRefinementsFrom` of the criterion proved in the file
`FiniteCoveringCriterionOnALargeSite.lean` of `StacksFrontier/CategoryTheory/Sites/Cohomology/`
`FilteredColimits/`.
It is the étale counterpart of
`AlgebraicGeometry.Stack.hasFiniteCoverRefinementsFrom_fppfTopology`, which is the same condition
for the fppf site.

## Main results

* `AlgebraicGeometry.BigFppfOver.exists_finite_affine_etaleCovering_refinement`: **Stacks 0218 in
  the big fppf category over `S`** — a covering sieve of the big étale topology localized at `S`
  at an object lying over an affine scheme is refined by a finite selected étale covering family
  whose members lie over affine schemes.
* `AlgebraicGeometry.Stack.hasFiniteCoverRefinementsFrom_etaleTopology`: condition (2) of
  Stacks 0GN4 for the étale site of `𝒳` and the objects lying over affine schemes.

## Implementation notes

The two steps are the ones of the fppf case, with Stacks 0218 in place of Stacks 021P.

The localization from `B.Schemes` to the big fppf category over `S` is
`AlgebraicGeometry.exists_finite_affine_etaleCovering_le_of_mem_etaleTopology` read through
`CategoryTheory.Sieve.overEquiv`: a covering sieve of the localized topology is by definition one
whose image covers downstairs, and the refinement is read back upstairs by equipping each of its
members with the composite structure morphism to `S`. Finiteness and affineness are unchanged by
that passage, affineness because `AlgebraicGeometry.IsAffineOver` is a condition on the underlying
scheme alone.

Transporting the refinement up to `𝒳` is
`AlgebraicGeometry.Stack.exists_chosenCovering_le_of_mem_associatedTopology`, which takes the
topology of the base and the class of chosen families as parameters; it is used here at
`AlgebraicGeometry.etaleTopology` and at the selected étale families. Its base-level hypothesis is
quantified over *every* object of the big fppf category over `S`, whereas Stacks 0218 needs the
target to be affine, so — exactly as in the fppf case — the class of families fed to it is taken
to be *conditional on affineness of the target*: for a non-affine target the class holds of every
family, and the tautological family of all arrows of the given sieve discharges the hypothesis
there. At the affine object the condition is then available in full.

The resulting family is indexed by a finite type in `Type (u + 1)`, while
`Stacks.Cohomology.ColimitsOfCohomology.HasFiniteCoverRefinementsFrom` asks for an indexing by
`Fin n`; `Finite.equivFin` reindexes it, and the two generated sieves agree because
`CategoryTheory.Sieve.mem_ofArrows_iff` describes membership through an existential over the index
type.

## References

* [Stacks Project, Tag 0218](https://stacks.math.columbia.edu/tag/0218)
* [Stacks Project, Tag 03FF](https://stacks.math.columbia.edu/tag/03FF)
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

/-- **Stacks 0218 in the big fppf category over `S`.** A covering sieve of the big étale topology
localized at `S` at an object `U` whose underlying scheme is affine is refined by a selected étale
covering family which is finite and whose members again lie over affine schemes.

This is `AlgebraicGeometry.exists_finite_affine_etaleCovering_le_of_mem_etaleTopology` localized
at `S`, by the same passage as in
`AlgebraicGeometry.BigFppfOver.exists_etaleCovering_le_of_mem_etaleTopology`: a covering sieve of
the localized topology is by definition one whose image under `CategoryTheory.Sieve.overEquiv`
covers downstairs, and the refinement of that image is read back upstairs by equipping each of its
members with the composite structure morphism to `S`. -/
theorem BigFppfOver.exists_finite_affine_etaleCovering_refinement
    {U : BigFppfOver B S hS} (hU : IsAffineOver B S hS U)
    {R : Sieve U} (hR : R ∈ (etaleTopology B).over (B.obj hS) U) :
    ∃ E : PreZeroHypercover.{u + 1} U, Finite E.I₀ ∧
      (∀ i, IsAffineOver B S hS (E.X i)) ∧
      etaleCovering B ⟨(BigFppfOver.forget B S hS).obj U,
        E.map (BigFppfOver.forget B S hS)⟩ ∧ E.presieve₀ ≤ R.arrows := by
  rw [GrothendieckTopology.mem_over_iff] at hR
  have hXaff : IsAffine (B.inclusion.obj ((BigFppfOver.forget B S hS).obj U)) := hU
  obtain ⟨E, hE, hfin, haff, hle⟩ :=
    exists_finite_affine_etaleCovering_le_of_mem_etaleTopology B hXaff hR
  refine ⟨⟨E.I₀, fun i => Over.mk (E.f i ≫ U.hom), fun i => Over.homMk (E.f i) rfl⟩,
    hfin, haff, hE, ?_⟩
  rw [PreZeroHypercover.presieve₀, Presieve.ofArrows_le_iff]
  exact fun i => (Sieve.overEquiv_iff R (E.f i)).mp (hle _ _ ⟨i⟩)

namespace Stack

variable (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))

/-- The class of covering families of the big fppf category over `S` which are finite with affine
sources and are selected *étale* covering families — asked only of the families whose target is
affine.

Making the class vacuous at a non-affine target is what lets
`AlgebraicGeometry.Stack.exists_chosenCovering_le_of_mem_associatedTopology`, whose base-level
hypothesis ranges over all objects, be applied with a base-level input that Stacks 0218 supplies
only over affine schemes. -/
private def FiniteAffineEtaleCoveringOverAffine
    (E : Covering.{u + 1, u, u + 1} (BigFppfOver B S hS)) : Prop :=
  IsAffineOver B S hS E.1 →
    Finite E.2.I₀ ∧ (∀ i, IsAffineOver B S hS (E.2.X i)) ∧
      etaleCovering B ⟨(BigFppfOver.forget B S hS).obj E.1,
        E.2.map (BigFppfOver.forget B S hS)⟩

/-- Every covering sieve of the big étale topology localized at `S` contains a family of
`AlgebraicGeometry.Stack.FiniteAffineEtaleCoveringOverAffine`: over an affine target this is
Stacks 0218 localized at `S`, and over any other target the class is vacuous, so the tautological
family of all arrows of the sieve will do. -/
private theorem exists_finiteAffineEtaleCoveringOverAffine
    ⦃U : BigFppfOver B S hS⦄ {R : Sieve U} (hR : R ∈ (etaleTopology B).over (B.obj hS) U) :
    ∃ E : PreZeroHypercover.{u + 1} U,
      FiniteAffineEtaleCoveringOverAffine B S hS ⟨U, E⟩ ∧ E.presieve₀ ≤ R.arrows := by
  classical
  by_cases hU : IsAffineOver B S hS U
  · obtain ⟨E, hfin, haff, hcov, hle⟩ :=
      BigFppfOver.exists_finite_affine_etaleCovering_refinement B S hS hU hR
    exact ⟨E, fun _ => ⟨hfin, haff, hcov⟩, hle⟩
  · refine ⟨⟨Σ V : BigFppfOver B S hS, {g : V ⟶ U // R g}, fun i => i.1, fun i => i.2.1⟩,
      fun h => absurd h hU, ?_⟩
    rw [PreZeroHypercover.presieve₀, Presieve.ofArrows_le_iff]
    exact fun i => i.2.2

/-- **Condition (2) of Stacks 0GN4 for the étale site of a category fibred in groupoids over the
big fppf category of `S`, at the objects lying over affine schemes.** Every covering sieve of an
object of `𝒳` lying over an affine scheme contains a finite covering family whose members again
lie over affine schemes, the topology on `𝒳` being the one it inherits (Stacks 06TP) from the big
étale topology of **Stacks 03FF** localized at `S`.

This is the second of the four conditions the proof of **Stacks 0GQV** checks, the collection `B`
of that proof being the objects of the site lying over affine schemes. For the fppf site the
source derives it from **Stacks 021P**; in the étale topology the corresponding input is
**Stacks 0218**, and that is what is used here, through
`AlgebraicGeometry.BigFppfOver.exists_finite_affine_etaleCovering_refinement`.

The refinement is transported to `𝒳` by
`AlgebraicGeometry.Stack.exists_chosenCovering_le_of_mem_associatedTopology` at the big étale
topology; the transported family covers because its image is a selected étale covering family of
the big fppf category over `S` and because in a category fibred in groupoids every morphism is
strongly cartesian over its image, which is what the covering families of **Stacks 06NU** ask of
its members. See the module documentation for the two bookkeeping steps: restricting the
base-level input to affine targets, and reindexing a finite index type by `Fin n`.

This is the étale counterpart of
`AlgebraicGeometry.Stack.hasFiniteCoverRefinementsFrom_fppfTopology`, and like it holds for every
category fibred in groupoids, with no quasi-compactness hypothesis. -/
@[stacks 0GQV "condition (2) of Stacks 0GN4 for the étale site, from Stacks 0218"]
theorem hasFiniteCoverRefinementsFrom_etaleTopology
    {x : 𝒳.val.obj} (hx : IsAffineObject B S hS 𝒳.val.p x) :
    HasFiniteCoverRefinementsFrom (associatedTopology B S hS 𝒳.val.p (etaleTopology B))
      {y : 𝒳.val.obj | IsAffineObject B S hS 𝒳.val.p y} x := by
  classical
  intro T hT
  obtain ⟨E, hE, hEle⟩ := exists_chosenCovering_le_of_mem_associatedTopology B S hS 𝒳.val.p
    (etaleTopology B) (FiniteAffineEtaleCoveringOverAffine B S hS)
    (fun _ _ hR => exists_finiteAffineEtaleCoveringOverAffine B S hS hR)
    𝒳.isFiberedInGroupoids T hT
  obtain ⟨hfin, haff, hcov⟩ := hE hx
  have hfin' : Finite E.I₀ := hfin
  let e : E.I₀ ≃ Fin (Nat.card E.I₀) := Finite.equivFin E.I₀
  have hsieve : Sieve.ofArrows (fun i => E.X (e.symm i)) (fun i => E.f (e.symm i)) =
      Sieve.ofArrows E.X E.f := by
    ext W g
    rw [Sieve.mem_ofArrows_iff, Sieve.mem_ofArrows_iff]
    refine ⟨fun ⟨i, a, h⟩ => ⟨e.symm i, a, h⟩, fun ⟨i, a, h⟩ => ⟨e i, ?_⟩⟩
    rw [e.symm_apply_apply]
    exact ⟨a, h⟩
  have hup : Sieve.ofArrows E.X E.f ∈
      associatedTopology B S hS 𝒳.val.p (etaleTopology B) x := by
    rw [associatedTopology, Functor.inheritedTopology_eq]
    refine Precoverage.generate_mem_toGrothendieck
      ⟨fun _ q _ => Functor.IsFiberedInGroupoids.isStronglyCartesian
        𝒳.isFiberedInGroupoids q, ?_⟩
    rw [GrothendieckTopology.mem_toPrecoverage_iff, Presieve.map_ofArrows]
    have hBcover : Sieve.ofArrows (fun i => 𝒳.val.p.obj (E.X i))
        (fun i => 𝒳.val.p.map (E.f i)) ∈
          ((etaleTopology B).over (B.obj hS)) (𝒳.val.p.obj x) := by
      rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
      have hpre : ((E.map 𝒳.val.p).map (BigFppfOver.forget B S hS)).presieve₀ ∈
          etalePrecoverage B ((BigFppfOver.forget B S hS).obj (𝒳.val.p.obj x)) :=
        ⟨(E.map 𝒳.val.p).map (BigFppfOver.forget B S hS), rfl, hcov⟩
      simpa [PreZeroHypercover.presieve₀, PreZeroHypercover.map] using
        Precoverage.generate_mem_toGrothendieck hpre
    exact hBcover
  refine ⟨Nat.card E.I₀, fun i => E.X (e.symm i), fun i => E.f (e.symm i),
    fun i => haff (e.symm i), ?_, ?_⟩
  · rwa [hsieve]
  · rw [hsieve, Sieve.ofArrows, Sieve.generate_le_iff]
    exact hEle

end Stack

end AlgebraicGeometry

end
