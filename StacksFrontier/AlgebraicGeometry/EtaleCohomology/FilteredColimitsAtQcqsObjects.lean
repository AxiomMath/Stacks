module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HigherDirectImageDirectSums

/-!
# Coverings of quasi-compact quasi-separated objects of the small étale site

Companions to the base's `Stacks.EtaleCohomology.qcqsEtaleObjects` and
`Stacks.EtaleCohomology.qcqsEtaleCovering`
(`StacksFrontier.AlgebraicGeometry.EtaleCohomology.HigherDirectImageDirectSums`), whose
`Stacks.EtaleCohomology.isIso_colimit_post_rightDerived_sheafSections_of_qcqs` is
[Stacks, Tag 0739] on the small étale site: étale cohomology over an object with quasi-compact
and quasi-separated underlying scheme commutes with filtered colimits.

## Main results

* `Stacks.EtaleCohomology.mem_qcqsEtaleObjects_of_iso` — membership in `qcqsEtaleObjects X` is
  invariant under isomorphism.
* `Stacks.EtaleCohomology.exists_qcqsCovering_le` — every covering sieve of an object of
  `qcqsEtaleObjects X` contains a member of `qcqsEtaleCovering X U` by objects with affine
  underlying scheme (from the base's `exists_finite_isAffine_covering_le`).
* `Stacks.EtaleCohomology.hasIntersectionsIn_qcqsEtaleObjects` — a member of
  `qcqsEtaleCovering X U` has all its iterated fibre products in `qcqsEtaleObjects X`.

## References

* [Stacks Project, Tag 0739](https://stacks.math.columbia.edu/tag/0739)
* [Stacks Project, Tag 03Q5](https://stacks.math.columbia.edu/tag/03Q5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe v u

namespace Stacks.EtaleCohomology

noncomputable section

variable {X : Scheme.{u}}

/-- Having quasi-compact and quasi-separated underlying scheme is invariant under isomorphism in
the small étale site. -/
theorem mem_qcqsEtaleObjects_of_iso {V W : X.Etale} (e : V ≅ W) (hW : W ∈ qcqsEtaleObjects X) :
    V ∈ qcqsEtaleObjects X := by
  let k := (Scheme.Etale.forget X ⋙ Over.forget X).mapIso e
  have : CompactSpace ((Scheme.Etale.forget X ⋙ Over.forget X).obj W) := hW.1
  have : QuasiSeparatedSpace ((Scheme.Etale.forget X ⋙ Over.forget X).obj W) := hW.2
  exact ⟨k.inv.homeomorph.compactSpace,
    (quasiSeparatedSpace_congr k.hom.homeomorph).mpr inferInstance⟩

attribute [local instance] AlgebraicGeometry.Etale.isStableUnderComposition
  Stacks.EtaleCohomology.etaleContainsIdentities etale_respectsIso

/-- **Cofinal coverings in `qcqsEtaleCovering`.** Every covering sieve of an object of
`qcqsEtaleObjects X` contains a finite covering family by objects with affine underlying scheme,
which is in particular a member of `qcqsEtaleCovering X U`. -/
theorem exists_qcqsCovering_le (U : X.Etale) (hU : U ∈ qcqsEtaleObjects X) (R : Sieve U)
    (hR : R ∈ X.smallEtaleTopology U) :
    ∃ E ∈ qcqsEtaleCovering X U, (∀ i, IsAffine (E.X i).left) ∧ E.sieve₀ ≤ R := by
  have := hU.1
  obtain ⟨E, hfin, haff, hcov, hle⟩ := exists_finite_isAffine_covering_le U R hR
  exact ⟨E, ⟨hfin, hU, fun i ↦ have := haff i; mem_qcqsEtaleObjects_of_isAffine _, hcov⟩,
    haff, hle⟩

/-- A family in `qcqsEtaleCovering X U` has all its iterated fibre products in
`qcqsEtaleObjects X`, by induction on the family from the binary case. -/
theorem hasIntersectionsIn_qcqsEtaleObjects (U : X.Etale) (E : PreZeroHypercover.{u} U)
    (hE : E ∈ qcqsEtaleCovering X U) :
    Stacks.Cohomology.HasIntersectionsIn (qcqsEtaleObjects X) E := by
  refine ⟨hE.1, hE.2.1, hE.2.2.1, fun n A ↦ ?_⟩
  exact Stacks.Cohomology.exists_widePullback_in (qcqsEtaleObjects X)
    (fun f g hu hv hw ↦ exists_pullbackCone_mem_qcqsEtaleObjects f g hu hv hw)
    hE.2.1 (n + 1) (fun i ↦ E.X (A i)) (fun i ↦ E.f (A i)) (fun i ↦ hE.2.2.1 (A i))

end

end Stacks.EtaleCohomology
