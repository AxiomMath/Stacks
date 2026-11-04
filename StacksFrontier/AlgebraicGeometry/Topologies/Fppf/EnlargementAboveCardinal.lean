module

public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.ChangeOfBigSites
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.CommonBigSites
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ContainingSet

/-!
# Enlarging a big fppf site past a given cardinal

Every big fppf site `B` is contained, in the sense of `AlgebraicGeometry.IsContained`, in a big
fppf site whose cutoff exceeds any prescribed cardinal of the universe of the schemes. The
larger site is the common enlargement (Stacks 022J,
`AlgebraicGeometry.exists_common_bigFppfSite`) of `B` and of a big fppf site with a cutoff above
the cardinal (`AlgebraicGeometry.BigFppfSite.ofCutoff`, at a strong limit cardinal supplied by
Stacks 000J).

That the common enlargement *contains* `B` — and not merely has a larger cutoff and a larger
covering bound — is because the chosen covering families of a big fppf site are, by definition,
*all* the fppf covering families of `Sch_κ` whose index sets are bounded by its covering bound
(`AlgebraicGeometry.BigFppfSite.IsCovering`): a chosen covering family of `B` is fppf and has a
small enough index set, and neither property changes in the larger site.

## Main results

* `AlgebraicGeometry.BigFppfSite.isContained_of_le`: a big fppf site whose cutoff and covering
  bound dominate those of `B` contains `B`.
* `AlgebraicGeometry.BigFppfSite.exists_isContained_lt_cutoff`: `B` is contained in a big fppf site
  with cutoff above a prescribed cardinal.

## References

* [Stacks Project, Tag 022J](https://stacks.math.columbia.edu/tag/022J)
* [Stacks Project, Tag 000J](https://stacks.math.columbia.edu/tag/000J)
* [Stacks Project, Tag 03FO](https://stacks.math.columbia.edu/tag/03FO)
-/

@[expose] public section

open CategoryTheory Cardinal

universe u

namespace AlgebraicGeometry.BigFppfSite

/-- An fppf covering family of `Sch_κ` stays an fppf covering family of `Sch_κ'` for `κ ≤ κ'`: the
condition is on the underlying family of schemes. -/
theorem isFppfCovering_map_of_le {κ κ' : Cardinal.{u}}
    (hle : schemeSizeBelow κ ≤ schemeSizeBelow κ')
    (E : Covering.{u + 1, u, u + 1} (SchemeBelow κ)) (hE : IsFppfCovering E) :
    IsFppfCovering (κ := κ') ⟨(ObjectProperty.ιOfLE hle).obj E.1,
      E.2.map (ObjectProperty.ιOfLE hle)⟩ := by
  change E.2.presieve₀ ∈ Scheme.fppfPrecoverage.comap (schemeBelowInclusion κ) E.1 at hE
  show (E.2.map (ObjectProperty.ιOfLE hle)).presieve₀ ∈ Scheme.fppfPrecoverage.comap
    (schemeBelowInclusion κ') _
  simpa [Precoverage.mem_comap_iff, PreZeroHypercover.presieve₀, PreZeroHypercover.map,
    Presieve.map_ofArrows] using hE

/-- **A big fppf site whose cutoff and covering bound dominate those of `B` contains `B`.** The
chosen covering families of a big fppf site are all its fppf covering families with index sets
bounded by its covering bound, so a chosen covering family of `B` stays one in the larger site. -/
theorem isContained_of_le {B C : BigFppfSite.{u}} (hcut : B.cutoff ≤ C.cutoff)
    (hcov : B.coveringBound ≤ C.coveringBound) : IsContained (τ := .fppf) B C := by
  have hle : schemeSizeBelow B.cutoff ≤ schemeSizeBelow C.cutoff :=
    fun T hT => lt_of_lt_of_le hT hcut
  exact ⟨hle, fun E hE => ⟨isFppfCovering_map_of_le hle E hE.1, hE.2.trans hcov⟩⟩

/-- **Every big fppf site is contained in one whose cutoff exceeds a given cardinal.** -/
theorem exists_isContained_lt_cutoff (B : BigFppfSite.{u}) (μ : Cardinal.{u}) :
    ∃ C : BigFppfSite.{u}, IsContained (τ := .fppf) B C ∧ μ < C.cutoff := by
  obtain ⟨κ, hμκ, hsl, hcof⟩ := Cardinal.exists_isStrongPrelimit_gt_of_aleph0_lt_cof (max ℵ₀ μ)
  have hκ : ℵ₀ < κ := (le_max_left _ _).trans_lt hμκ
  let B₁ := ofCutoff κ hκ hsl hcof (∅ : Set Scheme.{u}) (by simp)
  obtain ⟨C, hC⟩ := exists_common_bigFppfSite (ι := Bool) (fun b => if b then B else B₁)
  have hB := hC true
  have hB₁ := hC false
  simp only [if_true, Bool.false_eq_true, if_false] at hB hB₁
  exact ⟨C, isContained_of_le hB.1 hB.2,
    ((le_max_right _ _).trans_lt hμκ).trans_le hB₁.1⟩

end AlgebraicGeometry.BigFppfSite

end
