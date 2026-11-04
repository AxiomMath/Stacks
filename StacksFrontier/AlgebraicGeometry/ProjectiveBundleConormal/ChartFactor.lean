module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartNonvanishing
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartSection

/-!
# The section of the bundle, read on a chart, lands in the standard open of a frame

This completes the factorization half of clause 3 of [Stacks, Tag 0B3V]. Let `W` be an affine
open of the base carrying a section `s` of `ℰ` whose image `q(s)` spans `Γ(𝓛, W)`, and let
`σ|_W : W ⟶ Proj(Sym_A M)` be the section of the bundle read on the chart over `W`
(`Stacks.ProjectiveBundleConormal.chartSection`). **Then `σ|_W` factors through the standard open
`D₊(ι s)`**, which is the affine chart
`Stacks.ProjectiveBundleConormal.splitChartMap` identifies with the affine bundle on `ker p`.

Three statements are chained, and no new mathematics appears:

* `Stacks.ProjectiveBundleConormal.mem_nonvanishingLocusOn_tautologicalSection` says the
  degree-one section attached to `s` does not vanish at `σ(x)` for any `x` of `W`;
* `Stacks.ProjectiveBundleConormal.chartSection_comp_chartMap` says the point of the bundle
  named by `σ|_W` is `σ(x)`;
* `Stacks.ProjectiveBundleConormal.basicOpen_eq_nonvanishingLocus_pullbackSection` identifies
  `D₊(ι s)` with the nonvanishing locus of that section pulled back to the chart.

## Main results

* `Stacks.ProjectiveBundleConormal.chartSection_preimage_basicOpen_eq_top`: **`σ|_W` factors
  through `D₊(ι s)`.**

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjDegreeOne (unitSection)
open Stacks.ProjectiveBundleSplitting
open Stacks.SymGraded

universe u

namespace Stacks.ProjectiveBundleConormal

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent]

/-- **The degree-one section of `𝒪(1)` attached to a section of `ℰ` over `W`**: the value at the
pullback of `s` of the tautological map `u : π^*ℰ ⟶ 𝒪(1)`, a section of `𝒪(1)` over `π⁻¹W`. Its
nonvanishing locus is the standard open `D₊(ι s)` of the chart. -/
abbrev tautologicalSectionOver (W : X.Opens) (s : Γ(E, W)) :
    Γ(tautologicalTwist E (symPieces E), (bundle E).toBase ⁻¹ᵁ W) :=
  (tautologicalMap E (symPieces E)).val.app (op ((bundle E).toBase ⁻¹ᵁ W))
    (unitSection (bundle E).toBase E W s)

variable (Q : Stacks.Divisors.InvertibleQuotient X E)
  {σ : X ⟶ (bundle E).scheme} (hσ : σ ≫ (bundle E).toBase = 𝟙 X)
  (e : (Scheme.Modules.pullback σ).obj (tautologicalTwist E (symPieces E)) ≅ Q.L)
  (hqe : (Scheme.Modules.pullbackId X).inv.app E ≫
    (Scheme.Modules.pullbackCongr hσ).inv.app E ≫
      (Scheme.Modules.pullbackComp σ (bundle E).toBase).inv.app E ≫
        (Scheme.Modules.pullback σ).map (tautologicalMap E (symPieces E)) ≫ e.hom = Q.q)

include hσ e hqe in
/-- **The section of the bundle, read on the chart over `W`, factors through `D₊(ι s)`.** If `W`
is affine and the image `q(s)` of `s : Γ(ℰ, W)` spans `Γ(𝓛, W)`, then the whole of `W` is carried
by `Stacks.ProjectiveBundleConormal.chartSection` into the standard open of `ι s`.

So the conormal computation of clause 3 of [Stacks, Tag 0B3V] may be carried out on the affine
chart `Spec (Sym_A (ker p))` that `Stacks.ProjectiveBundleConormal.splitChartMap` identifies with
`D₊(ι s)`. -/
theorem chartSection_preimage_basicOpen_eq_top {W : X.Opens} (hW : IsAffineOpen W)
    (s : Γ(E, W)) (ht : Submodule.span Γ(X, W) {Q.q.app W s} = ⊤) :
    chartSection E hW hσ ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
        (SymmetricAlgebra.grading Γ(X, W) Γ(E, W))
        (SymmetricAlgebra.ι Γ(X, W) Γ(E, W) s) = ⊤ := by
  refine eq_top_iff.mpr fun y _ => ?_
  have hpt : (chartMap E (symPieces E) hW).base ((chartSection E hW hσ).base y)
      = σ.base (W.ι.base y) := by
    have h := congrArg (fun f : W.toScheme ⟶ (bundle E).scheme => f.base y)
      (chartSection_comp_chartMap E hW hσ)
    simpa using h
  have hσy := mem_nonvanishingLocusOn_tautologicalSection E Q hσ e hqe W hW s ht
    (x := W.ι.base y) y.2
  have hchart := (Set.ext_iff.mp
      (Stacks.NonvanishingLocusRestrict.preimage_nonvanishingLocusOn
        (chartMap E (symPieces E) hW) (tautologicalTwist E (symPieces E))
        (tautologicalSectionOver E W s))
      ((chartSection E hW hσ).base y)).mp
    (Eq.mpr
      (congrArg
        (fun z => z ∈ Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn
          (tautologicalTwist E (symPieces E)) ((bundle E).toBase ⁻¹ᵁ W)
          (tautologicalSectionOver E W s))
        hpt)
      hσy)
  have hres := Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn_res
    ((Scheme.Modules.pullback (chartMap E (symPieces E) hW)).obj
      (tautologicalTwist E (symPieces E)))
    (top_le_chartMap_preimage E (symPieces E) hW)
    (unitSection (chartMap E (symPieces E) hW) (tautologicalTwist E (symPieces E))
      ((bundle E).toBase ⁻¹ᵁ W) (tautologicalSectionOver E W s))
  have htop := (Set.ext_iff.mp hres ((chartSection E hW hσ).base y)).mpr ⟨trivial, hchart⟩
  exact (Set.ext_iff.mp
      (basicOpen_eq_nonvanishingLocus_pullbackSection E (symPieces E) hW s)
      ((chartSection E hW hσ).base y)).mpr
    ((Set.ext_iff.mp
      (Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn_top
        ((Scheme.Modules.pullback (chartMap E (symPieces E) hW)).obj
          (tautologicalTwist E (symPieces E)))
        (Scheme.Modules.pullbackSection (chartMap E (symPieces E) hW)
          (tautologicalTwist E (symPieces E)) ((bundle E).toBase ⁻¹ᵁ W) ⊤
          (top_le_chartMap_preimage E (symPieces E) hW) (tautologicalSectionOver E W s)))
      ((chartSection E hW hσ).base y)).mp htop)

end Stacks.ProjectiveBundleConormal

end
