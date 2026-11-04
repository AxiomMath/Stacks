module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.PullbackTautologicalSection
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.SpanNonvanishing
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartSourceTilde
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.LocalOnBase
public import StacksFrontier.AlgebraicGeometry.SectionPowerOverOpen.Basic

/-!
# The section of the bundle does not meet the hyperplane cut out by a frame

Clause 3 of [Stacks, Tag 0B3V] computes the conormal sheaf of a section `σ` of
`π : 𝐏(ℰ) ⟶ X` on a chart of the bundle, and the chart it uses is the standard open `D₊(ι s)`
attached to a section `s` of `ℰ` whose image generates `𝓛`. For that to be a chart *containing
the image of `σ`*, the pulled-back degree-one section attached to `s` must vanish nowhere over
the open where `s` was chosen. **This file proves that**, which is the remaining hypothesis of
the factorization criterion
`Stacks.ProjectiveBundleConormal.preimage_basicOpen_eq_top_pullbackSection`.

The proof is three transports and one piece of mathematics:

* `Stacks.ProjectiveBundleConormal.hom_pullbackSection_tautologicalMap` says the pulled-back
  section is `q(s)` once carried across `e : σ^*𝒪(1) ≅ 𝓛`, and
  `Stacks.SectionPowerOverOpen.mem_nonvanishingLocusOn_congr_iff` moves the nonvanishing locus
  across that isomorphism;
* `Stacks.ProjectiveBundleConormal.mem_nonvanishingLocusOn_of_span_eq_top` is the mathematics:
  on an affine open, a section spanning the sections of an invertible module vanishes nowhere;
* `Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn_res` undoes the restriction from
  `σ ⁻¹ᵁ (π ⁻¹ᵁ W)` to `W` that
  `AlgebraicGeometry.Scheme.Modules.pullbackSection` interposes, and
  `Stacks.NonvanishingLocusRestrict.preimage_nonvanishingLocusOn` — [Stacks, Tag 0H78] over an
  open — carries the locus upstairs to the bundle.

## Main results

* `Stacks.ProjectiveBundleConormal.mem_nonvanishingLocusOn_tautologicalSection`: **the image of
  a point of `W` under `σ` lies where the degree-one section attached to `s` does not vanish**,
  whenever `q(s)` spans `Γ(𝓛, W)` and `W` is affine.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
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
  (Q : Stacks.Divisors.InvertibleQuotient X E)
  {σ : X ⟶ (bundle E).scheme} (hσ : σ ≫ (bundle E).toBase = 𝟙 X)
  (e : (Scheme.Modules.pullback σ).obj (tautologicalTwist E (symPieces E)) ≅ Q.L)
  (hqe : (Scheme.Modules.pullbackId X).inv.app E ≫
    (Scheme.Modules.pullbackCongr hσ).inv.app E ≫
      (Scheme.Modules.pullbackComp σ (bundle E).toBase).inv.app E ≫
        (Scheme.Modules.pullback σ).map (tautologicalMap E (symPieces E)) ≫ e.hom = Q.q)

include hσ e hqe in
/-- **A section of the bundle classifying `q` avoids the hyperplane of a frame.** If `W` is an
affine open on which the image `q(s)` of a section `s` of `ℰ` spans `Γ(𝓛, W)`, then for every
point `x` of `W` the image `σ(x)` lies in the locus over `π⁻¹W` where the degree-one section of
`𝒪(1)` attached to `s` does not vanish.

This is the geometric content of clause 3 of [Stacks, Tag 0B3V]: the section classifying `q`
lands in the standard open cut out by any `s` whose image generates. -/
theorem mem_nonvanishingLocusOn_tautologicalSection (W : X.Opens) (hW : IsAffineOpen W)
    (s : Γ(E, W))
    (ht : Submodule.span Γ(X, W) {Q.q.app W s} = ⊤) {x : X} (hx : x ∈ W) :
    σ.base x ∈ Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn
      (tautologicalTwist E (symPieces E)) ((bundle E).toBase ⁻¹ᵁ W)
      ((tautologicalMap E (symPieces E)).val.app (op ((bundle E).toBase ⁻¹ᵁ W))
        (unitSection (bundle E).toBase E W s)) := by
  have hσπ : W ≤ σ ⁻¹ᵁ ((bundle E).toBase ⁻¹ᵁ W) := (preimage_toBase_preimage E hσ W).ge
  have hQ := mem_nonvanishingLocusOn_of_span_eq_top Q.L hW (Q.q.app W s) ht hx
  have hz : x ∈ Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn
      ((Scheme.Modules.pullback σ).obj (tautologicalTwist E (symPieces E))) W
      (Scheme.Modules.pullbackSection σ (tautologicalTwist E (symPieces E))
        ((bundle E).toBase ⁻¹ᵁ W) W hσπ
        ((tautologicalMap E (symPieces E)).val.app (op ((bundle E).toBase ⁻¹ᵁ W))
          (unitSection (bundle E).toBase E W s))) :=
    (Stacks.SectionPowerOverOpen.mem_nonvanishingLocusOn_congr_iff e W _ hx).mp
      (Eq.mpr
        (congrArg
          (fun y => x ∈ Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn Q.L W y)
          (hom_pullbackSection_tautologicalMap E Q hσ e hqe W s))
        hQ)
  have hres := Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn_res
    ((Scheme.Modules.pullback σ).obj (tautologicalTwist E (symPieces E))) hσπ
    (unitSection σ (tautologicalTwist E (symPieces E)) ((bundle E).toBase ⁻¹ᵁ W)
      ((tautologicalMap E (symPieces E)).val.app (op ((bundle E).toBase ⁻¹ᵁ W))
        (unitSection (bundle E).toBase E W s)))
  exact (Set.ext_iff.mp
      (Stacks.NonvanishingLocusRestrict.preimage_nonvanishingLocusOn σ
        (tautologicalTwist E (symPieces E))
        ((tautologicalMap E (symPieces E)).val.app (op ((bundle E).toBase ⁻¹ᵁ W))
          (unitSection (bundle E).toBase E W s))) x).mpr
    ((Set.ext_iff.mp hres x).mp hz).2

end Stacks.ProjectiveBundleConormal

end
