module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenSubstack
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesStable

/-!
# The open substack of stable curves of genus `g` (towards Stacks 0E78)

Stacks 0E78 decomposes `𝓜̄ = Curves^{stable}` into the open and closed substacks `𝓜̄_g`,
`g ≥ 2`, of stable families `f : X → S` with `R¹f_*𝒪_X` locally free of rank `g`. Its proof
combines Stacks 0E76 (the stable families form an open substack of `Curves`) with Stacks 0E6V
(the prestable families of genus `g` form an open and closed substack of `Curves^{prestable}`).
This file proves the openness step of that combination, in the intrinsic form of condition (o) of
Stacks 0E0E: the stable families of genus `g` are the intersection of the two open loci. By
Stacks 0E0E (`AlgebraicGeometry.isOpenImmersion_curvesSubstackInclusion_and_factors_iff`) condition
(o) makes `𝓜̄_g ⊂ Curves` an open substack with the universal property (1) of Stacks 0E78.

## Main results

* `AlgebraicGeometry.IsOpenCurvesLocus.of_iff`: condition (o) depends only on the property up to
  equivalence.
* `AlgebraicGeometry.isOpenCurvesLocus_isStableCurveFamilyOfGenus`: condition (o) for being stable
  of genus `g`, from the statements of Stacks 0E76 and of the genus-`g` part of Stacks 0E6V.

## Implementation notes

`AlgebraicGeometry.isOpenCurvesLocus_isStableCurveFamilyOfGenus` carries no `stacks` attribute:
its two inputs are explicit hypotheses. `h0E76` is the openness assertion of Stacks 0E76, which
depends on Stacks 0E74 (ampleness of the relative dualizing sheaf of Stacks 0E6Q, built from the
relative dualizing complex of Stacks 0E5X and 0E61, and the curve lemmas
0E3L, 0E3Q, 0E63, 0E64) and on Stacks 0D3D. `h0E6V` is
condition (o) for the prestable families of genus `g`, part (1) of Stacks 0E6V, whose proof
needs 0E0R, 0E6B and 0CTM. The closedness of `𝓜̄_g` in `𝓜̄`
and part (2) of Stacks 0E78 are not stated here: the first needs the decomposition of Stacks 0E6V
and the comparison of the genus of a fibre with the rank of `R¹f_*𝒪_X`, the second the relative
dualizing sheaf.

## References

* [Stacks Project, Tag 0E78](https://stacks.math.columbia.edu/tag/0E78)
* [Stacks Project, Tag 0E76](https://stacks.math.columbia.edu/tag/0E76)
* [Stacks Project, Tag 0E6V](https://stacks.math.columbia.edu/tag/0E6V)
* [Stacks Project, Tag 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- Condition (o) of Stacks 0E0E depends only on the property of families of curves up to
equivalence. -/
theorem IsOpenCurvesLocus.of_iff {P Q : ObjectProperty (CurveFamily B hZ)}
    (hP : IsOpenCurvesLocus B hZ P) (h : ∀ X, P X ↔ Q X) : IsOpenCurvesLocus B hZ Q := by
  intro G
  obtain ⟨W, hW, hchar⟩ := hP G
  exact ⟨W, hW, fun F a => (h F).symm.trans (hchar F a)⟩

variable (B hZ)

/-- **The stable families of genus `g` form an open substack** (the openness step of the proof
of Stacks 0E78). If the stable families satisfy condition (o) of Stacks 0E0E (the openness of
Stacks 0E76) and so do the prestable families of genus `g` (part (1) of Stacks 0E6V), then so do
the stable families of genus `g`: a stable family is prestable, so they are the intersection of
the two loci. -/
theorem isOpenCurvesLocus_isStableCurveFamilyOfGenus (g : ℕ)
    (h0E76 : IsOpenCurvesLocus B hZ (IsStableCurveFamily B hZ))
    (h0E6V : IsOpenCurvesLocus B hZ
      (fun X => IsPrestableCurveFamily B hZ X ∧ CurveFamily.HasGenus B hZ X g)) :
    IsOpenCurvesLocus B hZ (IsStableCurveFamilyOfGenus B hZ g) :=
  (h0E76.and h0E6V).of_iff fun _ => ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, h.1.1, h.2⟩⟩

end AlgebraicGeometry

end
