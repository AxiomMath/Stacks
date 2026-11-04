module

public import StacksFrontier.AlgebraicGeometry.DeterminantTwoTermChartComparison
public import StacksFrontier.AlgebraicGeometry.RestrictPushforwardCoherence

/-!
# The chart comparison of determinants carries the canonical element to the canonical element

Let `X` be a scheme, `L` a perfect object of `D(𝒪_X)` of Tor-amplitude in `[-1, 0]` of rank zero,
and `V ≤ W` affine opens of `X`. The chart comparison
`AlgebraicGeometry.DeterminantTwoTerm.chartDetModuleIso` carries the canonical element of More on
Algebra, Section 0FJI of the chart complex over `Γ(X, W)` to the canonical element of the chart
complex over `Γ(X, V)`.

This is the compatibility that makes the canonical global section of the determinant on an
arbitrary scheme well defined: the family of canonical elements on the affine charts is matched by
the comparisons, and so defines a section of the glued determinant.

## Main results

* `AlgebraicGeometry.DeterminantTwoTerm.chartDetModuleIso_one_tmul_delta`: **the chart comparison
  carries `δ` to `δ`.**

## Implementation notes

Both halves are already proved. The flat base change of the determinant carries the canonical
element to the canonical element by `TwoTermDeterminant.detBaseChange_one_tmul_delta`, and the
determinant of an isomorphism of perfect two-term objects carries the canonical element to the
canonical element by `TwoTermDeterminant.det_map_delta`; the chart comparison is the composite of
the two.

The two rank-zero hypotheses that appear are propositions — `TwoTermDeterminant.IsRankZero` is an
existential over presentations — so proof irrelevance identifies the one produced by
`TwoTermDeterminant.isRankZero_baseChange` with the one
`AlgebraicGeometry.DeterminantTwoTerm.IsRankZeroOn` supplies on the smaller chart, and no
transport is needed between them.

## References

* [Stacks Project, Lemma 36.39.1 (Tag 0FJX)](https://stacks.math.columbia.edu/tag/0FJX)
* [Stacks Project, Section 15.124 (Tag 0FJI)](https://stacks.math.columbia.edu/tag/0FJI)
* [Stacks Project, Lemma 15.124.4 (Tag 0FJM)](https://stacks.math.columbia.edu/tag/0FJM)
-/

@[expose] public noncomputable section

open CategoryTheory TwoTermDeterminant
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.DeterminantTwoTerm

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : Scheme.{u}}

/-- The determinant of an isomorphism of perfect two-term objects carries the canonical element
of a rank-zero object to the canonical element of the isomorphic one. -/
theorem detLinearEquivOfIso_delta {R : Type u} [CommRing R] {K K' : PerfectTwoTermComplex R}
    (e : K.obj ≅ K'.obj) (hK : IsRankZero K.obj) (hK' : IsRankZero K'.obj) :
    detLinearEquivOfIso e (delta K hK) = delta K' hK' :=
  det_map_delta (⟨ObjectProperty.isoMk (perfectTwoTermComplexProperty R) e⟩ :
    (⟨K⟩ : Core (PerfectTwoTermComplex R)) ⟶ ⟨K'⟩) hK hK'

/-- **The chart comparison of determinants carries the canonical element to the canonical
element.** For affine opens `V ≤ W` of `X` and a rank-zero `L`, the comparison
`AlgebraicGeometry.DeterminantTwoTerm.chartDetModuleIso` carries `1 ⊗ δ` of the chart complex over
`Γ(X, W)` to `δ` of the chart complex over `Γ(X, V)`. -/
theorem chartDetModuleIso_one_tmul_delta {L : PerfectTwoTermAmplitude X} (hL : IsRankZeroOn L)
    {V W : X.affineOpens} (h : V ≤ W) :
    letI : Algebra Γ(X, (W.1 : X.Opens)) Γ(X, (V.1 : X.Opens)) :=
      (affineRestriction X h).hom.toAlgebra
    chartDetModuleIso L h (1 ⊗ₜ[Γ(X, (W.1 : X.Opens))] delta (chartComplex L W) (hL W)) =
      delta (chartComplex L V) (hL V) := by
  let : Algebra Γ(X, (W.1 : X.Opens)) Γ(X, (V.1 : X.Opens)) :=
    (affineRestriction X h).hom.toAlgebra
  have hflat : Module.Flat Γ(X, (W.1 : X.Opens)) Γ(X, (V.1 : X.Opens)) :=
    V.2.moduleFlat_presheaf_map W.2 (AffineOpensGlue.coe_le_coe h)
  have hbc := detBaseChange_one_tmul_delta (affineRestriction X h).hom hflat
    (chartComplex L W) (hL W)
  change detLinearEquivOfIso
      (sourceComplexRestrictionIso V.2 W.2 (AffineOpensGlue.coe_le_coe h) L).symm
      (detBaseChange (affineRestriction X h).hom hflat (chartComplex L W)
        (1 ⊗ₜ[Γ(X, (W.1 : X.Opens))] delta (chartComplex L W) (hL W))) = _
  rw [hbc]
  exact detLinearEquivOfIso_delta _ _ (hL V)

end AlgebraicGeometry.DeterminantTwoTerm

end
