module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.CompactificationShriek
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineSmooth
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineIntegral
public import StacksFrontier.AlgebraicGeometry.Curves.PrescribedLowCohomologyFieldExtension
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.DenseOpenGeometricallyIrreducible
public import StacksFrontier.RingTheory.GeometricallyIrreducible.Defs
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ArithmeticFrobeniusInverse

/-!
# The projective line as a compactification of the affine line

For a field `k`, the chart `𝔸¹_k = Spec k[x] ⟶ ℙ¹_k` is an open immersion over `Spec k` into a
proper `k`-scheme, so it is a compactification of `𝔸¹_k ⟶ Spec k`
(`AlgebraicGeometry.affineLineProjectiveCompactification`). The projective line is geometrically
irreducible over `k`, because the affine line is (`k[x] ⊗ K = K[x]`) and is dense in it. Hence for
every extension `K` of `k` the base change `ℙ¹_K` is a smooth curve over `K`
(`AlgebraicGeometry.isCurve_affineLineProjectiveCompactification_fieldBaseChange`). These are the
hypotheses on the compactification of Poincaré duality on an open curve, applied to the fibres of
the Fourier family on `𝔸¹_{k'}` in the purity half of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main definitions

* `AlgebraicGeometry.affineLineProjectiveCompactification`.

## Main results

* `AlgebraicGeometry.geometricallyIrreducible_projectiveLine`.
* `AlgebraicGeometry.isCurve_affineLineProjectiveCompactification_fieldBaseChange`.
* `AlgebraicGeometry.smooth_affineLineProjectiveCompactification_fieldBaseChange`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Frobenius

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k]

/-- **`ℙ¹_k` as a compactification of `𝔸¹_k ⟶ Spec k`**, through the chart with coordinate
`x`. -/
public def affineLineProjectiveCompactification :
    CompactificationOf (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))))) :=
  CompactificationOf.ofFactor (X₀ := Over.mk (𝟙 (Spec (.of (Polynomial k)))))
    (projectiveLineXChart k) (projectiveLine k ↘ Spec (.of k))
    (Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))))
    (projectiveLineChart_comp_structureMorphism_algebraMap k (projectiveLineXIndex k))

/-- **The projective line is geometrically irreducible**: the affine line `Spec k[x]` is, and it
is a dense open of `ℙ¹_k`. -/
public theorem geometricallyIrreducible_projectiveLine :
    GeometricallyIrreducible (projectiveLine k ↘ Spec (.of k)) := by
  have h0 : projectiveLineXChart k ≫ (projectiveLine k ↘ Spec (.of k)) =
      Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) :=
    projectiveLineChart_comp_structureMorphism_algebraMap k (projectiveLineXIndex k)
  have h : GeometricallyIrreducible
      (projectiveLineXChart k ≫ (projectiveLine k ↘ Spec (.of k))) := by
    rw [h0]
    exact Algebra.isGeometricallyIrreducible_polynomial k
  exact geometricallyIrreducible_of_dense_isOpenImmersion (projectiveLineXChart k) _
    (denseRange_projectiveLineXChart k) h

variable (K : Type u) [Field K] [Algebra k K]

/-- **The base change of `ℙ¹_k` to an extension `K` is a curve over `K`.** -/
public instance isCurve_affineLineProjectiveCompactification_fieldBaseChange :
    IsCurve K (pullback.snd (Over.mk (affineLineProjectiveCompactification k).toBase).hom
      (specAlgebraMap k K)) :=
  haveI := geometricallyIrreducible_projectiveLine k
  isCurve_pullback_snd k K (projectiveLine k ↘ Spec (.of k))

/-- **The base change of `ℙ¹_k` to an extension `K` is smooth over `K`.** -/
public instance smooth_affineLineProjectiveCompactification_fieldBaseChange :
    Smooth (pullback.snd (Over.mk (affineLineProjectiveCompactification k).toBase).hom
      (specAlgebraMap k K)) :=
  inferInstanceAs (Smooth (pullback.snd (projectiveLine k ↘ Spec (.of k)) (specAlgebraMap k K)))

end AlgebraicGeometry

end
