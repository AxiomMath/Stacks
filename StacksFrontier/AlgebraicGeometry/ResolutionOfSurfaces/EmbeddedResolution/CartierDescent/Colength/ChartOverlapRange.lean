module

public import StacksFrontier.AlgebraicGeometry.Blowup.AffineChart

/-!
# The locus of the `b`-chart of a blowup on which `a/b` is invertible lies in the `a`-chart

Let `S` be a scheme, `ℐ` a quasi-coherent sheaf of ideals on `S`, `U` an affine open of `S` and
`a b ∈ ℐ(U)`. The second assertion of [Stacks, Tag 0804] presents the part of the blowup lying
over `U` by the affine charts `Stacks.Blowup.blowUpAffineChart`, the spectra of the affine blowup
algebras `Γ(S, U)[ℐ(U)/a]`. On the chart of `b` the fraction `a/b` is an honest element of the
chart algebra, and this file proves that the basic open it cuts out is carried into the chart of
`a`: on the overlap of the two charts each of `a` and `b` divides the other.

## Main results

* `Stacks.ResolutionOfSurfaces.CartierDescent.chartOverlapFraction`: the fraction `a/b` as an
  element of `Γ(S, U)[ℐ(U)/b]`.
* `Stacks.ResolutionOfSurfaces.CartierDescent.mem_opensRange_blowUpAffineChart_of_notMem`: a
  point of the chart of `b` at which `a/b` is invertible maps into the image of the chart of `a`.
* `Stacks.ResolutionOfSurfaces.CartierDescent.mem_opensRange_blowUpAffineChart_of_mem_basicOpen`:
  the same statement with the hypothesis read as membership of the basic open of `a/b`.

## Implementation notes

The argument is the `Proj` computation, not the stalk criterion of [Stacks, Tag 0BFL]. A chart
`Stacks.Blowup.specAffineBlowupι I b hb` of `Proj` of the Rees algebra of `I` is, by definition,
the standard open immersion `Proj.awayι` at the degree-one element `b⁽¹⁾` precomposed with
`Spec` of the identification `Stacks.Blowup.reesAwayEquivAffineBlowup` of the chart ring with
`R[I/b]`. Mathlib's `AlgebraicGeometry.Proj.awayι_preimage_basicOpen` computes the preimage of
`D₊(a⁽¹⁾)` in `D₊(b⁽¹⁾)` as the basic open of `HomogeneousLocalization.Away.isLocalizationElem`,
which in degree one is the fraction `a⁽¹⁾/b⁽¹⁾`; transporting it along
`Stacks.Blowup.reesAwayEquivAffineBlowup` turns it into the basic open of `a/b` in `Spec R[I/b]`,
which is `chartOverlapFraction`. Since `D₊(a⁽¹⁾)` is the range of the chart of `a`
(`Stacks.Blowup.opensRange_specAffineBlowupι`), that is the assertion.

The statement about the blowup of a scheme follows with no further geometry: the chart of the
blowup is the chart of `Proj` composed with `Stacks.Blowup.blowUpChart`, so a point of the range
of one chart of `Proj` is sent into the range of the composite. Nothing about injectivity of
`Stacks.Blowup.blowUpChart` is needed, and no ideal sheaf or stalk is unfolded, which keeps the
elaboration cost of the scheme-level statement to the two `Scheme.Hom.comp_apply` rewrites, as
in the `## Implementation notes` of `CartierDescent.SurfaceCharts`.

The fraction `a/b` is spelled `Localization.mk a ⟨b, Submonoid.mem_powers b⟩`, one of the
generators of `affineBlowup (ℐ.ideal U) b`, rather than through
`Stacks.Blowup.affineBlowupFraction`, whose ambient subalgebra is the `IsLocalization.mk'`
realization `affineBlowupAlgebra`: the two subalgebras are equal but not identical, and the
colength bookkeeping of [Stacks, Tag 0AGT] that consumes this statement works with
`affineBlowup`.

## References

* [Stacks Project, Tag 0AGT](https://stacks.math.columbia.edu/tag/0AGT)
* [Stacks Project, Tag 0804](https://stacks.math.columbia.edu/tag/0804)
* [Stacks Project, Tag 0BFL](https://stacks.math.columbia.edu/tag/0BFL)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry HomogeneousLocalization

namespace Stacks.ResolutionOfSurfaces.CartierDescent

section Ring

variable {R : Type u} [CommRing R] {I : Ideal R} {a b : R}

/-- **The fraction `a/b` on the chart of `b`.** For `a` in the ideal `I` and any `b : R`, the
element `a/b` of `Localization.Away b` is one of the generators of the affine blowup algebra
`R[I/b]`, hence an element of it. -/
public def chartOverlapFraction (ha : a ∈ I) (b : R) : affineBlowup I b :=
  ⟨Localization.mk a ⟨b, Submonoid.mem_powers b⟩, Algebra.subset_adjoin ⟨a, ha, rfl⟩⟩

/-- The fraction `Stacks.ResolutionOfSurfaces.CartierDescent.chartOverlapFraction`, read in the
localization `Localization.Away b`. -/
public theorem coe_chartOverlapFraction (ha : a ∈ I) (b : R) :
    (chartOverlapFraction ha b : Localization.Away b)
      = Localization.mk a ⟨b, Submonoid.mem_powers b⟩ :=
  rfl

/-- The degree-one element `a⁽¹⁾` of the Rees algebra, as the degree-one part of the grading. -/
private theorem reesDegOne_pow_one_eq (ha : a ∈ I) (ha' : a ∈ I ^ 1) :
    (Stacks.Blowup.reesDegOne I ha ^ 1 : reesAlgebra I)
      = (Stacks.Blowup.reesMonomial I 1 ⟨a, ha'⟩ : reesAlgebra I) := by
  rw [pow_one]
  exact Subtype.ext rfl

/-- The localization element of `AlgebraicGeometry.Proj.awayι_preimage_basicOpen` at two
degree-one elements of the Rees algebra is the fraction `a⁽¹⁾/b⁽¹⁾`, written as the chart
fraction `Stacks.Blowup.reesAwayMk`. -/
private theorem isLocalizationElem_eq_reesAwayMk (ha : a ∈ I) (hb : b ∈ I) (ha' : a ∈ I ^ 1) :
    Away.isLocalizationElem (Stacks.Blowup.reesDegOne_mem_reesGrading I hb)
        (Stacks.Blowup.reesDegOne_mem_reesGrading I ha)
      = Stacks.Blowup.reesAwayMk I b hb 1 ⟨a, ha'⟩ := by
  apply HomogeneousLocalization.val_injective
  simp only [Away.isLocalizationElem, Stacks.Blowup.reesAwayMk, Away.val_mk]
  exact congrArg (fun z => (Localization.mk z ⟨Stacks.Blowup.reesDegOne I hb ^ 1, 1, rfl⟩ :
    Localization (Submonoid.powers (Stacks.Blowup.reesDegOne I hb))))
    (reesDegOne_pow_one_eq ha ha')

/-- The chart identification `Stacks.Blowup.reesAwayEquivAffineBlowup` carries the fraction
`a⁽¹⁾/b⁽¹⁾` to the fraction `a/b`. -/
private theorem reesAwayEquivAffineBlowup_isLocalizationElem (ha : a ∈ I) (hb : b ∈ I) :
    Stacks.Blowup.reesAwayEquivAffineBlowup I b hb
        (Away.isLocalizationElem (Stacks.Blowup.reesDegOne_mem_reesGrading I hb)
          (Stacks.Blowup.reesDegOne_mem_reesGrading I ha))
      = chartOverlapFraction ha b := by
  have ha' : a ∈ I ^ 1 := by rwa [pow_one]
  apply Subtype.ext
  rw [isLocalizationElem_eq_reesAwayMk ha hb ha',
    Stacks.Blowup.coe_reesAwayEquivAffineBlowup_reesAwayMk, coe_chartOverlapFraction]
  exact congrArg (Localization.mk a) (Subtype.ext (pow_one b))

/-- **The preimage of the standard open of `a⁽¹⁾` in the chart of `b` is the basic open of the
fraction `a/b`.** -/
private theorem preimage_basicOpen_reesDegOne (ha : a ∈ I) (hb : b ∈ I) :
    Stacks.Blowup.specAffineBlowupι I b hb ⁻¹ᵁ
        Proj.basicOpen (Stacks.Blowup.reesGrading I) (Stacks.Blowup.reesDegOne I ha)
      = PrimeSpectrum.basicOpen (chartOverlapFraction ha b) := by
  rw [Stacks.Blowup.specAffineBlowupι, Scheme.Hom.comp_preimage,
    Proj.awayι_preimage_basicOpen (Stacks.Blowup.reesGrading I)
      (Stacks.Blowup.reesDegOne_mem_reesGrading I hb) Nat.one_pos
      (Stacks.Blowup.reesDegOne_mem_reesGrading I ha) Nat.one_pos,
    SpecMap_preimage_basicOpen]
  exact congrArg PrimeSpectrum.basicOpen (reesAwayEquivAffineBlowup_isLocalizationElem ha hb)

/-- **A point of the chart `Spec R[I/b]` of `Proj` of the Rees algebra at which `a/b` is
invertible lies in the image of the chart `Spec R[I/a]`.** -/
private theorem mem_range_specAffineBlowupι (ha : a ∈ I) (hb : b ∈ I)
    (v : PrimeSpectrum (CommRingCat.of (affineBlowup I b)))
    (hv : chartOverlapFraction ha b ∉ v.asIdeal) :
    (Stacks.Blowup.specAffineBlowupι I b hb).base v ∈
      Set.range (Stacks.Blowup.specAffineBlowupι I a ha).base := by
  have h1 : v ∈ Stacks.Blowup.specAffineBlowupι I b hb ⁻¹ᵁ
      Proj.basicOpen (Stacks.Blowup.reesGrading I) (Stacks.Blowup.reesDegOne I ha) := by
    rw [preimage_basicOpen_reesDegOne ha hb]
    exact (PrimeSpectrum.mem_basicOpen _ _).mpr hv
  change _ ∈ (Stacks.Blowup.specAffineBlowupι I a ha).opensRange
  rw [Stacks.Blowup.opensRange_specAffineBlowupι]
  exact h1

end Ring

section Scheme

variable {S : Scheme.{u}} {ℐ : S.IdealSheafData} {U : S.affineOpens} {a b : Γ(S, U.1)}

/-- **The locus of the chart of `b` on which `a/b` is invertible lies in the chart of `a`.** Let
`S` be a scheme, `ℐ` a quasi-coherent sheaf of ideals, `U` an affine open of `S` and
`a b ∈ ℐ(U)`. If `v` is a point of the affine chart `Spec Γ(S, U)[ℐ(U)/b]` of the blowup at
which the fraction `a/b` does not lie in the corresponding prime, then the image of `v` in the
blowup lies in the image of the chart `Spec Γ(S, U)[ℐ(U)/a]`.

Geometrically: on the overlap of the two charts of [Stacks, Tag 0804] each of `a` and `b`
divides the other, so `a/b` invertible forces membership in the chart of `a`. -/
public theorem mem_opensRange_blowUpAffineChart_of_notMem (ha : a ∈ ℐ.ideal U)
    (hb : b ∈ ℐ.ideal U) (v : PrimeSpectrum (CommRingCat.of (affineBlowup (ℐ.ideal U) b)))
    (hv : chartOverlapFraction ha b ∉ v.asIdeal) :
    (Stacks.Blowup.blowUpAffineChart ℐ U hb).base v ∈
      (Stacks.Blowup.blowUpAffineChart ℐ U ha).opensRange := by
  obtain ⟨w, hw⟩ := mem_range_specAffineBlowupι ha hb v hv
  refine ⟨w, ?_⟩
  rw [Stacks.Blowup.blowUpAffineChart, Stacks.Blowup.blowUpAffineChart, Scheme.Hom.comp_apply]
  exact congrArg (Stacks.Blowup.blowUpChart ℐ U).base hw

/-- **Basic-open form of
`Stacks.ResolutionOfSurfaces.CartierDescent.mem_opensRange_blowUpAffineChart_of_notMem`.** The
locus of the chart of `b` on which `a/b` is invertible is the basic open of `a/b`, and every one
of its points is sent into the image of the chart of `a`. -/
public theorem mem_opensRange_blowUpAffineChart_of_mem_basicOpen (ha : a ∈ ℐ.ideal U)
    (hb : b ∈ ℐ.ideal U) (v : PrimeSpectrum (CommRingCat.of (affineBlowup (ℐ.ideal U) b)))
    (hv : v ∈ PrimeSpectrum.basicOpen (chartOverlapFraction ha b)) :
    (Stacks.Blowup.blowUpAffineChart ℐ U hb).base v ∈
      (Stacks.Blowup.blowUpAffineChart ℐ U ha).opensRange :=
  mem_opensRange_blowUpAffineChart_of_notMem ha hb v ((PrimeSpectrum.mem_basicOpen _ _).mp hv)

end Scheme

end Stacks.ResolutionOfSurfaces.CartierDescent

end
