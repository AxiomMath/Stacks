module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedRingFunctoriality
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedIntegerValues

/-!
# The chart-level `θ` of Stacks Tag 01NK is functorial in the graded ring

Let `T` be a scheme, `L` an invertible `𝒪_T`-module, `φ : 𝒜 →+*ᵍ ℬ` a degree-preserving
homomorphism of graded rings and `ψ : B → Γ_*(T, L)` a graded map in the degreewise spelling
`Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections`.  Then `ψ` pulls back along `φ` to
`χ = ψ ∘ φ : A → Γ_*(T, L)`, which is
`Stacks.AlgebraicGeometry.ProjChartGradedRingFunctoriality.comap`, for the *same* scheme and the
*same* invertible module.

`Stacks.AlgebraicGeometry.ProjChartGradedRingFunctoriality` proves that the **morphism**
`r_{L, ψ}` of [Stacks, Tag 01NK] is compatible with that pullback, and its sibling
`ProjChartGradedPullback.lean` proves the compatibility in the other variable.  **Neither says
anything about `θ`**, the map on twists that is the tag's other half.  This file supplies the
chart-level half of that missing rung: the comparison `θ_f` of `χ` on the chart of a homogeneous
`f ∈ 𝒜 d` is the comparison `θ_{φ f}` of `ψ` on the chart of `φ f`, at the fraction `x / f ^ j`
and its image `φ x / (φ f) ^ j`.

## Main results

* `…chartSectionOf_comap` and `…intChartSectionOf_comap`: **the section `ψ(x) / ψ(f ^ j)` is
  functorial in the graded ring**, in natural and in arbitrary integer degree.
* `…chartSection_comap` and `…intChartSection_comap`: the same for the map on the degree-`n` part
  of `A_f`, stated at a representative of the fraction and its image.

## Implementation notes

**The whole content is one reindexing, and the degreewise congruences already absorb it.**  Both
sides of each statement are `ψ(φ x) / ψ(f ^ j)`-shaped quotients of the *same* two values of `ψ`;
the only discrepancy is that the left-hand side presents the denominator as `ψ(φ (f ^ j))`, having
read `f ^ j` in `A` before applying `φ`, and the right-hand side as `ψ((φ f) ^ j)`, having applied
`φ` to `f` first.  Those two elements of `B` are equal by `map_pow`, and
`Stacks.AlgebraicGeometry.ProjChartGradedDivision.divTop_toFun_congr` — with
`…intDivTop_intValue_congr` in [Stacks, Tag 01CU]'s family — is exactly the congruence that takes
an equality of denominators and of numerators and returns an equality of quotients, the
nonvanishing hypotheses being propositions.  So each of the two `…Of` statements is a single term,
and this is the same reconciliation that
`…ProjChartGradedRingFunctoriality.lift_comp_awayMap` performs for the *degree-zero* dehomogenised
ring map by `GradedSections.ratioOf_congr`.

**Nothing has to be transported across `comap`.**
`…ProjChartGradedRingFunctoriality.comap_toFun` holds by `rfl`, so the values of `χ` *are* the
values of `ψ` on the images and the two hypotheses `hV`, `hV'` bounding the open by a nonvanishing
locus have the same type up to reducible defeq.  Both are taken as arguments all the same, for the
reason the sibling file records: `GradedSections` reads the open through the proof that the
denominator does not vanish on it, so the spelling that proof is given in determines which open
the term carries.

**The statements are at a representative, not at an induced map on graded pieces.**  A map
`(A_f)_n ⟶ (B_{φ f})_n` induced by `φ` is not in this repository, and
`…chartSection`/`…intChartSection` are defined by choice over the representatives of a fraction
anyway (`…chartSection_mk`, `…intChartSection_mk`), so the two elements being compared are passed
in together with representatives `x / f ^ j` and `φ x / (φ f) ^ j` of each.  A consumer that has
such an induced map available obtains the map-level statement by applying these at any
representative.

## References

* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry HomogeneousLocalization HomogeneousIdeal Graded
open AlgebraicGeometry.ProjectiveSpectrum.Proj (integerGrading)
open Stacks.TensorPowers (natTensorPow)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.GradedLocalization (gradedPiece)
open Stacks.MorphismToProj (HomogeneousRatios)
open Stacks.AlgebraicGeometry.ProjChartFullGraded (GradedSections)
open Stacks.AlgebraicGeometry.ProjChartGradedDivision
open Stacks.AlgebraicGeometry.ProjChartGradedRingFunctoriality (comap)

universe u

namespace Stacks.AlgebraicGeometry.ProjChartGradedThetaRingFunctoriality

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ] (φ : 𝒜 →+*ᵍ ℬ)
  {T : Scheme.{u}} {L : T.Modules} [Stacks.Ample.IsInvertibleModule T L]
  (ψ : GradedSections ℬ L) {d : ℕ} {f : A} (hf : f ∈ 𝒜 d) {V : T.Opens}
  (hV : V ≤ nonvanishingOpen T (natTensorPow L d) ((comap φ ψ).toFun d ⟨f, hf⟩))
  (hV' : V ≤ nonvanishingOpen T (natTensorPow L d) (ψ.toFun d ⟨φ f, map_mem φ hf⟩))

/-! ### Natural degree -/

/-- **The section `χ(x) / χ(f ^ j)` is the section `ψ(φ x) / ψ((φ f) ^ j)`**, for `χ = ψ ∘ φ`.

Both sides are quotients of the same two values of `ψ`; the denominators are `ψ(φ (f ^ j))` on the
left and `ψ((φ f) ^ j)` on the right, equal by `map_pow`, which
`…ProjChartGradedDivision.divTop_toFun_congr` absorbs. -/
public theorem chartSectionOf_comap (n j : ℕ) {x : A} (hx : x ∈ 𝒜 (j * d + n)) :
    chartSectionOf (comap φ ψ) hf hV n j hx
      = chartSectionOf ψ (map_mem φ hf) hV' n j (map_mem φ hx) :=
  divTop_toFun_congr ψ (map_mem φ (HomogeneousRatios.pow_mem hf j))
    (HomogeneousRatios.pow_mem (map_mem φ hf) j) n (map_mem φ hx) (map_mem φ hx)
    ((comap φ ψ).le_nonvanishingOpen_pow hf hV j)
    (ψ.le_nonvanishingOpen_pow (map_mem φ hf) hV' j) rfl (map_pow φ f j) rfl

/-- **The chart-level comparison of `χ = ψ ∘ φ` in degree `n` is that of `ψ`**, read at a fraction
`x / f ^ j` of `A_f`-degree `n` and its image `φ x / (φ f) ^ j` in `B_{φ f}`.

Both maps are defined by choice and computed by *any* representative
(`…ProjChartGradedDivision.chartSection_mk`), so the two representatives supplied reduce the claim
to `chartSectionOf_comap`. -/
public theorem chartSection_comap (n : ℕ)
    (y : gradedPiece 𝒜 (integerGrading (S := A) 𝒜) f (n : ℤ))
    (z : gradedPiece ℬ (integerGrading (S := B) ℬ) (φ f) (n : ℤ))
    (j : ℕ) (x : A) (hx : x ∈ 𝒜 (j * d + n))
    (hy : (y : LocalizedModule.Away f A)
      = LocalizedModule.mk x (⟨f ^ j, ⟨j, rfl⟩⟩ : Submonoid.powers f))
    (hz : (z : LocalizedModule.Away (φ f) B)
      = LocalizedModule.mk (φ x) (⟨(φ f) ^ j, ⟨j, rfl⟩⟩ : Submonoid.powers (φ f))) :
    chartSection (comap φ ψ) hf hV n y = chartSection ψ (map_mem φ hf) hV' n z :=
  ((chartSection_mk (comap φ ψ) hf hV n y j x hx hy).trans
      (chartSectionOf_comap φ ψ hf hV hV' n j hx)).trans
    (chartSection_mk ψ (map_mem φ hf) hV' n z j (φ x) (map_mem φ hx) hz).symm

/-! ### Arbitrary integer degree -/

/-- **`chartSectionOf_comap` in [Stacks, Tag 01CU]'s family**, where the degree of the quotient
may be any integer.  The congruence is `…ProjChartGradedDivision.intDivTop_intValue_congr`. -/
public theorem intChartSectionOf_comap (n : ℤ) (j e : ℕ)
    (he : ((j * d : ℕ) : ℤ) + n = (e : ℕ)) {x : A} (hx : x ∈ 𝒜 e) :
    intChartSectionOf (comap φ ψ) hf hV n j e he hx
      = intChartSectionOf ψ (map_mem φ hf) hV' n j e he (map_mem φ hx) :=
  intDivTop_intValue_congr ψ n (map_mem φ (HomogeneousRatios.pow_mem hf j))
    (HomogeneousRatios.pow_mem (map_mem φ hf) j) (map_mem φ hx) (map_mem φ hx) he he
    (le_nonvanishingOpen_intValue_pow (comap φ ψ) hf hV j)
    (le_nonvanishingOpen_intValue_pow ψ (map_mem φ hf) hV' j) rfl (map_pow φ f j) rfl

/-- **`chartSection_comap` in arbitrary integer degree.**  This is the degreewise statement the
sheaf-level `θ` of [Stacks, Tag 01NK] is built from:
`…ProjChartGradedThetaBuild.pushTheta` glues the chart data of
`…ProjChartGradedDivision.intChartSectionHom`, and this is that datum's functoriality in the
graded ring. -/
public theorem intChartSection_comap (hd : 0 < d) (n : ℤ)
    (y : gradedPiece 𝒜 (integerGrading (S := A) 𝒜) f n)
    (z : gradedPiece ℬ (integerGrading (S := B) ℬ) (φ f) n)
    (j e : ℕ) (he : ((j * d : ℕ) : ℤ) + n = (e : ℕ)) (x : A) (hx : x ∈ 𝒜 e)
    (hy : (y : LocalizedModule.Away f A)
      = LocalizedModule.mk x (⟨f ^ j, ⟨j, rfl⟩⟩ : Submonoid.powers f))
    (hz : (z : LocalizedModule.Away (φ f) B)
      = LocalizedModule.mk (φ x) (⟨(φ f) ^ j, ⟨j, rfl⟩⟩ : Submonoid.powers (φ f))) :
    intChartSection (comap φ ψ) hf hV hd n y
      = intChartSection ψ (map_mem φ hf) hV' hd n z :=
  ((intChartSection_mk (comap φ ψ) hf hV hd n y j e he x hx hy).trans
      (intChartSectionOf_comap φ ψ hf hV hV' n j e he hx)).trans
    (intChartSection_mk ψ (map_mem φ hf) hV' hd n z j e he (φ x) (map_mem φ hx) hz).symm

end Stacks.AlgebraicGeometry.ProjChartGradedThetaRingFunctoriality

end
