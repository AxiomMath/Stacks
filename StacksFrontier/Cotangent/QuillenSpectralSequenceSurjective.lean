module

public import StacksFrontier.Cotangent.QuillenFiltration
public import StacksFrontier.Cotangent.SurjectionSiteFootnoteVanishing

/-!
# Quillen's spectral sequence for a surjective ring map

Let `A → B` be a surjective ring map, `C_{B/A}` the polynomial site (on its small model
`CommAlgCat.smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B)`), and
`Ω = Ω_{𝒪/A} ⊗_𝒪 B̲`.  [Stacks, Tag 08RF] asserts that there is a spectral sequence

`E₁^{p,q} = H_{-p-q}(C_{B/A}, Sym^p_{B̲}(Ω)) ⇒ Tor^A_{-p-q}(B, B)`

with `d_r` of bidegree `(r, -r + 1)`, and that `H_i(C_{B/A}, Sym^k_{B̲}(Ω)) = 0` for `i < k`.
This file states and proves the whole of it.

The spectral sequence is the one of the filtered complex `CommAlgCat.quillenFiltered` of
`StacksFrontier.Cotangent.QuillenFiltration`: the extended Moore cochain complex `C = Ō(U_•)` of
`Ō = 𝒪 ⊗_A B̲` on the standard point resolution, which computes `Lπ_!(Ō) = B ⊗^𝐋_A B`
(`CommAlgCat.leftDerivedColimQuotientTorIso`), filtered by `F^p = τ^{≤ -p}(𝒦^p(U_•))` where `𝒦`
is the augmentation ideal of `Ō`.  `CommAlgCat.nonempty_quillenFiltrationData` turns that filtered
complex into a `CommAlgCat.QuillenFiltrationData` on two inputs, both of which are now theorems:

* `𝒦ⁿ/𝒦ⁿ⁺¹ ≅ Sym^n_{B̲}(Ω)`, which is
  `CommAlgCat.smallPolynomialAugmentationGradedSymmetricPowerIso` and asks nothing of `A → B`;
* the footnote vanishing `H_i(C_{B/A}, 𝒦ⁿ) = 0` for `i < n`, which is, in `CommAlgCat`,
  `isZero_leftDerivedColim_smallPolynomialAugmentationIdealPow_of_surjective_unconditional`
  for a surjective `A → B` (it contains the convergence argument of the source, through Tags 08RE,
  068F, 08QJ and 08Q2).

`CommAlgCat.QuillenFiltrationData.toQuillenSpectralSequenceData` then produces the spectral
sequence (Tag 012M), its `E₁`-page, its vanishing for `p < 0`, and its abutment (Tag 012W).

## Main definitions

* `CommAlgCat.quillenFiltrationDataOfSurjective`: the filtered complex presenting Quillen's
  spectral sequence, for a surjective `A → B`.
* `CommAlgCat.quillenSpectralSequenceDataOfSurjective`: Quillen's spectral sequence, with its
  first-page identification and abutment.

## Main results

* `CommAlgCat.quillenSpectralSequence_of_surjective`: **[Stacks, Tag 08RF]**, whole: the
  spectral sequence exists, with the stated first page, `d_r` of bidegree `(r, -r + 1)` and
  abutment `Tor^A_{-p-q}(B, B)`, and `H_i(C_{B/A}, Sym^k_{B̲}(Ω)) = 0` for `i < k`.

## Implementation notes

`CommAlgCat.QuillenSpectralSequenceData A B` is the datum: `sequence` is a
`CohomologicalSpectralSequence (ModuleCat B) 1`, whose `r`-th page differential goes from
`(p, q)` to `(p + r, q - r + 1)` by definition of that type; `pageOneIso` is the identification
`E₁^{p,q} ≅ H_{-p-q}(C_{B/A}, Sym^p_{B̲}(Ω))`; `pageOne_isZero` is `E₁^{p,q} = 0` for `p < 0`
(where `Sym^p` does not exist); and `abutment` is `CategoryTheory.SpectralSequence.AbutsTo`: an
infinity page exists at every bidegree and every `Tor^A_{-n}(B, B)` carries a finite decreasing
filtration `F` whose graded pieces `F^p/F^{p+1}` are the terms `E_∞^{p, n - p}`.

`H_i(C_{B/A}, -)` is `L_i colim` over the opposite of the small model of the site, Tag 08PF's
homology of a category, as everywhere in the library's 08RD/08RF material
(`CommAlgCat.symmetricPowerSiteHomology`, extended by zero to `i < 0`).

## References

* [Stacks Project, Tag 08RF](https://stacks.math.columbia.edu/tag/08RF)
* [Stacks Project, Tag 012M](https://stacks.math.columbia.edu/tag/012M)
* [Stacks Project, Tag 012W](https://stacks.math.columbia.edu/tag/012W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CommAlgCat

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A)

/-- **The filtered complex presenting Quillen's spectral sequence**, for a surjective `A → B`:
`CommAlgCat.quillenFiltered` on the standard point resolution, with its degreewise finiteness, its
being the whole complex in nonpositive filtration degrees, the identification of its cohomology
with `Tor^A_{-n}(B, B)`, and the identification of the first page of its spectral sequence with
`H_{-p-q}(C_{B/A}, Sym^p_{B̲}(Ω))`.  The last uses the graded pieces
`𝒦ⁿ/𝒦ⁿ⁺¹ ≅ Sym^n_{B̲}(Ω)` and the footnote vanishing `H_i(C_{B/A}, 𝒦ⁿ) = 0` for `i < n`, both
proved. -/
def quillenFiltrationDataOfSurjective
    (h : Function.Surjective (algebraMap A (B : Type u))) : QuillenFiltrationData A B where
  complex :=
    quillenFiltered A B (standardResolutionVarCardinal A B)
      (standardResolutionSmallCosimplicialObject A B)
  isDegreewiseFinite :=
    isDegreewiseFinite_quillenFiltration A B (standardResolutionVarCardinal A B)
      (standardResolutionSmallCosimplicialObject A B)
  filtrationSubobject_eq_top :=
    filtrationSubobject_quillenFiltered_eq_top A B (standardResolutionVarCardinal A B)
      (standardResolutionSmallCosimplicialObject A B)
  cohomologyIso := quillenCohomologyIso A B (leftDerivedColimQuotientTorIso A B)
  pageOneIso := quillenPageOneIso A B
    (smallPolynomialAugmentationGradedSymmetricPowerIso A B (standardResolutionVarCardinal A B))
    (isZero_leftDerivedColim_smallPolynomialAugmentationIdealPow_of_surjective_unconditional
      A B h)

/-- **Quillen's spectral sequence** for a surjective `A → B`: the spectral sequence of the
filtered complex `CommAlgCat.quillenFiltrationDataOfSurjective`, read from its first page, with
`E₁^{p,q} ≅ H_{-p-q}(C_{B/A}, Sym^p_{B̲}(Ω))` and abutting to `Tor^A_{-p-q}(B, B)`. -/
def quillenSpectralSequenceDataOfSurjective
    (h : Function.Surjective (algebraMap A (B : Type u))) : QuillenSpectralSequenceData A B :=
  (quillenFiltrationDataOfSurjective A B h).toQuillenSpectralSequenceData A B

/-- **Stacks 08RF (Quillen spectral sequence).** Let `A → B` be a surjective ring map and
`Ω = Ω_{𝒪/A} ⊗_𝒪 B̲` on the polynomial site `C_{B/A}`.  Then

* there is a cohomological spectral sequence of `B`-modules `(E_r)_{r ≥ 1}`, with `d_r` of
  bidegree `(r, -r + 1)`, first page `E₁^{p,q} ≅ H_{-p-q}(C_{B/A}, Sym^p_{B̲}(Ω))` (and `0` for
  `p < 0`), converging to `Tor^A_{-p-q}(B, B)`: it has an infinity page at every bidegree, and
  each `Tor^A_{-n}(B, B)` carries a finite decreasing filtration with
  `E_∞^{p, n - p} ≅ F^p/F^{p+1}`; and
* `H_i(C_{B/A}, Sym^k_{B̲}(Ω)) = 0` for `i < k`.

The first conjunct is `CommAlgCat.QuillenSpectralSequenceData A B` inhabited, the datum being
`CommAlgCat.quillenSpectralSequenceDataOfSurjective`; the second is stated on the same entries
`CommAlgCat.symmetricPowerSiteHomology` the first page is identified with. -/
@[stacks 08RF "whole theorem, for a surjective A → B: the spectral sequence exists as a \
  CohomologicalSpectralSequence of B-modules starting at page 1, so d_r has bidegree (r, -r + 1) \
  by definition of that type; its first page is identified with \
  E₁^{p,q} = H_{-p-q}(C_{B/A}, Sym^p_{B̲}(Ω)) (pageOneIso, zero for p < 0 by pageOne_isZero); it \
  converges to Tor^A_{-p-q}(B, B) in the sense of SpectralSequence.AbutsTo: an infinity page at \
  every bidegree and, on each Tor^A_{-n}(B, B), a finite decreasing filtration whose graded \
  pieces are the infinity-page terms. The second conjunct is the final vanishing \
  H_i(C_{B/A}, Sym^k_{B̲}(Ω)) = 0 for i < k. H_i(C_{B/A}, -) is L_i colim over the opposite of \
  the small model of the polynomial site (Tag 08PF), extended by zero to i < 0; Tor^A_i(B, B) is \
  the i-th left derived functor of B ⊗_A - at B. The sequence is that of the filtered complex \
  C = Ō(U_•) on the standard point resolution, filtered by τ^{≤ -p}(𝒦^p(U_•)), whose \
  cohomology is Lπ_!(Ō) = B ⊗^L_A B; every input (𝒦ⁿ/𝒦ⁿ⁺¹ = Sym^n(Ω), the footnote vanishing \
  H_i(C_{B/A}, 𝒦ⁿ) = 0 for i < n via Tags 08RE, 068F, 08QJ, 08Q2) is proved."]
theorem quillenSpectralSequence_of_surjective
    (h : Function.Surjective (algebraMap A (B : Type u))) :
    Nonempty (QuillenSpectralSequenceData A B) ∧
      ∀ (k : ℕ) (i : ℤ), i < k → IsZero (symmetricPowerSiteHomology A B k i) := by
  refine ⟨⟨quillenSpectralSequenceDataOfSurjective A B h⟩, fun k i hik => ?_⟩
  rcases lt_or_ge i 0 with hi | hi
  · exact isZero_symmetricPowerSiteHomology_of_neg A B k hi
  · lift i to ℕ using hi
    rw [symmetricPowerSiteHomology_natCast]
    exact isZero_leftDerivedColim_symmetricPower_polynomialCotangent_of_surjective A B h k i
      (by exact_mod_cast hik)

end CommAlgCat

end
