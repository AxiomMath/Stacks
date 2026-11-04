module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CartierDescent.ChartFibre
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CartierDescent.ChartInFractionField
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CartierDescent.ChartResidualSupport
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CartierDescent.Colength.ChartTransport
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CartierDescent.Colength.ColengthChain
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CartierDescent.RegularParameters
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CartierDescent.ResidualSupport

/-!
# The colength drop in the affine blowup algebras

The colength drop of [Stacks, Tag 0AGT] is proved in the sibling file
`CartierDescent.Colength.ColengthChain` for the two charts read as subalgebras of the fraction
field of `R`, since that is where they can be compared. The scheme-theoretic charts of the
blowup, however, are the spectra of the affine blowup algebras `R[I/x]` and `R[I/y]` of
[Stacks, Tag 052Q], which live in the two away-localizations `R_x` and `R_y`. This file restates
the colength drop for those algebras, transporting the data along the isomorphisms
`Stacks.ResolutionOfSurfaces.CartierDescent.affineBlowupSpanPairEquivAdjoin` of the sibling file
`CartierDescent.ChartInFractionField`.

## Main results

* `Stacks.ResolutionOfSurfaces.CartierDescent.sum_length_affineBlowup_lt`: for a two-dimensional
  regular local ring `R` with `𝔪 = (x, y)`, an ideal `L` of finite colength and residual ideals
  `Rx`, `Ry` on the two charts satisfying the chart equations, the sum of the local colengths of
  `Rx` over all primes above it, plus the sum of the local colengths of `Ry` over any family of
  primes above it containing the chart element `x / y`, is strictly smaller than the colength of
  `L`.
* `Stacks.ResolutionOfSurfaces.CartierDescent.length_quotient_add_sum_length_affineBlowup_lt`: the
  same drop with every length taken over `R`, the first chart contributing its whole residual
  quotient.

## Implementation notes

The centre ideal is kept behind a variable `I` with a hypothesis `hI : I = Ideal.span {x, y}`,
as in the sibling file `CartierDescent.ResidualSupport`: the scheme-theoretic chart is the one of
`(centre A).ideal ⊤`, which is that span but not syntactically, and rewriting the ideal inside
the *type* `affineBlowup I x` is a dependent rewrite. Everything the ideal's identity is needed
for is therefore packaged in two private declarations that discharge it by `subst`, namely the
isomorphism onto the chart in the fraction field and the Artinian hypothesis on the residual
quotient. Instantiating those at `x, y` and at `y, x` covers both charts, the second span being
the first by `Set.pair_comm`.

The chart element `x / y` of the second chart is passed as a parameter `σ` with its defining
property, rather than written out: its membership in `R[I/y]` is a fact about the generating set
of the affine blowup algebra that the caller already has in whatever form it needs.

## References

* [Stacks Project, Tag 0AGT](https://stacks.math.columbia.edu/tag/0AGT)
* [Stacks Project, Tag 052Q](https://stacks.math.columbia.edu/tag/052Q)
-/

@[expose] public noncomputable section

open Stacks.AffineBlowup

universe u

namespace Stacks.ResolutionOfSurfaces.CartierDescent

section Helpers

variable {R : Type u} [CommRing R] {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]

/-- `Stacks.ResolutionOfSurfaces.CartierDescent.affineBlowupSpanPairEquivAdjoin` with the centre
behind a variable, so that it applies to the chart of an ideal which is a two-element span
without being syntactically one. -/
private def affineBlowupEquivAdjoin (I : Ideal R) {x y : R}
    (hI : I = Ideal.span ({x, y} : Set R)) (haz : algebraMap R K x ≠ 0) :
    affineBlowup I x ≃ₐ[R] Algebra.adjoin R ({algebraMap R K y / algebraMap R K x} : Set K) := by
  subst hI
  exact affineBlowupSpanPairEquivAdjoin (K := K) x haz y

/-- The isomorphism `Stacks.ResolutionOfSurfaces.CartierDescent.affineBlowupEquivAdjoin` does not
move elements: it is the embedding of the away-localization into the fraction field. -/
private theorem coe_affineBlowupEquivAdjoin (I : Ideal R) {x y : R}
    (hI : I = Ideal.span ({x, y} : Set R)) (haz : algebraMap R K x ≠ 0)
    (z : affineBlowup I x) :
    ((affineBlowupEquivAdjoin (K := K) I hI haz z :
        Algebra.adjoin R ({algebraMap R K y / algebraMap R K x} : Set K)) : K) =
      awayToFractionField x haz (z : Localization.Away x) := by
  subst hI
  rfl

end Helpers

/-- `Stacks.ResolutionOfSurfaces.CartierDescent.isArtinianRing_quotient` with the centre behind a
variable. -/
private theorem isArtinianRing_quotient' (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {x y : R} (hreg : RingTheory.Sequence.IsRegular R [x, y])
    (hspan : Ideal.span ({x, y} : Set R) = IsLocalRing.maximalIdeal R)
    (I : Ideal R) (hI : I = Ideal.span ({x, y} : Set R))
    (Lc : Ideal (affineBlowup I x)) (k : ℕ)
    (hxk : algebraMap R (affineBlowup I x) x ^ k ∈ Lc)
    (hL : ¬ Lc ≤ Ideal.span {algebraMap R (affineBlowup I x) x}) :
    IsArtinianRing (affineBlowup I x ⧸ Lc) := by
  subst hI
  exact isArtinianRing_quotient R hreg hspan Lc k hxk hL

/-- **The colength drop transported to two abstract chart rings.** Given ring isomorphisms of
`Bt` and `Ct` onto the two chart subalgebras `B`, `C` of a field `K` containing `R`, commuting
with the structure maps, the colength drop of
`Stacks.ResolutionOfSurfaces.CartierDescent.sum_length_localization_quotient_lt` reads as a
statement about ideals and primes of `Bt` and `Ct`.

Everything the isomorphisms are used for is in the sibling file
`CartierDescent.Colength.ChartTransport`: the chart equation, non-invertibility of the chart
generator, the Artinian residual quotient, the matching of the families of primes, and the local
colengths themselves. -/
private theorem sum_length_lt_of_chartEquiv (R : Type u) [CommRing R] [IsNoetherianRing R]
    {K : Type u} [Field K] [Algebra R K] (hinj : Function.Injective (algebraMap R K))
    {x y : R} {t s : K} (hts : t * s = 1)
    (hxt : algebraMap R K x * t = algebraMap R K y) (hxne : x ≠ 0)
    (hreg : ∀ a : R, a * y ∈ Ideal.span ({x} : Set R) → a ∈ Ideal.span ({x} : Set R))
    {B C : Subalgebra R K} (hB : B = Algebra.adjoin R ({t} : Set K))
    (hC : C = Algebra.adjoin R ({s} : Set K)) (hsC : s ∈ C)
    {Bt Ct : Type u} [CommRing Bt] [CommRing Ct] [Algebra R Bt] [Algebra R Ct]
    (eB : Bt ≃+* ↥B) (hcB : ∀ r : R, eB (algebraMap R Bt r) = algebraMap R ↥B r)
    (eC : Ct ≃+* ↥C) (hcC : ∀ r : R, eC (algebraMap R Ct r) = algebraMap R ↥C r)
    (L : Ideal R) [IsArtinian R (R ⧸ L)] {d : ℕ} (hd : 0 < d)
    (Rx : Ideal Bt) (Ry : Ideal Ct) [IsArtinianRing (Bt ⧸ Rx)] [IsArtinianRing (Ct ⧸ Ry)]
    (hRx : Ideal.span {algebraMap R Bt x ^ d} * Rx = Ideal.map (algebraMap R Bt) L)
    (hRy : Ideal.span {algebraMap R Ct y ^ d} * Ry = Ideal.map (algebraMap R Ct) L)
    (hxnu : ¬ IsUnit (algebraMap R Bt x))
    (Sx : Finset (PrimeSpectrum Bt)) (hSx : ∀ w : PrimeSpectrum Bt, w ∈ Sx ↔ Rx ≤ w.asIdeal)
    (SyAll Sy : Finset (PrimeSpectrum Ct))
    (hSyAll : ∀ v : PrimeSpectrum Ct, v ∈ SyAll ↔ Ry ≤ v.asIdeal) (hSyle : Sy ⊆ SyAll)
    (hSy2 : ∀ v ∈ Sy, eC.symm ⟨s, hsC⟩ ∈ v.asIdeal) :
    ∑ w ∈ Sx, Module.length (Localization.AtPrime w.asIdeal)
        (Localization.AtPrime w.asIdeal ⧸
          Ideal.map (algebraMap Bt (Localization.AtPrime w.asIdeal)) Rx) +
      ∑ v ∈ Sy, Module.length (Localization.AtPrime v.asIdeal)
        (Localization.AtPrime v.asIdeal ⧸
          Ideal.map (algebraMap Ct (Localization.AtPrime v.asIdeal)) Ry) <
      Module.length R (R ⧸ L) := by
  have := isArtinianRing_quotient_map_of_ringEquiv eB Rx
  have := isArtinianRing_quotient_map_of_ringEquiv eC Ry
  have hmem : ∀ p ∈ Sy.map (PrimeSpectrum.comapEquiv eC).toEquiv.toEmbedding,
      (⟨s, hsC⟩ : ↥C) ∈ p.asIdeal := by
    intro p hp
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.1 hp
    exact hSy2 v hv
  have hkey := sum_length_localization_quotient_lt hinj hts hxt hxne hreg hB hC hsC L hd
    (Ideal.map (eB : Bt →+* ↥B) Rx) (Ideal.map (eC : Ct →+* ↥C) Ry)
    (span_pow_mul_map_eq_map_of_commutes eB hcB x d Rx L hRx)
    (span_pow_mul_map_eq_map_of_commutes eC hcC y d Ry L hRy)
    (not_isUnit_algebraMap_of_commutes eB hcB x hxnu)
    (Sx.map (PrimeSpectrum.comapEquiv eB).toEquiv.toEmbedding)
    (mem_map_comapEquiv_iff eB Rx Sx hSx)
    (SyAll.map (PrimeSpectrum.comapEquiv eC).toEquiv.toEmbedding)
    (Sy.map (PrimeSpectrum.comapEquiv eC).toEquiv.toEmbedding)
    (mem_map_comapEquiv_iff eC Ry SyAll hSyAll) (Finset.map_subset_map.2 hSyle) hmem
  rw [Finset.sum_map, Finset.sum_map] at hkey
  refine lt_of_le_of_lt (le_of_eq ?_) hkey
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun w _ => ?_)
    (Finset.sum_congr rfl fun v _ => ?_)
  · exact length_localization_quotient_eq_of_ringEquiv eB Rx w
  · exact length_localization_quotient_eq_of_ringEquiv eC Ry v

/-- **The colength drop transported to two abstract chart rings, over the base ring.** Same
situation as `Stacks.ResolutionOfSurfaces.CartierDescent.sum_length_lt_of_chartEquiv`, with every
length taken over `R`: the `R`-colength of the residual ideal on the first chart, plus the sum of
the `R`-colengths of the residual ideal on the second over the given family of primes, is strictly
smaller than the `R`-colength of `L`.

The transports are the base-ring forms
`Module.quotient_length_eq_of_ringEquiv_commutes` and
`Stacks.ResolutionOfSurfaces.CartierDescent.length_localization_quotient_eq_of_commutes`, which
need the isomorphisms to commute with the structure maps — exactly the hypotheses `hcB`, `hcC`
already carry. -/
private theorem length_quotient_add_sum_length_lt_of_chartEquiv (R : Type u) [CommRing R]
    [IsNoetherianRing R] {K : Type u} [Field K] [Algebra R K]
    (hinj : Function.Injective (algebraMap R K))
    {x y : R} {t s : K} (hts : t * s = 1)
    (hxt : algebraMap R K x * t = algebraMap R K y) (hxne : x ≠ 0)
    (hreg : ∀ a : R, a * y ∈ Ideal.span ({x} : Set R) → a ∈ Ideal.span ({x} : Set R))
    {B C : Subalgebra R K} (hB : B = Algebra.adjoin R ({t} : Set K))
    (hC : C = Algebra.adjoin R ({s} : Set K)) (hsC : s ∈ C)
    {Bt Ct : Type u} [CommRing Bt] [CommRing Ct] [Algebra R Bt] [Algebra R Ct]
    (eB : Bt ≃+* ↥B) (hcB : ∀ r : R, eB (algebraMap R Bt r) = algebraMap R ↥B r)
    (eC : Ct ≃+* ↥C) (hcC : ∀ r : R, eC (algebraMap R Ct r) = algebraMap R ↥C r)
    (L : Ideal R) [IsArtinian R (R ⧸ L)] {d : ℕ} (hd : 0 < d)
    (Rx : Ideal Bt) (Ry : Ideal Ct) [IsArtinianRing (Bt ⧸ Rx)] [IsArtinianRing (Ct ⧸ Ry)]
    (hRx : Ideal.span {algebraMap R Bt x ^ d} * Rx = Ideal.map (algebraMap R Bt) L)
    (hRy : Ideal.span {algebraMap R Ct y ^ d} * Ry = Ideal.map (algebraMap R Ct) L)
    (hxnu : ¬ IsUnit (algebraMap R Bt x))
    (Sx : Finset (PrimeSpectrum Bt)) (hSx : ∀ w : PrimeSpectrum Bt, w ∈ Sx ↔ Rx ≤ w.asIdeal)
    (SyAll Sy : Finset (PrimeSpectrum Ct))
    (hSyAll : ∀ v : PrimeSpectrum Ct, v ∈ SyAll ↔ Ry ≤ v.asIdeal) (hSyle : Sy ⊆ SyAll)
    (hSy2 : ∀ v ∈ Sy, eC.symm ⟨s, hsC⟩ ∈ v.asIdeal) :
    Module.length R (Bt ⧸ Rx) +
      ∑ v ∈ Sy, Module.length R (Localization.AtPrime v.asIdeal ⧸
        Ideal.map (algebraMap Ct (Localization.AtPrime v.asIdeal)) Ry) <
      Module.length R (R ⧸ L) := by
  have := isArtinianRing_quotient_map_of_ringEquiv eB Rx
  have := isArtinianRing_quotient_map_of_ringEquiv eC Ry
  have hmem : ∀ p ∈ Sy.map (PrimeSpectrum.comapEquiv eC).toEquiv.toEmbedding,
      (⟨s, hsC⟩ : ↥C) ∈ p.asIdeal := by
    intro p hp
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.1 hp
    exact hSy2 v hv
  have hkey := length_quotient_add_sum_length_localization_lt hinj hts hxt hxne hreg hB hC hsC L hd
    (Ideal.map (eB : Bt →+* ↥B) Rx) (Ideal.map (eC : Ct →+* ↥C) Ry)
    (span_pow_mul_map_eq_map_of_commutes eB hcB x d Rx L hRx)
    (span_pow_mul_map_eq_map_of_commutes eC hcC y d Ry L hRy)
    (not_isUnit_algebraMap_of_commutes eB hcB x hxnu)
    (Sx.map (PrimeSpectrum.comapEquiv eB).toEquiv.toEmbedding)
    (mem_map_comapEquiv_iff eB Rx Sx hSx)
    (SyAll.map (PrimeSpectrum.comapEquiv eC).toEquiv.toEmbedding)
    (Sy.map (PrimeSpectrum.comapEquiv eC).toEquiv.toEmbedding)
    (mem_map_comapEquiv_iff eC Ry SyAll hSyAll) (Finset.map_subset_map.2 hSyle) hmem
  rw [Finset.sum_map] at hkey
  refine lt_of_le_of_lt (le_of_eq ?_) hkey
  exact congrArg₂ (· + ·)
    (Module.quotient_length_eq_of_ringEquiv_commutes eB hcB Rx)
    (Finset.sum_congr rfl fun v _ => length_localization_quotient_eq_of_commutes eC hcC Ry v)

/-- `Stacks.ResolutionOfSurfaces.CartierDescent.sum_length_affineBlowup_lt` with the fraction
field of `R` as an explicit parameter, that being where the comparison of the two charts runs
while the statement does not mention it. -/
private theorem sum_length_affineBlowup_lt_aux (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (hdim : ringKrullDim R = 2) {x y : R}
    (hspan : Ideal.span ({x, y} : Set R) = IsLocalRing.maximalIdeal R)
    (I : Ideal R) (hI : I = Ideal.span ({x, y} : Set R))
    (L : Ideal R) [IsArtinian R (R ⧸ L)] {d : ℕ} (hd : 0 < d)
    (Rx : Ideal (affineBlowup I x)) (Ry : Ideal (affineBlowup I y))
    (hRx : Ideal.span {algebraMap R (affineBlowup I x) x ^ d} * Rx =
      Ideal.map (algebraMap R (affineBlowup I x)) L)
    (hRy : Ideal.span {algebraMap R (affineBlowup I y) y ^ d} * Ry =
      Ideal.map (algebraMap R (affineBlowup I y)) L)
    (kx : ℕ) (hkx : algebraMap R (affineBlowup I x) x ^ kx ∈ Rx)
    (hnx : ¬ Rx ≤ Ideal.span {algebraMap R (affineBlowup I x) x})
    (ky : ℕ) (hky : algebraMap R (affineBlowup I y) y ^ ky ∈ Ry)
    (hny : ¬ Ry ≤ Ideal.span {algebraMap R (affineBlowup I y) y})
    (Sx : Finset (PrimeSpectrum (affineBlowup I x)))
    (hSx : ∀ w : PrimeSpectrum (affineBlowup I x), w ∈ Sx ↔ Rx ≤ w.asIdeal)
    (Sy : Finset (PrimeSpectrum (affineBlowup I y)))
    (hSy1 : ∀ v ∈ Sy, Ry ≤ v.asIdeal)
    (σ : affineBlowup I y)
    (hσ : (σ : Localization.Away y) = Localization.mk x ⟨y, Submonoid.mem_powers y⟩)
    (hSy2 : ∀ v ∈ Sy, σ ∈ v.asIdeal) :
    ∑ w ∈ Sx, Module.length (Localization.AtPrime w.asIdeal)
        (Localization.AtPrime w.asIdeal ⧸
          Ideal.map (algebraMap (affineBlowup I x) (Localization.AtPrime w.asIdeal)) Rx) +
      ∑ v ∈ Sy, Module.length (Localization.AtPrime v.asIdeal)
        (Localization.AtPrime v.asIdeal ⧸
          Ideal.map (algebraMap (affineBlowup I y) (Localization.AtPrime v.asIdeal)) Ry) <
      Module.length R (R ⧸ L) := by
  classical
  have : IsDomain R := IsRegularLocalRing.isDomain R
  have hspan' : Ideal.span ({y, x} : Set R) = IsLocalRing.maximalIdeal R := by
    rw [Set.pair_comm]; exact hspan
  have hI' : I = Ideal.span ({y, x} : Set R) := by rw [hI, Set.pair_comm]
  have hregxy := isRegular_pair_of_span hdim hspan
  have hregyx := isRegular_pair_of_span hdim hspan'
  have hyne : y ≠ 0 := fun h =>
    not_dvd_of_span_pair_eq_maximalIdeal hdim hspan (h ▸ dvd_zero x)
  have hxne : x ≠ 0 := fun h =>
    not_dvd_of_span_pair_eq_maximalIdeal hdim hspan' (h ▸ dvd_zero y)
  have hax : algebraMap R K x ≠ 0 := algebraMap_ne_zero_of_ne_zero hxne
  have hay : algebraMap R K y ≠ 0 := algebraMap_ne_zero_of_ne_zero hyne
  have : IsArtinianRing (affineBlowup I x ⧸ Rx) :=
    isArtinianRing_quotient' R hregxy hspan I hI Rx kx hkx hnx
  have : IsArtinianRing (affineBlowup I y ⧸ Ry) :=
    isArtinianRing_quotient' R hregyx hspan' I hI' Ry ky hky hny
  have hfinY : {v : PrimeSpectrum (affineBlowup I y) | Ry ≤ v.asIdeal}.Finite := by
    refine Set.Finite.of_finite_image (f := PrimeSpectrum.asIdeal) ?_
      (fun w _ w' _ h => PrimeSpectrum.ext h)
    refine (finite_setOf_isPrime_le' hregyx hspan' I hI' Ry ky hky hny).subset ?_
    rintro p ⟨w, hw, rfl⟩
    exact ⟨w.isPrime, hw⟩
  have heCσ : affineBlowupEquivAdjoin (K := K) I hI' hay σ =
      chartGen R (algebraMap R K x / algebraMap R K y) := by
    refine Subtype.ext ?_
    rw [coe_affineBlowupEquivAdjoin I hI' hay σ, hσ, awayToFractionField_mk_self y hay x]
    rfl
  refine sum_length_lt_of_chartEquiv R (IsFractionRing.injective R K) (by field_simp)
    (by field_simp) hxne
    (fun a ha => mem_span_singleton_of_mul_mem_span_singleton hregxy a ha) rfl rfl
    (Algebra.self_mem_adjoin_singleton R _)
    (affineBlowupEquivAdjoin (K := K) I hI hax).toRingEquiv
    (fun r => (affineBlowupEquivAdjoin (K := K) I hI hax).commutes r)
    (affineBlowupEquivAdjoin (K := K) I hI' hay).toRingEquiv
    (fun r => (affineBlowupEquivAdjoin (K := K) I hI' hay).commutes r) L hd Rx Ry hRx hRy
    (not_isUnit_algebraMap' hregxy hspan I hI) Sx hSx hfinY.toFinset Sy
    (fun v => Set.Finite.mem_toFinset hfinY)
    (fun v hv => (Set.Finite.mem_toFinset hfinY).2 (hSy1 v hv)) ?_
  intro v hv
  have hsym : (affineBlowupEquivAdjoin (K := K) I hI' hay).toRingEquiv.symm
      (chartGen R (algebraMap R K x / algebraMap R K y)) = σ := by
    rw [← heCσ]
    exact (affineBlowupEquivAdjoin (K := K) I hI' hay).symm_apply_apply σ
  exact hsym ▸ hSy2 v hv

/-- `...length_quotient_add_sum_length_affineBlowup_lt` with the fraction field of `R` as an
explicit parameter, that being where the comparison of the two charts runs while the statement
does not mention it. -/
private theorem length_quotient_add_sum_length_affineBlowup_lt_aux (R : Type u) [CommRing R]
    [IsRegularLocalRing R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (hdim : ringKrullDim R = 2) {x y : R}
    (hspan : Ideal.span ({x, y} : Set R) = IsLocalRing.maximalIdeal R)
    (I : Ideal R) (hI : I = Ideal.span ({x, y} : Set R))
    (L : Ideal R) [IsArtinian R (R ⧸ L)] {d : ℕ} (hd : 0 < d)
    (Rx : Ideal (affineBlowup I x)) (Ry : Ideal (affineBlowup I y))
    (hRx : Ideal.span {algebraMap R (affineBlowup I x) x ^ d} * Rx =
      Ideal.map (algebraMap R (affineBlowup I x)) L)
    (hRy : Ideal.span {algebraMap R (affineBlowup I y) y ^ d} * Ry =
      Ideal.map (algebraMap R (affineBlowup I y)) L)
    (kx : ℕ) (hkx : algebraMap R (affineBlowup I x) x ^ kx ∈ Rx)
    (hnx : ¬ Rx ≤ Ideal.span {algebraMap R (affineBlowup I x) x})
    (ky : ℕ) (hky : algebraMap R (affineBlowup I y) y ^ ky ∈ Ry)
    (hny : ¬ Ry ≤ Ideal.span {algebraMap R (affineBlowup I y) y})
    (Sy : Finset (PrimeSpectrum (affineBlowup I y)))
    (hSy1 : ∀ v ∈ Sy, Ry ≤ v.asIdeal)
    (σ : affineBlowup I y)
    (hσ : (σ : Localization.Away y) = Localization.mk x ⟨y, Submonoid.mem_powers y⟩)
    (hSy2 : ∀ v ∈ Sy, σ ∈ v.asIdeal) :
    Module.length R (affineBlowup I x ⧸ Rx) +
      ∑ v ∈ Sy, Module.length R (Localization.AtPrime v.asIdeal ⧸
        Ideal.map (algebraMap (affineBlowup I y) (Localization.AtPrime v.asIdeal)) Ry) <
      Module.length R (R ⧸ L) := by
  classical
  have : IsDomain R := IsRegularLocalRing.isDomain R
  have hspan' : Ideal.span ({y, x} : Set R) = IsLocalRing.maximalIdeal R := by
    rw [Set.pair_comm]; exact hspan
  have hI' : I = Ideal.span ({y, x} : Set R) := by rw [hI, Set.pair_comm]
  have hregxy := isRegular_pair_of_span hdim hspan
  have hregyx := isRegular_pair_of_span hdim hspan'
  have hyne : y ≠ 0 := fun h =>
    not_dvd_of_span_pair_eq_maximalIdeal hdim hspan (h ▸ dvd_zero x)
  have hxne : x ≠ 0 := fun h =>
    not_dvd_of_span_pair_eq_maximalIdeal hdim hspan' (h ▸ dvd_zero y)
  have hax : algebraMap R K x ≠ 0 := algebraMap_ne_zero_of_ne_zero hxne
  have hay : algebraMap R K y ≠ 0 := algebraMap_ne_zero_of_ne_zero hyne
  have : IsArtinianRing (affineBlowup I x ⧸ Rx) :=
    isArtinianRing_quotient' R hregxy hspan I hI Rx kx hkx hnx
  have : IsArtinianRing (affineBlowup I y ⧸ Ry) :=
    isArtinianRing_quotient' R hregyx hspan' I hI' Ry ky hky hny
  have hfinX : {w : PrimeSpectrum (affineBlowup I x) | Rx ≤ w.asIdeal}.Finite := by
    refine Set.Finite.of_finite_image (f := PrimeSpectrum.asIdeal) ?_
      (fun w _ w' _ h => PrimeSpectrum.ext h)
    refine (finite_setOf_isPrime_le' hregxy hspan I hI Rx kx hkx hnx).subset ?_
    rintro p ⟨w, hw, rfl⟩
    exact ⟨w.isPrime, hw⟩
  have hfinY : {v : PrimeSpectrum (affineBlowup I y) | Ry ≤ v.asIdeal}.Finite := by
    refine Set.Finite.of_finite_image (f := PrimeSpectrum.asIdeal) ?_
      (fun w _ w' _ h => PrimeSpectrum.ext h)
    refine (finite_setOf_isPrime_le' hregyx hspan' I hI' Ry ky hky hny).subset ?_
    rintro p ⟨w, hw, rfl⟩
    exact ⟨w.isPrime, hw⟩
  have heCσ : affineBlowupEquivAdjoin (K := K) I hI' hay σ =
      chartGen R (algebraMap R K x / algebraMap R K y) := by
    refine Subtype.ext ?_
    rw [coe_affineBlowupEquivAdjoin I hI' hay σ, hσ, awayToFractionField_mk_self y hay x]
    rfl
  refine length_quotient_add_sum_length_lt_of_chartEquiv R (IsFractionRing.injective R K)
    (by field_simp) (by field_simp) hxne
    (fun a ha => mem_span_singleton_of_mul_mem_span_singleton hregxy a ha) rfl rfl
    (Algebra.self_mem_adjoin_singleton R _)
    (affineBlowupEquivAdjoin (K := K) I hI hax).toRingEquiv
    (fun r => (affineBlowupEquivAdjoin (K := K) I hI hax).commutes r)
    (affineBlowupEquivAdjoin (K := K) I hI' hay).toRingEquiv
    (fun r => (affineBlowupEquivAdjoin (K := K) I hI' hay).commutes r) L hd Rx Ry hRx hRy
    (not_isUnit_algebraMap' hregxy hspan I hI) hfinX.toFinset
    (fun w => Set.Finite.mem_toFinset hfinX) hfinY.toFinset Sy
    (fun v => Set.Finite.mem_toFinset hfinY)
    (fun v hv => (Set.Finite.mem_toFinset hfinY).2 (hSy1 v hv)) ?_
  intro v hv
  have hsym : (affineBlowupEquivAdjoin (K := K) I hI' hay).toRingEquiv.symm
      (chartGen R (algebraMap R K x / algebraMap R K y)) = σ := by
    rw [← heCσ]
    exact (affineBlowupEquivAdjoin (K := K) I hI' hay).symm_apply_apply σ
  exact hsym ▸ hSy2 v hv

/-- **The colength drop in the affine blowup algebras.** Let `R` be a two-dimensional regular
local ring with `𝔪 = (x, y)`, let `I` be that span, let `L` be an ideal of `R` with `R ⧸ L` of
finite length, let `d` be positive, and let `Rx`, `Ry` be ideals of the two charts `R[I/x]`,
`R[I/y]` which satisfy the chart equations `(ξ ^ d)·Rx = L·R[I/x]` and `(η ^ d)·Ry = L·R[I/y]`,
contain a power of the chart generator and are not contained in the ideal it generates. Let `Sx`
be the set of *all* primes of `R[I/x]` above `Rx`, and `Sy` any set of primes of `R[I/y]` above
`Ry` which contain the chart element `x / y`. Then

`∑_{w ∈ Sx} ℓ(R[I/x]_w ⧸ Rx) + ∑_{v ∈ Sy} ℓ(R[I/y]_v ⧸ Ry) < ℓ_R(R ⧸ L)`.

This is the inequality of [Stacks, Tag 0AGT] in the form the blowup's affine charts deliver. -/
public theorem sum_length_affineBlowup_lt (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (hdim : ringKrullDim R = 2) {x y : R}
    (hspan : Ideal.span ({x, y} : Set R) = IsLocalRing.maximalIdeal R)
    (I : Ideal R) (hI : I = Ideal.span ({x, y} : Set R))
    (L : Ideal R) [IsArtinian R (R ⧸ L)] {d : ℕ} (hd : 0 < d)
    (Rx : Ideal (affineBlowup I x)) (Ry : Ideal (affineBlowup I y))
    (hRx : Ideal.span {algebraMap R (affineBlowup I x) x ^ d} * Rx =
      Ideal.map (algebraMap R (affineBlowup I x)) L)
    (hRy : Ideal.span {algebraMap R (affineBlowup I y) y ^ d} * Ry =
      Ideal.map (algebraMap R (affineBlowup I y)) L)
    (kx : ℕ) (hkx : algebraMap R (affineBlowup I x) x ^ kx ∈ Rx)
    (hnx : ¬ Rx ≤ Ideal.span {algebraMap R (affineBlowup I x) x})
    (ky : ℕ) (hky : algebraMap R (affineBlowup I y) y ^ ky ∈ Ry)
    (hny : ¬ Ry ≤ Ideal.span {algebraMap R (affineBlowup I y) y})
    (Sx : Finset (PrimeSpectrum (affineBlowup I x)))
    (hSx : ∀ w : PrimeSpectrum (affineBlowup I x), w ∈ Sx ↔ Rx ≤ w.asIdeal)
    (Sy : Finset (PrimeSpectrum (affineBlowup I y)))
    (hSy1 : ∀ v ∈ Sy, Ry ≤ v.asIdeal)
    (σ : affineBlowup I y)
    (hσ : (σ : Localization.Away y) = Localization.mk x ⟨y, Submonoid.mem_powers y⟩)
    (hSy2 : ∀ v ∈ Sy, σ ∈ v.asIdeal) :
    ∑ w ∈ Sx, Module.length (Localization.AtPrime w.asIdeal)
        (Localization.AtPrime w.asIdeal ⧸
          Ideal.map (algebraMap (affineBlowup I x) (Localization.AtPrime w.asIdeal)) Rx) +
      ∑ v ∈ Sy, Module.length (Localization.AtPrime v.asIdeal)
        (Localization.AtPrime v.asIdeal ⧸
          Ideal.map (algebraMap (affineBlowup I y) (Localization.AtPrime v.asIdeal)) Ry) <
      Module.length R (R ⧸ L) := by
  have : IsDomain R := IsRegularLocalRing.isDomain R
  exact sum_length_affineBlowup_lt_aux R (FractionRing R) hdim hspan I hI L hd Rx Ry hRx hRy
    kx hkx hnx ky hky hny Sx hSx Sy hSy1 σ hσ hSy2

/-- **The colength drop in the affine blowup algebras, over the base ring.** Same situation as
`Stacks.ResolutionOfSurfaces.CartierDescent.sum_length_affineBlowup_lt`, with every length taken
over `R`:

`ℓ_R(R[I/x] ⧸ Rx) + ∑_{v ∈ Sy} ℓ_R(R[I/y]_v ⧸ Ry) < ℓ_R(R ⧸ L)`.

The first chart contributes its whole residual quotient rather than a sum over the primes above
`Rx`, those primes being all of them. This is the form of the inequality of [Stacks, Tag 0AGT]
that bounds the length over the base of the global sections of the residual quotient: a sum of
local colengths taken over the local rings themselves is in general strictly smaller, by the
degrees of the residue field extensions at the points of the exceptional divisor. -/
public theorem length_quotient_add_sum_length_affineBlowup_lt (R : Type u) [CommRing R]
    [IsRegularLocalRing R] (hdim : ringKrullDim R = 2) {x y : R}
    (hspan : Ideal.span ({x, y} : Set R) = IsLocalRing.maximalIdeal R)
    (I : Ideal R) (hI : I = Ideal.span ({x, y} : Set R))
    (L : Ideal R) [IsArtinian R (R ⧸ L)] {d : ℕ} (hd : 0 < d)
    (Rx : Ideal (affineBlowup I x)) (Ry : Ideal (affineBlowup I y))
    (hRx : Ideal.span {algebraMap R (affineBlowup I x) x ^ d} * Rx =
      Ideal.map (algebraMap R (affineBlowup I x)) L)
    (hRy : Ideal.span {algebraMap R (affineBlowup I y) y ^ d} * Ry =
      Ideal.map (algebraMap R (affineBlowup I y)) L)
    (kx : ℕ) (hkx : algebraMap R (affineBlowup I x) x ^ kx ∈ Rx)
    (hnx : ¬ Rx ≤ Ideal.span {algebraMap R (affineBlowup I x) x})
    (ky : ℕ) (hky : algebraMap R (affineBlowup I y) y ^ ky ∈ Ry)
    (hny : ¬ Ry ≤ Ideal.span {algebraMap R (affineBlowup I y) y})
    (Sy : Finset (PrimeSpectrum (affineBlowup I y)))
    (hSy1 : ∀ v ∈ Sy, Ry ≤ v.asIdeal)
    (σ : affineBlowup I y)
    (hσ : (σ : Localization.Away y) = Localization.mk x ⟨y, Submonoid.mem_powers y⟩)
    (hSy2 : ∀ v ∈ Sy, σ ∈ v.asIdeal) :
    Module.length R (affineBlowup I x ⧸ Rx) +
      ∑ v ∈ Sy, Module.length R (Localization.AtPrime v.asIdeal ⧸
        Ideal.map (algebraMap (affineBlowup I y) (Localization.AtPrime v.asIdeal)) Ry) <
      Module.length R (R ⧸ L) := by
  have : IsDomain R := IsRegularLocalRing.isDomain R
  exact length_quotient_add_sum_length_affineBlowup_lt_aux R (FractionRing R) hdim hspan I hI L hd
    Rx Ry hRx hRy kx hkx hnx ky hky hny Sy hSy1 σ hσ hSy2

end Stacks.ResolutionOfSurfaces.CartierDescent

end
