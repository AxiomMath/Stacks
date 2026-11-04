module

public import StacksFrontier.Algebra.Homology.SpectralSequence.DerivedTensor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Vanishing at the origin of a cohomological spectral sequence

Let `E` be an `E₂`-cohomological spectral sequence. If every second-page term that could be the
source or the target of a differential touching the origin `(0, 0)` vanishes, then no differential
into or out of the origin is ever nonzero, so the term at the origin is the same on every page.
The positions in question are `(-r, r - 1)` for the incoming differentials and `(r, 1 - r)` for the
outgoing ones, for `r ≥ 2`.

If moreover the spectral sequence is the one associated to a decreasing filtration of a cochain
complex `T`, then it abuts to the cohomology of `T`, and the term at the origin on a sufficiently
late page is a subquotient of `H⁰(T)`. So if `H⁰(T) = 0` as well, the second-page term at the
origin vanishes.

## Main definitions

* `Stacks.SpectralSequence.derivedTensorHomology`: `Hⁱ(K ⊗^L L)` for objects `K`, `L` of the
  derived category of `A`-modules.
* `Stacks.SpectralSequence.singleHomology`: `Hⁱ(K)`, placed in degree zero of the derived
  category.

## Main results

* `Stacks.SpectralSequence.isZero_page_of_isZero_pageTwo`: a second-page term that vanishes
  vanishes on every later page.
* `Stacks.SpectralSequence.d_eq_zero_at_origin`: under the two vanishing hypotheses, every
  differential into or out of the origin is zero.
* `Stacks.SpectralSequence.nonempty_pageTwo_iso_page_origin`: hence the origin is unchanged from
  the second page onwards.
* `Stacks.SpectralSequence.isZero_pageTwo_origin_of_isZero_page`: if the origin vanishes on some
  page, it vanishes on the second page.
* `Stacks.SpectralSequence.exists_isZero_page_of_isZero_homology`: for the spectral sequence of a
  filtered complex, a position whose total degree has vanishing cohomology vanishes on some page.
* `Stacks.SpectralSequence.isZero_pageTwo_origin_of_isZero_homology`: the combination — the
  second-page term at the origin vanishes.
* `Stacks.SpectralSequence.isZero_derivedTensorHomology_singleHomology`: if `H^q(K) = 0`, then
  `H^p(H^q(K)[0] ⊗^L L) = 0` for every `p`.
* `Stacks.SpectralSequence.isZero_derivedTensorHomology_zero_singleHomology_zero`: for
  bounded-above `K` and `L`, if `H⁰(K ⊗^L L) = 0`, `H^q(K) = 0` for `q < 0` and
  `H^{-r}(H^{r-1}(K)[0] ⊗^L L) = 0` for `r ≥ 2`, then `H⁰(H⁰(K)[0] ⊗^L L) = 0`.

## References

* [Stacks Project, Tag 0ECC](https://stacks.math.columbia.edu/tag/0ECC)
* [Stacks Project, Tag 0662](https://stacks.math.columbia.edu/tag/0662)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CochainComplex.DerivedTensorSpectralSequence

universe u

namespace Stacks.SpectralSequence

variable {C : Type*} [Category C] [Abelian C]

/-- A second-page term which vanishes vanishes on every later page. -/
@[ega "0 11.1.6" "partial"]
theorem isZero_page_of_isZero_pageTwo (E : E₂CohomologicalSpectralSequence C) {p q : ℤ}
    (h : IsZero ((E.page 2).X (p, q))) (r : ℤ) (hr : 2 ≤ r) :
    IsZero ((E.page r hr).X (p, q)) := by
  induction r, hr using Int.leInduction with
  | base => exact h
  | succ r hr ih =>
    exact ((HomologicalComplex.ExactAt.of_isZero ih).isZero_homology).of_iso
      (E.iso r (r + 1) (p, q)).symm

variable (E : E₂CohomologicalSpectralSequence C)
  (hOut : ∀ r : ℤ, 2 ≤ r → IsZero ((E.page 2).X (r, 1 - r)))
  (hIn : ∀ r : ℤ, 2 ≤ r → IsZero ((E.page 2).X (-r, r - 1)))

include hOut hIn

/-- If every second-page term at an outgoing position `(r, 1 - r)` and at an incoming position
`(-r, r - 1)` vanishes, then on every page the differentials into and out of the origin are
zero. -/
theorem d_eq_zero_at_origin (r : ℤ) (hr : 2 ≤ r) :
    (E.page r hr).d (0, 0) (r, 1 - r) = 0 ∧ (E.page r hr).d (-r, r - 1) (0, 0) = 0 :=
  ⟨(isZero_page_of_isZero_pageTwo E (hOut r hr) r hr).eq_of_tgt _ _,
    (isZero_page_of_isZero_pageTwo E (hIn r hr) r hr).eq_of_src _ _⟩

/-- Under the same hypotheses the term at the origin is unchanged from the second page onwards. -/
theorem nonempty_pageTwo_iso_page_origin (r : ℤ) (hr : 2 ≤ r) :
    Nonempty ((E.page 2).X (0, 0) ≅ (E.page r hr).X (0, 0)) := by
  induction r, hr using Int.leInduction with
  | base => exact ⟨Iso.refl _⟩
  | succ r hr ih =>
    obtain ⟨e⟩ := ih
    obtain ⟨hout, hin⟩ := d_eq_zero_at_origin E hOut hIn r hr
    have hscf : ((E.page r hr).sc (0, 0)).f = 0 := by
      change (E.page r hr).d ((ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)).prev (0, 0)) (0, 0) = 0
      rwa [ComplexShape.prev_eq' _ (i := (0, 0)) (j := (-r, r - 1)) (by simp [ComplexShape.up'])]
    have hscg : ((E.page r hr).sc (0, 0)).g = 0 := by
      change (E.page r hr).d (0, 0) ((ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)).next (0, 0)) = 0
      rwa [ComplexShape.next_eq' _ (i := (0, 0)) (j := (r, 1 - r)) (by simp [ComplexShape.up'])]
    let eH : (E.page r hr).homology (0, 0) ≅ (E.page r hr).X (0, 0) :=
      (ShortComplex.HomologyData.ofZeros ((E.page r hr).sc (0, 0)) hscf hscg).left.homologyIso
    exact ⟨e ≪≫ eH.symm ≪≫ E.iso r (r + 1) (0, 0)⟩

/-- If the term at the origin vanishes on some page, it already vanishes on the second page. -/
theorem isZero_pageTwo_origin_of_isZero_page (r : ℤ) (hr : 2 ≤ r)
    (hStable : IsZero ((E.page r hr).X (0, 0))) :
    IsZero ((E.page 2).X (0, 0)) :=
  hStable.of_iso (nonempty_pageTwo_iso_page_origin E hOut hIn r hr).some

end Stacks.SpectralSequence

namespace Stacks.SpectralSequence

variable {C : Type u} [Category C] [Abelian C]

/-- For the spectral sequence associated to a decreasing filtration of a cochain complex `T`, a
position `(p, q)` whose total degree carries vanishing cohomology of `T` vanishes on some page. -/
theorem exists_isZero_page_of_isZero_homology (T : CochainComplex C ℤ)
    (F : ∀ _p n : ℤ, Subobject (T.X n)) (E : AssociatedFiltrationSpectralSequence T F)
    (p q : ℤ) (h : IsZero (T.homology (p + q))) :
    ∃ r : ℤ, ∃ hr : 2 ≤ r, IsZero ((E.spectralSequence.page r hr).X (p, q)) := by
  obtain ⟨r, hr, hstable⟩ := E.abuts p q
  obtain ⟨_, _, comparison, _, _, hcomp, _, _, _⟩ := hstable r hr le_rfl
  have hfiltration : IsZero (inducedHomologyFiltration T F p (p + q) : C) :=
    IsZero.of_mono (Subobject.arrow _) h
  have hgraded : IsZero (inducedHomologyGradedPiece T F E.decreasing p (p + q)) :=
    have : Epi (inducedHomologyGradedπ T F E.decreasing p (p + q)) := by
      dsimp only [inducedHomologyGradedπ, inducedHomologyGradedPiece]
      infer_instance
    IsZero.of_epi (inducedHomologyGradedπ T F E.decreasing p (p + q)) hfiltration
  exact ⟨r, hr, hgraded.of_iso (asIso comparison).symm⟩

/-- Let `T` be a cochain complex with a decreasing filtration, and let `E` be the associated
spectral sequence. If `H⁰(T) = 0`, and every second-page term at an outgoing position `(r, 1 - r)`
or an incoming position `(-r, r - 1)` vanishes for `r ≥ 2`, then the second-page term at the
origin vanishes. -/
theorem isZero_pageTwo_origin_of_isZero_homology (T : CochainComplex C ℤ)
    (F : ∀ _p n : ℤ, Subobject (T.X n)) (E : AssociatedFiltrationSpectralSequence T F)
    (habut : IsZero (T.homology 0))
    (hOut : ∀ r : ℤ, 2 ≤ r → IsZero ((E.spectralSequence.page 2).X (r, 1 - r)))
    (hIn : ∀ r : ℤ, 2 ≤ r → IsZero ((E.spectralSequence.page 2).X (-r, r - 1))) :
    IsZero ((E.spectralSequence.page 2).X (0, 0)) := by
  obtain ⟨r, hr, hzero⟩ :=
    exists_isZero_page_of_isZero_homology T F E 0 0 (by simpa using habut)
  exact isZero_pageTwo_origin_of_isZero_page E.spectralSequence hOut hIn r hr hzero

end Stacks.SpectralSequence

namespace Stacks.SpectralSequence

open CategoryTheory.MonoidalCategory CochainComplex.DerivedTensor

attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A]

/-- `Hⁱ` of the derived tensor product of two objects of the derived category of `A`-modules. -/
noncomputable abbrev derivedTensorHomology
    (K L : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) : ModuleCat.{u} A :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
    (((canonicalDerivedTensorProductFunctor A).obj K).obj L)

/-- `Hⁱ(K)`, placed in degree zero of the derived category. -/
noncomputable abbrev singleHomology (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) :
    DerivedCategory (ModuleCat.{u} A) :=
  (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K)

/-- If `H^q(K) = 0`, then `H^p(H^q(K)[0] ⊗^L L) = 0` for every `p`. -/
theorem isZero_derivedTensorHomology_singleHomology
    (K L : DerivedCategory (ModuleCat.{u} A)) (q : ℤ)
    (hq : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) q).obj K)) (p : ℤ) :
    IsZero (derivedTensorHomology A (singleHomology A K q) L p) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).map_isZero
    (((canonicalDerivedTensorProductFunctor A).flip.obj L).map_isZero
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map_isZero hq))

/-- Let `K` and `L` be bounded-above objects of the derived category of `A`-modules. Suppose

* `H⁰(K ⊗^L L) = 0`;
* `H^q(K) = 0` for `q < 0`;
* `H^{-r}(H^{r-1}(K)[0] ⊗^L L) = 0` for every `r ≥ 2`.

Then `H⁰(H⁰(K)[0] ⊗^L L) = 0`. -/
@[stacks 0ECC "the cohomological step: the tensor spectral sequence at the origin"]
theorem isZero_derivedTensorHomology_zero_singleHomology_zero
    (K L : DerivedCategory.Minus (ModuleCat.{u} A))
    (habut : IsZero (derivedTensorHomology A K.1 L.1 0))
    (hneg : ∀ q : ℤ, q < 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) q).obj K.1))
    (hTor : ∀ r : ℤ, 2 ≤ r →
      IsZero (derivedTensorHomology A (singleHomology A K.1 (r - 1)) L.1 (-r))) :
    IsZero (derivedTensorHomology A (singleHomology A K.1 0) L.1 0) := by
  obtain ⟨P, Q, bP, bQ, hPb, hPproj, hQb, hQproj, hPflat, hQflat, eK, eL, _E, E', rest⟩ :=
    CochainComplex.DerivedTensorSpectralSequence.exists_derived_tensor_spectral_sequences A K L
  obtain ⟨_, _, _, _, abutmentIso, _, _, _, secondDerivedE₂Iso, _, _, _, _, _⟩ := rest
  have hOut : ∀ r : ℤ, 2 ≤ r → IsZero ((E'.spectralSequence.page 2).X (r, 1 - r)) :=
    fun r hr ↦ (isZero_derivedTensorHomology_singleHomology A K.1 L.1 (1 - r)
      (hneg (1 - r) (by lia)) r).of_iso (secondDerivedE₂Iso r (1 - r))
  have hIn : ∀ r : ℤ, 2 ≤ r → IsZero ((E'.spectralSequence.page 2).X (-r, r - 1)) :=
    fun r hr ↦ (hTor r hr).of_iso (secondDerivedE₂Iso (-r) (r - 1))
  exact (isZero_pageTwo_origin_of_isZero_homology _ _ E' (habut.of_iso (abutmentIso 0)) hOut
    hIn).of_iso (secondDerivedE₂Iso 0 0).symm

end Stacks.SpectralSequence
