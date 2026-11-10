module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.Data.Int.Interval
public import StacksFrontier.Algebra.Homology.Resolution.ProjectiveResolution
public import StacksFrontier.Algebra.Homology.SpectralSequence.DoubleComplex
public import StacksFrontier.Algebra.Homology.SpectralSequence.HomologicalFiltration
public import StacksFrontier.Homology.TensorComplex.SingleTensor
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.KFlat.QuasiIso
public import StacksFrontier.Homology.TensorComplex.Monoidal
public import StacksFrontier.Homology.Tor.DerivedTensor
public import StacksFrontier.Homology.TorAmplitude.FaithfullyFlat
public import StacksCore.Tactic.StacksAttribute

/-!
# Spectral sequences for derived tensor products

Let `R` be a commutative ring and let `P^•`, `Q^•` be cochain complexes of `R`-modules which are
strictly bounded above, by `bP` and `bQ`. The total tensor complex `P^• ⊗ Q^•` carries two
decreasing filtrations by subcomplexes,
```
'F^p(P ⊗ Q)^n = ⨁_{i + j = n, i ≥ p} P^i ⊗ Q^j,   ''F^p(P ⊗ Q)^n = ⨁_{i + j = n, j ≥ p} P^i ⊗ Q^j,
```
by the degree in `P`, respectively in `Q`. Each is finite in every degree, so each gives a
convergent cohomological spectral sequence abutting to `H^*(P^• ⊗ Q^•)`, with second pages
```
'E_2^{p,q} = H^p(P^• ⊗ H^q(Q^•)),                 ''E_2^{p,q} = H^p(H^q(P^•) ⊗ Q^•),
```
where a module is regarded as a complex in degree zero. Taking for `P^•` and `Q^•` bounded-above
complexes of projectives representing objects `K`, `L` of `D^-(Mod_R)` — such complexes are
K-flat, so `P^• ⊗ Q^•` computes `K ⊗^L L` — these become the two standard spectral sequences
```
'E_2^{p,q} = H^p(K ⊗^L H^q(L)),                   ''E_2^{p,q} = H^p(H^q(K) ⊗^L L)
```
for the derived tensor product, both abutting to `H^{p+q}(K ⊗^L L)`.

## Main definitions

* `firstDegreeFiltration` and `secondDegreeFiltration`: the two canonical filtrations of a total
  tensor complex, by the degree in the first, respectively the second, factor.
* `AssociatedFiltrationSpectralSequence`: the spectral sequence canonically associated to a
  decreasing filtration of a cochain complex, bundled together with the identification of each
  page with the corresponding cycle-boundary subquotient, the characterisation of its
  differentials and of its page-turning isomorphisms, and the comparison from the associated
  graded of the induced filtration on cohomology.

## Main results

* `associatedSpectralSequenceOfFiniteFiltration`: a degreewise finite decreasing filtration of a
  cochain complex has an `AssociatedFiltrationSpectralSequence`.
* `exists_derived_tensor_spectral_sequences`: both spectral sequences for two bounded-above
  objects of the derived category of a commutative ring, with their second pages identified with
  `H^p(K ⊗^L H^q(L))` and `H^p(H^q(K) ⊗^L L)` and their abutment identified with
  `H^{p+q}(K ⊗^L L)`.

## Implementation notes

The tensor product of cochain complexes is the total complex of the degreewise tensor-product
double complex, so the two filtrations above are the two filtrations of the total complex of a
double complex, and the identification of the second pages is the corresponding statement for
double complexes.

`AssociatedFiltrationSpectralSequence` records the canonical subquotient presentation of the
spectral sequence of a filtered complex, rather than just the abstract spectral sequence: its
`pageIso` identifies each page with `Z_r^{p,q}/(D_r^{p,q} ⊓ Z_r^{p,q})`, its
`differential_commutes` says that the page differentials are the maps induced by `d`, its
`filteredPageTurnIso` fields pin the page turn by the classes of `(r+1)`-cycles, and its `abuts`
field provides the canonical isomorphism from `gr^p H^n` to the stable page. This is what makes
the two tensor spectral sequences comparable to the double-complex ones, whose pages are given in
the same presentation.

The page index `q` used here is the complementary degree, so that `filteredPageObject T F r p q`
is the page object in total degree `n = p + q`; the underlying subquotient machinery in
`FilteredComplexSpectralSequence` is indexed by `p` and the total degree `n` instead.

## References

* [The Stacks Project, Tag 0662](https://stacks.math.columbia.edu/tag/0662)
* [The Stacks Project, Tag 012X](https://stacks.math.columbia.edu/tag/012X)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open FilteredComplexSpectralSequence

namespace CochainComplex.DerivedTensorSpectralSequence

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The decreasing filtration of `P ⊗ Q` by the degree in `P`: in degree `n`, the sum of the
summands `P^i ⊗ Q^j` with `i + j = n` and `i ≥ p`. -/
public noncomputable def firstDegreeFiltration
    {R : Type u} [CommRing R] (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (bP bQ a n : ℤ) :
    Subobject (((tensorLeft P).obj Q).X n) :=
  (Finset.Icc (max a (n - bQ)) bP).sup fun i ↦
    imageSubobject (HomologicalComplex.ιTensorObj P Q i (n - i) n (by omega))

/-- The decreasing filtration of `P ⊗ Q` by the degree in `Q`: in degree `n`, the sum of the
summands `P^i ⊗ Q^j` with `i + j = n` and `j ≥ p`. -/
public noncomputable def secondDegreeFiltration
    {R : Type u} [CommRing R] (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (bP bQ a n : ℤ) :
    Subobject (((tensorLeft P).obj Q).X n) :=
  (Finset.Icc (max a (n - bP)) bQ).sup fun j ↦
    imageSubobject (HomologicalComplex.ιTensorObj P Q (n - j) j n (by omega))

/-- The canonical `r`-page object attached to a decreasing filtration `F` of a cochain complex:
the cycles `Z_r^{p,q}` modulo their intersection with the boundaries `D_r^{p,q}`, in total degree
`n = p + q`. -/
public noncomputable abbrev filteredPageObject (T : CochainComplex C ℤ)
    (F : ∀ _p n : ℤ, Subobject (T.X n)) (r p q : ℤ) : C :=
  pageObj T F r p (p + q)

/-- The quotient map from the filtered cycles `Z_r^{p,q}` to the corresponding page object. -/
public noncomputable abbrev filteredPageπ (T : CochainComplex C ℤ)
    (F : ∀ _p n : ℤ, Subobject (T.X n)) (r p q : ℤ) :
    (cycles T F r p (p + q) : C) ⟶ filteredPageObject T F r p q :=
  cokernel.π (den T F r p (p + q))

/-- The filtration induced by `F` on the cohomology of `T`: the classes of the cycles of `T` which
lie in `F^p T^n`. -/
public noncomputable def inducedHomologyFiltration (T : CochainComplex C ℤ)
    (F : ∀ _p n : ℤ, Subobject (T.X n)) (p n : ℤ) : Subobject (T.homology n) :=
  (Subobject.exists (T.homologyπ n)).obj
    ((Subobject.pullback (T.iCycles n)).obj (F p n))

/-- The associated graded object `gr^p H^n(T)` of the filtration induced by `F` on cohomology. -/
public noncomputable def inducedHomologyGradedPiece (T : CochainComplex C ℤ)
    (F : ∀ _p n : ℤ, Subobject (T.X n))
    (hF : ∀ p p' n, p ≤ p' → F p' n ≤ F p n) (p n : ℤ) : C :=
  cokernel (Subobject.ofLE (inducedHomologyFiltration T F (p + 1) n)
    (inducedHomologyFiltration T F p n)
    ((Subobject.exists (T.homologyπ n)).monotone
      ((Subobject.pullback (T.iCycles n)).monotone (hF p (p + 1) n (by omega)))))

/-- The quotient map from a step of the induced cohomology filtration to its graded piece. -/
public noncomputable def inducedHomologyGradedπ (T : CochainComplex C ℤ)
    (F : ∀ _p n : ℤ, Subobject (T.X n))
    (hF : ∀ p p' n, p ≤ p' → F p' n ≤ F p n) (p n : ℤ) :
    (inducedHomologyFiltration T F p n : C) ⟶ inducedHomologyGradedPiece T F hF p n :=
  cokernel.π (Subobject.ofLE (inducedHomologyFiltration T F (p + 1) n)
    (inducedHomologyFiltration T F p n)
    ((Subobject.exists (T.homologyπ n)).monotone
      ((Subobject.pullback (T.iCycles n)).monotone (hF p (p + 1) n (by omega)))))

/-- An identification of every page of a cohomological spectral sequence with the corresponding
cycle-boundary subquotient of a filtered complex. -/
public abbrev PageIdentifications (T : CochainComplex C ℤ)
    (F : ∀ _p n : ℤ, Subobject (T.X n)) (E : E₂CohomologicalSpectralSequence C) :=
  ∀ (r p q : ℤ) (hr : 2 ≤ r), (E.page r hr).X (p, q) ≅ filteredPageObject T F r p q

/-- The page identifications intertwine the spectral-sequence differential with the unique map on
the subquotients induced by the differential of the filtered complex. -/
public def HasCanonicalPageDifferentials (T : CochainComplex C ℤ)
    (F : ∀ _p n : ℤ, Subobject (T.X n)) (E : E₂CohomologicalSpectralSequence C)
    (e : PageIdentifications T F E) : Prop :=
  ∀ (r p q : ℤ) (hr : 2 ≤ r),
    ∃ (z : (cycles T F r p (p + q) : C) ⟶
          (cycles T F r (p + r) ((p + r) + (q + 1 - r)) : C))
      (d : filteredPageObject T F r p q ⟶ filteredPageObject T F r (p + r) (q + 1 - r)),
      z ≫ (cycles T F r (p + r) ((p + r) + (q + 1 - r))).arrow =
          (cycles T F r p (p + q)).arrow ≫
            T.d (p + q) ((p + r) + (q + 1 - r)) ∧
      filteredPageπ T F r p q ≫ d = z ≫ filteredPageπ T F r (p + r) (q + 1 - r) ∧
      (E.page r hr).d (p, q) (p + r, q + 1 - r) ≫
          (e r (p + r) (q + 1 - r) hr).hom = (e r p q hr).hom ≫ d

/-- On every sufficiently late page, the canonical comparison from the associated graded of the
induced filtration on cohomology to that page is an isomorphism. The last equation characterizes
this comparison using filtered cocycles. -/
public def CanonicallyAbutsTo (T : CochainComplex C ℤ)
    (F : ∀ _p n : ℤ, Subobject (T.X n)) (E : E₂CohomologicalSpectralSequence C)
    (hF : ∀ p p' n, p ≤ p' → F p' n ≤ F p n) (e : PageIdentifications T F E) : Prop :=
  ∀ p q : ℤ, ∃ r₀ : ℤ, 2 ≤ r₀ ∧ ∀ (r : ℤ) (hr : 2 ≤ r), r₀ ≤ r →
    (E.page r hr).d (p, q) (p + r, q + 1 - r) = 0 ∧
    (E.page r hr).d (p - r, q + r - 1) (p, q) = 0 ∧
    ∃ (comparison : inducedHomologyGradedPiece T F hF p (p + q) ⟶
          (E.page r hr).X (p, q))
      (a : ((Subobject.pullback (T.iCycles (p + q))).obj (F p (p + q)) : C) ⟶
          (cycles T F r p (p + q) : C))
      (b : ((Subobject.pullback (T.iCycles (p + q))).obj (F p (p + q)) : C) ⟶
          (inducedHomologyFiltration T F p (p + q) : C)),
      IsIso comparison ∧
      a ≫ (cycles T F r p (p + q)).arrow =
          ((Subobject.pullback (T.iCycles (p + q))).obj (F p (p + q))).arrow ≫
            T.iCycles (p + q) ∧
      b ≫ (inducedHomologyFiltration T F p (p + q)).arrow =
          ((Subobject.pullback (T.iCycles (p + q))).obj (F p (p + q))).arrow ≫
            T.homologyπ (p + q) ∧
      b ≫ inducedHomologyGradedπ T F hF p (p + q) ≫ comparison =
        a ≫ filteredPageπ T F r p q ≫ (e r p q hr).inv

/-- The spectral sequence canonically associated to a decreasing filtration of a cochain complex.
Its pages are the canonical cycle-boundary subquotients, its differentials are induced by the
complex differential, and its stable-page maps are the canonical comparisons from the associated
graded of the induced cohomology filtration. -/
public structure AssociatedFiltrationSpectralSequence (T : CochainComplex C ℤ)
    (F : ∀ _p n : ℤ, Subobject (T.X n)) where
  /-- The underlying cohomological spectral sequence. -/
  spectralSequence : E₂CohomologicalSpectralSequence C
  /-- The filtration is decreasing. -/
  decreasing : ∀ p p' n, p ≤ p' → F p' n ≤ F p n
  /-- The differential preserves the filtration. -/
  differential_le : ∀ p n, (Subobject.exists (T.d n (n + 1))).obj (F p n) ≤ F p (n + 1)
  /-- Every page is canonically the corresponding cycle-boundary subquotient. -/
  pageIso : PageIdentifications T F spectralSequence
  /-- A page written as the canonical cycle-boundary subquotient complex of the filtration. -/
  filteredPage (r : ℤ) (hr : 2 ≤ r := by omega) :
    HomologicalComplex C (ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ))
  /-- The objects of the canonical filtered page are the cycle-boundary subquotients. -/
  filteredPageObjectIso (r p q : ℤ) (hr : 2 ≤ r) :
    (filteredPage r hr).X (p, q) ≅ filteredPageObject T F r p q
  /-- The identification of the abstract spectral-sequence page with its canonical filtered-page
  model. -/
  spectralSequencePageIso (r : ℤ) (hr : 2 ≤ r) :
    spectralSequence.page r hr ≅ filteredPage r hr
  /-- The two descriptions of the identification with the cycle-boundary quotient agree. -/
  spectralSequencePageIso_hom (r p q : ℤ) (hr : 2 ≤ r) :
    (spectralSequencePageIso r hr).hom.f (p, q) ≫ (filteredPageObjectIso r p q hr).hom =
      (pageIso r p q hr).hom
  /-- These page identifications intertwine the two canonical differentials. -/
  differential_commutes : HasCanonicalPageDifferentials T F spectralSequence pageIso
  /-- The canonical page-turning isomorphism between the homology of one filtered page and the
  next filtered page. -/
  filteredPageTurnIso (r p q : ℤ) (hr : 2 ≤ r) :
    (filteredPage r hr).homology (p, q) ≅ (filteredPage (r + 1) (by omega)).X (p, q)
  /-- The map from `Z_{r+1}` to the cycles of the `r`-th filtered page. -/
  pageTurnCyclesLift (r p q : ℤ) (hr : 2 ≤ r) :
    (cycles T F (r + 1) p (p + q) : C) ⟶ (filteredPage r hr).cycles (p, q)
  /-- The cycle lift is induced by the inclusion `Z_{r+1} ≤ Z_r` followed by the quotient map. -/
  pageTurnCyclesLift_comm (r p q : ℤ) (hr : 2 ≤ r) :
    pageTurnCyclesLift r p q hr ≫ (filteredPage r hr).iCycles (p, q) =
      Subobject.ofLE (cycles T F (r + 1) p (p + q)) (cycles T F r p (p + q))
          (cycles_succ_le T F decreasing r p (p + q)) ≫
        filteredPageπ T F r p q ≫ (filteredPageObjectIso r p q hr).inv
  /-- The classes coming from `Z_{r+1}` generate the homology of the `r`-th filtered page. -/
  pageTurnCycles_epi (r p q : ℤ) (hr : 2 ≤ r) :
    Epi (pageTurnCyclesLift r p q hr ≫ (filteredPage r hr).homologyπ (p, q))
  /-- The page-turning isomorphism is characterized by the quotient maps from `Z_{r+1}`. -/
  filteredPageTurnIso_hom (r p q : ℤ) (hr : 2 ≤ r) :
    pageTurnCyclesLift r p q hr ≫ (filteredPage r hr).homologyπ (p, q) ≫
        (filteredPageTurnIso r p q hr).hom =
      filteredPageπ T F (r + 1) p q ≫
        (filteredPageObjectIso (r + 1) p q (by omega)).inv
  /-- The spectral-sequence transition is the canonical filtered-page transition. -/
  pageTurn_commutes (r p q : ℤ) (hr : 2 ≤ r) :
    HomologicalComplex.homologyMap (spectralSequencePageIso r hr).hom (p, q) ≫
        (filteredPageTurnIso r p q hr).hom =
      (spectralSequence.iso r (r + 1) (p, q) rfl hr).hom ≫
        (spectralSequencePageIso (r + 1) (by omega)).hom.f (p, q)
  /-- The canonical stable-page comparisons are isomorphisms. -/
  abuts : CanonicallyAbutsTo T F spectralSequence decreasing pageIso

section Filtrations

private theorem firstDegreeFiltration_antitone
    {R : Type u} [CommRing R] (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (bP bQ : ℤ) :
    ∀ p p' n : ℤ, p ≤ p' →
      firstDegreeFiltration P Q bP bQ p' n ≤ firstDegreeFiltration P Q bP bQ p n := by
  intro p p' n h
  classical
  unfold firstDegreeFiltration
  apply Finset.sup_mono
  intro i hi
  simp only [Finset.mem_Icc] at hi ⊢
  constructor
  · omega
  · exact hi.2

private theorem secondDegreeFiltration_antitone
    {R : Type u} [CommRing R] (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (bP bQ : ℤ) :
    ∀ p p' n : ℤ, p ≤ p' →
      secondDegreeFiltration P Q bP bQ p' n ≤ secondDegreeFiltration P Q bP bQ p n := by
  intro p p' n h
  classical
  unfold secondDegreeFiltration
  apply Finset.sup_mono
  intro j hj
  simp only [Finset.mem_Icc] at hj ⊢
  constructor
  · omega
  · exact hj.2

private theorem firstDegreeFiltration_eq_bot_of_bound
    {R : Type u} [CommRing R] (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (bP bQ p n : ℤ) (hp : bP < p) :
    firstDegreeFiltration P Q bP bQ p n = ⊥ := by
  classical
  unfold firstDegreeFiltration
  rw [Finset.Icc_eq_empty_of_lt (lt_of_lt_of_le hp (le_max_left p (n - bQ)))]
  simp

private theorem secondDegreeFiltration_eq_bot_of_bound
    {R : Type u} [CommRing R] (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (bP bQ p n : ℤ) (hp : bQ < p) :
    secondDegreeFiltration P Q bP bQ p n = ⊥ := by
  classical
  unfold secondDegreeFiltration
  rw [Finset.Icc_eq_empty_of_lt (lt_of_lt_of_le hp (le_max_left p (n - bP)))]
  simp

end Filtrations

section FilteredConstruction

variable (T : CochainComplex C ℤ) (F : ∀ _p n : ℤ, Subobject (T.X n))
  (hF : ∀ p p' n, p ≤ p' → F p' n ≤ F p n)

/-- Restrict the pages of a cohomological spectral sequence to those starting at two.

This is an `abbrev` on purpose: the identifications below are stated for the pages of the
restricted sequence and proved for the pages of the original one, so the restriction has to be
transparent to the unifier. -/
private abbrev eTwoSequence (E : CohomologicalSpectralSequence C 0) :
    E₂CohomologicalSpectralSequence C where
  page r hr := E.page r (by omega)
  iso r r' pq h hr := E.iso r r' pq h (by omega)

/-- The bidegree `(p + r, q + 1 - r)` is the successor of `(p, q)` on the `r`-th page. -/
private lemma pageShape_rel (r p q : ℤ) :
    (p, q) + (r, 1 - r) = ((p + r, q + 1 - r) : ℤ × ℤ) :=
  Prod.ext rfl (by simp only [Prod.snd_add]; ring)

/-- The classes of the `(r+1)`-cycles are killed by the `r`-th page differential: they factor
through the cycles of the `r`-th page, which the differential annihilates. -/
private lemma cycles_succ_comp_pageMap (r p n : ℤ) :
    (Subobject.ofLE _ _ (cycles_succ_le T F hF r p n) ≫ cokernel.π (den T F r p n)) ≫
      pageMap T F r p n = 0 := by
  have key : Subobject.ofLE _ _ (cycles_succ_le T F hF r p n) ≫ cokernel.π (den T F r p n) =
      (Subobject.ofLE _ _ (cyclesSucc_le_kernelNumerator T F hF r p n) ≫
          cokernel.π (Subobject.ofLE _ _ (den_le_kernelNumerator T F hF r p n))) ≫
        pageCyclesι T F hF r p n := by
    rw [Category.assoc, π_comp_pageCyclesι, ← Category.assoc, Subobject.ofLE_comp_ofLE]
  rw [key, Category.assoc, pageCyclesι_comp_pageMap, comp_zero]

/-- The version of `cycles_succ_comp_pageMap` stated for the differential of the page complex. -/
private lemma cycles_succ_comp_pageComplex_d (r p q : ℤ) :
    (Subobject.ofLE _ _ (cycles_succ_le T F hF r p (p + q)) ≫ filteredPageπ T F r p q) ≫
      (pageComplex T F r).d (p, q) (p + r, q + 1 - r) = 0 := by
  rw [pageComplex_d T F r (pq := (p, q)) (pq' := (p + r, q + 1 - r)) (pageShape_rel r p q),
    pageMap']
  simp only [← Category.assoc]
  -- the filtration hypothesis is a proof argument, so matching cannot recover it
  rw [cycles_succ_comp_pageMap T F hF r p (p + q), zero_comp]

/-- The canonical lift of `Z_{r+1}^{p,q}` to the cycles of the `r`-th page. -/
private noncomputable def pageTurnLift (r p q : ℤ) :
    (cycles T F (r + 1) p (p + q) : C) ⟶ (pageComplex T F r).cycles (p, q) :=
  (pageComplex T F r).liftCycles
    (Subobject.ofLE _ _ (cycles_succ_le T F hF r p (p + q)) ≫ filteredPageπ T F r p q)
    (p + r, q + 1 - r)
    (ComplexShape.next_eq' _ (by rw [ComplexShape.up'_Rel]; exact pageShape_rel r p q))
    (cycles_succ_comp_pageComplex_d T F hF r p q)

private lemma pageTurnLift_iCycles (r p q : ℤ) :
    pageTurnLift T F hF r p q ≫ (pageComplex T F r).iCycles (p, q) =
      Subobject.ofLE _ _ (cycles_succ_le T F hF r p (p + q)) ≫ filteredPageπ T F r p q :=
  HomologicalComplex.liftCycles_i ..

/-- The page turn sends the class of an `(r+1)`-cycle in the homology of the `r`-th page to its
class on the `(r+1)`-st page. -/
private lemma pageTurnLift_homologyπ (r p q : ℤ) :
    pageTurnLift T F hF r p q ≫ (pageComplex T F r).homologyπ (p, q) ≫
        (pageHomologyIso T F hF r (p, q)).hom =
      filteredPageπ T F (r + 1) p q := by
  simpa only [Category.id_comp] using
    homologyπ_comp_pageHomologyIso_hom T F hF r (p, q) (pageTurnLift T F hF r p q) (𝟙 _)
      (Subobject.ofLE _ _ (cycles_succ_le T F hF r p (p + q)))
      (by rw [Subobject.ofLE_arrow, Category.id_comp])
      (pageTurnLift_iCycles T F hF r p q)

private lemma pageTurnLift_homologyπ_epi (r p q : ℤ) :
    Epi (pageTurnLift T F hF r p q ≫ (pageComplex T F r).homologyπ (p, q)) := by
  have h : pageTurnLift T F hF r p q ≫ (pageComplex T F r).homologyπ (p, q) =
      filteredPageπ T F (r + 1) p q ≫ (pageHomologyIso T F hF r (p, q)).inv := by
    rw [← pageTurnLift_homologyπ T F hF r p q, Category.assoc, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [h]
  infer_instance

/-- The spectral sequence of a decreasing, differential-preserving filtration of a cochain
complex, assembled with a given stable-page comparison. -/
private noncomputable def associatedFiltrationSpectralSequence
    (hd : ∀ p n, (Subobject.exists (T.d n (n + 1))).obj (F p n) ≤ F p (n + 1))
    (h : CanonicallyAbutsTo T F (eTwoSequence (spectralSequence T F hF)) hF
      fun r p q hr ↦ eIso T F hF r p q (p + q) (by omega) rfl) :
    AssociatedFiltrationSpectralSequence T F where
  spectralSequence := eTwoSequence (spectralSequence T F hF)
  decreasing := hF
  differential_le := hd
  pageIso r p q hr := eIso T F hF r p q (p + q) (by omega) rfl
  filteredPage r _ := pageComplex T F r
  filteredPageObjectIso _ _ _ _ := Iso.refl _
  spectralSequencePageIso _ _ := Iso.refl _
  spectralSequencePageIso_hom r p q hr := by simp
  differential_commutes r p q hr := by
    refine ⟨deltaCycles' T F r p (p + q) (p + r) (p + r + (q + 1 - r)) rfl (by omega),
      (pageComplex T F r).d (p, q) (p + r, q + 1 - r),
      deltaCycles'_arrow T F r p (p + q) (p + r) (p + r + (q + 1 - r)) rfl (by omega), ?_, ?_⟩
    · rw [pageComplex_d T F r (pq := (p, q)) (pq' := (p + r, q + 1 - r)) (pageShape_rel r p q),
        π_comp_pageMap']
    · simp only [eIso_hom_rfl, Category.comp_id, Category.id_comp]
  filteredPageTurnIso r p q _ := pageHomologyIso T F hF r (p, q)
  pageTurnCyclesLift r p q _ := pageTurnLift T F hF r p q
  pageTurnCyclesLift_comm r p q _ := by
    simpa only [Iso.refl_inv, Category.comp_id] using pageTurnLift_iCycles T F hF r p q
  pageTurnCycles_epi r p q _ := pageTurnLift_homologyπ_epi T F hF r p q
  filteredPageTurnIso_hom r p q _ := by
    simpa only [Iso.refl_inv, Category.comp_id] using pageTurnLift_homologyπ T F hF r p q
  pageTurn_commutes r p q hr := by
    simp only [Iso.refl_hom, HomologicalComplex.homologyMap_id, Category.id_comp,
      HomologicalComplex.id_f, Category.comp_id]
  abuts := h

end FilteredConstruction

section StablePages

open CategoryTheory.Preadditive

set_option backward.isDefEq.respectTransparency false

/-- A cycle represents a class coming from `V` precisely when it differs from a cycle in `V` by a
boundary. -/
private lemma homologyClass_factors_iff (S : ShortComplex C)
    (V : Subobject S.cycles) {A : C} (c : A ⟶ S.cycles) :
    (imageSubobject (V.arrow ≫ S.homologyπ)).Factors (c ≫ S.homologyπ) ↔
      (imageSubobject S.f ⊔ imageSubobject (V.arrow ≫ S.iCycles)).Factors
        (c ≫ S.iCycles) := by
  constructor
  · intro h
    obtain ⟨A', e, he, x, hx⟩ := (Subobject.imageSubobject_factors_iff _ _).1 h
    have hzero : (e ≫ c - x ≫ V.arrow) ≫ S.homologyπ = 0 := by
      rw [sub_comp, Category.assoc, Category.assoc, hx, sub_self]
    obtain ⟨A'', e', he', y, hy⟩ :=
      (CokernelCofork.IsColimit.comp_π_eq_zero_iff_up_to_refinements
        S.homologyIsCokernel _).1 hzero
    apply Subobject.factors_of_epi_comp (e' ≫ e)
    have hc : (e' ≫ e) ≫ c ≫ S.iCycles =
        y ≫ S.f + (e' ≫ x) ≫ V.arrow ≫ S.iCycles := by
      have hh := congrArg (fun f ↦ f ≫ S.iCycles) hy
      simp only [comp_sub, sub_comp, Category.assoc, S.toCycles_i] at hh
      simp only [Category.assoc]
      exact sub_eq_iff_eq_add.mp hh
    rw [hc]
    exact Subobject.factors_add _ _
      (Subobject.sup_factors_of_factors_left (imageSubobject_factors_comp_self S.f y))
      (Subobject.sup_factors_of_factors_right
        (imageSubobject_factors_comp_self (V.arrow ≫ S.iCycles) (e' ≫ x)))
  · intro h
    obtain ⟨A', e, he, x, y, hxy⟩ := Subobject.exists_refinement_of_factors_sup _ h
    have hxzero : (imageSubobject S.f).arrow ≫ S.g = 0 :=
      imageSubobject_arrow_comp_eq_zero S.zero
    let x' := S.liftCycles (imageSubobject S.f).arrow hxzero
    have hx' : x' ≫ S.homologyπ = 0 := by
      apply (cancel_epi (factorThruImageSubobject S.f)).1
      rw [comp_zero, ← Category.assoc]
      have hf : factorThruImageSubobject S.f ≫ x' = S.toCycles := by
        apply (cancel_mono S.iCycles).1
        simp only [Category.assoc, x', S.liftCycles_i, imageSubobject_arrow_comp, S.toCycles_i]
      rw [hf, S.toCycles_comp_homologyπ]
    obtain ⟨A'', e', he', y', hy'⟩ :=
      (Subobject.imageSubobject_factors_iff (V.arrow ≫ S.iCycles) _).1
        (Subobject.factors_comp_arrow y)
    have hc : (e' ≫ e) ≫ c = (e' ≫ x) ≫ x' + y' ≫ V.arrow := by
      apply (cancel_mono S.iCycles).1
      simp only [add_comp, Category.assoc, x', S.liftCycles_i]
      rw [hxy, comp_add, hy']
    apply Subobject.factors_of_epi_comp (e' ≫ e)
    rw [← Category.assoc, hc, add_comp, Category.assoc, hx', comp_zero, zero_add,
      Category.assoc]
    exact imageSubobject_factors_comp_self (V.arrow ≫ S.homologyπ) y'

/-- The projection of a subobject onto its image under a morphism. -/
private noncomputable def subobjectImageProjection {X Y : C} (f : X ⟶ Y)
    (P : Subobject X) : (P : C) ⟶ ((Subobject.exists f).obj P : C) :=
  ((Subobject.exists f).obj P).factorThru (P.arrow ≫ f) (Subobject.factors_arrow_comp f P)

private lemma subobjectImageProjection_arrow {X Y : C} (f : X ⟶ Y) (P : Subobject X) :
    subobjectImageProjection f P ≫ ((Subobject.exists f).obj P).arrow = P.arrow ≫ f :=
  Subobject.factorThru_arrow _ _ _

private lemma subobjectImageProjection_epi {X Y : C} (f : X ⟶ Y) (P : Subobject X) :
    Epi (subobjectImageProjection f P) := by
  rw [epi_iff_surjective_up_to_refinements]
  intro A y
  obtain ⟨A', e, he, x, hx⟩ := (Subobject.exists_factors_iff f P _).1
    (Subobject.factors_comp_arrow y)
  refine ⟨A', e, he, x, ?_⟩
  apply (cancel_mono ((Subobject.exists f).obj P).arrow).1
  simpa only [Category.assoc, subobjectImageProjection_arrow] using hx

private lemma filteredCocycles_factors (T : CochainComplex C ℤ)
    (F : ∀ _p n : ℤ, Subobject (T.X n)) (r p q : ℤ) :
    (cycles T F r p (p + q)).Factors
      (((Subobject.pullback (T.iCycles (p + q))).obj (F p (p + q))).arrow ≫
        T.iCycles (p + q)) := by
  apply cycles_factors
  · exact (pullback_factors_iff _ _ _).1 (Subobject.factors_self _)
  · rw [Category.assoc, T.iCycles_d, comp_zero]
    exact Subobject.factors_zero

/-- The actual cocycles lying in `F^p` are cycles on every page. -/
private noncomputable def filteredCocyclesToCycles (T : CochainComplex C ℤ)
    (F : ∀ _p n : ℤ, Subobject (T.X n)) (r p q : ℤ) :
    ((Subobject.pullback (T.iCycles (p + q))).obj (F p (p + q)) : C) ⟶
      (cycles T F r p (p + q) : C) :=
  (cycles T F r p (p + q)).factorThru _ (filteredCocycles_factors T F r p q)

private lemma filteredCocyclesToCycles_arrow (T : CochainComplex C ℤ)
    (F : ∀ _p n : ℤ, Subobject (T.X n)) (r p q : ℤ) :
    filteredCocyclesToCycles T F r p q ≫ (cycles T F r p (p + q)).arrow =
      ((Subobject.pullback (T.iCycles (p + q))).obj (F p (p + q))).arrow ≫
        T.iCycles (p + q) :=
  Subobject.factorThru_arrow _ _ _

/-- Once `F^{p+r}` has vanished in degree `n + 1`, the `r`-cycles are the actual cocycles in
`F^p`. -/
private lemma filteredCocyclesToCycles_isIso (T : CochainComplex C ℤ)
    (F : ∀ _p n : ℤ, Subobject (T.X n)) (r p q : ℤ)
    (h : F (p + r) (p + q + 1) = ⊥) :
    IsIso (filteredCocyclesToCycles T F r p q) := by
  let V := (Subobject.pullback (T.iCycles (p + q))).obj (F p (p + q))
  let Z := cycles T F r p (p + q)
  have hz : Z.arrow ≫ T.d (p + q) (p + q + 1) = 0 := by
    apply (Subobject.bot_factors_iff_zero _).mp
    rw [← h]
    exact (Subobject.le_pullback_iff _ _ _).1 inf_le_right
  let z := T.liftCycles Z.arrow (p + q + 1) (ComplexShape.next_eq' _ rfl) hz
  have hf : V.Factors z := by
    apply (pullback_factors_iff _ _ _).2
    rw [HomologicalComplex.liftCycles_i]
    exact Subobject.factors_of_le _ (cycles_le_F T F r p (p + q))
      (Subobject.factors_self Z)
  let b := V.factorThru z hf
  refine ⟨⟨b, ?_, ?_⟩⟩
  · apply (cancel_mono (V.arrow ≫ T.iCycles (p + q))).1
    simp only [Category.assoc, b, Subobject.factorThru_arrow_assoc, z,
      HomologicalComplex.liftCycles_i, Category.id_comp]
    exact filteredCocyclesToCycles_arrow T F r p q
  · apply (cancel_mono Z.arrow).1
    rw [Category.assoc, filteredCocyclesToCycles_arrow, ← Category.assoc,
      Subobject.factorThru_arrow, HomologicalComplex.liftCycles_i, Category.id_comp]

private lemma cycles_eq_image_filteredCocycles (T : CochainComplex C ℤ)
    (F : ∀ _p n : ℤ, Subobject (T.X n)) (r p q : ℤ)
    (h : F (p + r) (p + q + 1) = ⊥) :
    cycles T F r p (p + q) =
      imageSubobject
        (((Subobject.pullback (T.iCycles (p + q))).obj (F p (p + q))).arrow ≫
          T.iCycles (p + q)) := by
  have := filteredCocyclesToCycles_isIso T F r p q h
  rw [imageSubobject_mono, ← Subobject.mk_arrow (cycles T F r p (p + q))]
  exact (Subobject.mk_eq_mk_of_comm _ _ (asIso (filteredCocyclesToCycles T F r p q))
    (filteredCocyclesToCycles_arrow T F r p q)).symm

private lemma exists_pullback_eq_inf {X Y : C} (f : X ⟶ Y) (P : Subobject Y) :
    (Subobject.exists f).obj ((Subobject.pullback f).obj P) = imageSubobject f ⊓ P := by
  apply le_antisymm
  · apply le_inf
    · rw [Subobject.exists_eq_imageSubobject]
      exact imageSubobject_comp_le _ _
    · exact (Subobject.exists_le_iff_le_pullback _ _ _).2 le_rfl
  · apply Subobject.le_of_factors
    let B := imageSubobject f ⊓ P
    obtain ⟨A, e, he, x, hx⟩ := (Subobject.imageSubobject_factors_iff f B.arrow).1
      (Subobject.factors_of_le _ inf_le_left (Subobject.factors_self B))
    have hf : ((Subobject.pullback f).obj P).Factors x := by
      apply (pullback_factors_iff _ _ _).2
      rw [← hx]
      exact Subobject.factors_of_factors_right _
        (Subobject.factors_of_le _ inf_le_right (Subobject.factors_self B))
    apply (Subobject.exists_factors_iff _ _ _).2
    refine ⟨A, e, he, ((Subobject.pullback f).obj P).factorThru x hf, ?_⟩
    rwa [← Category.assoc, Subobject.factorThru_arrow]

/-- On a stable page the boundaries are the cocycles of the next filtration step together with
the actual boundaries of `T`, cut down to `F^p`. -/
private lemma stable_boundaries_eq (T : CochainComplex C ℤ)
    (F : ∀ _p n : ℤ, Subobject (T.X n))
    (hF : ∀ p p' n, p ≤ p' → F p' n ≤ F p n) (r p q : ℤ)
    (hbot : F (p + r) (p + q + 1) = ⊥)
    (htop : F (p - r + 1) (p + q - 1) = ⊤) :
    boundaries T F r p (p + q) =
      (imageSubobject
        (((Subobject.pullback (T.iCycles (p + q))).obj (F (p + 1) (p + q))).arrow ≫
          T.iCycles (p + q)) ⊔ imageSubobject (T.d (p + q - 1) (p + q))) ⊓ F p (p + q) := by
  have hcycles : cycles T F (r - 1) (p + 1) (p + q) =
      imageSubobject
        (((Subobject.pullback (T.iCycles (p + q))).obj (F (p + 1) (p + q))).arrow ≫
          T.iCycles (p + q)) := by
    have hh := cycles_eq_image_filteredCocycles T F (r - 1) (p + 1) (q - 1)
      (by
        rw [show p + 1 + (r - 1) = p + r by omega,
          show p + 1 + (q - 1) + 1 = p + q + 1 by omega]
        exact hbot)
    rwa [show p + 1 + (q - 1) = p + q by omega] at hh
  have hle : imageSubobject
      (((Subobject.pullback (T.iCycles (p + q))).obj (F (p + 1) (p + q))).arrow ≫
        T.iCycles (p + q)) ≤ F p (p + q) := by
    rw [← hcycles]
    exact (cycles_le_F T F (r - 1) (p + 1) (p + q)).trans
      (hF p (p + 1) (p + q) (by omega))
  rw [boundaries, hcycles, cycles, htop, top_inf_eq,
    show p - r + 1 + (r - 1) = p by omega,
    show p + q - 1 + 1 = p + q by omega, exists_pullback_eq_inf,
    sup_inf_assoc_of_le _ hle]

/-- On a stable page the quotient of filtered cocycles is the associated graded of cohomology,
compatibly with both canonical quotient maps. -/
private lemma exists_stablePageIso (T : CochainComplex C ℤ)
    (F : ∀ _p n : ℤ, Subobject (T.X n))
    (hF : ∀ p p' n, p ≤ p' → F p' n ≤ F p n) (r p q : ℤ)
    (hbot : F (p + r) (p + q + 1) = ⊥)
    (htop : F (p - r + 1) (p + q - 1) = ⊤) :
    ∃ e : inducedHomologyGradedPiece T F hF p (p + q) ≅ filteredPageObject T F r p q,
      subobjectImageProjection (T.homologyπ (p + q))
          ((Subobject.pullback (T.iCycles (p + q))).obj (F p (p + q))) ≫
        inducedHomologyGradedπ T F hF p (p + q) ≫ e.hom =
      filteredCocyclesToCycles T F r p q ≫ filteredPageπ T F r p q := by
  let V := (Subobject.pullback (T.iCycles (p + q))).obj (F p (p + q))
  let W := (Subobject.pullback (T.iCycles (p + q))).obj (F (p + 1) (p + q))
  let a := filteredCocyclesToCycles T F r p q
  let b := subobjectImageProjection (T.homologyπ (p + q)) V
  let u := b ≫ inducedHomologyGradedπ T F hF p (p + q)
  let v := a ≫ filteredPageπ T F r p q
  have : Epi b := subobjectImageProjection_epi _ _
  have : IsIso a := filteredCocyclesToCycles_isIso T F r p q hbot
  have : Epi (inducedHomologyGradedπ T F hF p (p + q)) := by
    dsimp only [inducedHomologyGradedπ, inducedHomologyGradedPiece]
    infer_instance
  have : Epi u := by dsimp only [u]; infer_instance
  have : Epi v := by dsimp only [v]; infer_instance
  have hprev : (ComplexShape.up ℤ).prev (p + q) = p + q - 1 := by
    apply ComplexShape.prev_eq'
    change p + q - 1 + 1 = p + q
    omega
  have him : imageSubobject (T.sc (p + q)).f =
      imageSubobject (T.d (p + q - 1) (p + q)) := by
    change imageSubobject (T.d ((ComplexShape.up ℤ).prev (p + q)) (p + q)) = _
    rw [hprev]
  have hker : ∀ {A : C} (g : A ⟶ (V : C)), g ≫ u = 0 ↔ g ≫ v = 0 := by
    intro A g
    have hcZ : (cycles T F r p (p + q)).Factors
        (g ≫ V.arrow ≫ T.iCycles (p + q)) := by
      rw [← filteredCocyclesToCycles_arrow, ← Category.assoc]
      exact Subobject.factors_comp_arrow _
    have hcF : (F p (p + q)).Factors (g ≫ V.arrow ≫ T.iCycles (p + q)) :=
      Subobject.factors_of_le _ (cycles_le_F T F r p (p + q)) hcZ
    have hchar := homologyClass_factors_iff (T.sc (p + q)) W (g ≫ V.arrow)
    rw [him, sup_comm] at hchar
    dsimp only [u, v, inducedHomologyGradedπ, filteredPageπ, den, inducedHomologyFiltration]
    rw [← Category.assoc, Subobject.comp_cokernel_π_eq_zero_iff _ (Subobject.ofLE_arrow _),
      ← Category.assoc, Subobject.comp_cokernel_π_eq_zero_iff _ (Subobject.ofLE_arrow _)]
    simp only [Category.assoc, b, subobjectImageProjection_arrow,
      a, filteredCocyclesToCycles_arrow]
    rw [Subobject.exists_eq_imageSubobject]
    rw [show (imageSubobject (W.arrow ≫ T.homologyπ (p + q))).Factors
        (g ≫ V.arrow ≫ T.homologyπ (p + q)) ↔
      (imageSubobject (W.arrow ≫ T.iCycles (p + q)) ⊔
        imageSubobject (T.d (p + q - 1) (p + q))).Factors
          (g ≫ V.arrow ≫ T.iCycles (p + q)) from by
      simpa only [Category.assoc, HomologicalComplex.homologyπ,
        HomologicalComplex.iCycles] using hchar]
    rw [stable_boundaries_eq T F hF r p q hbot htop,
      Subobject.inf_factors, Subobject.inf_factors]
    exact ⟨fun h ↦ ⟨⟨h, hcF⟩, hcZ⟩, fun h ↦ h.1.1⟩
  obtain ⟨e, he⟩ := Subobject.exists_iso_of_epi_of_kernel u v
    ((hker (kernel.ι u)).1 (kernel.condition u))
    ((hker (kernel.ι v)).2 (kernel.condition v))
  exact ⟨e, by simpa only [u, v, Category.assoc] using he⟩

private lemma filteredPageObject_isZero_of_cycles_le_boundaries (T : CochainComplex C ℤ)
    (F : ∀ _p n : ℤ, Subobject (T.X n)) (r p q : ℤ)
    (h : cycles T F r p (p + q) ≤ boundaries T F r p (p + q)) :
    IsZero (filteredPageObject T F r p q) := by
  have hπ : filteredPageπ T F r p q = 0 := by
    have hh := (Subobject.comp_cokernel_π_eq_zero_iff
      (den T F r p (p + q)) (Subobject.ofLE_arrow _) (𝟙 _)).2
        (by
          simpa only [Category.id_comp] using
            Subobject.factors_of_le _ (le_inf h le_rfl)
              (Subobject.factors_self (cycles T F r p (p + q))))
    simpa only [Category.id_comp] using hh
  rw [IsZero.iff_id_eq_zero]
  apply (cancel_epi (filteredPageπ T F r p q)).1
  simp only [Category.comp_id, comp_zero, hπ]

private lemma filteredPageObject_isZero_of_eq_bot (T : CochainComplex C ℤ)
    (F : ∀ _p n : ℤ, Subobject (T.X n)) (r p q : ℤ) (h : F p (p + q) = ⊥) :
    IsZero (filteredPageObject T F r p q) := by
  apply filteredPageObject_isZero_of_cycles_le_boundaries
  exact (cycles_le_F T F r p (p + q)).trans (by rw [h]; exact bot_le)

private lemma filteredPageObject_isZero_of_succ_eq_top (T : CochainComplex C ℤ)
    (F : ∀ _p n : ℤ, Subobject (T.X n)) (r p q : ℤ) (h : F (p + 1) (p + q) = ⊤) :
    IsZero (filteredPageObject T F r p q) := by
  apply filteredPageObject_isZero_of_cycles_le_boundaries
  apply le_trans (b := cycles T F (r - 1) (p + 1) (p + q))
  · simp only [cycles, h, top_inf_eq, show p + 1 + (r - 1) = p + r by omega]
    exact inf_le_right
  · exact le_sup_left

/-- A degreewise finite decreasing filtration abuts canonically: on every sufficiently late page
the incoming and outgoing differentials vanish and the canonical comparison from the associated
graded of the induced cohomology filtration is an isomorphism. -/
private lemma canonicallyAbutsTo_of_finite (T : CochainComplex C ℤ)
    (F : ∀ _p n : ℤ, Subobject (T.X n))
    (hF : ∀ p p' n, p ≤ p' → F p' n ≤ F p n)
    (hfinite : ∀ n, ∃ lo hi : ℤ, F lo n = ⊤ ∧ F hi n = ⊥)
    (E : E₂CohomologicalSpectralSequence C) (e : PageIdentifications T F E) :
    CanonicallyAbutsTo T F E hF e := by
  intro p q
  obtain ⟨lo, _, hlo, _⟩ := hfinite (p + q - 1)
  obtain ⟨_, hi, _, hhi⟩ := hfinite (p + q + 1)
  refine ⟨max 2 (max (hi - p) (p + 1 - lo)), le_max_left _ _, ?_⟩
  intro r hr hbound
  have hbot : F (p + r) (p + q + 1) = ⊥ := by
    apply le_bot_iff.mp
    rw [← hhi]
    exact hF hi (p + r) (p + q + 1) (by omega)
  have htop : F (p - r + 1) (p + q - 1) = ⊤ := by
    apply top_le_iff.mp
    rw [← hlo]
    exact hF (p - r + 1) lo (p + q - 1) (by omega)
  have hout : IsZero ((E.page r hr).X (p + r, q + 1 - r)) := by
    apply IsZero.of_iso _ (e r (p + r) (q + 1 - r) hr)
    apply filteredPageObject_isZero_of_eq_bot
    rw [show p + r + (q + 1 - r) = p + q + 1 by omega]
    exact hbot
  have hin : IsZero ((E.page r hr).X (p - r, q + r - 1)) := by
    apply IsZero.of_iso _ (e r (p - r) (q + r - 1) hr)
    apply filteredPageObject_isZero_of_succ_eq_top
    rw [show p - r + (q + r - 1) = p + q - 1 by omega]
    exact htop
  refine ⟨hout.eq_of_tgt _ _, hin.eq_of_src _ _, ?_⟩
  obtain ⟨comparison, hc⟩ := exists_stablePageIso T F hF r p q hbot htop
  refine ⟨comparison.hom ≫ (e r p q hr).inv, filteredCocyclesToCycles T F r p q,
    subobjectImageProjection (T.homologyπ (p + q))
      ((Subobject.pullback (T.iCycles (p + q))).obj (F p (p + q))),
    inferInstance, filteredCocyclesToCycles_arrow T F r p q,
    subobjectImageProjection_arrow _ _, ?_⟩
  simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ (e r p q hr).inv) hc

/-- **The spectral sequence of a degreewise finite filtration.** A decreasing filtration of a
cochain complex which is preserved by the differential and is finite in every degree has an
`AssociatedFiltrationSpectralSequence`: the canonical subquotient pages, the differentials induced
by `d`, the page turns pinned by the classes of `(r+1)`-cycles, and the canonical isomorphism from
`gr^p H^n` to the stable page. -/
@[no_expose] public noncomputable def associatedSpectralSequenceOfFiniteFiltration
    (T : CochainComplex C ℤ) (F : ∀ _p n : ℤ, Subobject (T.X n))
    (hF : ∀ p p' n, p ≤ p' → F p' n ≤ F p n)
    (hd : ∀ p n, (Subobject.exists (T.d n (n + 1))).obj (F p n) ≤ F p (n + 1))
    (hfinite : ∀ n, ∃ lo hi : ℤ, F lo n = ⊤ ∧ F hi n = ⊥) :
    AssociatedFiltrationSpectralSequence T F :=
  associatedFiltrationSpectralSequence T F hF hd
    (canonicallyAbutsTo_of_finite T F hF hfinite _ _)

end StablePages

section TensorFiltrations

open CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
  (bP bQ : ℤ) [P.IsStrictlyLE bP] [Q.IsStrictlyLE bQ]

/-- The degreewise tensor-product double complex of `P` and `Q`, whose total complex is
`P ⊗ Q`. -/
private abbrev tensorDouble :
    HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (((curriedTensor (ModuleCat.{u} R)).mapBifunctorHomologicalComplex
    (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj P).obj Q

private lemma tensorTerm_isZero_of_bound (i j : ℤ) (h : bP < i ∨ bQ < j) :
    IsZero (P.X i ⊗ Q.X j) := by
  rcases h with h | h
  · exact (tensorRight (Q.X j)).map_isZero (P.isZero_of_isStrictlyLE bP i h)
  · exact (tensorLeft (P.X i)).map_isZero (Q.isZero_of_isStrictlyLE bQ j h)

/-- The image of a summand inclusion vanishes, hence is below any subobject, outside the bounds. -/
private lemma image_ιTensorObj_le_of_bound (i j n : ℤ) (h : i + j = n) (hb : bP < i ∨ bQ < j)
    (S : Subobject ((P ⊗ Q).X n)) :
    imageSubobject (HomologicalComplex.ιTensorObj P Q i j n h) ≤ S := by
  rw [(tensorTerm_isZero_of_bound P Q bP bQ i j hb).eq_of_src
    (HomologicalComplex.ιTensorObj P Q i j n h) 0]
  simp

/-- A subobject containing the image of a summand inclusion has that inclusion factor through
it. -/
private lemma factors_ιTensorObj_of_image_le (i j n : ℤ) (h : i + j = n)
    (S : Subobject ((P ⊗ Q).X n))
    (hS : imageSubobject (HomologicalComplex.ιTensorObj P Q i j n h) ≤ S) :
    S.Factors (HomologicalComplex.ιTensorObj P Q i j n h) :=
  Subobject.factors_of_le _ hS (by simpa only [Category.id_comp] using
    imageSubobject_factors_comp_self (HomologicalComplex.ιTensorObj P Q i j n h) (𝟙 _))

private lemma image_ιTensorObj_le_firstDegreeFiltration (p i j n : ℤ) (h : i + j = n)
    (hi : p ≤ i) :
    imageSubobject (HomologicalComplex.ιTensorObj P Q i j n h) ≤
      firstDegreeFiltration P Q bP bQ p n := by
  classical
  by_cases hb : i ≤ bP ∧ j ≤ bQ
  · have hj : j = n - i := by omega
    subst hj
    unfold firstDegreeFiltration
    exact Finset.le_sup (s := Finset.Icc (max p (n - bQ)) bP)
      (f := fun k : ℤ ↦ imageSubobject (HomologicalComplex.ιTensorObj P Q k (n - k) n (by omega)))
      (b := i) (by simp only [Finset.mem_Icc]; omega)
  · exact image_ιTensorObj_le_of_bound P Q bP bQ i j n h (by omega) _

private lemma image_ιTensorObj_le_secondDegreeFiltration (p i j n : ℤ) (h : i + j = n)
    (hj : p ≤ j) :
    imageSubobject (HomologicalComplex.ιTensorObj P Q i j n h) ≤
      secondDegreeFiltration P Q bP bQ p n := by
  classical
  by_cases hb : i ≤ bP ∧ j ≤ bQ
  · have hi : i = n - j := by omega
    subst hi
    unfold secondDegreeFiltration
    exact Finset.le_sup (s := Finset.Icc (max p (n - bP)) bQ)
      (f := fun k : ℤ ↦ imageSubobject (HomologicalComplex.ιTensorObj P Q (n - k) k n (by omega)))
      (b := j) (by simp only [Finset.mem_Icc]; omega)
  · exact image_ιTensorObj_le_of_bound P Q bP bQ i j n h (by omega) _

private lemma tensorSubobject_eq_top (n : ℤ) (S : Subobject ((P ⊗ Q).X n))
    (hS : ∀ (i j : ℤ) (h : i + j = n),
      imageSubobject (HomologicalComplex.ιTensorObj P Q i j n h) ≤ S) : S = ⊤ := by
  have : Epi S.arrow := ⟨by
    intro A f g hfg
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro i j hij
    have hf := factors_ιTensorObj_of_image_le P Q i j n hij S (hS i j hij)
    change HomologicalComplex.ιTensorObj P Q i j n hij ≫ f =
      HomologicalComplex.ιTensorObj P Q i j n hij ≫ g
    rw [← S.factorThru_arrow _ hf, Category.assoc, Category.assoc, hfg]⟩
  have : IsIso S.arrow := isIso_of_mono_of_epi _
  exact Subobject.eq_top_of_isIso_arrow S

private lemma firstDegreeFiltration_eq_top (n : ℤ) :
    firstDegreeFiltration P Q bP bQ (n - bQ) n = ⊤ := by
  apply tensorSubobject_eq_top
  intro i j h
  by_cases hi : n - bQ ≤ i
  · exact image_ιTensorObj_le_firstDegreeFiltration P Q bP bQ (n - bQ) i j n h hi
  · exact image_ιTensorObj_le_of_bound P Q bP bQ i j n h (Or.inr (by omega)) _

private lemma secondDegreeFiltration_eq_top (n : ℤ) :
    secondDegreeFiltration P Q bP bQ (n - bP) n = ⊤ := by
  apply tensorSubobject_eq_top
  intro i j h
  by_cases hj : n - bP ≤ j
  · exact image_ιTensorObj_le_secondDegreeFiltration P Q bP bQ (n - bP) i j n h hj
  · exact image_ιTensorObj_le_of_bound P Q bP bQ i j n h (Or.inl (by omega)) _

private lemma tensorDifferential_factors (i j n : ℤ) (h : i + j = n)
    (S : Subobject ((P ⊗ Q).X (n + 1)))
    (h₁ : S.Factors (HomologicalComplex.ιTensorObj P Q (i + 1) j (n + 1) (by omega)))
    (h₂ : S.Factors (HomologicalComplex.ιTensorObj P Q i (j + 1) (n + 1) (by omega))) :
    S.Factors (HomologicalComplex.ιTensorObj P Q i j n h ≫ (P ⊗ Q).d n (n + 1)) := by
  change S.Factors (HomologicalComplex.ιMapBifunctor P Q (curriedTensor _) _ i j n h ≫
    (HomologicalComplex.mapBifunctor P Q (curriedTensor _) _).d n (n + 1))
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
    HomologicalComplex.mapBifunctor.d₁_eq P Q (curriedTensor _) _
      (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl) j (n + 1)
      (by change i + 1 + j = n + 1; omega),
    HomologicalComplex.mapBifunctor.d₂_eq P Q (curriedTensor _) _ i
      (show (ComplexShape.up ℤ).Rel j (j + 1) from rfl) (n + 1)
      (by change i + (j + 1) = n + 1; omega)]
  apply Subobject.factors_add
  · rw [Units.smul_def, ← Preadditive.zsmul_comp]
    exact Subobject.factors_of_factors_right _ h₁
  · rw [Units.smul_def, ← Preadditive.zsmul_comp]
    exact Subobject.factors_of_factors_right _ h₂

/-- A summand inclusion whose composite with the differential factors through `S` has image
below the pullback of `S` along the differential. -/
private lemma image_ιTensorObj_le_pullback_differential (i j n : ℤ) (h : i + j = n)
    (S : Subobject ((P ⊗ Q).X (n + 1)))
    (hf : S.Factors (HomologicalComplex.ιTensorObj P Q i j n h ≫ (P ⊗ Q).d n (n + 1))) :
    imageSubobject (HomologicalComplex.ιTensorObj P Q i j n h) ≤
      (Subobject.pullback ((P ⊗ Q).d n (n + 1))).obj S :=
  imageSubobject_le _ (((Subobject.pullback ((P ⊗ Q).d n (n + 1))).obj S).factorThru _
    ((pullback_factors_iff _ _ _).2 hf)) (Subobject.factorThru_arrow _ _ _)

private lemma firstDegreeFiltration_differential_le (p n : ℤ) :
    (Subobject.exists ((P ⊗ Q).d n (n + 1))).obj
        (firstDegreeFiltration P Q bP bQ p n) ≤
      firstDegreeFiltration P Q bP bQ p (n + 1) := by
  classical
  rw [Subobject.exists_le_iff_le_pullback]
  apply Finset.sup_le
  intro i hi
  have hip : p ≤ i := le_of_max_le_left (Finset.mem_Icc.1 hi).1
  let S := firstDegreeFiltration P Q bP bQ p (n + 1)
  have hf : S.Factors (HomologicalComplex.ιTensorObj P Q i (n - i) n (by omega) ≫
      (P ⊗ Q).d n (n + 1)) := by
    apply tensorDifferential_factors
    · exact factors_ιTensorObj_of_image_le P Q _ _ _ (by omega) S
        (image_ιTensorObj_le_firstDegreeFiltration P Q bP bQ p (i + 1) (n - i)
          (n + 1) (by omega) (by omega))
    · exact factors_ιTensorObj_of_image_le P Q _ _ _ (by omega) S
        (image_ιTensorObj_le_firstDegreeFiltration P Q bP bQ p i (n - i + 1)
          (n + 1) (by omega) hip)
  exact image_ιTensorObj_le_pullback_differential P Q i (n - i) n (by omega) S hf

private lemma secondDegreeFiltration_differential_le (p n : ℤ) :
    (Subobject.exists ((P ⊗ Q).d n (n + 1))).obj
        (secondDegreeFiltration P Q bP bQ p n) ≤
      secondDegreeFiltration P Q bP bQ p (n + 1) := by
  classical
  rw [Subobject.exists_le_iff_le_pullback]
  apply Finset.sup_le
  intro j hj
  have hjp : p ≤ j := le_of_max_le_left (Finset.mem_Icc.1 hj).1
  let S := secondDegreeFiltration P Q bP bQ p (n + 1)
  have hf : S.Factors (HomologicalComplex.ιTensorObj P Q (n - j) j n (by omega) ≫
      (P ⊗ Q).d n (n + 1)) := by
    apply tensorDifferential_factors
    · exact factors_ιTensorObj_of_image_le P Q _ _ _ (by omega) S
        (image_ιTensorObj_le_secondDegreeFiltration P Q bP bQ p (n - j + 1) j
          (n + 1) (by omega) hjp)
    · exact factors_ιTensorObj_of_image_le P Q _ _ _ (by omega) S
        (image_ιTensorObj_le_secondDegreeFiltration P Q bP bQ p (n - j) (j + 1)
          (n + 1) (by omega) (by omega))
  exact image_ιTensorObj_le_pullback_differential P Q (n - j) j n (by omega) S hf

/-- The filtration by the degree in `P` is the filtration of the total complex of the
tensor-product double complex by its first coordinate. -/
private lemma firstDegreeFiltration_eq_stepSubobject (p n : ℤ) :
    firstDegreeFiltration P Q bP bQ p n =
      HomologicalComplex₂.stepSubobject (tensorDouble P Q) (fun i (_ : ℤ) ↦ i) p n := by
  classical
  apply le_antisymm
  · apply Finset.sup_le
    intro i hi
    simp only [Finset.mem_Icc, max_le_iff] at hi
    exact HomologicalComplex₂.imageSubobject_ιTotal_le_totalProjector
      (K := tensorDouble P Q) _ i (n - i) n (by omega) hi.1.1
  · exact HomologicalComplex₂.totalProjector_le_of_forall (K := tensorDouble P Q) _ n _
      fun i j h hp ↦ image_ιTensorObj_le_firstDegreeFiltration P Q bP bQ p i j n h hp

/-- The filtration by the degree in `Q` is the filtration of the total complex of the
tensor-product double complex by its second coordinate. -/
private lemma secondDegreeFiltration_eq_stepSubobject (p n : ℤ) :
    secondDegreeFiltration P Q bP bQ p n =
      HomologicalComplex₂.stepSubobject (tensorDouble P Q) (fun (_ : ℤ) j ↦ j) p n := by
  classical
  apply le_antisymm
  · apply Finset.sup_le
    intro j hj
    simp only [Finset.mem_Icc, max_le_iff] at hj
    exact HomologicalComplex₂.imageSubobject_ιTotal_le_totalProjector
      (K := tensorDouble P Q) _ (n - j) j n (by omega) hj.1.1
  · exact HomologicalComplex₂.totalProjector_le_of_forall (K := tensorDouble P Q) _ n _
      fun i j h hp ↦ image_ιTensorObj_le_secondDegreeFiltration P Q bP bQ p i j n h hp

/-- The convergent spectral sequence of the filtration by degree in the first complex. -/
private noncomputable def firstTensorSpectralSequence :
    AssociatedFiltrationSpectralSequence (P ⊗ Q) (firstDegreeFiltration P Q bP bQ) :=
  associatedSpectralSequenceOfFiniteFiltration (P ⊗ Q) (firstDegreeFiltration P Q bP bQ)
    (firstDegreeFiltration_antitone P Q bP bQ)
    (firstDegreeFiltration_differential_le P Q bP bQ)
    (fun n ↦ ⟨n - bQ, bP + 1, firstDegreeFiltration_eq_top P Q bP bQ n,
      firstDegreeFiltration_eq_bot_of_bound P Q bP bQ (bP + 1) n (by omega)⟩)

/-- The convergent spectral sequence of the filtration by degree in the second complex. -/
private noncomputable def secondTensorSpectralSequence :
    AssociatedFiltrationSpectralSequence (P ⊗ Q) (secondDegreeFiltration P Q bP bQ) :=
  associatedSpectralSequenceOfFiniteFiltration (P ⊗ Q) (secondDegreeFiltration P Q bP bQ)
    (secondDegreeFiltration_antitone P Q bP bQ)
    (secondDegreeFiltration_differential_le P Q bP bQ)
    (fun n ↦ ⟨n - bP, bQ + 1, secondDegreeFiltration_eq_top P Q bP bQ n,
      secondDegreeFiltration_eq_bot_of_bound P Q bP bQ (bQ + 1) n (by omega)⟩)

end TensorFiltrations

section SecondPages

open CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex
open FilteredComplexSpectralSequence Opposite

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- The vertical cohomology of the tensor double complex, for a complex of flat modules in the
first variable: `H^q_{II}(P ⊗ Q)^p = P^p ⊗ H^q(Q)`. -/
private noncomputable def tensorVerticalHomologyIso
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    [∀ n, Module.Flat R (P.X n)] (q : ℤ) :
    (((homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) q).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (tensorDouble P Q)) ≅
    ((tensorRight (Q.homology q)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P := by
  refine Hom.isoOfComponents (fun n ↦ (Q.sc q).mapHomologyIso (tensorLeft (P.X n))) ?_
  intro i j hij
  symm
  change ShortComplex.homologyMap ((Q.sc q).mapNatTrans
      ((curriedTensor (ModuleCat.{u} R)).map (P.d i j))) ≫ _ = _
  rw [ShortComplex.homologyMap_mapNatTrans]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

/-- Tensoring on the right with a flat module preserves homology. Mathlib records the exactness
and the preservation of finite limits, but derives `PreservesHomology` only on the left. -/
private theorem tensorRight_preservesHomology (M : ModuleCat.{u} R) [Module.Flat R M] :
    (tensorRight M).PreservesHomology := by
  apply Functor.preservesHomology_of_map_exact
  intro S hS
  exact Module.Flat.rTensor_shortComplex_exact M S hS

/-- The horizontal cohomology of the tensor double complex, for a complex of flat modules in the
second variable: `H^q_I(P ⊗ Q)^p = H^q(P) ⊗ Q^p`. -/
private noncomputable def tensorHorizontalHomologyIso
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    [∀ n, Module.Flat R (Q.X n)] (q : ℤ) :
    (tensorDouble P Q).homology q ≅
      ((tensorLeft (P.homology q)).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q := by
  haveI : ∀ n : ℤ, (tensorRight (Q.X n)).PreservesHomology := fun n ↦
    tensorRight_preservesHomology (Q.X n)
  refine Hom.isoOfComponents (fun n ↦
    (((tensorDouble P Q).sc q).mapHomologyIso
      (eval (ModuleCat.{u} R) (ComplexShape.up ℤ) n)).symm ≪≫
      (P.sc q).mapHomologyIso (tensorRight (Q.X n))) ?_
  intro i j hij
  symm
  apply (cancel_epi
    (((tensorDouble P Q).sc q).mapHomologyIso (eval _ (ComplexShape.up ℤ) i)).hom).1
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
  have h := NatTrans.app_homology
    (show eval (ModuleCat.{u} R) (ComplexShape.up ℤ) i ⟶ eval _ (ComplexShape.up ℤ) j from
      { app := fun K ↦ K.d i j
        naturality := fun K L f ↦ f.comm i j }) ((tensorDouble P Q).sc q)
  change ((tensorDouble P Q).homology q).d i j = _ at h
  rw [h]
  simp only [Iso.hom_inv_id_assoc, Category.assoc]
  change ShortComplex.homologyMap ((P.sc q).mapNatTrans
      ((curriedTensor (ModuleCat.{u} R)).flip.map (Q.d i j))) ≫ _ = _
  rw [ShortComplex.homologyMap_mapNatTrans]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

/-- The second page of the spectral sequence of the first filtration of the tensor double
complex, as the cohomology of the complex of vertical cohomologies. -/
private lemma nonempty_firstDoubleE₂Iso (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (bP bQ : ℤ) [P.IsStrictlyLE bP] [Q.IsStrictlyLE bQ] (p q : ℤ) :
    Nonempty (filteredPageObject (P ⊗ Q) (firstDegreeFiltration P Q bP bQ) 2 p q ≅
      (((homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) q).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (tensorDouble P Q)).homology p) := by
  have hFeq : firstDegreeFiltration P Q bP bQ =
      HomologicalComplex₂.stepSubobject (tensorDouble P Q) (fun i (_ : ℤ) ↦ i) := by
    funext a n
    exact firstDegreeFiltration_eq_stepSubobject P Q bP bQ a n
  set K := tensorDouble P Q with hK
  set F := HomologicalComplex₂.stepSubobject K (fun i (_ : ℤ) ↦ i) with hF
  have hanti : ∀ a a' n : ℤ, a ≤ a' → F a' n ≤ F a n := fun a a' n h ↦
    HomologicalComplex₂.totalProjector_le (K := K) _ _ (fun _ _ hi ↦ h.trans hi) n
  obtain ⟨-, -, h₂⟩ := HomologicalComplex₂.exists_iso_pages_totalFiltration₁ K F
    (fun a n ↦ (K.mk_totalFiltration_ι_f (fun i (_ : ℤ) ↦ i) (fun _ _ ↦ by omega)
      (fun _ _ ↦ le_rfl) a n).symm)
    (cycles (K.total (ComplexShape.up ℤ)) F) (fun _ _ _ ↦ rfl)
    (boundaries (K.total (ComplexShape.up ℤ)) F) (fun _ _ _ ↦ rfl)
    (spectralSequence (K.total (ComplexShape.up ℤ)) F hanti)
    (fun r a b n hr hn ↦ eIso (K.total (ComplexShape.up ℤ)) F hanti r a b n hr hn)
    (fun r a b n hr hn ↦ ⟨deltaCycles (K.total (ComplexShape.up ℤ)) F r a n,
      deltaCycles_arrow (K.total (ComplexShape.up ℤ)) F r a n,
      CochainComplex.Tor.den_π_eIso_inv_comp_d (K.total (ComplexShape.up ℤ)) F hanti
        r hr a b n hn⟩)
  refine ⟨?_⟩
  refine (eqToIso (by rw [hFeq]) : filteredPageObject (P ⊗ Q)
    (firstDegreeFiltration P Q bP bQ) 2 p q ≅ filteredPageObject (P ⊗ Q) F 2 p q) ≪≫ ?_
  exact (eIso (K.total (ComplexShape.up ℤ)) F hanti 2 p q (p + q) (by omega) rfl).symm ≪≫
    (h₂ p q).some

/-- The second page of the spectral sequence of the second filtration of the tensor double
complex, as the cohomology of the complex of horizontal cohomologies. -/
private lemma nonempty_secondDoubleE₂Iso (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (bP bQ : ℤ) [P.IsStrictlyLE bP] [Q.IsStrictlyLE bQ] (p q : ℤ) :
    Nonempty (filteredPageObject (P ⊗ Q) (secondDegreeFiltration P Q bP bQ) 2 p q ≅
      ((tensorDouble P Q).homology q).homology p) := by
  have hFeq : secondDegreeFiltration P Q bP bQ =
      HomologicalComplex₂.stepSubobject (tensorDouble P Q) (fun (_ : ℤ) j ↦ j) := by
    funext a n
    exact secondDegreeFiltration_eq_stepSubobject P Q bP bQ a n
  set K := tensorDouble P Q with hK
  set F := HomologicalComplex₂.stepSubobject K (fun (_ : ℤ) j ↦ j) with hF
  have hanti : ∀ a a' n : ℤ, a ≤ a' → F a' n ≤ F a n := fun a a' n h ↦
    HomologicalComplex₂.totalProjector_le (K := K) _ _ (fun _ _ hi ↦ h.trans hi) n
  obtain ⟨-, -, h₂⟩ := HomologicalComplex₂.exists_iso_pages_totalFiltration₂ K F
    (fun a n ↦ (K.mk_totalFiltration_ι_f (fun (_ : ℤ) j ↦ j) (fun _ _ ↦ le_rfl)
      (fun _ _ ↦ by omega) a n).symm)
    (cycles (K.total (ComplexShape.up ℤ)) F) (fun _ _ _ ↦ rfl)
    (boundaries (K.total (ComplexShape.up ℤ)) F) (fun _ _ _ ↦ rfl)
    (spectralSequence (K.total (ComplexShape.up ℤ)) F hanti)
    (fun r a b n hr hn ↦ eIso (K.total (ComplexShape.up ℤ)) F hanti r a b n hr hn)
    (fun r a b n hr hn ↦ ⟨deltaCycles (K.total (ComplexShape.up ℤ)) F r a n,
      deltaCycles_arrow (K.total (ComplexShape.up ℤ)) F r a n,
      CochainComplex.Tor.den_π_eIso_inv_comp_d (K.total (ComplexShape.up ℤ)) F hanti
        r hr a b n hn⟩)
  refine ⟨?_⟩
  refine (eqToIso (by rw [hFeq]) : filteredPageObject (P ⊗ Q)
    (secondDegreeFiltration P Q bP bQ) 2 p q ≅ filteredPageObject (P ⊗ Q) F 2 p q) ≪≫ ?_
  exact (eIso (K.total (ComplexShape.up ℤ)) F hanti 2 p q (p + q) (by omega) rfl).symm ≪≫
    (h₂ p q).some

end SecondPages

section DerivedComparison

open CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex
open TotalTensorComplex.SingleTensor

attribute [local instance] HasDerivedCategory.standard

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- The braiding of the total tensor product of cochain complexes of modules. -/
private noncomputable def tensorSwap (P Q : CochainComplex (ModuleCat.{u} R) ℤ) :
    P ⊗ Q ≅ Q ⊗ P := by
  letI := (TotalTensorComplex.cochainComplex_symmetricMonoidalCategory R).choose
  exact β_ P Q

/-- Tensoring on the right with a module placed in degree zero is tensoring degreewise. -/
private noncomputable def tensorSingleIso (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (M : ModuleCat.{u} R) :
    P ⊗ (single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj M ≅
      ((tensorRight M).mapHomologicalComplex (ComplexShape.up ℤ)).obj P :=
  tensorSwap _ _ ≪≫ singleTensorIso M P ≪≫
    (NatIso.mapHomologicalComplex (BraidedCategory.tensorLeftIsoTensorRight M)
      (ComplexShape.up ℤ)).app P

/-- The homology comparison induced by K-flat representatives and the derived tensor product. -/
private noncomputable def tensorHomologyIsoDerived
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : P.KFlat) (hQ : Q.KFlat)
    (K L : DerivedCategory (ModuleCat.{u} R))
    (eK : K ≅ DerivedCategory.Q.obj P) (eL : L ≅ DerivedCategory.Q.obj Q) (n : ℤ) :
    (P ⊗ Q).homology n ≅ (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj
      (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).obj K).obj L) :=
  ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).mapIso
    (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).mapIso eK).app L ≪≫
      ((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).obj
        (DerivedCategory.Q.obj P)).mapIso eL ≪≫
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).comparison P Q hP hQ) ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) n).app (P ⊗ Q)).symm

private lemma tensorHomologyIsoDerived_symm
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : P.KFlat) (hQ : Q.KFlat)
    (K L : DerivedCategory (ModuleCat.{u} R))
    (eK : K ≅ DerivedCategory.Q.obj P) (eL : L ≅ DerivedCategory.Q.obj Q) (n : ℤ) :
    (tensorHomologyIsoDerived P Q hP hQ K L eK eL n).symm =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).mapIso
        (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).mapIso eK).app L ≪≫
          ((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).obj
            (DerivedCategory.Q.obj P)).mapIso eL ≪≫
          (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).comparison P Q hP hQ) ≪≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) n).app (P ⊗ Q) := rfl

private lemma exists_projective_representative
    (K : DerivedCategory (ModuleCat.{u} R)) (b : ℤ) [K.IsLE b] :
    ∃ P : CochainComplex (ModuleCat.{u} R) ℤ,
      P.IsStrictlyLE b ∧ (∀ i, Projective (P.X i)) ∧
        Nonempty (K ≅ DerivedCategory.Q.obj P) := by
  obtain ⟨L, hL, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isLE K b
  obtain ⟨P, -⟩ := ProjectiveResolutionLemma.statement3 b L hL
  have : QuasiIso P.α := P.quasiIso
  exact ⟨P.complex, P.boundedAbove, P.projective,
    ⟨e ≪≫ (asIso (DerivedCategory.Q.map P.α)).symm⟩⟩

private lemma quasiIso_tensorRight_of_kFlat
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (hK : K.KFlat)
    {A B : CochainComplex (ModuleCat.{u} R) ℤ} (f : A ⟶ B) [QuasiIso f] :
    QuasiIso ((tensorRight K).map f) := by
  have hf : HomotopyCategory.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)
      ((HomotopyCategory.quotient _ _).map f) :=
    (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 (show QuasiIso f from inferInstance)
  have h := CochainComplex.KFlat.kFlat_tright_preserves_quasiIso K hK
    ((HomotopyCategory.quotient _ _).map f) hf
  change HomotopyCategory.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)
    ((HomotopyCategory.quotient _ _ ⋙ Tright K).map f) at h
  unfold Tright at h
  rw [descendF_comp_quotient] at h
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).1 h

private lemma quasiIso_tensorLeft_of_kFlat
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (hK : K.KFlat)
    {A B : CochainComplex (ModuleCat.{u} R) ℤ} (f : A ⟶ B) [QuasiIso f] :
    QuasiIso ((tensorLeft K).map f) := by
  let := (TotalTensorComplex.cochainComplex_symmetricMonoidalCategory R).choose
  have : QuasiIso ((tensorRight K).map f) := quasiIso_tensorRight_of_kFlat K hK f
  have heq : (tensorLeft K).map f ≫ (β_ K B).hom =
      (β_ K A).hom ≫ (tensorRight K).map f :=
    BraidedCategory.braiding_naturality_right K f
  have : QuasiIso ((tensorLeft K).map f ≫ (β_ K B).hom) := by
    rw [heq]
    infer_instance
  exact (quasiIso_iff_comp_right _ (β_ K B).hom).1 this

private noncomputable def representativeHomologyIso
    (K : DerivedCategory (ModuleCat.{u} R)) (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (e : K ≅ DerivedCategory.Q.obj P) (q : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) q).obj K ≅ P.homology q :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} R) q).mapIso e ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) q).app P

private noncomputable def tensorSingleHomologyIsoDerived
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : P.KFlat)
    (K : DerivedCategory (ModuleCat.{u} R)) (eK : K ≅ DerivedCategory.Q.obj P)
    (M : ModuleCat.{u} R) (p : ℤ) :
    (P ⊗ (single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj M).homology p ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) p).obj
        (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).obj K).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)) := by
  let Q := Classical.choice (ProjectiveResolutionLemma.statement1 M)
  have : ∀ i, Projective (Q.complex.X i) := Q.projective
  have : ∀ i, Module.Flat R (Q.complex.X i) := fun i ↦ inferInstance
  have : Q.complex.IsStrictlyLE 0 := Q.boundedAbove
  have hQ : Q.complex.KFlat := CochainComplex.KFlat.kFlat_of_flat Q.complex 0
  have : QuasiIso Q.α := Q.quasiIso
  have : QuasiIso ((tensorLeft P).map Q.α) := quasiIso_tensorLeft_of_kFlat P hP Q.α
  let eM : (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M ≅
      DerivedCategory.Q.obj Q.complex :=
    (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) 0).app M ≪≫
      (asIso (DerivedCategory.Q.map Q.α)).symm
  exact (asIso (homologyMap ((tensorLeft P).map Q.α) p)).symm ≪≫
    tensorHomologyIsoDerived P Q.complex hP hQ K _ eK eM p

private noncomputable def firstOrdinaryToDerivedIso
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (hP : P.KFlat)
    (K L : DerivedCategory (ModuleCat.{u} R))
    (eK : K ≅ DerivedCategory.Q.obj P) (eL : L ≅ DerivedCategory.Q.obj Q) (p q : ℤ) :
    (P ⊗ (single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj (Q.homology q)).homology p ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) p).obj
        (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).obj K).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
            ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) q).obj L))) :=
  tensorSingleHomologyIsoDerived P hP K eK (Q.homology q) p ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) p).mapIso
      (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).obj K).mapIso
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).mapIso
          (representativeHomologyIso L Q eL q).symm))

private noncomputable def secondOrdinaryToDerivedIso
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (hQ : Q.KFlat)
    (K L : DerivedCategory (ModuleCat.{u} R))
    (eK : K ≅ DerivedCategory.Q.obj P) (eL : L ≅ DerivedCategory.Q.obj Q) (p q : ℤ) :
    ((single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj (P.homology q) ⊗ Q).homology p ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) p).obj
        (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
            ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) q).obj K))).obj L) :=
  homologyMapIso (tensorSwap _ Q) p ≪≫ firstOrdinaryToDerivedIso Q P hQ L K eL eK p q ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) p).mapIso
      (CochainComplex.DerivedTensor.derivedTensorProductCommIso L
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) q).obj K)))

/-- The filtered second page of the first tensor spectral sequence, as `H^p(P ⊗ H^q(Q))`. -/
private lemma nonempty_firstTensorE₂Iso (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (bP bQ : ℤ) [P.IsStrictlyLE bP] [Q.IsStrictlyLE bQ]
    [∀ n, Module.Flat R (P.X n)] (p q : ℤ) :
    Nonempty (filteredPageObject (P ⊗ Q) (firstDegreeFiltration P Q bP bQ) 2 p q ≅
      (P ⊗ (single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj (Q.homology q)).homology p) :=
  ⟨(nonempty_firstDoubleE₂Iso P Q bP bQ p q).some ≪≫
    homologyMapIso (tensorVerticalHomologyIso P Q q) p ≪≫
    (homologyMapIso (tensorSingleIso P (Q.homology q)) p).symm⟩

/-- The filtered second page of the second tensor spectral sequence, as `H^p(H^q(P) ⊗ Q)`. -/
private lemma nonempty_secondTensorE₂Iso (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (bP bQ : ℤ) [P.IsStrictlyLE bP] [Q.IsStrictlyLE bQ]
    [∀ n, Module.Flat R (Q.X n)] (p q : ℤ) :
    Nonempty (filteredPageObject (P ⊗ Q) (secondDegreeFiltration P Q bP bQ) 2 p q ≅
      ((single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj (P.homology q) ⊗ Q).homology p) :=
  ⟨(nonempty_secondDoubleE₂Iso P Q bP bQ p q).some ≪≫
    homologyMapIso (tensorHorizontalHomologyIso P Q q) p ≪≫
    (homologyMapIso (singleTensorIso (P.homology q) Q) p).symm⟩

end DerivedComparison

section Main

open CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex

attribute [local instance] HasDerivedCategory.standard

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- **Stacks 0662.** For two bounded-above objects `K`, `L` of the derived category of a
commutative ring `R` there are two convergent spectral sequences
`'E_2^{p,q} = H^p(K ⊗^L H^q(L))` and `''E_2^{p,q} = H^p(H^q(K) ⊗^L L)`, both abutting to
`H^{p+q}(K ⊗^L L)`.

They are the spectral sequences of the two canonical filtrations of the total tensor complex
`P^• ⊗ Q^•` of bounded-above complexes of projectives representing `K` and `L`; the abutment
isomorphism is the one induced by those representatives and the canonical K-flat comparison of
the derived tensor product, and the derived second-page isomorphisms factor through the
filtered-complex second-page isomorphisms. -/
@[stacks 0662]
public theorem exists_derived_tensor_spectral_sequences
    (R : Type u) [CommRing R]
    (K L : DerivedCategory.Minus (ModuleCat.{u} R)) :
    ∃ (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (bP bQ : ℤ),
      P.IsStrictlyLE bP ∧ (∀ i : ℤ, Projective (P.X i)) ∧
      Q.IsStrictlyLE bQ ∧ (∀ i : ℤ, Projective (Q.X i)) ∧
      ∃ (hPflat : P.KFlat) (hQflat : Q.KFlat)
        (eK : K.1 ≅ DerivedCategory.Q.obj P)
        (eL : L.1 ≅ DerivedCategory.Q.obj Q)
        (E : AssociatedFiltrationSpectralSequence ((tensorLeft P).obj Q)
            (firstDegreeFiltration P Q bP bQ))
        (E' : AssociatedFiltrationSpectralSequence ((tensorLeft P).obj Q)
            (secondDegreeFiltration P Q bP bQ))
        (firstFilteredE₂Iso : ∀ p q : ℤ,
          filteredPageObject ((tensorLeft P).obj Q) (firstDegreeFiltration P Q bP bQ)
              2 p q ≅
          ((tensorLeft P).obj ((single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
            (Q.homology q))).homology p)
        (secondFilteredE₂Iso : ∀ p q : ℤ,
          filteredPageObject ((tensorLeft P).obj Q) (secondDegreeFiltration P Q bP bQ)
              2 p q ≅
          ((tensorLeft ((single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
            (P.homology q))).obj Q).homology p)
        (firstE₂Iso : ∀ p q : ℤ, (E.spectralSequence.page 2).X (p, q) ≅
          ((tensorLeft P).obj ((single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
            (Q.homology q))).homology p)
        (secondE₂Iso : ∀ p q : ℤ, (E'.spectralSequence.page 2).X (p, q) ≅
          ((tensorLeft ((single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
            (P.homology q))).obj Q).homology p)
        (abutmentIso : ∀ n : ℤ, ((tensorLeft P).obj Q).homology n ≅
          (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj
            (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).obj
              K.1).obj L.1))
        (firstOrdinaryToDerivedE₂Iso : ∀ p q : ℤ,
          ((tensorLeft P).obj ((single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
            (Q.homology q))).homology p ≅
          (DerivedCategory.homologyFunctor (ModuleCat.{u} R) p).obj
            (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).obj K.1).obj
              ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
                ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) q).obj L.1))))
        (secondOrdinaryToDerivedE₂Iso : ∀ p q : ℤ,
          ((tensorLeft ((single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
            (P.homology q))).obj Q).homology p ≅
          (DerivedCategory.homologyFunctor (ModuleCat.{u} R) p).obj
            (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).obj
              ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
                ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) q).obj K.1))).obj L.1))
        (firstDerivedE₂Iso : ∀ p q : ℤ, (E.spectralSequence.page 2).X (p, q) ≅
          (DerivedCategory.homologyFunctor (ModuleCat.{u} R) p).obj
            (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).obj K.1).obj
              ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
                ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) q).obj L.1))))
        (secondDerivedE₂Iso : ∀ p q : ℤ, (E'.spectralSequence.page 2).X (p, q) ≅
          (DerivedCategory.homologyFunctor (ModuleCat.{u} R) p).obj
            (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).obj
              ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
                ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) q).obj K.1))).obj L.1)),
        (∀ p q : ℤ, (firstE₂Iso p q).hom =
          (E.pageIso 2 p q (by omega)).hom ≫ (firstFilteredE₂Iso p q).hom) ∧
        (∀ p q : ℤ, (secondE₂Iso p q).hom =
          (E'.pageIso 2 p q (by omega)).hom ≫ (secondFilteredE₂Iso p q).hom) ∧
        (∀ p q : ℤ, (firstDerivedE₂Iso p q).hom =
          (firstE₂Iso p q).hom ≫ (firstOrdinaryToDerivedE₂Iso p q).hom) ∧
        (∀ p q : ℤ, (secondDerivedE₂Iso p q).hom =
          (secondE₂Iso p q).hom ≫ (secondOrdinaryToDerivedE₂Iso p q).hom) ∧
        (∀ n : ℤ,
          (abutmentIso n).symm =
            (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).mapIso
              (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor
                  R).mapIso eK).app L.1 ≪≫
                ((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).obj
                  (DerivedCategory.Q.obj P)).mapIso eL ≪≫
                (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).comparison P Q
                  hPflat hQflat) ≪≫
              (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) n).app
                ((tensorLeft P).obj Q)) := by
  classical
  obtain ⟨bP, hK⟩ := K.2
  obtain ⟨bQ, hL⟩ := L.2
  have : K.1.IsLE bP := hK
  have : L.1.IsLE bQ := hL
  obtain ⟨P, hPb, hPproj, ⟨eK⟩⟩ := exists_projective_representative K.1 bP
  obtain ⟨Q, hQb, hQproj, ⟨eL⟩⟩ := exists_projective_representative L.1 bQ
  have := hPb
  have := hQb
  have := hPproj
  have := hQproj
  have hPf : ∀ i, Module.Flat R (P.X i) := fun i ↦ inferInstance
  have hQf : ∀ i, Module.Flat R (Q.X i) := fun i ↦ inferInstance
  have hPflat : P.KFlat := CochainComplex.KFlat.kFlat_of_flat P bP
  have hQflat : Q.KFlat := CochainComplex.KFlat.kFlat_of_flat Q bQ
  let E := firstTensorSpectralSequence P Q bP bQ
  let E' := secondTensorSpectralSequence P Q bP bQ
  let f := fun p q ↦ (nonempty_firstTensorE₂Iso P Q bP bQ p q).some
  let g := fun p q ↦ (nonempty_secondTensorE₂Iso P Q bP bQ p q).some
  let f' := fun p q ↦ E.pageIso 2 p q (by omega) ≪≫ f p q
  let g' := fun p q ↦ E'.pageIso 2 p q (by omega) ≪≫ g p q
  let a := tensorHomologyIsoDerived P Q hPflat hQflat K.1 L.1 eK eL
  let a₁ := firstOrdinaryToDerivedIso P Q hPflat K.1 L.1 eK eL
  let a₂ := secondOrdinaryToDerivedIso P Q hQflat K.1 L.1 eK eL
  refine ⟨P, Q, bP, bQ, hPb, hPproj, hQb, hQproj, hPflat, hQflat, eK, eL,
    E, E', f, g, f', g', a, a₁, a₂,
    (fun p q ↦ f' p q ≪≫ a₁ p q), (fun p q ↦ g' p q ≪≫ a₂ p q),
    (fun _ _ ↦ rfl), (fun _ _ ↦ rfl), (fun _ _ ↦ rfl), (fun _ _ ↦ rfl), ?_⟩
  intro n
  exact tensorHomologyIsoDerived_symm P Q hPflat hQflat K.1 L.1 eK eL n

end Main

end CochainComplex.DerivedTensorSpectralSequence

end
