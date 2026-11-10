module

public import StacksFrontier.Algebra.Homology.SpectralSequence.NatRestrict
public import StacksCore.Algebra.Homology.SpectralSequence.PageInfinity

/-!
# The infinity page under reindexing and start-page shift

`CochainComplex.Filtered.nonempty_pageInfinityIso_gr` identifies the infinity page of
the spectral sequence of a filtered complex with the associated graded of the filtration induced
on cohomology, for a `CategoryTheory.CohomologicalSpectralSequence C 0`, i.e. a spectral sequence
indexed by `ℤ × ℤ` and starting at the page `0`.  The consumers of that identification -- the
filtered abutment data of [Stacks, Tag 01F2] and [Stacks, Tag 01F6] -- ask for a
`CategoryTheory.CohomologicalSpectralSequenceNat C 2`, indexed by `ℕ × ℕ` and starting at the page
`2`.  `CategoryTheory.SpectralSequence.natRestrict` performs the reindexing and
`CategoryTheory.SpectralSequence.shiftStart` the start-page shift; this file shows that both
transport `pageInfinity`.

Both transports go through `SpectralSequence.pageInfinityIso` at a page `r` large enough for both
sequences, where the page objects agree **on the nose**: `natRestrict` has
`X pq = X (ComplexShape.natEmb pq)` and `shiftStart` has `page r = page r` by definition, so the
only content is the bookkeeping of `HasEdgeMonoAtFrom`/`HasEdgeEpiAtFrom` at that page.  This is
the same phenomenon as
`CategoryTheory.SpectralSequence.natRestrictE₂Comp_pageTwoIso`, which is an
`Iso.refl` because page `2` at `(p, q) : ℕ × ℕ` is page `2` at `((p : ℤ), (q : ℤ))`.

## Main definitions

* `CategoryTheory.SpectralSequence.shiftStart`: a spectral sequence starting at `r₀`, read as one
  starting at any `r₁ ≥ r₀`.  It is an `abbrev`, so that the pages of the shifted sequence are
  transparently the pages of the original one.
* `CategoryTheory.SpectralSequence.natRestrictE₂Shift`: the composite passage from a
  `CohomologicalSpectralSequence C 0` lying in the first quadrant to an
  `E₂CohomologicalSpectralSequenceNat C`.

## Main results

* `CategoryTheory.SpectralSequence.shiftStart_pageInfinityIso`: the infinity page is unchanged by
  a start-page shift.
* `CategoryTheory.SpectralSequence.natRestrict_pageInfinityIso`: the infinity page of the
  first-quadrant restriction at `pq : ℕ × ℕ` is the infinity page of the ambient sequence at
  `ComplexShape.natEmb pq`.
* `CategoryTheory.SpectralSequence.natRestrictE₂Shift_pageInfinityIso`: the two combined, in the
  shape a filtered abutment datum needs.
* `CategoryTheory.SpectralSequence.hasPageInfinityAt_of_isFirstQuadrant`: a first-quadrant
  cohomological spectral sequence indexed by `ℤ × ℤ` has an infinity page at *every* bidegree, not
  only in the first quadrant; this is the `ℤ × ℤ` analogue of
  `CategoryTheory.CohomologicalSpectralSequenceNat.instHasPageInfinityAtProdNat` and it
  is what lets the transports below carry no `HasPageInfinityAt` hypothesis.

## Implementation notes

The direction of the edge-vanishing transports is worth recording, because only one direction is
available.  `HasEdgeMonoAt pq r` quantifies over the *sources* of differentials into `pq`; the
restriction to `ℕ × ℕ` has fewer sources, so ambient vanishing implies restricted vanishing and
not conversely.  Likewise `HasEdgeMonoAt pq r` for `shiftStart` carries the weaker side condition
`r₁ ≤ r` in place of `r₀ ≤ r`, so the ambient statement implies the shifted one.  Both transports
therefore take their hypothesis on the *ambient* sequence, which is the side on which the
convergence results for filtered complexes, such as
`CochainComplex.Filtered.nonempty_pageInfinityIso_gr`, are stated.

`hasPageInfinityAt_of_isFirstQuadrant` holds at every bidegree of `ℤ × ℤ` and not only in the
first quadrant, because the two vanishing arguments look at a *neighbour* of the bidegree: the
differentials into `x` on the page `r` come from `(x.1 - r, x.2 - 1 + r)`, whose first coordinate
is negative once `x.1 < r`, and those out of `x` land in `(x.1 + r, x.2 + 1 - r)`, whose second
coordinate is negative once `x.2 + 1 < r`.  Neither needs `x` itself to lie in the first quadrant.

## References

* [Stacks Project, Tag 01F2](https://stacks.math.columbia.edu/tag/01F2)
* [Stacks Project, Tag 01F6](https://stacks.math.columbia.edu/tag/01F6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite ComplexShape

namespace CategoryTheory.SpectralSequence

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/-! ### Shifting the start page -/

section ShiftStart

variable {κ : Type*} {c : ℤ → ComplexShape κ} {r₀ r₁ : ℤ}

/-- **A spectral sequence starting at `r₀`, read as one starting at `r₁ ≥ r₀`.**  Nothing is
discarded: the pages and the page-turn isomorphisms are those of the original sequence, only the
range of admissible page indices is narrowed.

This is an `abbrev` on purpose: statements about the pages of the shifted sequence have to be
provable by statements about the pages of the original one, so the shift must be transparent to
the unifier. -/
abbrev shiftStart (E : SpectralSequence C c r₀) (h : r₀ ≤ r₁) : SpectralSequence C c r₁ where
  page r hr := E.page r (h.trans hr)
  iso r r' pq hrr' hr := E.iso r r' pq hrr' (h.trans hr)

/-- The pages of a start-shifted spectral sequence are the pages of the original one. -/
@[simp]
lemma shiftStart_page (E : SpectralSequence C c r₀) (h : r₀ ≤ r₁) (r : ℤ) (hr : r₁ ≤ r) :
    (E.shiftStart h).page r hr = E.page r (h.trans hr) :=
  rfl

/-- **A morphism of spectral sequences, read between the start-shifted sequences.**  The
components are those of the original morphism; only the range of admissible page indices is
narrowed.

This is `Stacks.Cohomology.CechSpectral.restrictR₀` on morphisms, spelled here so that this file
need not depend on the Čech spectral sequence development of Stacks Tag 01ES; the two agree by
definition. -/
abbrev shiftStartMap {E E' : SpectralSequence C c r₀} (f : E ⟶ E') (h : r₀ ≤ r₁) :
    E.shiftStart h ⟶ E'.shiftStart h where
  hom r hr := f.hom r (h.trans hr)
  comm r r' pq hrr' hr := f.comm r r' pq hrr' (h.trans hr)

/-- The components of `shiftStartMap` are the components of the original morphism. -/
@[simp]
lemma shiftStartMap_hom {E E' : SpectralSequence C c r₀} (f : E ⟶ E') (h : r₀ ≤ r₁) (r : ℤ)
    (hr : r₁ ≤ r) :
    (shiftStartMap f h).hom r hr = f.hom r (h.trans hr) :=
  rfl

/-- Vanishing of the differentials into `pq` on the page `r` transports to a start-shifted
spectral sequence, as soon as `r` is an admissible page there. -/
lemma shiftStart_hasEdgeMonoAt (E : SpectralSequence C c r₀) (h : r₀ ≤ r₁) (pq : κ) (r : ℤ)
    (hr : r₁ ≤ r) [E.HasEdgeMonoAt pq r] :
    (E.shiftStart h).HasEdgeMonoAt pq r where
  le := hr
  zero pq' := E.d_eq_zero_of_hasEdgeMonoAt pq' pq r

/-- Vanishing of the differentials out of `pq` on the page `r` transports to a start-shifted
spectral sequence, as soon as `r` is an admissible page there. -/
lemma shiftStart_hasEdgeEpiAt (E : SpectralSequence C c r₀) (h : r₀ ≤ r₁) (pq : κ) (r : ℤ)
    (hr : r₁ ≤ r) [E.HasEdgeEpiAt pq r] :
    (E.shiftStart h).HasEdgeEpiAt pq r where
  le := hr
  zero pq' := E.d_eq_zero_of_hasEdgeEpiAt pq pq' r

/-- **A start-shifted spectral sequence stabilises wherever the original one does.**  The page
from which the differentials vanish is pushed up to `max r₁ r`, which is admissible on both
sides. -/
instance shiftStart_hasPageInfinityAt (E : SpectralSequence C c r₀) (h : r₀ ≤ r₁) (pq : κ)
    [E.HasPageInfinityAt pq] :
    (E.shiftStart h).HasPageInfinityAt pq where
  nonempty_hasEdgeMonoSet := by
    obtain ⟨r, hr⟩ := E.nonempty_hasEdgeMonoSet pq
    refine ⟨max r₁ r, le_max_left _ _, fun r' hr' => ?_⟩
    have := hr.2 r' ((le_max_right _ _).trans hr')
    exact shiftStart_hasEdgeMonoAt E h pq r' ((le_max_left _ _).trans hr')
  nonempty_hasEdgeEpiSet := by
    obtain ⟨r, hr⟩ := E.nonempty_hasEdgeEpiSet pq
    refine ⟨max r₁ r, le_max_left _ _, fun r' hr' => ?_⟩
    have := hr.2 r' ((le_max_right _ _).trans hr')
    exact shiftStart_hasEdgeEpiAt E h pq r' ((le_max_left _ _).trans hr')

/-- **The infinity page is unchanged by a start-page shift, read at a supplied page `r`.**  Both
sides are the page `E_r^{pq}`, where the page objects agree by definition of `shiftStart`.

The page is an argument rather than a choice, and that is the whole point: a page chosen at each
spectral sequence separately serves no comparison *between* two of them, because
`CategoryTheory.SpectralSequence.Hom.mapPageInfinity_eq` computes the map induced on the infinity
pages on a *single* page.  This is the same device as
`CochainComplex.Filtered.IsStableFrom` one level down, and it is what
`shiftStart_pageInfinityIsoAt_naturality` needs.  `shiftStart_pageInfinityIso` is this
definition at the page `max (E.rMin pq) ((E.shiftStart h).rMin pq)`. -/
def shiftStart_pageInfinityIsoAt (E : SpectralSequence C c r₀) (h : r₀ ≤ r₁) (pq : κ) (r : ℤ)
    [E.HasPageInfinityAt pq] [E.HasEdgeMonoAtFrom pq r] [E.HasEdgeEpiAtFrom pq r]
    [(E.shiftStart h).HasEdgeMonoAtFrom pq r] [(E.shiftStart h).HasEdgeEpiAtFrom pq r] :
    (E.shiftStart h).pageInfinity pq ≅ E.pageInfinity pq :=
  (E.shiftStart h).pageInfinityIso pq r ≪≫ (E.pageInfinityIso pq r).symm

/-- **The infinity page is unchanged by a start-page shift.**  Both sides are the common page
`E_r^{pq}` for `r` beyond the stabilisation point of either sequence, where the page objects agree
by definition of `shiftStart`.

This is `shiftStart_pageInfinityIsoAt` at the page `max (E.rMin pq) ((E.shiftStart h).rMin pq)`,
so that there is one comparison and not two. -/
def shiftStart_pageInfinityIso (E : SpectralSequence C c r₀) (h : r₀ ≤ r₁) (pq : κ)
    [E.HasPageInfinityAt pq] :
    (E.shiftStart h).pageInfinity pq ≅ E.pageInfinity pq :=
  letI r := max (E.rMin pq) ((E.shiftStart h).rMin pq)
  haveI : E.HasEdgeMonoAtFrom pq r := E.hasEdgeMonoAtFrom_of_GE _ _ _ (le_max_left _ _)
  haveI : E.HasEdgeEpiAtFrom pq r := E.hasEdgeEpiAtFrom_of_GE _ _ _ (le_max_left _ _)
  haveI : (E.shiftStart h).HasEdgeMonoAtFrom pq r :=
    (E.shiftStart h).hasEdgeMonoAtFrom_of_GE _ _ _ (le_max_right _ _)
  haveI : (E.shiftStart h).HasEdgeEpiAtFrom pq r :=
    (E.shiftStart h).hasEdgeEpiAtFrom_of_GE _ _ _ (le_max_right _ _)
  shiftStart_pageInfinityIsoAt E h pq r

/-- **The identification of the infinity pages across a start-page shift is natural in the
spectral sequence**, at a page `r` admissible for all four sequences involved.

Both induced maps are computed on the page `r` by
`CategoryTheory.SpectralSequence.Hom.mapPageInfinity_eq`, where they are *the same* morphism:
`shiftStartMap f h` has the components of `f`. -/
theorem shiftStart_pageInfinityIsoAt_naturality {E E' : SpectralSequence C c r₀} (f : E ⟶ E')
    (h : r₀ ≤ r₁) (pq : κ) (r : ℤ) (hr : r₁ ≤ r)
    [E.HasPageInfinityAt pq] [E'.HasPageInfinityAt pq]
    [E.HasEdgeMonoAtFrom pq r] [E.HasEdgeEpiAtFrom pq r]
    [E'.HasEdgeMonoAtFrom pq r] [E'.HasEdgeEpiAtFrom pq r]
    [(E.shiftStart h).HasEdgeMonoAtFrom pq r] [(E.shiftStart h).HasEdgeEpiAtFrom pq r]
    [(E'.shiftStart h).HasEdgeMonoAtFrom pq r] [(E'.shiftStart h).HasEdgeEpiAtFrom pq r] :
    Hom.mapPageInfinity (shiftStartMap f h) pq ≫
        (shiftStart_pageInfinityIsoAt E' h pq r).hom =
      (shiftStart_pageInfinityIsoAt E h pq r).hom ≫ Hom.mapPageInfinity f pq := by
  rw [Hom.mapPageInfinity_eq (shiftStartMap f h) pq r hr,
    Hom.mapPageInfinity_eq f pq r (h.trans hr), shiftStart_pageInfinityIsoAt,
    shiftStart_pageInfinityIsoAt]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]

/-- A start-page shift preserves first-quadrant vanishing: it has fewer pages to check. -/
lemma shiftStart_isFirstQuadrant {u : ℤ → ℤ × ℤ}
    (E : SpectralSequence C (fun r => up' (u r)) r₀) (h : r₀ ≤ r₁) (hE : IsFirstQuadrant E) :
    IsFirstQuadrant (E.shiftStart h) :=
  fun r hr x hx => hE r (h.trans hr) x hx

end ShiftStart

/-! ### Stabilisation of a first-quadrant spectral sequence indexed by `ℤ × ℤ` -/

section FirstQuadrant

variable {r₀ : ℤ} (E : CohomologicalSpectralSequence C r₀)
  (hE : IsFirstQuadrant (u := fun r => ((r, 1 - r) : ℤ × ℤ)) E)

include hE

/-- **In a first-quadrant cohomological spectral sequence the differentials into `x` vanish on the
page `r` as soon as `x.1 < r`**, because their source `(x.1 - r, x.2 - 1 + r)` then has negative
first coordinate and is therefore a zero object. -/
lemma hasEdgeMonoAt_of_isFirstQuadrant (x : ℤ × ℤ) (r : ℤ) (hr₀ : r₀ ≤ r) (hr : x.1 < r) :
    E.HasEdgeMonoAt x r where
  le := hr₀
  zero x' := by
    by_cases h : (up' ((r, 1 - r) : ℤ × ℤ)).Rel x' x
    · rw [ComplexShape.up'_Rel] at h
      subst h
      refine (hE r hr₀ x' (Or.inl ?_)).eq_of_src _ _
      simp only [Prod.fst_add] at hr
      omega
    · exact (E.page r hr₀).shape _ _ h

/-- **In a first-quadrant cohomological spectral sequence the differentials out of `x` vanish on
the page `r` as soon as `x.2 + 1 < r`**, because their target `(x.1 + r, x.2 + 1 - r)` then has
negative second coordinate and is therefore a zero object. -/
lemma hasEdgeEpiAt_of_isFirstQuadrant (x : ℤ × ℤ) (r : ℤ) (hr₀ : r₀ ≤ r) (hr : x.2 + 1 < r) :
    E.HasEdgeEpiAt x r where
  le := hr₀
  zero x' := by
    by_cases h : (up' ((r, 1 - r) : ℤ × ℤ)).Rel x x'
    · rw [ComplexShape.up'_Rel] at h
      subst h
      refine (hE r hr₀ _ (Or.inr ?_)).eq_of_tgt _ _
      simp only [Prod.snd_add]
      omega
    · exact (E.page r hr₀).shape _ _ h

/-- **A first-quadrant cohomological spectral sequence indexed by `ℤ × ℤ` has an infinity page at
every bidegree.**  This is the `ℤ × ℤ` counterpart of
`CategoryTheory.CohomologicalSpectralSequenceNat.instHasPageInfinityAtProdNat`; note that
it holds at *every* `x : ℤ × ℤ` and not only in the first quadrant, since the arguments look at the
source and the target of the differentials rather than at `x` itself. -/
lemma hasPageInfinityAt_of_isFirstQuadrant (x : ℤ × ℤ) : E.HasPageInfinityAt x where
  nonempty_hasEdgeMonoSet :=
    ⟨max r₀ (x.1 + 1), le_max_left _ _, fun r hr =>
      have := max_le_iff.1 hr
      hasEdgeMonoAt_of_isFirstQuadrant E hE x r this.1 (by omega)⟩
  nonempty_hasEdgeEpiSet :=
    ⟨max r₀ (x.2 + 2), le_max_left _ _, fun r hr =>
      have := max_le_iff.1 hr
      hasEdgeEpiAt_of_isFirstQuadrant E hE x r this.1 (by omega)⟩

/-- **In a first-quadrant cohomological spectral sequence the differentials into `x` have
vanished for good from the page `x.1 + 1` on.**  The bound depends on the bidegree alone, so this
is the form in which *one* page serves a whole family of spectral sequences -- which is what a
naturality statement about the infinity page needs. -/
lemma hasEdgeMonoAtFrom_of_isFirstQuadrant (x : ℤ × ℤ) (r : ℤ) (hr₀ : r₀ ≤ r) (hr : x.1 < r)
    [E.HasPageInfinityAt x] :
    E.HasEdgeMonoAtFrom x r :=
  HasEdgeMonoAtFrom.mk' E x r
    (fun k => hasEdgeMonoAt_of_isFirstQuadrant E hE x (r + k) (by omega) (by omega)) hr₀

/-- **In a first-quadrant cohomological spectral sequence the differentials out of `x` have
vanished for good from the page `x.2 + 2` on.**  As with `hasEdgeMonoAtFrom_of_isFirstQuadrant`,
the bound depends on the bidegree alone. -/
lemma hasEdgeEpiAtFrom_of_isFirstQuadrant (x : ℤ × ℤ) (r : ℤ) (hr₀ : r₀ ≤ r) (hr : x.2 + 1 < r)
    [E.HasPageInfinityAt x] :
    E.HasEdgeEpiAtFrom x r :=
  HasEdgeEpiAtFrom.mk' E x r
    (fun k => hasEdgeEpiAt_of_isFirstQuadrant E hE x (r + k) (by omega) (by omega)) hr₀

end FirstQuadrant

/-! ### The infinity page under the first-quadrant reindexing -/

section NatRestrict

variable {r₀ : ℤ} {u : ℤ → ℤ × ℤ} (E : SpectralSequence C (fun r => up' (u r)) r₀)
  (hE : IsFirstQuadrant E)

/-- Vanishing of the differentials into `natEmb pq` transports to the first-quadrant restriction:
the restriction has fewer sources of differentials into `pq`. -/
lemma natRestrict_hasEdgeMonoAt (pq : ℕ × ℕ) (r : ℤ) [E.HasEdgeMonoAt (natEmb pq) r] :
    (E.natRestrict hE).HasEdgeMonoAt pq r where
  le := E.le₀_of_hasEdgeMonoAt (natEmb pq) r
  zero pq' := E.d_eq_zero_of_hasEdgeMonoAt (natEmb pq') (natEmb pq) r

/-- Vanishing of the differentials out of `natEmb pq` transports to the first-quadrant
restriction: the restriction has fewer targets of differentials out of `pq`. -/
lemma natRestrict_hasEdgeEpiAt (pq : ℕ × ℕ) (r : ℤ) [E.HasEdgeEpiAt (natEmb pq) r] :
    (E.natRestrict hE).HasEdgeEpiAt pq r where
  le := E.le₀_of_hasEdgeEpiAt (natEmb pq) r
  zero pq' := E.d_eq_zero_of_hasEdgeEpiAt (natEmb pq) (natEmb pq') r

/-- **The first-quadrant restriction stabilises wherever the ambient sequence does.** -/
instance natRestrict_hasPageInfinityAt (pq : ℕ × ℕ) [E.HasPageInfinityAt (natEmb pq)] :
    (E.natRestrict hE).HasPageInfinityAt pq where
  nonempty_hasEdgeMonoSet := by
    obtain ⟨r, hr⟩ := E.nonempty_hasEdgeMonoSet (natEmb pq)
    exact ⟨r, hr.1, fun r' hr' => have := hr.2 r' hr'; natRestrict_hasEdgeMonoAt E hE pq r'⟩
  nonempty_hasEdgeEpiSet := by
    obtain ⟨r, hr⟩ := E.nonempty_hasEdgeEpiSet (natEmb pq)
    exact ⟨r, hr.1, fun r' hr' => have := hr.2 r' hr'; natRestrict_hasEdgeEpiAt E hE pq r'⟩

/-- **The page object of the first-quadrant restriction at `pq` is the page object of the ambient
sequence at `ComplexShape.natEmb pq`**, by definition of `HomologicalComplex.natRestrict`, so this
is the identity.

It is *named* rather than left implicit because `CategoryTheory.SpectralSequence.natRestrict` is a
semireducible definition.  A composite that silently crosses the two spellings is well typed only
at default transparency, and `rw` and `simp`, which match at `instances` transparency, then refuse
to touch it -- the error reads "the target expression is not type-correct under the `implicit`
transparency level".  Mediating every crossing by this identity keeps each composite well typed
where the tactics can see it. -/
def natRestrict_pageXIso (pq : ℕ × ℕ) (r : ℤ) (hr : r₀ ≤ r) :
    ((E.natRestrict hE).page r hr).X pq ≅ (E.page r hr).X (natEmb pq) :=
  Iso.refl _

/-- `natRestrict_pageXIso` is the identity.  Deliberately *not* a `simp` lemma: rewriting it away
puts an identity morphism back at the crossing of the two spellings, where neither
`CategoryTheory.Category.id_comp` nor `CategoryTheory.Category.comp_id` can apply. -/
lemma natRestrict_pageXIso_hom (pq : ℕ × ℕ) (r : ℤ) (hr : r₀ ≤ r) :
    (natRestrict_pageXIso E hE pq r hr).hom = 𝟙 _ :=
  rfl

/-- **The infinity page transports along the first-quadrant reindexing, read at a supplied page
`r`.**  At `pq : ℕ × ℕ` both sides are the page `E_r` at `ComplexShape.natEmb pq`, the two
spellings of it being mediated by `natRestrict_pageXIso`.

As with `shiftStart_pageInfinityIsoAt`, the page is an argument rather than a choice, so that one
page can serve two spectral sequences at once; this is what
`natRestrict_pageInfinityIsoAt_naturality` needs. -/
def natRestrict_pageInfinityIsoAt (pq : ℕ × ℕ) (r : ℤ) [E.HasPageInfinityAt (natEmb pq)]
    [E.HasEdgeMonoAtFrom (natEmb pq) r] [E.HasEdgeEpiAtFrom (natEmb pq) r]
    [(E.natRestrict hE).HasEdgeMonoAtFrom pq r] [(E.natRestrict hE).HasEdgeEpiAtFrom pq r] :
    (E.natRestrict hE).pageInfinity pq ≅ E.pageInfinity (natEmb pq) :=
  (E.natRestrict hE).pageInfinityIso pq r ≪≫
    natRestrict_pageXIso E hE pq r (E.le₀_of_hasEdgeEpiAtFrom (natEmb pq) r) ≪≫
    (E.pageInfinityIso (natEmb pq) r).symm

/-- `natRestrict_pageInfinityIsoAt`, as a composition of morphisms rather than of
isomorphisms. -/
lemma natRestrict_pageInfinityIsoAt_hom (pq : ℕ × ℕ) (r : ℤ) [E.HasPageInfinityAt (natEmb pq)]
    [E.HasEdgeMonoAtFrom (natEmb pq) r] [E.HasEdgeEpiAtFrom (natEmb pq) r]
    [(E.natRestrict hE).HasEdgeMonoAtFrom pq r] [(E.natRestrict hE).HasEdgeEpiAtFrom pq r] :
    (natRestrict_pageInfinityIsoAt E hE pq r).hom =
      ((E.natRestrict hE).pageInfinityIso pq r).hom ≫
        (natRestrict_pageXIso E hE pq r (E.le₀_of_hasEdgeEpiAtFrom (natEmb pq) r)).hom ≫
          (E.pageInfinityIso (natEmb pq) r).inv :=
  rfl

/-- **The infinity page transports along the first-quadrant reindexing.**  At `pq : ℕ × ℕ` the
infinity page of `E.natRestrict hE` is the infinity page of `E` at `ComplexShape.natEmb pq`: both
are the common page `E_r` at that bidegree for `r` beyond the stabilisation point of either
sequence, where the page objects agree on the nose because
`HomologicalComplex.natRestrict` is given by `X pq = X (natEmb pq)`.

This is `natRestrict_pageInfinityIsoAt` at the page
`max (E.rMin (natEmb pq)) ((E.natRestrict hE).rMin pq)`, so that there is one comparison and not
two. -/
def natRestrict_pageInfinityIso (pq : ℕ × ℕ) [E.HasPageInfinityAt (natEmb pq)] :
    (E.natRestrict hE).pageInfinity pq ≅ E.pageInfinity (natEmb pq) :=
  letI r := max (E.rMin (natEmb pq)) ((E.natRestrict hE).rMin pq)
  haveI : E.HasEdgeMonoAtFrom (natEmb pq) r := E.hasEdgeMonoAtFrom_of_GE _ _ _ (le_max_left _ _)
  haveI : E.HasEdgeEpiAtFrom (natEmb pq) r := E.hasEdgeEpiAtFrom_of_GE _ _ _ (le_max_left _ _)
  haveI : (E.natRestrict hE).HasEdgeMonoAtFrom pq r :=
    (E.natRestrict hE).hasEdgeMonoAtFrom_of_GE _ _ _ (le_max_right _ _)
  haveI : (E.natRestrict hE).HasEdgeEpiAtFrom pq r :=
    (E.natRestrict hE).hasEdgeEpiAtFrom_of_GE _ _ _ (le_max_right _ _)
  natRestrict_pageInfinityIsoAt E hE pq r

end NatRestrict

section NatRestrictNaturality

variable {r₀ : ℤ} {u : ℤ → ℤ × ℤ} {E E' : SpectralSequence C (fun r => up' (u r)) r₀}
  (f : E ⟶ E') (hE : IsFirstQuadrant E) (hE' : IsFirstQuadrant E')

/-- **The identification of the page objects across the first-quadrant reindexing is natural**:
the component of `natRestrictMap f hE hE'` at `pq` is the component of `f` at
`ComplexShape.natEmb pq`, so the square is the identity square. -/
@[reassoc]
lemma natRestrictMap_pageXIso_naturality (pq : ℕ × ℕ) (r : ℤ) (hr : r₀ ≤ r) :
    ((natRestrictMap f hE hE').hom r hr).f pq ≫ (natRestrict_pageXIso E' hE' pq r hr).hom =
      (natRestrict_pageXIso E hE pq r hr).hom ≫ (f.hom r hr).f (natEmb pq) := by
  change ((natRestrictMap f hE hE').hom r hr).f pq ≫ 𝟙 _ =
    𝟙 _ ≫ (f.hom r hr).f (natEmb pq)
  rw [Category.comp_id, Category.id_comp]
  rfl

/-- **The identification of the infinity pages across the first-quadrant reindexing is natural in
the spectral sequence**, at a page `r` admissible for all four sequences involved.

Both induced maps are computed on the page `r` by
`CategoryTheory.SpectralSequence.Hom.mapPageInfinity_eq`, where they are *the same* morphism: the
component of `natRestrictMap f hE hE'` at `pq` is the component of `f` at
`ComplexShape.natEmb pq`. -/
theorem natRestrict_pageInfinityIsoAt_naturality (pq : ℕ × ℕ) (r : ℤ) (hr : r₀ ≤ r)
    [E.HasPageInfinityAt (natEmb pq)] [E'.HasPageInfinityAt (natEmb pq)]
    [E.HasEdgeMonoAtFrom (natEmb pq) r] [E.HasEdgeEpiAtFrom (natEmb pq) r]
    [E'.HasEdgeMonoAtFrom (natEmb pq) r] [E'.HasEdgeEpiAtFrom (natEmb pq) r]
    [(E.natRestrict hE).HasEdgeMonoAtFrom pq r] [(E.natRestrict hE).HasEdgeEpiAtFrom pq r]
    [(E'.natRestrict hE').HasEdgeMonoAtFrom pq r] [(E'.natRestrict hE').HasEdgeEpiAtFrom pq r] :
    Hom.mapPageInfinity (natRestrictMap f hE hE') pq ≫
        (natRestrict_pageInfinityIsoAt E' hE' pq r).hom =
      (natRestrict_pageInfinityIsoAt E hE pq r).hom ≫ Hom.mapPageInfinity f (natEmb pq) := by
  rw [Hom.mapPageInfinity_eq (natRestrictMap f hE hE') pq r hr,
    Hom.mapPageInfinity_eq f (natEmb pq) r hr, natRestrict_pageInfinityIsoAt_hom,
    natRestrict_pageInfinityIsoAt_hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [natRestrictMap_pageXIso_naturality_assoc f hE hE' pq r hr]

end NatRestrictNaturality

/-! ### The two transports composed -/

section ShiftNatRestrict

variable {r₀ r₁ : ℤ} {u : ℤ → ℤ × ℤ} {E E' : SpectralSequence C (fun r => up' (u r)) r₀}
  (h : r₀ ≤ r₁) (hE : IsFirstQuadrant (E.shiftStart h)) (hE' : IsFirstQuadrant (E'.shiftStart h))

/-- **The infinity page survives both the start-page shift and the first-quadrant reindexing, read
at a supplied page `r`.**

This is `natRestrict_pageInfinityIsoAt` followed by `shiftStart_pageInfinityIsoAt` at one and the
same page.  The shift `h` and the first-quadrant hypothesis `hE` are parameters rather than the
particular `(0 : ℤ) ≤ 2` and `shiftStart_isFirstQuadrant` that `natRestrictE₂Shift` supplies, so
that no proof term is baked into the statement and the two naturality squares below compose by
rewriting. -/
def shiftNatRestrict_pageInfinityIsoAt (pq : ℕ × ℕ) (r : ℤ)
    [E.HasPageInfinityAt (natEmb pq)]
    [E.HasEdgeMonoAtFrom (natEmb pq) r] [E.HasEdgeEpiAtFrom (natEmb pq) r]
    [(E.shiftStart h).HasEdgeMonoAtFrom (natEmb pq) r]
    [(E.shiftStart h).HasEdgeEpiAtFrom (natEmb pq) r]
    [((E.shiftStart h).natRestrict hE).HasEdgeMonoAtFrom pq r]
    [((E.shiftStart h).natRestrict hE).HasEdgeEpiAtFrom pq r] :
    ((E.shiftStart h).natRestrict hE).pageInfinity pq ≅ E.pageInfinity (natEmb pq) :=
  natRestrict_pageInfinityIsoAt (E.shiftStart h) hE pq r ≪≫
    shiftStart_pageInfinityIsoAt E h (natEmb pq) r

/-- **The identification of the infinity pages across the start-page shift followed by the
first-quadrant reindexing is natural in the spectral sequence**, at a page `r` admissible for every
sequence involved.

The two squares of `natRestrict_pageInfinityIsoAt_naturality` and
`shiftStart_pageInfinityIsoAt_naturality`, pasted. -/
theorem shiftNatRestrict_pageInfinityIsoAt_naturality (f : E ⟶ E') (pq : ℕ × ℕ) (r : ℤ)
    (hr : r₁ ≤ r)
    [E.HasPageInfinityAt (natEmb pq)] [E'.HasPageInfinityAt (natEmb pq)]
    [E.HasEdgeMonoAtFrom (natEmb pq) r] [E.HasEdgeEpiAtFrom (natEmb pq) r]
    [E'.HasEdgeMonoAtFrom (natEmb pq) r] [E'.HasEdgeEpiAtFrom (natEmb pq) r]
    [(E.shiftStart h).HasEdgeMonoAtFrom (natEmb pq) r]
    [(E.shiftStart h).HasEdgeEpiAtFrom (natEmb pq) r]
    [(E'.shiftStart h).HasEdgeMonoAtFrom (natEmb pq) r]
    [(E'.shiftStart h).HasEdgeEpiAtFrom (natEmb pq) r]
    [((E.shiftStart h).natRestrict hE).HasEdgeMonoAtFrom pq r]
    [((E.shiftStart h).natRestrict hE).HasEdgeEpiAtFrom pq r]
    [((E'.shiftStart h).natRestrict hE').HasEdgeMonoAtFrom pq r]
    [((E'.shiftStart h).natRestrict hE').HasEdgeEpiAtFrom pq r] :
    Hom.mapPageInfinity (natRestrictMap (shiftStartMap f h) hE hE') pq ≫
        (shiftNatRestrict_pageInfinityIsoAt h hE' pq r).hom =
      (shiftNatRestrict_pageInfinityIsoAt h hE pq r).hom ≫ Hom.mapPageInfinity f (natEmb pq) := by
  rw [shiftNatRestrict_pageInfinityIsoAt, shiftNatRestrict_pageInfinityIsoAt, Iso.trans_hom,
    Iso.trans_hom, ← Category.assoc,
    natRestrict_pageInfinityIsoAt_naturality (shiftStartMap f h) hE hE' pq r hr, Category.assoc,
    shiftStart_pageInfinityIsoAt_naturality f h (natEmb pq) r hr, ← Category.assoc]

end ShiftNatRestrict

/-! ### From a page-zero sequence on `ℤ × ℤ` to a first-quadrant `E₂` sequence -/

section Composite

variable (E : CohomologicalSpectralSequence C 0)
  (hE : IsFirstQuadrant (u := fun r => ((r, 1 - r) : ℤ × ℤ)) E)

/-- **A cohomological spectral sequence starting at the page `0` and lying in the first quadrant,
as a first-quadrant `E₂` cohomological spectral sequence.**  This is the passage from the
presentation in which [Stacks, Tag 012W] and
`CochainComplex.Filtered.nonempty_pageInfinityIso_gr` deliver a spectral sequence to the
presentation a filtered abutment datum asks for. -/
abbrev natRestrictE₂Shift : E₂CohomologicalSpectralSequenceNat C :=
  (E.shiftStart (by omega : (0 : ℤ) ≤ 2)).natRestrict
    (shiftStart_isFirstQuadrant E (by omega) hE)

/-- **The infinity page survives both the start-page shift and the first-quadrant reindexing.**
At `pq : ℕ × ℕ` the infinity page of `natRestrictE₂Shift E hE` is the infinity page of `E` at
`((pq.1 : ℤ), (pq.2 : ℤ))`.

This is the statement that lets `CochainComplex.Filtered.pageInfinityIsoGr` -- which is about a
`CohomologicalSpectralSequence C 0` indexed by `ℤ × ℤ` -- be used as the `gradedIso` field of
`Stacks.Cohomology.Leray.FirstQuadrantAbutment`, which is about a
`CohomologicalSpectralSequenceNat C 2`. -/
def natRestrictE₂Shift_pageInfinityIso (pq : ℕ × ℕ) :
    (natRestrictE₂Shift E hE).pageInfinity pq ≅ E.pageInfinity (natEmb pq) :=
  haveI : E.HasPageInfinityAt (natEmb pq) := hasPageInfinityAt_of_isFirstQuadrant E hE _
  natRestrict_pageInfinityIso _ (shiftStart_isFirstQuadrant E (by omega) hE) pq ≪≫
    shiftStart_pageInfinityIso E (by omega) (natEmb pq)

end Composite

end CategoryTheory.SpectralSequence

end
