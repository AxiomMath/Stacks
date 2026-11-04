module

public import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.Data.Set.Finite.Basic
public import StacksCore.Algebra.Homology.SpectralSequence.PageInfinity

/-!
# Renumbering a spectral sequence

Two renumberings of a spectral sequence are provided.

The first, `CategoryTheory.SpectralSequence.restrictPages`, forgets the pages below some
`r₁ ≥ r₀`. Nothing is changed about the pages that remain, their differentials, or the
identifications of a page with the homology of the previous one.

The second, `CategoryTheory.SpectralSequence.truncationRenumber`, is the change of indexing that
turns the spectral sequence of a canonical truncation filtration into the usual indexing of a
second spectral sequence: the new bidegree `(i, j)` is the old bidegree `(-j, i + 2j)`, and the
new page `r` is the old page `r - 1`. A spectral sequence whose first page is indexed so that
`E_1^{p, q}` involves `H^{-p}` in total degree `p + q` thereby becomes one whose second page
`E_2^{i, j}` involves `H^j` in total degree `i + j`.

The bidegree change is an equivalence of `ℤ × ℤ` carrying the differential shape
`ComplexShape.up' (r, 1 - r)` of the new page `r` to the shape `ComplexShape.up' (r - 1, 2 - r)`
of the old page `r - 1`; the renumbered pages are therefore literally the restrictions of the old
pages along the resulting embedding of complex shapes, and the renumbered object is a
cohomological spectral sequence starting at page two with no further bookkeeping.

Because the renumbered pages are the old pages restricted along an injective bidegree change, the
whole stabilisation apparatus of the infinity page transports across the renumbering with nothing
to prove beyond the bookkeeping of which page one is looking at: the differentials into and out of
`(i, j)` on the new page `r` *are* the differentials into and out of `(-j, i + 2j)` on the old page
`r - 1`, and the two page objects are equal. The last section records this, ending in
`truncationRenumber_pageInfinityIso`, which identifies the two infinity pages, and
`truncationRenumber_finite_not_isZero_page_two`, which carries boundedness in each total degree
across the renumbering (total degree is preserved: `(-j) + (i + 2j) = i + j`).

## Main definitions

* `CategoryTheory.SpectralSequence.restrictPages`: discard the pages below `r₁`.
* `CategoryTheory.SpectralSequence.truncationRenumberingEquiv`: the bidegree change
  `(i, j) ↦ (-j, i + 2j)`.
* `CategoryTheory.SpectralSequence.truncationRenumberingEmbedding`: the same, as an embedding of
  the complex shapes of the two pages it compares.
* `CategoryTheory.SpectralSequence.truncationRenumber`: a cohomological spectral sequence
  beginning at page one, renumbered to begin at page two.

## Main results

* `CategoryTheory.SpectralSequence.truncationRenumberingEquiv_rel`: the bidegree change carries
  the differential shape of page `r` to that of page `r - 1`.
* `CategoryTheory.SpectralSequence.truncationRenumber_hasPageInfinityAt`: the renumbered sequence
  stabilises at `(i, j)` wherever the original one stabilises at `(-j, i + 2j)`.
* `CategoryTheory.SpectralSequence.truncationRenumber_pageInfinityIso`: **the infinity page
  transports along the renumbering**, `E_∞^{i, j}` of the renumbered sequence being
  `E_∞^{-j, i + 2j}` of the original one.
* `CategoryTheory.SpectralSequence.truncationRenumber_finite_not_isZero_page_two`: boundedness in
  each total degree transports along the renumbering.

## Implementation notes

`restrictPages` and `CategoryTheory.SpectralSequence.shiftStart`
(`StacksFrontier/Algebra/Homology/SpectralSequence/ConvergenceNat.lean`) have the same body and are
therefore definitionally equal; the latter lives one import layer further on, which is why this
file states the renumbering against the former.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.SpectralSequence

/-- Forget the pages before `r₁` of a spectral sequence starting at `r₀`. -/
abbrev restrictPages {C : Type*} [Category* C] [Abelian C]
    {κ : Type*} {c : ℤ → ComplexShape κ} {r₀ : ℤ}
    (E : SpectralSequence C c r₀) (r₁ : ℤ) (h : r₀ ≤ r₁) :
    SpectralSequence C c r₁ where
  page r hr := E.page r (h.trans hr)
  iso r r' pq hrr' hr := E.iso r r' pq hrr' (h.trans hr)

/-- The change of bidegree `(i, j) ↦ (-j, i + 2j)` relating the indexing of the spectral sequence
of a canonical truncation filtration to the usual indexing of a second spectral sequence. -/
def truncationRenumberingEquiv : (ℤ × ℤ) ≃ (ℤ × ℤ) where
  toFun ij := (-ij.2, ij.1 + 2 * ij.2)
  invFun pq := (2 * pq.1 + pq.2, -pq.1)
  left_inv ij := by ext <;> dsimp <;> omega
  right_inv pq := by ext <;> dsimp <;> omega

/-- The change of bidegree identifies the differential shape on page `r` with the one on page
`r - 1`. -/
lemma truncationRenumberingEquiv_rel (r : ℤ) (ij ij' : ℤ × ℤ) :
    (ComplexShape.up' (r, 1 - r)).Rel ij ij' ↔
      (ComplexShape.up' (r - 1, 1 - (r - 1))).Rel
        (truncationRenumberingEquiv ij) (truncationRenumberingEquiv ij') := by
  show ij + (r, 1 - r) = ij' ↔ _ + (r - 1, 1 - (r - 1)) = _
  simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, truncationRenumberingEquiv,
    Equiv.coe_fn_mk]
  omega

/-- The change of bidegree as an embedding of the complex shape of page `r` into that of page
`r - 1`. -/
def truncationRenumberingEmbedding (r : ℤ) :
    (ComplexShape.up' (r, 1 - r)).Embedding
      (ComplexShape.up' (r - 1, 1 - (r - 1))) :=
  ComplexShape.Embedding.mk' _ _ truncationRenumberingEquiv
    truncationRenumberingEquiv.injective (truncationRenumberingEquiv_rel r)

/-- The embedding `truncationRenumberingEmbedding r` both preserves and reflects the relation
of the complex shapes. -/
instance truncationRenumberingEmbedding_isRelIff (r : ℤ) :
    (truncationRenumberingEmbedding r).IsRelIff := by
  dsimp [truncationRenumberingEmbedding]
  infer_instance

/-- Renumber a cohomological spectral sequence beginning at page one so that the new page `r` is
the old page `r - 1`, with bidegrees changed by `(i, j) ↦ (-j, i + 2j)`. -/
def truncationRenumber {C : Type*} [Category* C] [Abelian C]
    (E : CohomologicalSpectralSequence C 1) :
    CohomologicalSpectralSequence C 2 := by
  refine
    { page := fun r hr ↦ (E.page (r - 1) (by omega)).restriction
        (truncationRenumberingEmbedding r)
      iso := fun r r' ij hrr' hr ↦ ?_ }
  exact (E.page (r - 1) (by omega)).restrictionHomologyIso
      (truncationRenumberingEmbedding r)
      (ij - (r, 1 - r)) ij (ij + (r, 1 - r))
      (ComplexShape.prev_eq' _ (sub_add_cancel _ _)) (ComplexShape.next_eq' _ rfl) rfl rfl rfl
      (ComplexShape.prev_eq' _ ((truncationRenumberingEmbedding r).rel (sub_add_cancel _ _)))
      (ComplexShape.next_eq' _ ((truncationRenumberingEmbedding r).rel rfl)) ≪≫
    E.iso (r - 1) (r' - 1) (truncationRenumberingEquiv ij) (by omega) (by omega)

/-! ### The infinity page and boundedness across the renumbering -/

section PageInfinity

variable {C : Type*} [Category* C] [Abelian C] (E : CohomologicalSpectralSequence C 1)

/-- The page `r` of the renumbered spectral sequence is the page `r - 1` of the original one,
restricted along the bidegree change. -/
lemma truncationRenumber_page (r : ℤ) (hr : 2 ≤ r) :
    (truncationRenumber E).page r hr =
      (E.page (r - 1) (by omega)).restriction (truncationRenumberingEmbedding r) :=
  rfl

/-- The bidegree change, on an explicit pair. -/
lemma truncationRenumberingEmbedding_f (r i j : ℤ) :
    (truncationRenumberingEmbedding r).f (i, j) = (-j, i + 2 * j) :=
  rfl

/-- **Vanishing of the differentials into a bidegree transports along the renumbering.**  The
differentials into `(i, j)` on the page `r` of the renumbered sequence *are* the differentials
into `(-j, i + 2j)` on the page `r - 1` of the original one, since the new page is the old one
restricted along the bidegree change. -/
lemma truncationRenumber_hasEdgeMonoAt (i j r : ℤ) (hr : 2 ≤ r)
    [E.HasEdgeMonoAt (-j, i + 2 * j) (r - 1)] :
    (truncationRenumber E).HasEdgeMonoAt (i, j) r where
  le := hr
  zero ij' := E.d_eq_zero_of_hasEdgeMonoAt (-ij'.2, ij'.1 + 2 * ij'.2) (-j, i + 2 * j) (r - 1)

/-- **Vanishing of the differentials out of a bidegree transports along the renumbering.**  Dual
to `truncationRenumber_hasEdgeMonoAt`. -/
lemma truncationRenumber_hasEdgeEpiAt (i j r : ℤ) (hr : 2 ≤ r)
    [E.HasEdgeEpiAt (-j, i + 2 * j) (r - 1)] :
    (truncationRenumber E).HasEdgeEpiAt (i, j) r where
  le := hr
  zero ij' := E.d_eq_zero_of_hasEdgeEpiAt (-j, i + 2 * j) (-ij'.2, ij'.1 + 2 * ij'.2) (r - 1)

/-- **The renumbered spectral sequence stabilises wherever the original one does.**  The page from
which the differentials at `(i, j)` have vanished for good is the successor of the one at
`(-j, i + 2j)`, pushed up to at least `2` so as to be admissible. -/
instance truncationRenumber_hasPageInfinityAt (i j : ℤ) [E.HasPageInfinityAt (-j, i + 2 * j)] :
    (truncationRenumber E).HasPageInfinityAt (i, j) where
  nonempty_hasEdgeMonoSet := by
    obtain ⟨r, hr⟩ := E.nonempty_hasEdgeMonoSet (-j, i + 2 * j)
    refine ⟨max 2 (r + 1), le_max_left _ _, fun r' hr' => ?_⟩
    have h : r + 1 ≤ r' := (le_max_right 2 (r + 1)).trans hr'
    have := hr.2 (r' - 1) (by omega)
    exact truncationRenumber_hasEdgeMonoAt E i j r' ((le_max_left 2 (r + 1)).trans hr')
  nonempty_hasEdgeEpiSet := by
    obtain ⟨r, hr⟩ := E.nonempty_hasEdgeEpiSet (-j, i + 2 * j)
    refine ⟨max 2 (r + 1), le_max_left _ _, fun r' hr' => ?_⟩
    have h : r + 1 ≤ r' := (le_max_right 2 (r + 1)).trans hr'
    have := hr.2 (r' - 1) (by omega)
    exact truncationRenumber_hasEdgeEpiAt E i j r' ((le_max_left 2 (r + 1)).trans hr')

/-- **The page object of the renumbered sequence at `(i, j)` is the page object of the original
sequence at `(-j, i + 2j)` one page down**, by definition of `HomologicalComplex.restriction`.

It is *named* rather than left implicit because `truncationRenumber` is a semireducible
definition: a composite that silently crosses the two spellings is well typed only at default
transparency, and `rw` and `simp`, which match at `instances` transparency, then refuse to touch
it.  Mediating every crossing by this isomorphism keeps each composite well typed where the
tactics can see it.  The old page is a separate argument `s` together with `r - 1 = s`, so that a
consumer at a numeral page -- `r = 2`, `s = 1` -- is not left with `2 - 1` to reduce. -/
def truncationRenumber_pageXIso (i j r s : ℤ) (hr : 2 ≤ r) (hs : 1 ≤ s) (hrs : r - 1 = s) :
    ((truncationRenumber E).page r hr).X (i, j) ≅ (E.page s hs).X (-j, i + 2 * j) :=
  eqToIso (by subst hrs; rfl)

/-- **The infinity page transports along the renumbering, read at a supplied pair of pages.**  At
`(i, j)` both sides are the page `s = r - 1` of the original sequence at `(-j, i + 2j)`, the two
spellings of it being mediated by `truncationRenumber_pageXIso`.

As with `CategoryTheory.SpectralSequence.shiftStart_pageInfinityIsoAt`, the page is an argument
rather than a choice, so that one page can serve two spectral sequences at once. -/
def truncationRenumber_pageInfinityIsoAt (i j r s : ℤ) (hr : 2 ≤ r) (hs : 1 ≤ s) (hrs : r - 1 = s)
    [E.HasPageInfinityAt (-j, i + 2 * j)]
    [E.HasEdgeMonoAtFrom (-j, i + 2 * j) s] [E.HasEdgeEpiAtFrom (-j, i + 2 * j) s]
    [(truncationRenumber E).HasPageInfinityAt (i, j)]
    [(truncationRenumber E).HasEdgeMonoAtFrom (i, j) r]
    [(truncationRenumber E).HasEdgeEpiAtFrom (i, j) r] :
    (truncationRenumber E).pageInfinity (i, j) ≅ E.pageInfinity (-j, i + 2 * j) :=
  (truncationRenumber E).pageInfinityIso (i, j) r ≪≫
    truncationRenumber_pageXIso E i j r s hr hs hrs ≪≫
    (E.pageInfinityIso (-j, i + 2 * j) s).symm

/-- **The infinity page transports along the renumbering.**  The term `E_∞^{i, j}` of the
renumbered spectral sequence is the term `E_∞^{-j, i + 2j}` of the original one: both are the
common page `E_s` at `(-j, i + 2j)` for `s` beyond the stabilisation point of either sequence,
where the page objects agree on the nose.

This is `truncationRenumber_pageInfinityIsoAt` at the old page
`max 1 (max (E.rMin (-j, i + 2j)) ((truncationRenumber E).rMin (i, j) - 1))`, so that there is one
comparison and not two. -/
def truncationRenumber_pageInfinityIso (i j : ℤ) [E.HasPageInfinityAt (-j, i + 2 * j)] :
    (truncationRenumber E).pageInfinity (i, j) ≅ E.pageInfinity (-j, i + 2 * j) :=
  letI s : ℤ := max 1 (max (E.rMin (-j, i + 2 * j)) ((truncationRenumber E).rMin (i, j) - 1))
  haveI hs : (1 : ℤ) ≤ s := le_max_left _ _
  haveI hsM : E.rMin (-j, i + 2 * j) ≤ s := (le_max_left _ _).trans (le_max_right _ _)
  haveI hsR : (truncationRenumber E).rMin (i, j) - 1 ≤ s :=
    (le_max_right _ _).trans (le_max_right _ _)
  haveI : E.HasEdgeMonoAtFrom (-j, i + 2 * j) s :=
    E.hasEdgeMonoAtFrom_of_GE (-j, i + 2 * j) (E.rMin (-j, i + 2 * j)) s hsM
  haveI : E.HasEdgeEpiAtFrom (-j, i + 2 * j) s :=
    E.hasEdgeEpiAtFrom_of_GE (-j, i + 2 * j) (E.rMin (-j, i + 2 * j)) s hsM
  haveI : (truncationRenumber E).HasEdgeMonoAtFrom (i, j) (s + 1) :=
    (truncationRenumber E).hasEdgeMonoAtFrom_of_GE (i, j)
      ((truncationRenumber E).rMin (i, j)) (s + 1) (by omega)
  haveI : (truncationRenumber E).HasEdgeEpiAtFrom (i, j) (s + 1) :=
    (truncationRenumber E).hasEdgeEpiAtFrom_of_GE (i, j)
      ((truncationRenumber E).rMin (i, j)) (s + 1) (by omega)
  truncationRenumber_pageInfinityIsoAt E i j (s + 1) s (by omega) hs (by omega)

/-- **Boundedness in each total degree transports along the renumbering.**  The term of total
degree `n` at `(i, n - i)` on the second page of the renumbered sequence is the term at
`(i - n, n - (i - n))` on the first page of the original one, so the set of bidegrees of total
degree `n` carrying a nonzero term is the translate by `n` of the original one, and in particular
is finite as soon as the original one is. -/
lemma truncationRenumber_finite_not_isZero_page_two
    (h : ∀ n : ℤ, {p : ℤ | ¬ IsZero ((E.page 1 le_rfl).X (p, n - p))}.Finite) (n : ℤ) :
    {i : ℤ | ¬ IsZero (((truncationRenumber E).page 2 (by omega)).X (i, n - i))}.Finite := by
  refine Set.Finite.subset ((h n).preimage (f := fun i : ℤ => i - n) ?_) ?_
  · intro a _ b _ hab
    have hab' : a - n = b - n := hab
    omega
  · intro i hi hz
    have hpair : ((-(n - i) : ℤ), i + 2 * (n - i)) = ((i - n : ℤ), n - (i - n)) := by
      simp only [Prod.mk.injEq]
      omega
    exact hi (IsZero.of_iso hz
      (truncationRenumber_pageXIso E i (n - i) 2 1 (by omega) le_rfl (by omega) ≪≫
        eqToIso (congrArg (E.page 1 le_rfl).X hpair)))

end PageInfinity

end CategoryTheory.SpectralSequence
