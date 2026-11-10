module

public import StacksCore.Algebra.Homology.SpectralSequence.PageInfinity
public import StacksFrontier.Algebra.Homology.SpectralSequence.FirstQuadrant

/-!
# The infinity page of the first quadrant repackaging

`StacksFrontier.Algebra.Homology.SpectralSequence.FirstQuadrant` turns a cohomological spectral
sequence `E` indexed by `ℤ × ℤ` whose pages vanish outside the first quadrant into one
indexed by `ℕ × ℕ`, `CategoryTheory.SpectralSequence.firstQuadrantNat E hE`, whose pages are
*literally* the restrictions of the pages of `E` to the first quadrant. This file carries that
repackaging through to the infinity page of
`StacksCore.Algebra.Homology.SpectralSequence.PageInfinity`.

Two things are needed. First, both spectral sequences have an infinity page at every position of
the first quadrant. On the `ℕ × ℕ` side this is already an instance
(`CategoryTheory.CohomologicalSpectralSequenceNat.instHasPageInfinityAt`): the complex shape
`ComplexShape.spectralSequenceNat (r, 1 - r)` simply has no differential into `(p, q)` once
`p < r` nor out of `(p, q)` once `q + 1 < r`, because the source or the target would leave
`ℕ × ℕ`. On the `ℤ × ℤ` side the differentials exist on every page, and what makes them vanish
is the first quadrant hypothesis: the source `(p - r, q + r - 1)` of the differential into
`(p, q)` has negative first coordinate once `p < r`, and the target `(p + r, q + 1 - r)` of the
differential out of `(p, q)` has negative second coordinate once `q + 1 < r`, so the vanishing
of the pages outside the first quadrant, which is what `IsFirstQuadrant` asserts, kills them.
That is `IsFirstQuadrant.hasPageInfinityAt`, and it holds at *every* `pq : ℤ × ℤ`, not only in
the first quadrant.

Second, the two infinity pages agree. Both are a page of the respective spectral sequence at a
position where all differentials into and out of it vanish, and at a position `(p, q)` of the
first quadrant one single page `r` works for both sides, namely any `r` with `p + 1 ≤ r` and
`q + 2 ≤ r`. On that page the two objects are *the same object*
(`CategoryTheory.SpectralSequence.firstQuadrantNat_page_X` is `rfl`), so the comparison is the
composite of the two `pageInfinityIso`s.

## Main definitions

* `CategoryTheory.SpectralSequence.firstQuadrantNatPageXIso`: the identification of a term of a
  page of `firstQuadrantNat E hE` with the corresponding term of the page of `E`. It is
  `Iso.refl`: nothing is transported, the objects are equal by `rfl`.
* `CategoryTheory.SpectralSequence.firstQuadrantNatPageInfinityIsoOfLE`: the comparison of the
  infinity page of `firstQuadrantNat E hE` at `pq : ℕ × ℕ` with the infinity page of `E` at the
  image of `pq`, computed on a page `r` with `pq.1 + 1 ≤ r` and `pq.2 + 2 ≤ r`.
* `CategoryTheory.SpectralSequence.firstQuadrantNatPageInfinityIso`: the same comparison on the
  least such page, `max (pq.1 + 1) (pq.2 + 2)`.

## Main results

* `CategoryTheory.SpectralSequence.IsFirstQuadrant.hasEdgeMonoAt`,
  `CategoryTheory.SpectralSequence.IsFirstQuadrant.hasEdgeEpiAt`: in a first quadrant spectral
  sequence indexed by `ℤ × ℤ`, the differentials into `pq` on the page `r` vanish as soon as
  `pq.1 < r`, and those out of `pq` as soon as `pq.2 + 1 < r`.
* `CategoryTheory.SpectralSequence.IsFirstQuadrant.hasPageInfinityAt`: hence such a spectral
  sequence has an infinity page at every position.
* The `ℕ × ℕ`-indexed repackaging has an infinity page at every position, by instance
  resolution: `StacksCore.Algebra.Homology.SpectralSequence.PageInfinity` has this instance for
  every `CohomologicalSpectralSequenceNat`.
* `CategoryTheory.SpectralSequence.firstQuadrantNatPageInfinityIsoOfLE_hom`: the comparison is,
  by `rfl`, the composite `E_∞ ≅ E_r = E_r ≅ E_∞` of the two `pageInfinityIso`s across the
  identity identification of the two pages.

## Implementation notes

* The edge hypotheses on the `ℤ × ℤ` side are stated with the inequalities `pq.1 < r` and
  `pq.2 + 1 < r` that come out of the proof ("the source has negative first coordinate", "the
  target has negative second coordinate"), while the `ℕ × ℕ` side of
  `StacksCore.Algebra.Homology.SpectralSequence.PageInfinity` is stated with `pq.1 + 1 ≤ r` and
  `pq.2 + 2 ≤ r`. Over `ℤ` these are the same two conditions; the definitions below take the
  second spelling, so that they can be fed to both sides unchanged.
* `IsFirstQuadrant` is a plain `Prop`, not a class, so `HasPageInfinityAt`, `HasEdgeMonoAtFrom`
  and `HasEdgeEpiAtFrom` for the `ℤ × ℤ`-indexed spectral sequence cannot be registered as
  instances; they are lemmas, and the definitions below introduce them with `haveI`. The
  `ℕ × ℕ` side needs no hypothesis at all and is found by instance resolution.
* Nothing in this file carries a `@[stacks]` attribute, for the reason given in
  `StacksFrontier.Algebra.Homology.SpectralSequence.FirstQuadrant`: the content is a comparison of
  two of Mathlib's presentations of a spectral sequence, not a statement of the Stacks project.
-/

@[expose] public section

open CategoryTheory Category Limits ComplexShape HomologicalComplex

namespace CategoryTheory.SpectralSequence

variable {C : Type*} [Category C] [Abelian C] {E : E₂CohomologicalSpectralSequence C}

/-- In a first quadrant cohomological spectral sequence indexed by `ℤ × ℤ`, every differential
into `pq` on the page `r` vanishes as soon as `pq.1 < r`: the source of such a differential is
`(pq.1 - r, pq.2 + r - 1)`, whose first coordinate is negative, so the page vanishes there. -/
lemma IsFirstQuadrant.hasEdgeMonoAt (hE : IsFirstQuadrant E) (pq : ℤ × ℤ) (r : ℤ) (hr : 2 ≤ r)
    (hp : pq.1 < r) : E.HasEdgeMonoAt pq r where
  le := hr
  zero pq' := by
    by_cases h : (ComplexShape.up' ((r, 1 - r) : ℤ × ℤ)).Rel pq' pq
    · rw [ComplexShape.up'_Rel] at h
      subst h
      refine (hE r hr pq' (Or.inl ?_)).eq_of_src _ _
      simp only [Prod.fst_add] at hp
      omega
    · exact (E.page r hr).shape _ _ h

/-- In a first quadrant cohomological spectral sequence indexed by `ℤ × ℤ`, every differential
out of `pq` on the page `r` vanishes as soon as `pq.2 + 1 < r`: the target of such a differential
is `(pq.1 + r, pq.2 + 1 - r)`, whose second coordinate is negative, so the page vanishes
there. -/
lemma IsFirstQuadrant.hasEdgeEpiAt (hE : IsFirstQuadrant E) (pq : ℤ × ℤ) (r : ℤ) (hr : 2 ≤ r)
    (hq : pq.2 + 1 < r) : E.HasEdgeEpiAt pq r where
  le := hr
  zero pq' := by
    by_cases h : (ComplexShape.up' ((r, 1 - r) : ℤ × ℤ)).Rel pq pq'
    · rw [ComplexShape.up'_Rel] at h
      subst h
      refine (hE r hr _ (Or.inr ?_)).eq_of_tgt _ _
      simp only [Prod.snd_add]
      omega
    · exact (E.page r hr).shape _ _ h

/-- A first quadrant cohomological spectral sequence indexed by `ℤ × ℤ` has an infinity page at
every position: the differentials into `pq` vanish from the page `max 2 (pq.1 + 1)` on, and those
out of `pq` from the page `max 2 (pq.2 + 2)` on. -/
lemma IsFirstQuadrant.hasPageInfinityAt (hE : IsFirstQuadrant E) (pq : ℤ × ℤ) :
    E.HasPageInfinityAt pq where
  nonempty_hasEdgeMonoSet :=
    ⟨max 2 (pq.1 + 1), le_max_left _ _, fun r hr =>
      hE.hasEdgeMonoAt pq r (by omega) (by omega)⟩
  nonempty_hasEdgeEpiSet :=
    ⟨max 2 (pq.2 + 2), le_max_left _ _, fun r hr =>
      hE.hasEdgeEpiAt pq r (by omega) (by omega)⟩

/-- In a first quadrant cohomological spectral sequence indexed by `ℤ × ℤ`, all the differentials
into `pq` vanish from the page `r` on as soon as `pq.1 + 1 ≤ r`. -/
lemma IsFirstQuadrant.hasEdgeMonoAtFrom (hE : IsFirstQuadrant E) (pq : ℤ × ℤ) (r : ℤ) (hr : 2 ≤ r)
    (hp : pq.1 + 1 ≤ r) [E.HasPageInfinityAt pq] : E.HasEdgeMonoAtFrom pq r where
  le := E.rToMin_LE pq r ⟨hr, fun r' hr' => hE.hasEdgeMonoAt pq r' (by omega) (by omega)⟩

/-- In a first quadrant cohomological spectral sequence indexed by `ℤ × ℤ`, all the differentials
out of `pq` vanish from the page `r` on as soon as `pq.2 + 2 ≤ r`. -/
lemma IsFirstQuadrant.hasEdgeEpiAtFrom (hE : IsFirstQuadrant E) (pq : ℤ × ℤ) (r : ℤ) (hr : 2 ≤ r)
    (hq : pq.2 + 2 ≤ r) [E.HasPageInfinityAt pq] : E.HasEdgeEpiAtFrom pq r where
  le := E.rFromMin_LE pq r ⟨hr, fun r' hr' => hE.hasEdgeEpiAt pq r' (by omega) (by omega)⟩

/-- A term of a page of the `ℕ × ℕ`-indexed repackaging *is* the corresponding term of the page
of the original `ℤ × ℤ`-indexed spectral sequence: this identification is `Iso.refl`, the two
objects being equal by `rfl` (`firstQuadrantNat_page_X`). -/
noncomputable def firstQuadrantNatPageXIso (E : E₂CohomologicalSpectralSequence C)
    (hE : IsFirstQuadrant E)
    (r : ℤ) (hr : 2 ≤ r) (pq : ℕ × ℕ) :
    ((firstQuadrantNat E hE).page r hr).X pq ≅ (E.page r hr).X ((pq.1 : ℤ), (pq.2 : ℤ)) :=
  Iso.refl _

/-- The isomorphism `firstQuadrantNatPageXIso` is the identity isomorphism. -/
@[simp]
lemma firstQuadrantNatPageXIso_eq_refl (E : E₂CohomologicalSpectralSequence C)
    (hE : IsFirstQuadrant E) (r : ℤ) (hr : 2 ≤ r) (pq : ℕ × ℕ) :
    firstQuadrantNatPageXIso E hE r hr pq = Iso.refl _ := rfl

/-- The infinity page of the first quadrant repackaging at `pq : ℕ × ℕ` is the infinity page of
the original spectral sequence at the image of `pq` in `ℤ × ℤ`. The comparison is computed on a
page `r` late enough that all the differentials into and out of the position have vanished on
both sides, which by `IsFirstQuadrant.hasEdgeMonoAtFrom`, `IsFirstQuadrant.hasEdgeEpiAtFrom`,
`CohomologicalSpectralSequenceNat.hasEdgeMonoAtFrom` and
`CohomologicalSpectralSequenceNat.hasEdgeEpiAtFrom` is the single condition
`pq.1 + 1 ≤ r` and `pq.2 + 2 ≤ r` for both. -/
noncomputable def firstQuadrantNatPageInfinityIsoOfLE (E : E₂CohomologicalSpectralSequence C)
    (hE : IsFirstQuadrant E) (pq : ℕ × ℕ) (r : ℤ) (hp : (pq.1 : ℤ) + 1 ≤ r)
    (hq : (pq.2 : ℤ) + 2 ≤ r) :
    (firstQuadrantNat E hE).pageInfinity pq ≅ E.pageInfinity ((pq.1 : ℤ), (pq.2 : ℤ)) :=
  haveI hr : (2 : ℤ) ≤ r := by omega
  haveI : E.HasPageInfinityAt ((pq.1 : ℤ), (pq.2 : ℤ)) := hE.hasPageInfinityAt _
  haveI : E.HasEdgeMonoAtFrom ((pq.1 : ℤ), (pq.2 : ℤ)) r :=
    hE.hasEdgeMonoAtFrom _ r hr (by change (pq.1 : ℤ) + 1 ≤ r; omega)
  haveI : E.HasEdgeEpiAtFrom ((pq.1 : ℤ), (pq.2 : ℤ)) r :=
    hE.hasEdgeEpiAtFrom _ r hr (by change (pq.2 : ℤ) + 2 ≤ r; omega)
  haveI : (firstQuadrantNat E hE).HasEdgeMonoAtFrom pq r :=
    CohomologicalSpectralSequenceNat.hasEdgeMonoAtFrom _ pq r hp hr
  haveI : (firstQuadrantNat E hE).HasEdgeEpiAtFrom pq r :=
    CohomologicalSpectralSequenceNat.hasEdgeEpiAtFrom _ pq r hq hr
  (firstQuadrantNat E hE).pageInfinityIso pq r ≪≫
    (E.pageInfinityIso ((pq.1 : ℤ), (pq.2 : ℤ)) r).symm

section

variable (E : E₂CohomologicalSpectralSequence C) (hE : IsFirstQuadrant E) (pq : ℕ × ℕ) (r : ℤ)
  (hp : (pq.1 : ℤ) + 1 ≤ r) (hq : (pq.2 : ℤ) + 2 ≤ r)
  [E.HasPageInfinityAt ((pq.1 : ℤ), (pq.2 : ℤ))]
  [E.HasEdgeMonoAtFrom ((pq.1 : ℤ), (pq.2 : ℤ)) r] [E.HasEdgeEpiAtFrom ((pq.1 : ℤ), (pq.2 : ℤ)) r]
  [(firstQuadrantNat E hE).HasEdgeMonoAtFrom pq r]
  [(firstQuadrantNat E hE).HasEdgeEpiAtFrom pq r]

/-- Nothing is transported: the comparison of the two infinity pages is the composite
`E_∞ ≅ E_r = E_r ≅ E_∞` of the two `pageInfinityIso`s, the middle equality being the identity on
one and the same object. -/
lemma firstQuadrantNatPageInfinityIsoOfLE_hom :
    (firstQuadrantNatPageInfinityIsoOfLE E hE pq r hp hq).hom =
      ((firstQuadrantNat E hE).pageInfinityIso pq r).hom ≫
        (E.pageInfinityIso ((pq.1 : ℤ), (pq.2 : ℤ)) r).inv := by
  rfl

/-- The inverse of the comparison of the two infinity pages, as a composite of the two
`pageInfinityIso`s. -/
lemma firstQuadrantNatPageInfinityIsoOfLE_inv :
    (firstQuadrantNatPageInfinityIsoOfLE E hE pq r hp hq).inv =
      (E.pageInfinityIso ((pq.1 : ℤ), (pq.2 : ℤ)) r).hom ≫
        ((firstQuadrantNat E hE).pageInfinityIso pq r).inv := by
  rfl

end

/-- The infinity page of the first quadrant repackaging at `pq : ℕ × ℕ` is the infinity page of
the original spectral sequence at the image of `pq` in `ℤ × ℤ`, computed on the least page
`max (pq.1 + 1) (pq.2 + 2)` on which both sides have stabilised. -/
noncomputable def firstQuadrantNatPageInfinityIso (E : E₂CohomologicalSpectralSequence C)
    (hE : IsFirstQuadrant E) (pq : ℕ × ℕ) :
    (firstQuadrantNat E hE).pageInfinity pq ≅ E.pageInfinity ((pq.1 : ℤ), (pq.2 : ℤ)) :=
  firstQuadrantNatPageInfinityIsoOfLE E hE pq (max ((pq.1 : ℤ) + 1) ((pq.2 : ℤ) + 2))
    (le_max_left _ _) (le_max_right _ _)

/-- `firstQuadrantNatPageInfinityIso` is `firstQuadrantNatPageInfinityIsoOfLE` computed on the page
`max (pq.1 + 1) (pq.2 + 2)`. -/
lemma firstQuadrantNatPageInfinityIso_eq (E : E₂CohomologicalSpectralSequence C)
    (hE : IsFirstQuadrant E) (pq : ℕ × ℕ) :
    firstQuadrantNatPageInfinityIso E hE pq =
      firstQuadrantNatPageInfinityIsoOfLE E hE pq (max ((pq.1 : ℤ) + 1) ((pq.2 : ℤ) + 2))
        (le_max_left _ _) (le_max_right _ _) := rfl

end CategoryTheory.SpectralSequence

end
