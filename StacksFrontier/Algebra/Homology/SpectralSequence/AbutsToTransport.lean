module

public import StacksCore.CategoryTheory.Abelian.Subobject
public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsTo
public import StacksFrontier.Algebra.Homology.SpectralSequence.Renumbering

/-!
# Transporting an abutment along an isomorphism or a change of indexing

`CategoryTheory.SpectralSequence.AbutsTo E H` asserts that some finite decreasing filtration of
each `H n` has the terms `E_∞^{p,n-p}` of the infinity page as its graded pieces.  The family `H`
occurs in that statement only through subobjects of `H n` and the cokernels of the inclusions
between them, so an isomorphism `H n ≅ H' n` in each degree should carry the assertion from `H`
to `H'`.  This file proves that it does.

The second transport is along a change of *indexing* rather than of abutment:
`CategoryTheory.SpectralSequence.truncationRenumber`
(`StacksFrontier/Algebra/Homology/SpectralSequence/Renumbering.lean`) replaces the bidegree `(p, q)`
by `(i, j)` with `(p, q) = (-j, i + 2j)` and the page `r` by `r + 1`.  Total degree is unchanged,
`(-j) + (i + 2j) = i + j`, so the *same* family `H` is abutted to; what moves is the index of the
filtration, since the filtration of `H n` is indexed by the first bidegree coordinate and that
coordinate is `p = -j = i - n` before the renumbering and `i` after it.  The transported
filtration is therefore `(n, i) ↦ F n (i - n)`, a translation in each total degree, which is again
decreasing and again reaches `⊤` and `⊥`; the graded pieces are literally the old ones, and the
infinity pages are identified by
`CategoryTheory.SpectralSequence.truncationRenumber_pageInfinityIso`.

The one piece the transport needs beyond `Subobject.mapIsoToOrderIso` -- which moves the
filtration itself -- is the **compatibility of `Subobject.ofLE` with `Subobject.map`**: pushing
two nested subobjects `X₁ ≤ X₂` of `Y` forward along a monomorphism `n : Y ⟶ A` carries the
inclusion `X₁ ⟶ X₂` to the inclusion `n(X₁) ⟶ n(X₂)`, under the identifications
`Stacks.CategoryTheory.Subobject.mapObjIso` of the underlying objects.  That square is
`CategoryTheory.Subobject.ofLE_map_comp_mapObjIso_hom` here.  It is general category theory --
no additivity, no abelianness, only `Mono n` -- and is absent from Mathlib at the pinned
revision, where the `Subobject.map`/`Subobject.ofLE` interface stops at `Subobject.map_mk`,
`Subobject.map_obj_injective` and `Subobject.mapIsoToOrderIso`.

Its cokernel-level consequence is *not* new: `CategoryTheory.Abelian.Subobject.cokernelOfLEMapIso`
of `StacksCore/CategoryTheory/Abelian/Subobject.lean` already builds `n(X₂)/n(X₁) ≅ X₂/X₁` in an
abelian category, with the square inlined anonymously in its proof.  The transport below uses
that iso; naming the square records the general statement the iso rests on.

## Main results

* `CategoryTheory.Subobject.ofLE_map_comp_mapObjIso_hom`: `Subobject.ofLE` commutes with
  `Subobject.map` along a monomorphism, under `mapObjIso`.
* `CategoryTheory.SpectralSequence.AbutsTo.of_iso`: **abutment transports along a degreewise
  isomorphism of the abutment family.**
* `CategoryTheory.SpectralSequence.AbutsTo.of_nonempty_iso`: the same from merely nonempty
  isomorphism types, which is the form in which [Stacks, Tag 015N] delivers its identification
  of `H^n(K)` with `H^n(R(G ∘ F)(X))`.
* `CategoryTheory.SpectralSequence.AbutsTo.truncationRenumber`: **abutment transports along the
  truncation renumbering** `(i, j) ↦ (-j, i + 2j)`, to the same abutment family.
* `CategoryTheory.SpectralSequence.AbutsTo.restrictPages`,
  `CategoryTheory.SpectralSequence.AbutsTo.truncationRenumberRestrictPages`: the same after
  discarding the pages below the first, which is the shape in which the renumbering of a
  filtered-complex spectral sequence is taken.

## Implementation notes

* The transported filtration is `fun n p => (Subobject.map (e n).hom).obj (F n p)`.  It reaches
  `⊤` and `⊥` at the same indices as `F` because `Subobject.map_top` together with
  `Subobject.mk_eq_top_of_isIso` sends `⊤` to `⊤` for an isomorphism, and `Subobject.map_bot`
  sends `⊥` to `⊥` for any monomorphism.
* No compatibility between the identifications at two degrees is asked for, and none is
  produced: `AbutsTo` is a proposition whose witnessing isomorphisms are existentially
  quantified, so the transport composes the given `e n` with a chosen witness degreewise.

## References

* [Stacks Project, Tag 01F2](https://stacks.math.columbia.edu/tag/01F2)
* [Stacks Project, Tag 015N](https://stacks.math.columbia.edu/tag/015N)
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Subobject

variable {C : Type u} [Category.{v} C]

/-- **`Subobject.ofLE` is compatible with `Subobject.map`.**  For nested subobjects `X₁ ≤ X₂` of
`Y` and a monomorphism `n : Y ⟶ A`, the inclusion of the pushed-forward subobjects
`n(X₁) ⟶ n(X₂)` agrees with the inclusion `X₁ ⟶ X₂` under the identifications
`Stacks.CategoryTheory.Subobject.mapObjIso` of underlying objects:

```
n(X₁) --ofLE--> n(X₂)
  |               |
mapObjIso      mapObjIso
  v               v
 X₁  ---ofLE-->  X₂
```

This is the square `Subobject.mapIsoToOrderIso` leaves unproved: that order isomorphism moves
subobjects along an isomorphism of ambient objects but says nothing about the morphisms
witnessing inequalities, which is what a construction depending on `ofLE` -- a subquotient, say
-- has to move.  Its cokernel-level consequence in an abelian category is
`CategoryTheory.Abelian.Subobject.cokernelOfLEMapIso`. -/
@[reassoc]
lemma ofLE_map_comp_mapObjIso_hom {Y A : C} (n : Y ⟶ A) [Mono n] {X₁ X₂ : Subobject Y}
    (h : X₁ ≤ X₂) :
    ofLE _ _ ((map n).monotone h) ≫ (mapObjIso n X₂).hom =
      (mapObjIso n X₁).hom ≫ ofLE X₁ X₂ h := by
  rw [← cancel_mono (X₂.arrow ≫ n), Category.assoc, Category.assoc, ofLE_arrow_assoc,
    mapObjIso_hom_arrow, mapObjIso_hom_arrow, ofLE_arrow]

end CategoryTheory.Subobject

namespace CategoryTheory.SpectralSequence

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- **Abutment transports along a degreewise isomorphism of the abutment family.**  If a
cohomological spectral sequence `E` abuts to `H` and `e n : H n ≅ H' n` for every `n`, then `E`
abuts to `H'`.

The witnessing filtration is the image of the one for `H` under `Subobject.map (e n).hom`, which
is an order isomorphism of subobject lattices (`Subobject.mapIsoToOrderIso`), so it is again
decreasing and again reaches `⊤` and `⊥`; its graded pieces are identified with those of the
original filtration by `CategoryTheory.Abelian.Subobject.cokernelOfLEMapIso`, whose underlying
compatibility is `CategoryTheory.Subobject.ofLE_map_comp_mapObjIso_hom`. -/
theorem AbutsTo.of_iso {r₀ : ℤ} {E : CohomologicalSpectralSequence C r₀} {H H' : ℤ → C}
    (hE : AbutsTo E H) (e : ∀ n : ℤ, H n ≅ H' n) : AbutsTo E H' := by
  obtain ⟨hinf, F, hF, hbounds, hgr⟩ := hE
  refine ⟨hinf, fun n p => (Subobject.map (e n).hom).obj (F n p),
    fun n _ _ hpq => (Subobject.map (e n).hom).monotone (hF n hpq), fun n => ?_, fun p q => ?_⟩
  · obtain ⟨a, b, hab, ha, hb⟩ := hbounds n
    refine ⟨a, b, hab, ?_, ?_⟩
    · change (Subobject.map (e n).hom).obj (F n a) = ⊤
      rw [ha, Subobject.map_top, Subobject.mk_eq_top_of_isIso]
    · change (Subobject.map (e n).hom).obj (F n b) = ⊥
      rw [hb, Subobject.map_bot]
  · exact ⟨(hgr p q).some ≪≫
      (Abelian.Subobject.cokernelOfLEMapIso (e (p + q)).hom (hF (p + q) (by omega))).symm⟩

/-- **Abutment transports along a degreewise nonempty isomorphism type.**  This is the form the
identifications of [Stacks, Tag 015N] come in: that statement concludes
`∀ n, Nonempty (H^n(K) ≅ H^n(R(G ∘ F)(X)))`, with no compatibility between the identifications
at two degrees, which is exactly what `AbutsTo` needs and no more. -/
theorem AbutsTo.of_nonempty_iso {r₀ : ℤ} {E : CohomologicalSpectralSequence C r₀} {H H' : ℤ → C}
    (hE : AbutsTo E H) (e : ∀ n : ℤ, Nonempty (H n ≅ H' n)) : AbutsTo E H' :=
  hE.of_iso fun n => (e n).some

/-- **Abutment transports along the truncation renumbering.**  If a cohomological spectral
sequence beginning at page one abuts to `H`, so does its renumbering, whose bidegree `(i, j)` is
the old bidegree `(-j, i + 2j)` and whose page `r` is the old page `r - 1`.

The abutment family is unchanged because the renumbering preserves total degree,
`(-j) + (i + 2j) = i + j`.  What changes is the indexing of the filtration of `H n`, which in
`AbutsTo` is by the first bidegree coordinate: that coordinate is `i - n` before the renumbering
and `i` after it, so the witnessing filtration is the translate `(n, i) ↦ F n (i - n)` of the
given one.  The graded pieces are then the same subquotients of `H n` as before, and the infinity
pages are identified by
`CategoryTheory.SpectralSequence.truncationRenumber_pageInfinityIso`. -/
theorem AbutsTo.truncationRenumber {E : CohomologicalSpectralSequence C 1} {H : ℤ → C}
    (hE : AbutsTo E H) : AbutsTo E.truncationRenumber H := by
  obtain ⟨hinf, F, hF, hbounds, hgr⟩ := hE
  have hinf' : ∀ i j : ℤ, E.truncationRenumber.HasPageInfinityAt (i, j) := by
    intro i j
    have := hinf (-j) (i + 2 * j)
    exact truncationRenumber_hasPageInfinityAt E i j
  have hgr' : ∀ (p q n a b : ℤ) (_ : n = p + q) (ha : a = p + 1) (hb : b = p),
      Nonempty (E.pageInfinity (p, q) ≅
        cokernel (Subobject.ofLE (F n a) (F n b) (hF n (by omega)))) := by
    intro p q n a b hn ha hb
    subst hn
    subst ha
    subst hb
    exact hgr _ _
  refine ⟨hinf', fun n s => F n (s - n), fun n s s' hss' => hF n (by omega), fun n => ?_, ?_⟩
  · obtain ⟨a, b, hab, ha, hb⟩ := hbounds n
    exact ⟨a + n, b + n, by omega, by simpa using ha, by simpa using hb⟩
  · intro i j
    have := hinf (-j) (i + 2 * j)
    exact ⟨truncationRenumber_pageInfinityIso E i j ≪≫
      (hgr' (-j) (i + 2 * j) (i + j) (i + 1 - (i + j)) (i - (i + j))
        (by omega) (by omega) (by omega)).some⟩

/-- **Abutment is unaffected by discarding the pages below `r₁`.**  `restrictPages` and
`CategoryTheory.SpectralSequence.shiftStart` have the same body and are therefore definitionally
equal, so this is `CategoryTheory.SpectralSequence.AbutsTo.shiftStart` read on the spelling that
`CategoryTheory.SpectralSequence.truncationRenumber` consumes. -/
theorem AbutsTo.restrictPages {r₀ r₁ : ℤ} {E : CohomologicalSpectralSequence C r₀} {H : ℤ → C}
    (hE : AbutsTo E H) (h : r₀ ≤ r₁) : AbutsTo (E.restrictPages r₁ h) H :=
  hE.shiftStart h

/-- **Abutment transports along the truncation renumbering of a sequence read from its first
page.**  This is the composite of `AbutsTo.restrictPages` and `AbutsTo.truncationRenumber`, in the
shape taken by the renumbering of the spectral sequence of a filtered complex -- which begins at
page zero, while the renumbering is of the sequence read from page one. -/
theorem AbutsTo.truncationRenumberRestrictPages {r₀ : ℤ} {E : CohomologicalSpectralSequence C r₀}
    {H : ℤ → C} (hE : AbutsTo E H) (h : r₀ ≤ 1) :
    AbutsTo (E.restrictPages 1 h).truncationRenumber H :=
  (hE.restrictPages h).truncationRenumber

end CategoryTheory.SpectralSequence

end
