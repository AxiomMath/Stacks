module

public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Canonical

/-!
# A page vanishes where the filtration stands still

Let `K^•` be a complex of an abelian category filtered by subcomplexes `F^pK^•`.  Every page of
the spectral sequence of [Stacks, Tag 012M] is the subquotient
`E_r^{p,q} = Z_r^{p,q}/(D_r^{p,q} ⊓ Z_r^{p,q})` of `K^n`, `n = p + q`, where

`Z_r^{p,q} = F^pK^n ⊓ (d^n)^{-1}(F^{p+r}K^{n+1})`,
`D_r^{p,q} = Z_{r-1}^{p+1,q-1} ⊔ d^{n-1}(Z_{r-1}^{p-r+1,n-1})`.

The first summand of `D_r^{p,q}` is `Z_{r-1}^{p+1,q-1} = F^{p+1}K^n ⊓ (d^n)^{-1}(F^{p+r}K^{n+1})`,
because `(p + 1) + (r - 1) = p + r`.  So it is *literally* `Z_r^{p,q}` as soon as
`F^pK^n = F^{p+1}K^n`, and then `Z_r^{p,q} ≤ D_r^{p,q}` and the page vanishes.  No finiteness, no
boundedness, no convergence and no condition on `r` beyond `0 ≤ r` enter; the hypothesis is a
single equality of subobjects of `K^n`, at the one degree `n = p + q`.

This is the standard reason a spectral sequence built from a filtration that is already the whole
complex in nonpositive filtration degrees is concentrated in `p ≥ 0` — one of the clauses of
Quillen's spectral sequence, [Stacks, Tag 08RF].

## Main results

* `CochainComplex.Filtered.isZero_page_of_filtration_eq`: the statement for an arbitrary
  presentation of the pages as cycle-boundary subquotients, in the `(F, Z, D, E, hE)` shape that
  [Stacks, Tag 012M], [Stacks, Tag 012W] and [Stacks, Tag 0132] state their conclusions in.
* `CochainComplex.Filtered.isZero_page_of_filtrationSubobject_eq`: the same for the canonical
  spectral sequence `CochainComplex.Filtered.spectralSequenceFunctor`.
* `CochainComplex.Filtered.isZero_page_of_lt_of_eq_top`: **a filtration which is everything in
  nonpositive filtration degrees gives a spectral sequence concentrated in `p ≥ 0`.**

## Implementation notes

The hypotheses `hZ` and `hD` of `isZero_page_of_filtration_eq` pin `Z` and `D` but nothing pins
`F` beyond them: no `hF` is needed, so the lemma applies to any family of subobjects out of which
cycles and boundaries have been formed in the usual way, whether or not it comes from a filtration
by subcomplexes.

## References

* [Stacks Project, Tag 012M](https://stacks.math.columbia.edu/tag/012M)
* [Stacks Project, Tag 08RF](https://stacks.math.columbia.edu/tag/08RF)
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CochainComplex.Filtered

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- **A page of the spectral sequence of a filtered complex vanishes where the filtration of that
degree does not move.**  If `F^pK^n = F^{p+1}K^n` for `n = p + q`, then `E_r^{p,q} = 0` for every
`r ≥ 0`: the first summand `Z_{r-1}^{p+1,q-1}` of `D_r^{p,q}` is then `Z_r^{p,q}` itself.

The pages are presented as in [Stacks, Tag 012W], by an isomorphism `hE` of each with the
subquotient `Z_r^{p,q}/(D_r^{p,q} ⊓ Z_r^{p,q})`, which is the presentation a consumer of
[Stacks, Tag 012M] already has. -/
theorem isZero_page_of_filtration_eq (K : FilteredObject (CochainComplex C ℤ) ℤᵒᵖ)
    (F : ∀ (_p n : ℤ), Subobject (K.X.X n))
    (Z : ∀ (_r _p n : ℤ), Subobject (K.X.X n))
    (hZ : ∀ r p n : ℤ, Z r p n =
      F p n ⊓ (Subobject.pullback (K.X.d n (n + 1))).obj (F (p + r) (n + 1)))
    (D : ∀ (_r _p n : ℤ), Subobject (K.X.X n))
    (hD : ∀ r p n : ℤ, D r p n = Z (r - 1) (p + 1) n ⊔
      (Subobject.«exists» (K.X.d (n - 1) n)).obj (Z (r - 1) (p - r + 1) (n - 1)))
    (E : CohomologicalSpectralSequence C 0)
    (hE : ∀ (r p q n : ℤ) (hr : 0 ≤ r) (_ : n = p + q), (E.page r hr).X (p, q) ≅
      cokernel (Subobject.ofLE _ _ (inf_le_right : D r p n ⊓ Z r p n ≤ Z r p n)))
    (r p q n : ℤ) (hr : 0 ≤ r) (hn : n = p + q) (h : F p n = F (p + 1) n) :
    IsZero ((E.page r hr).X (p, q)) := by
  refine isZero_page K Z D E hE r p q n hr hn ?_
  rw [hD r p n, hZ r p n, hZ (r - 1) (p + 1) n, h, show p + 1 + (r - 1) = p + r from by ring]
  exact le_sup_left

/-- **`isZero_page_of_filtration_eq` for the canonical spectral sequence of a filtered
complex.**  Its pages are the cycle-boundary subquotients on the nose
(`CochainComplex.Filtered.pageIso`), so the presentation hypotheses are discharged and the
equality of filtration steps is the only one left. -/
theorem isZero_page_of_filtrationSubobject_eq (K : Filtered C) (r p q n : ℤ) (hr : 0 ≤ r)
    (hn : n = p + q)
    (h : filtrationSubobject K p n = filtrationSubobject K (p + 1) n) :
    IsZero (((spectralSequenceFunctor.obj K).page r hr).X (p, q)) :=
  isZero_page_of_filtration_eq K (filtrationSubobject K)
    (FilteredComplexSpectralSequence.cycles K.X (filtrationSubobject K)) (fun _ _ _ => rfl)
    (FilteredComplexSpectralSequence.boundaries K.X (filtrationSubobject K)) (fun _ _ _ => rfl) _
    (fun r p q n hr hn => by subst hn; exact pageIso K r p q hr) r p q n hr hn h

/-- **A filtration which is everything in nonpositive filtration degrees gives a spectral sequence
concentrated in `p ≥ 0`.**  For `p < 0` both `F^pK^n` and `F^{p+1}K^n` are `K^n`, so
`isZero_page_of_filtrationSubobject_eq` applies.

This is the vanishing clause of the `E₁`-page display of [Stacks, Tag 08RG]: the symmetric powers
`Sym^p` which index the columns of Quillen's spectral sequence exist only for `p ≥ 0`. -/
theorem isZero_page_of_lt_of_eq_top (K : Filtered C)
    (h : ∀ p n : ℤ, p ≤ 0 → filtrationSubobject K p n = ⊤)
    (r p q : ℤ) (hr : 0 ≤ r) (hp : p < 0) :
    IsZero (((spectralSequenceFunctor.obj K).page r hr).X (p, q)) :=
  isZero_page_of_filtrationSubobject_eq K r p q (p + q) hr rfl
    ((h p (p + q) (by omega)).trans (h (p + 1) (p + q) (by omega)).symm)

end CochainComplex.Filtered

end
